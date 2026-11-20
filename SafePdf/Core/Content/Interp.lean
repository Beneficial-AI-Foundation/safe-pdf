import SafePdf.Core.Content.Ops
import SafePdf.Core.Content.DisplayList

/-!
# Content-stream interpreter core (Plan.md §6 Phase 5, §3 C6)

Runs the operators produced by `Core.Content.Ops.tokenize` through the graphics state machine
of `Core.Content.GState` and emits the typed `DisplayList` (task 5.2a). ISO 32000-2
references: §8.2 and Annex A (operator table), §8.4.4 (graphics state operators), §8.5 (path
construction and painting), §8.6.8 (colour operators), §9.3–9.4 (text state, text objects,
text showing), §8.9.7 (inline images), §14.6 (marked content), §7.8.2 (`BX`/`EX`).

## Design decisions

* **Total by construction, never fails** (M5). `interp` is an `Array.foldl` of `exec` over
  the operators. Malformed operands (too few, wrong type, invalid enumerations such as `5 J`)
  skip the operator and count one warning; when there are too many operands the **last**
  `n` are used (as pdf.js and MuPDF do). Unknown operators emit `DisplayItem.unsupported`
  (for the M5 coverage report) and count in `Result.unsupported`; outside `BX … EX` they also
  count a warning (§7.8.2: inside a compatibility section they are ignored silently).
* **State** (`Machine`): `Core` (`GState`, `TextMatrices`, the current path in page space with
  its current point and subpath start, the in-text flag and the `BX` depth), the `q`/`Q`
  stack and the pending clip set by `W`/`W*`. The stack and the pending clip live outside
  `Core`, so every "simple" operator leaves them unchanged by construction.
* **`q` at `Limits.maxGStateDepth`** is skipped with a warning (consistent with "never
  fail"); the matching `Q` then restores the outer state, as an unbalanced `Q` on an empty
  stack is ignored (`GStack.restore`) with a warning.
* **Paths and clipping**: points are mapped to page space with the CTM when the segment is
  built; `re` → `moveTo` + 3 `lineTo` + `closePath`, `v`/`y` → `curveTo`. `l`, `c`, `v`, `y`
  without a current point are skipped (warning). A painting operator (`S s f F f* B B* b b*
  n`) emits `Paint.items` for a non-empty path (with the clip in force *before* it), then, if
  `W`/`W*` was pending, intersects the clip and emits a `clip` item; the path is then cleared.
  So one operator can emit 3 items (`W … b`), but the `W` itself emitted none: the potential
  `items + [clip pending]` grows by at most `Paint.maxItems` per operator, which gives
  `interp_items_le`.
* **Colour**: `CS`/`cs` map `DeviceGray`/`G`, `DeviceRGB`/`RGB`, `DeviceCMYK`/`CMYK` and
  `Pattern`; any other name is a resource (`ColorSpace.other name 0 .gray`, `0` = component
  count unknown until 5.2b resolves `/Resources /ColorSpace`) and `SC`/`sc`/`SCN`/`scn` on it
  keep the alternate's initial colour. Components are clamped (`Comp.ofFixed`). `G g RG rg K k`
  also set the device space.
* **Text**: `Tj`/`TJ`/`'`/`"` emit one `glyphRun` (needs a font from `Tf`, else skipped with a
  warning) and advance `Tm` by `tx`: per string, `Config.advance` (the font-metric advance in
  text space, including `Tc`/`Tw`/`Tz`; the default stub returns 0); per `TJ` number `a`,
  `-(a / 1000) · Tfs · Th` exactly as §9.4.4 states. Text operators outside `BT … ET` are
  executed but warned.
* **Ignored without warning**: `gs` (ExtGState resolution is 5.2b), `d0`/`d1`, marked content
  `BMC BDC EMC MP DP`. `ri`/`i` are recorded in the `GState`.
* **XObjects, shadings, inline images**: `Do` emits a placeholder
  `image (.xobject name 0 0)` (5.2b resolves it to an image or expands a form); `sh` a
  `shading` item (resource `.page`, resolved by 5.2b; with the fill snapshot for `ca`, blend
  mode and soft mask, task 7.3f); `BI` an `image (.inline dict data)` item with the raw data.
-/

namespace SafePdf.Core.Content

open SafePdf

/-- Interpreter configuration. -/
structure Config where
  /-- Resource limits (`maxGStateDepth`). -/
  limits : Limits := {}
  /-- Horizontal displacement, in text space, of showing a string with the given text state
  (font metrics, `Tc`, `Tw`, `Tz`; ISO 32000-2 §9.4.4). Phase 6 supplies real widths; the
  default stub returns 0. -/
  advance : TextState → List UInt8 → Fixed := fun _ _ => Fixed.zero

instance : Inhabited Config := ⟨{}⟩

/-- The interpreter state except the `q`/`Q` stack and the pending clip. -/
structure Core where
  /-- The graphics state. -/
  gs : GState := {}
  /-- `Tm`/`Tlm`. -/
  tm : TextMatrices := {}
  /-- The current path, in page space. -/
  path : Path := {}
  /-- The current point, in page space. -/
  cur : Option Point := none
  /-- Start of the current subpath, in page space. -/
  start : Option Point := none
  /-- Inside `BT … ET`. -/
  inText : Bool := false
  /-- Nesting depth of `BX … EX`. -/
  bxDepth : Nat := 0
  deriving Inhabited

/-- Pattern-colour bookkeeping of one painting mode (task 7.3f), maintained by the resource
runner (5.2b), never by `exec`: the `/ColorSpace` resource name of the current pattern space
(`[/Pattern base]` spaces), and the underlying colour the last `SCN`/`scn` gave an uncoloured
(PaintType 2) pattern, with that pattern's name. Not saved by `q`/`Q` (consumers check the
name against the current colour). -/
structure PatState where
  /-- Resource name of the current pattern colour space, if it was named. -/
  space : Option Name := none
  /-- Pattern name and underlying colour of the last `SCN`/`scn` with colour operands. -/
  under : Option (Name × Color) := none
  deriving Inhabited

/-- The full interpreter state. -/
structure Machine where
  /-- Everything but the stack and pending clip. -/
  core : Core := {}
  /-- Saved graphics states (`q`). -/
  stack : GStack := {}
  /-- Clip rule set by `W`/`W*`, applied at the next painting operator. -/
  pending : Option FillRule := none
  /-- Pattern bookkeeping for filling (task 7.3f; runner only). -/
  patFill : PatState := {}
  /-- Pattern bookkeeping for stroking (task 7.3f; runner only). -/
  patStroke : PatState := {}
  deriving Inhabited

/-- Interpreter output. -/
structure Result where
  /-- The display list. -/
  items : DisplayList := #[]
  /-- Recovered malformations. -/
  warnings : Nat := 0
  /-- Number of unknown operators (each also an `unsupported` item). -/
  unsupported : Nat := 0
  deriving Inhabited

namespace Interp

/-! ## Operands -/

/-- A numeric operand. -/
def num? : PdfObject → Option Fixed
  | .int i => some (Fixed.ofInt i)
  | .real d => some (Fixed.ofDecimal d)
  | _ => none

/-- A nonnegative integer operand. -/
def nat? : PdfObject → Option Nat
  | .int i => if 0 ≤ i then some i.toNat else none
  | _ => none

/-- The last `n` operands, if there are at least `n`. -/
def lastN (n : Nat) (o : List PdfObject) : Option (List PdfObject) :=
  if n ≤ o.length then some (o.drop (o.length - n)) else none

/-- The last `n` operands, all numeric. -/
def nums (n : Nat) (o : List PdfObject) : Option (List Fixed) :=
  match lastN n o with
  | some xs => xs.mapM num?
  | none => none

/-- The last operand, if a name. -/
def lastName? (o : List PdfObject) : Option Name :=
  match o.getLast? with
  | some (.name n) => some n
  | _ => none

/-- The last operand, if a string. -/
def lastString? (o : List PdfObject) : Option (List UInt8) :=
  match o.getLast? with
  | some (.string s) => some s
  | _ => none

/-! ## Output of one simple operator -/

/-- New core, at most one item, warnings, unknown-operator count. -/
abbrev Out := Core × Option DisplayItem × Nat × Nat

/-- Done, no item, no warning. -/
def ok (c : Core) : Out := (c, none, 0, 0)

/-- Skipped: state unchanged, one warning. -/
def bad (c : Core) : Out := (c, none, 1, 0)

/-! ## Graphics state helpers -/

/-- Replace the graphics state (no path array is touched). -/
def setGs (c : Core) (g : GState) : Core := { c with gs := g }

/-- Replace the text state. -/
def setText (c : Core) (t : TextState) : Core := setGs c { c.gs with text := t }

/-- Replace the line style. -/
def setLine (c : Core) (l : LineStyle) : Core := setGs c { c.gs with line := l }

/-! ## Colour -/

/-- A device colour from exactly its components (clamped). -/
def deviceColor (s : DeviceSpace) (xs : List Fixed) : Option Color :=
  match s, xs with
  | .gray, [g] => some (.gray (Comp.ofFixed g))
  | .rgb, [r, g, b] => some (.rgb (Comp.ofFixed r) (Comp.ofFixed g) (Comp.ofFixed b))
  | .cmyk, [c, m, y, k] =>
    some (.cmyk (Comp.ofFixed c) (Comp.ofFixed m) (Comp.ofFixed y) (Comp.ofFixed k))
  | _, _ => none

/-- The colour space named by a `CS`/`cs` operand (device families and `Pattern`; any other
name is a resource, resolved in 5.2b). -/
def spaceOfName (n : Name) : ColorSpace :=
  if n = Name.ofString "DeviceGray" || n = Name.ofString "G" then .device .gray
  else if n = Name.ofString "DeviceRGB" || n = Name.ofString "RGB" then .device .rgb
  else if n = Name.ofString "DeviceCMYK" || n = Name.ofString "CMYK" then .device .cmyk
  else if n = Name.ofString "Pattern" then .pattern
  else .other n 0 .gray

/-- The colour set by `SC`/`sc`/`SCN`/`scn` in space `sp`. -/
def colorIn (sp : ColorSpace) (o : List PdfObject) : Option Color :=
  match sp with
  | .device s =>
    match nums s.nComps o with
    | some xs => deviceColor s xs
    | none => none
  | .pattern =>
    match lastName? o with
    | some n => some (.pattern n)
    | none => none
  | .other _ _ alt => some alt.initialColor

/-- Set the stroking (`stroke = true`) or non-stroking colour space and colour. -/
def setColor (c : Core) (stroke : Bool) (sp : ColorSpace) (col : Color) : Core :=
  if stroke then setGs c { c.gs with strokeSpace := sp, strokeColor := col }
  else setGs c { c.gs with fillSpace := sp, fillColor := col }

/-- `G`/`g`/`RG`/`rg`/`K`/`k`: device space and colour from operands. -/
def deviceOp (c : Core) (stroke : Bool) (s : DeviceSpace) (o : List PdfObject) : Out :=
  match nums s.nComps o with
  | some xs =>
    match deviceColor s xs with
    | some col => ok (setColor c stroke (.device s) col)
    | none => bad c
  | none => bad c

/-- `SC`/`sc`/`SCN`/`scn`. -/
def colorOp (c : Core) (stroke : Bool) (o : List PdfObject) : Out :=
  let sp := if stroke then c.gs.strokeSpace else c.gs.fillSpace
  match colorIn sp o with
  | some col => ok (setColor c stroke sp col)
  | none => bad c

/-- `CS`/`cs`. -/
def spaceOp (c : Core) (stroke : Bool) (o : List PdfObject) : Out :=
  match lastName? o with
  | some n =>
    let sp := spaceOfName n
    ok (setColor c stroke sp sp.initialColor)
  | none => bad c

/-! ## Paths -/

/-- Append segments, moving the current point and subpath start. The core is destructured
first so the path array stays unshared and is extended in place. -/
def addSegs (c : Core) (segs : List Segment) (cur start : Option Point) : Core :=
  match c with
  | ⟨gs, tm, path, _, _, it, bx⟩ => ⟨gs, tm, ⟨segs.foldl Array.push path.segs⟩, cur, start, it, bx⟩

/-- A user-space point mapped to page space by the CTM. -/
def pt (c : Core) (x y : Fixed) : Point := Matrix.apply c.gs.ctm ⟨x, y⟩

/-- Path construction operators `m l c v y h re` (`code` selects which). -/
def pathOp (c : Core) (code : Nat) (o : List PdfObject) : Out :=
  match code with
  | 0 => -- m
    match nums 2 o with
    | some [x, y] => let p := pt c x y; ok (addSegs c [.moveTo p] (some p) (some p))
    | _ => bad c
  | 1 => -- l
    match nums 2 o, c.cur with
    | some [x, y], some _ => let p := pt c x y; ok (addSegs c [.lineTo p] (some p) c.start)
    | _, _ => bad c
  | 2 => -- c
    match nums 6 o, c.cur with
    | some [x1, y1, x2, y2, x3, y3], some _ =>
      let p := pt c x3 y3
      ok (addSegs c [.curveTo (pt c x1 y1) (pt c x2 y2) p] (some p) c.start)
    | _, _ => bad c
  | 3 => -- v
    match nums 4 o, c.cur with
    | some [x2, y2, x3, y3], some q =>
      let p := pt c x3 y3
      ok (addSegs c [.curveTo q (pt c x2 y2) p] (some p) c.start)
    | _, _ => bad c
  | 4 => -- y
    match nums 4 o, c.cur with
    | some [x1, y1, x3, y3], some _ =>
      let p := pt c x3 y3
      ok (addSegs c [.curveTo (pt c x1 y1) p p] (some p) c.start)
    | _, _ => bad c
  | 5 => -- h
    match c.cur with
    | some _ => ok (addSegs c [.closePath] c.start c.start)
    | none => ok c
  | _ => -- re
    match nums 4 o with
    | some [x, y, w, h] =>
      let p0 := pt c x y
      let x1 := Fixed.add x w
      let y1 := Fixed.add y h
      ok (addSegs c [.moveTo p0, .lineTo (pt c x1 y), .lineTo (pt c x1 y1),
        .lineTo (pt c x y1), .closePath] (some p0) (some p0))
    | _ => bad c

/-! ## Text -/

/-- `Td`: `Tlm := translate(tx, ty) × Tlm`, `Tm := Tlm`. -/
def moveText (c : Core) (tx ty : Fixed) : Core :=
  let tlm := Matrix.mul (Matrix.translate tx ty) c.tm.tlm
  { c with tm := ⟨tlm, tlm⟩ }

/-- `T*`: `0 -TL Td`. -/
def nextLine (c : Core) : Core := moveText c Fixed.zero (Fixed.neg c.gs.text.leading)

/-- Horizontal displacement of a `TJ` number `a`: `-(a / 1000) · Tfs · Th`. -/
def adjustTx (t : TextState) (size a : Fixed) : Fixed :=
  let th := Fixed.div t.horizScaling (Fixed.ofInt 100)
  Fixed.mul (Fixed.mul (Fixed.neg (Fixed.div a (Fixed.ofInt 1000))) size) th

/-- Total horizontal displacement of a run. -/
def runTx (cfg : Config) (t : TextState) (size : Fixed) : List TextPart → Fixed
  | [] => Fixed.zero
  | .str s :: rest => Fixed.add (cfg.advance t s) (runTx cfg t size rest)
  | .adjust a :: rest => Fixed.add (adjustTx t size a) (runTx cfg t size rest)

/-- Emit a glyph run for `parts` and advance `Tm`. Needs a font (`Tf`). -/
def showText (cfg : Config) (c : Core) (parts : List TextPart) (w : Nat) : Out :=
  match c.gs.text.font with
  | none => bad c
  | some f =>
    let t := c.gs.text
    let run : GlyphRun :=
      { font := f, tm := c.tm.tm, ctm := c.gs.ctm, charSpacing := t.charSpacing,
        wordSpacing := t.wordSpacing, horizScaling := t.horizScaling, rise := t.rise,
        renderMode := t.renderMode, parts := parts, fill := c.gs.fillStyle,
        stroke := c.gs.strokeStyle }
    let tm' := Matrix.mul (Matrix.translate (runTx cfg t f.size parts) Fixed.zero) c.tm.tm
    let w' := w + (if c.inText then 0 else 1)
    ({ c with tm := { c.tm with tm := tm' } }, some (.glyphRun run c.gs.clip), w', 0)

/-- A `TJ` array element. -/
def textPart? : PdfObject → Option TextPart
  | .string s => some (.str s)
  | o => (num? o).map .adjust

/-! ## Operator classification -/

/-- How `exec` dispatches an operator. -/
inductive OpKind where
  /-- `q` -/
  | save
  /-- `Q` -/
  | restore
  /-- A painting operator (`none` for `n`); `close` for `s`, `b`, `b*`. -/
  | paint (p : Option Paint) (close : Bool)
  /-- `W`, `W*` -/
  | clip (rule : FillRule)
  /-- Everything else (`simple`). -/
  | simple

/-- Classify an operator by its bytes. -/
def opKind : List UInt8 → OpKind
  | [113] => .save                                        -- q
  | [81] => .restore                                      -- Q
  | [83] => .paint (some .stroke) false                   -- S
  | [115] => .paint (some .stroke) true                   -- s
  | [102] => .paint (some (.fill .nonzero)) false         -- f
  | [70] => .paint (some (.fill .nonzero)) false          -- F
  | [102, 42] => .paint (some (.fill .evenOdd)) false     -- f*
  | [66] => .paint (some (.fillStroke .nonzero)) false    -- B
  | [66, 42] => .paint (some (.fillStroke .evenOdd)) false -- B*
  | [98] => .paint (some (.fillStroke .nonzero)) true     -- b
  | [98, 42] => .paint (some (.fillStroke .evenOdd)) true -- b*
  | [110] => .paint none false                            -- n
  | [87] => .clip .nonzero                                -- W
  | [87, 42] => .clip .evenOdd                            -- W*
  | _ => .simple

/-! ## Simple operators -/

/-- Every operator that neither saves/restores the state, paints a path nor sets a clip. -/
def simple (cfg : Config) (c : Core) (op : Op) : Out :=
  let o := op.operands
  match op.op with
  -- graphics state (§8.4.4)
  | [99, 109] => -- cm
    match nums 6 o with
    | some [a, b, c', d, e, f] =>
      ok (setGs c { c.gs with ctm := Matrix.mul ⟨a, b, c', d, e, f⟩ c.gs.ctm })
    | _ => bad c
  | [119] => -- w
    match nums 1 o with
    | some [x] => ok (setLine c { c.gs.line with width := x })
    | _ => bad c
  | [74] => -- J
    match (lastN 1 o).bind List.head? |>.bind nat? |>.bind LineCap.ofNat? with
    | some cap => ok (setLine c { c.gs.line with cap := cap })
    | none => bad c
  | [106] => -- j
    match (lastN 1 o).bind List.head? |>.bind nat? |>.bind LineJoin.ofNat? with
    | some j => ok (setLine c { c.gs.line with join := j })
    | none => bad c
  | [77] => -- M
    match nums 1 o with
    | some [x] => ok (setLine c { c.gs.line with miterLimit := x })
    | _ => bad c
  | [100] => -- d
    match lastN 2 o with
    | some [.array xs, ph] =>
      match xs.mapM num?, num? ph with
      | some arr, some phase => ok (setLine c { c.gs.line with dash := ⟨arr, phase⟩ })
      | _, _ => bad c
    | _ => bad c
  | [114, 105] => -- ri
    match lastName? o with
    | some n => ok (setGs c { c.gs with renderingIntent := n })
    | none => bad c
  | [105] => -- i
    match nums 1 o with
    | some [x] => ok (setGs c { c.gs with flatness := x })
    | _ => bad c
  | [103, 115] => ok c -- gs: ExtGState resolution is 5.2b
  -- colour (§8.6.8)
  | [67, 83] => spaceOp c true o      -- CS
  | [99, 115] => spaceOp c false o    -- cs
  | [83, 67] => colorOp c true o      -- SC
  | [83, 67, 78] => colorOp c true o  -- SCN
  | [115, 99] => colorOp c false o    -- sc
  | [115, 99, 110] => colorOp c false o -- scn
  | [71] => deviceOp c true .gray o   -- G
  | [103] => deviceOp c false .gray o -- g
  | [82, 71] => deviceOp c true .rgb o   -- RG
  | [114, 103] => deviceOp c false .rgb o -- rg
  | [75] => deviceOp c true .cmyk o   -- K
  | [107] => deviceOp c false .cmyk o -- k
  -- path construction (§8.5.2)
  | [109] => pathOp c 0 o -- m
  | [108] => pathOp c 1 o -- l
  | [99] => pathOp c 2 o  -- c
  | [118] => pathOp c 3 o -- v
  | [121] => pathOp c 4 o -- y
  | [104] => pathOp c 5 o -- h
  | [114, 101] => pathOp c 6 o -- re
  -- text objects and state (§9.3, §9.4)
  | [66, 84] => -- BT
    ((({ c with tm := {}, inText := true } : Core)), none, (if c.inText then 1 else 0), 0)
  | [69, 84] => -- ET
    (({ c with inText := false } : Core), none, (if c.inText then 0 else 1), 0)
  | [84, 99] => -- Tc
    match nums 1 o with
    | some [x] => ok (setText c { c.gs.text with charSpacing := x })
    | _ => bad c
  | [84, 119] => -- Tw
    match nums 1 o with
    | some [x] => ok (setText c { c.gs.text with wordSpacing := x })
    | _ => bad c
  | [84, 122] => -- Tz
    match nums 1 o with
    | some [x] => ok (setText c { c.gs.text with horizScaling := x })
    | _ => bad c
  | [84, 76] => -- TL
    match nums 1 o with
    | some [x] => ok (setText c { c.gs.text with leading := x })
    | _ => bad c
  | [84, 102] => -- Tf
    match lastN 2 o with
    | some [.name n, sz] =>
      match num? sz with
      | some s => ok (setText c { c.gs.text with font := some { name := n, size := s } })
      | none => bad c
    | _ => bad c
  | [84, 114] => -- Tr
    match (lastN 1 o).bind List.head? |>.bind nat? |>.bind TextRenderMode.ofNat? with
    | some m => ok (setText c { c.gs.text with renderMode := m })
    | none => bad c
  | [84, 115] => -- Ts
    match nums 1 o with
    | some [x] => ok (setText c { c.gs.text with rise := x })
    | _ => bad c
  | [84, 100] => -- Td
    match nums 2 o with
    | some [x, y] => ok (moveText c x y)
    | _ => bad c
  | [84, 68] => -- TD
    match nums 2 o with
    | some [x, y] => ok (moveText (setText c { c.gs.text with leading := Fixed.neg y }) x y)
    | _ => bad c
  | [84, 109] => -- Tm
    match nums 6 o with
    | some [a, b, c', d, e, f] =>
      let m : Matrix := ⟨a, b, c', d, e, f⟩
      ok { c with tm := ⟨m, m⟩ }
    | _ => bad c
  | [84, 42] => ok (nextLine c) -- T*
  | [84, 106] => -- Tj
    match lastString? o with
    | some s => showText cfg c [.str s] 0
    | none => bad c
  | [84, 74] => -- TJ
    match o.getLast? with
    | some (.array xs) =>
      let parts := xs.filterMap textPart?
      showText cfg c parts (if parts.length = xs.length then 0 else 1)
    | _ => bad c
  | [39] => -- '
    match lastString? o with
    | some s => showText cfg (nextLine c) [.str s] 0
    | none => bad c
  | [34] => -- "
    match lastN 3 o with
    | some [aw, ac, .string s] =>
      match num? aw, num? ac with
      | some aw, some ac =>
        let c1 := setText c { c.gs.text with wordSpacing := aw, charSpacing := ac }
        showText cfg (nextLine c1) [.str s] 0
      | _, _ => bad c
    | _ => bad c
  | [100, 48] => ok c -- d0 (Type 3 glyph metrics)
  | [100, 49] => ok c -- d1
  -- XObjects, shadings, inline images (§8.8, §8.7.4.2, §8.9.7)
  | [68, 111] => -- Do
    match lastName? o with
    | some n => (c, some (.image (.xobject n 0 0) c.gs.ctm c.gs.fillStyle c.gs.clip), 0, 0)
    | none => bad c
  | [115, 104] => -- sh
    match lastName? o with
    | some n => (c, some (.shading n .page c.gs.ctm c.gs.fillStyle c.gs.clip), 0, 0)
    | none => bad c
  | [66, 73] => -- BI (from the tokenizer: the dictionary and the raw data)
    match o with
    | [.dict d] => (c, some (.image (.inline d op.data) c.gs.ctm c.gs.fillStyle c.gs.clip), 0, 0)
    | _ => bad c
  -- marked content (§14.6) and compatibility (§7.8.2)
  | [66, 77, 67] | [66, 68, 67] | [69, 77, 67] | [77, 80] | [68, 80] => ok c
  | [66, 88] => ok { c with bxDepth := c.bxDepth + 1 } -- BX
  | [69, 88] => -- EX
    match c.bxDepth with
    | 0 => bad c
    | n + 1 => ok { c with bxDepth := n }
  | name => (c, some (.unsupported name), (if c.bxDepth = 0 then 1 else 0), 1)

/-! ## Painting, clipping, save/restore -/

/-- Close the current subpath (`s`, `b`, `b*`). -/
def closeCore (c : Core) : Core :=
  match c.cur with
  | some _ => addSegs c [.closePath] c.start c.start
  | none => c

/-- The items of a painting operator (`none` for `n`). -/
def paintItemsOf (p : Option Paint) (path : Path) (gs : GState) : List DisplayItem :=
  match p with
  | some p => p.items path gs
  | none => []

/-- At most `Paint.maxItems` paint items. -/
theorem paintItemsOf_length_le (p : Option Paint) (path : Path) (gs : GState) :
    (paintItemsOf p path gs).length ≤ Paint.maxItems := by
  cases p with
  | none => simp [paintItemsOf, Paint.maxItems]
  | some p => exact Paint.items_length_le p path gs

/-- A painting operator: paint items for a non-empty path, then the pending clip; the path is
cleared. -/
def paintStep (m : Machine) (p : Option Paint) (close : Bool) :
    Machine × List DisplayItem × Nat × Nat :=
  match m with
  | ⟨c0, stack, pending, pf, ps⟩ =>
    let c := if close then closeCore c0 else c0
    match c with
    | ⟨gs, tm, path, _, _, inText, bx⟩ =>
      let empty := path.segs.isEmpty
      let paintItems : List DisplayItem := if empty then [] else paintItemsOf p path gs
      let clipItems : List DisplayItem :=
        match pending with
        | some r => if empty then [] else [.clip path r]
        | none => []
      let gs' : GState :=
        match pending with
        | some r => if empty then gs else { gs with clip := ⟨path, r⟩ :: gs.clip }
        | none => gs
      (⟨⟨gs', tm, {}, none, none, inText, bx⟩, stack, none, pf, ps⟩, paintItems ++ clipItems, 0, 0)

/-- Execute one operator: new machine, emitted items, warnings, unknown-operator count. -/
def exec (cfg : Config) (m : Machine) (op : Op) : Machine × List DisplayItem × Nat × Nat :=
  match opKind op.op with
  | .save =>
    match m.stack.push cfg.limits m.core.gs with
    | .ok s => ({ m with stack := s }, [], 0, 0)
    | .error _ => (m, [], 1, 0)
  | .restore =>
    let w := if m.stack.depth = 0 then 1 else 0
    let r := m.stack.restore m.core.gs
    ({ m with core := { m.core with gs := r.1 }, stack := r.2 }, [], w, 0)
  | .paint p close => paintStep m p close
  | .clip r => ({ m with pending := some r }, [], 0, 0)
  | .simple =>
    let r := simple cfg m.core op
    ({ m with core := r.1 }, r.2.1.toList, r.2.2.1, r.2.2.2)

/-- Append a list of items. -/
def pushAll (a : DisplayList) : List DisplayItem → DisplayList
  | [] => a
  | x :: xs => pushAll (a.push x) xs

/-- Size after `pushAll`. -/
theorem size_pushAll (a : DisplayList) (l : List DisplayItem) :
    (pushAll a l).size = a.size + l.length := by
  induction l generalizing a with
  | nil => simp [pushAll]
  | cons x xs ih => simp [pushAll, ih]; omega

/-- One fold step: run `exec`, append its items, add its counts. -/
def stepAcc (cfg : Config) (acc : Machine × Result) (op : Op) : Machine × Result :=
  match acc with
  | (m, ⟨items, w, u⟩) =>
    match exec cfg m op with
    | (m', its, w', u') => (m', ⟨pushAll items its, w + w', u + u'⟩)

end Interp

open Interp

/-- Run the operators from the initial state; returns the final machine and the output. -/
def runOps (cfg : Config) (ops : Array Op) : Machine × Result :=
  ops.foldl (stepAcc cfg) ({}, {})

/-- **Entry point.** Interpret a tokenized content stream. Total; never fails. -/
def interp (cfg : Config) (ops : Array Op) : Result := (runOps cfg ops).2

/-- Tokenize and interpret a decoded content stream; warnings of both stages are added. -/
def interpBytes (cfg : Config) (bytes : ByteArray) : Result :=
  let t := Ops.tokenize cfg.limits bytes
  let r := interp cfg t.ops
  { r with warnings := r.warnings + t.warnings }

/-! ## Theorems -/

namespace Interp

/-- `1` when a clip is pending. -/
def pendBit (m : Machine) : Nat := if m.pending.isSome then 1 else 0

/-- A painting step emits at most `Paint.maxItems` items plus the pending clip, and clears
the pending clip. -/
theorem paintStep_bound (m : Machine) (p : Option Paint) (close : Bool) :
    (paintStep m p close).2.1.length + pendBit (paintStep m p close).1
      ≤ pendBit m + Paint.maxItems := by
  obtain ⟨c0, stack, pending⟩ := m
  simp only [paintStep]
  generalize (if close = true then closeCore c0 else c0) = c
  obtain ⟨gs, tm, path, cur, start, inText, bx⟩ := c
  simp only [pendBit, List.length_append, Option.isSome_none]
  have := paintItemsOf_length_le p path gs
  cases pending <;> by_cases he : path.segs.isEmpty = true <;>
    simp only [he, ↓reduceIte, Bool.false_eq_true, List.length_nil, List.length_cons,
      Option.isSome_some, Option.isSome_none] <;> omega

/-- **Per-operator bound** on the potential `items + [clip pending]`. -/
theorem exec_bound (cfg : Config) (m : Machine) (op : Op) :
    (exec cfg m op).2.1.length + pendBit (exec cfg m op).1 ≤ pendBit m + Paint.maxItems := by
  unfold exec
  split
  · split <;> simp [pendBit, Paint.maxItems]
  · simp [pendBit, Paint.maxItems]
  · exact paintStep_bound m _ _
  · simp only [pendBit, Option.isSome_some, List.length_nil, Paint.maxItems]; split <;> omega
  · have : (simple cfg m.core op).2.1.toList.length ≤ 1 := by
      cases (simple cfg m.core op).2.1 <;> simp
    simp only [pendBit, Paint.maxItems] at *
    omega

/-- The potential of an accumulator. -/
def pot (acc : Machine × Result) : Nat := acc.2.items.size + pendBit acc.1

/-- One fold step raises the potential by at most `Paint.maxItems`. -/
theorem stepAcc_pot (cfg : Config) (acc : Machine × Result) (op : Op) :
    pot (stepAcc cfg acc op) ≤ pot acc + Paint.maxItems := by
  obtain ⟨m, items, w, u⟩ := acc
  have h := exec_bound cfg m op
  simp only [stepAcc, pot]
  generalize exec cfg m op = r at h
  obtain ⟨m', its, w', u'⟩ := r
  simp only [size_pushAll] at *
  omega

/-- Folding over a list raises the potential by at most `Paint.maxItems` per operator. -/
theorem foldl_pot (cfg : Config) (l : List Op) (acc : Machine × Result) :
    pot (l.foldl (stepAcc cfg) acc) ≤ pot acc + Paint.maxItems * l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons op rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (stepAcc cfg acc op)
    have h2 := stepAcc_pot cfg acc op
    rw [Nat.mul_succ]
    omega

/-- `exec` keeps the `q`/`Q` stack within `Limits.maxGStateDepth`. -/
theorem exec_bounded (cfg : Config) (m : Machine) (op : Op)
    (h : m.stack.Bounded cfg.limits) : (exec cfg m op).1.stack.Bounded cfg.limits := by
  unfold exec
  split
  · split
    · exact GStack.push_bounded ‹_›
    · exact h
  · exact GStack.restore_bounded h _
  · obtain ⟨c0, stack, pending⟩ := m
    exact h
  · exact h
  · exact h

/-- Folding keeps the stack bounded. -/
theorem foldl_bounded (cfg : Config) (l : List Op) (acc : Machine × Result)
    (h : acc.1.stack.Bounded cfg.limits) :
    (l.foldl (stepAcc cfg) acc).1.stack.Bounded cfg.limits := by
  induction l generalizing acc with
  | nil => exact h
  | cons op rest ih =>
    apply ih
    obtain ⟨m, items, w, u⟩ := acc
    have := exec_bounded cfg m op h
    simp only [stepAcc]
    generalize exec cfg m op = r at this
    obtain ⟨m', its, w', u'⟩ := r
    exact this

end Interp

open Interp

/-- **Bound** (task 5.2a): the display list has at most `Paint.maxItems` items per operator. -/
theorem interp_items_le (cfg : Config) (ops : Array Op) :
    (interp cfg ops).items.size ≤ Paint.maxItems * ops.size := by
  have h := foldl_pot cfg ops.toList ({}, {})
  rw [Array.foldl_toList] at h
  simp only [pot, pendBit, Array.length_toList] at h
  simp only [interp, runOps]
  have : ((({} : Result)).items.size) = 0 := rfl
  have h0 : (({} : Machine).pending.isSome) = false := rfl
  simp only [this, h0, Bool.false_eq_true, ↓reduceIte] at h
  omega

/-- **Bound** for the bytes entry point: at most `Paint.maxItems` items per byte. -/
theorem interpBytes_items_le (cfg : Config) (bytes : ByteArray) :
    (interpBytes cfg bytes).items.size ≤ Paint.maxItems * bytes.size := by
  have h1 := interp_items_le cfg (Ops.tokenize cfg.limits bytes).ops
  have h2 := Ops.tokenize_ops_le cfg.limits bytes
  have h3 := Nat.mul_le_mul_left Paint.maxItems h2
  simp only [interpBytes]
  omega

/-- **`q`/`Q` balance**: the saved-state stack never exceeds `Limits.maxGStateDepth`. -/
theorem runOps_stack_bounded (cfg : Config) (ops : Array Op) :
    (runOps cfg ops).1.stack.depth ≤ cfg.limits.maxGStateDepth := by
  have := foldl_bounded cfg ops.toList ({}, {}) (GStack.bounded_empty cfg.limits)
  rw [Array.foldl_toList] at this
  exact this

/-! ## Samples -/

section Tests

private def run (s : String) : Result := interpBytes {} s.toUTF8

private def kinds (s : String) : List String := (run s).items.toList.map DisplayItem.kind

private def fi (n : Int) : Fixed := Fixed.ofInt n

private def P (x y : Int) : Point := ⟨fi x, fi y⟩

private def pathOf : DisplayItem → Option Path
  | .fillPath p .. | .strokePath p .. | .clip p _ => some p
  | _ => none

private def fillColorOf : DisplayItem → Option Color
  | .fillPath _ _ st _ => some st.color
  | _ => none

private def strokeOf : DisplayItem → Option StrokeStyle
  | .strokePath _ st _ => some st
  | _ => none

private def runOf : DisplayItem → Option GlyphRun
  | .glyphRun r _ => some r
  | _ => none

private def clipOf : DisplayItem → Option Clip
  | .fillPath _ _ _ cl | .strokePath _ _ cl | .glyphRun _ cl | .image _ _ _ cl => some cl
  | _ => none

private def item (s : String) (i : Nat) : Option DisplayItem := (run s).items[i]?

-- rectangle fill: page-space path, re expanded
#guard kinds "0 0 10 20 re f" == ["fillPath"]
#guard ((item "0 0 10 20 re f" 0).bind pathOf) ==
  some ⟨#[.moveTo (P 0 0), .lineTo (P 10 0), .lineTo (P 10 20), .lineTo (P 0 20), .closePath]⟩
#guard (run "0 0 10 20 re f").warnings == 0
-- stroke with cm scaling: points scaled, width kept in user space with the CTM
#guard ((item "2 0 0 2 0 0 cm 3 w 1 1 m 5 1 l S" 0).bind pathOf) ==
  some ⟨#[.moveTo (P 2 2), .lineTo (P 10 2)]⟩
#guard ((item "2 0 0 2 0 0 cm 3 w 1 1 m 5 1 l S" 0).bind strokeOf).map (·.line.width) ==
  some (fi 3)
#guard ((item "2 0 0 2 0 0 cm 3 w 1 1 m 5 1 l S" 0).bind strokeOf).map (·.ctm) ==
  some (Matrix.scale (fi 2) (fi 2))
-- q … Q restores the colour
#guard ((item "q 1 0 0 rg Q 0 0 1 1 re f" 0).bind fillColorOf) == some (.gray Comp.zero)
#guard ((item "q 1 0 0 rg 0 0 1 1 re f Q" 0).bind fillColorOf) ==
  some (.rgb Comp.one Comp.zero Comp.zero)
#guard ((item "0 0 1 1 re 2 g f" 0).bind fillColorOf) == some (.gray Comp.one) -- clamped
#guard ((item "/DeviceCMYK cs 0 0 0 1 sc 0 0 1 1 re f" 0).bind fillColorOf) ==
  some (.cmyk Comp.zero Comp.zero Comp.zero Comp.one)
#guard ((item "/Pattern cs /P0 scn 0 0 1 1 re f" 0).bind fillColorOf) ==
  some (.pattern (Name.ofString "P0"))
-- B: fill then stroke; b closes
#guard kinds "0 0 m 1 0 l 1 1 l b" == ["fillPath", "strokePath"]
#guard ((item "0 0 m 1 0 l 1 1 l b" 0).bind pathOf).map (·.segs.size) == some 4
-- text block
private def txt : String :=
  "BT /F1 12 Tf 72 700 Td (Hi) Tj [(A) -250 (B)] TJ (C) Tj 0 -14 TD (D) ' ET"
#guard kinds txt == ["glyphRun", "glyphRun", "glyphRun", "glyphRun"]
#guard ((item txt 0).bind runOf).map (·.tm) == some (Matrix.translate (fi 72) (fi 700))
#guard ((item txt 0).bind runOf).map (·.parts) == some [.str [72, 105]]
#guard ((item txt 1).bind runOf).map (·.parts) ==
  some [.str [65], .adjust (fi (-250)), .str [66]]
-- the TJ adjustment -250 at 12pt moves Tm by 3
#guard ((item txt 2).bind runOf).map (·.tm) == some (Matrix.translate (fi 75) (fi 700))
-- TD sets the leading to 14 and ' moves another line down
#guard ((item txt 3).bind runOf).map (·.tm) == some (Matrix.translate (fi 72) (fi 672))
#guard (run txt).warnings == 0
#guard ((item txt 0).bind runOf).map (·.startMatrix) ==
  some ⟨fi 12, Fixed.zero, Fixed.zero, fi 12, fi 72, fi 700⟩
#guard (run "BT (x) Tj ET").warnings == 1  -- no font: skipped
#guard kinds "BT (x) Tj ET" == []
-- W n clip: a clip item, and later items carry the clip
#guard kinds "0 0 5 5 re W n 0 0 10 10 re f" == ["clip", "fillPath"]
#guard ((item "0 0 5 5 re W n 0 0 10 10 re f" 1).bind clipOf).map (·.length) == some 1
#guard ((item "0 0 5 5 re W* f" 0).bind clipOf).map (·.length) == some 0
#guard kinds "0 0 5 5 re W* B" == ["fillPath", "strokePath", "clip"]
#guard ((item "q 0 0 5 5 re W n Q 0 0 1 1 re f" 1).bind clipOf).map (·.length) == some 0
-- inline image followed by more operators
#guard kinds "BI /W 2 /H 2 /CS /G /BPC 8 ID \x01\x02\x03\x04 EI 0 0 1 1 re f" ==
  ["image", "fillPath"]
#guard (run "BI /W 2 /H 2 /CS /G /BPC 8 ID \x01\x02\x03\x04 EI 0 0 1 1 re f").warnings == 0
-- XObject and shading placeholders
#guard kinds "/Im0 Do /Sh0 sh" == ["image", "shading"]
-- unknown operator: unsupported item and a warning; inside BX … EX no warning
#guard kinds "1 2 foo" == ["unsupported"]
#guard (run "1 2 foo").warnings == 1
#guard (run "1 2 foo").unsupported == 1
#guard kinds "BX 1 2 foo EX" == ["unsupported"]
#guard (run "BX 1 2 foo EX").warnings == 0
#guard (run "BX 1 2 foo EX").unsupported == 1
-- malformed operands: skipped with a warning
#guard (run "/x w 0 0 1 1 re f").warnings == 1
#guard (run "5 J 1 l").warnings == 2         -- bad cap; lineto without current point
#guard kinds "(a) 0 0 1 rg 0 0 1 1 re f" == ["fillPath"]   -- extra operand: last 3 used
#guard (run "1 rg").warnings == 1
-- lexer garbage mid-stream recovers
#guard kinds "0 0 1 1 re ) f 0 0 1 1 re /a#zz f" == ["fillPath", "fillPath"]
#guard (run "0 0 1 1 re ) f 0 0 1 1 re /a#zz f").warnings == 2
-- q at the depth limit is skipped; unbalanced Q is ignored
#guard (interpBytes { limits := { maxGStateDepth := 1 } } "q q Q Q".toUTF8).warnings == 2
#guard (run "Q").warnings == 1
#guard (runOps {} (Ops.tokenize {} "q q q Q".toUTF8).ops).1.stack.depth == 2
-- marked content, gs, ri, i, d are known
#guard (run "/Span <</MCID 0>> BDC /P BMC EMC EMC /GS0 gs /Perceptual ri 1 i [3 1] 0 d").warnings
  == 0
#guard kinds "/Span <</MCID 0>> BDC /P BMC EMC EMC /GS0 gs /Perceptual ri 1 i [3 1] 0 d" == []

end Tests

end SafePdf.Core.Content
