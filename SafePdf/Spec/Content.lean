import SafePdf.Core.Content.Interp

/-!
# Content-stream interpreter: transition specification (task 5.3)

Plan.md §6 Phase 5 ("interpreter state transitions specified as an inductive relation; impl
proven against it") and §5.1 (spec / impl / equivalence). ISO 32000-2 references: §8.4.4
(graphics state operators), §8.5.2–8.5.4 (path construction, painting, clipping), §8.6.8
(colour operators), §9.3–9.4 (text state, text objects, text positioning and showing), §8.8,
§8.7.4.2, §8.9.7 (`Do`, `sh`, inline images), §14.6 (marked content), §7.8.2 (`BX`/`EX`).

## The relation

`Step cfg m op m' is`: executing operator `op` in machine state `m` (`Core.Content.Machine`:
the `Core` state, the `q`/`Q` stack and the pending clip) yields state `m'` and appends the
display items `is`. It has three constructors:

* `Step.defined`: `op` has one of the effects listed by `Effect` (below);
* `Step.skip`: `op` is a known operator (`keywords`) but **no** `Effect` applies (malformed or
  missing operands, `l`/`c`/`v`/`y` without a current point, text shown without a font, `q`
  at `Limits.maxGStateDepth`, `Q` on an empty stack, `EX` without `BX`): nothing changes and
  nothing is emitted (the impl counts a warning);
* `Step.unknown`: `op` is not one of the 71 operators of `keywords`: nothing changes and one
  `DisplayItem.unsupported` is emitted (for the M5 coverage report).

`Effect cfg m op m' is` lists the effect of every known operator declaratively:

* **`q`**: pushes the current graphics state (only below the depth limit). **`Q`**: restores
  the most recently saved state and pops it (only on a non-empty stack).
* **`cm`**: `CTM := M × CTM` (`Matrix.mul M CTM`, in this order: `Matrix.mul` rounds and is
  not associative). **`w J j M d ri i`** set their graphics-state parameter.
* **Path construction** (`m l c v y h re`): segments are appended in page space (each point
  mapped by the CTM when the segment is built); `m` and `re` start a subpath, `l c v y` need
  a current point, `v` uses the current point as first control point, `y` the end point as
  second; `h` closes the current subpath (no-op without a current point); `re` appends the
  closed four-corner subpath `(x,y) (x+w,y) (x+w,y+h) (x,y+h)`.
* **Painting** (`S s f F f* B B* b b* n`, `PaintKw`): `s b b*` first close the subpath; for a
  non-empty path the items are `paintItems` (fill then stroke for `B`; each with the clip in
  force *before* the operator; for fill-and-stroke bracketed by a non-isolated knockout group
  unless the stroke alpha is 0, or 1 with `Normal`, as MuPDF 1.25.1 `pdf_show_path`, task
  7.3i), followed by a `clip` item if `W`/`W*` was pending; the clip
  is intersected only after painting; the path, the current point and the pending clip are
  cleared. An empty path paints nothing and leaves the clip unchanged.
* **`W`, `W*`**: mark the clip rule as pending until the next painting operator.
* **Colour** (`CS cs SC SCN sc scn G g RG rg K k`): set the stroking or non-stroking space
  and colour (`DeviceKw`, `SpaceKw`, `ColourKw`).
* **Text** (`BT ET Tc Tw Tz TL Tf Tr Ts Td TD Tm T* Tj TJ ' "`): `BT` resets `Tm = Tlm = I`;
  `Td`: `Tlm := translate(tx, ty) × Tlm`, `Tm := Tlm`; `TD` also sets `TL := -ty`; `T*` is
  `0 -TL Td`; a show operator emits one `glyphRun` (font from `Tf` required) carrying `Tm`,
  the CTM, the text state, the colour snapshots and the clip, then advances `Tm` by the
  displacement of §9.4.4 (`displacement`); `'` is `T*` then `Tj`; `"` sets `Tw`, `Tc` then
  `'`. Without a font, `Tj`/`TJ` are skipped while `'`/`"` still perform their `T*`
  (and `Tw`/`Tc`) parts (`quoteNoFont`, `dquoteNoFont`), as the impl does.
* **`Do`, `sh`, `BI`**: emit an image/shading placeholder with the CTM, fill snapshot and clip.
* **`BX`/`EX`** count the compatibility nesting; **`gs d0 d1 BMC BDC EMC MP DP`** change
  nothing (`IgnoredKw`; ExtGState resolution is task 5.2b).

Every one of the 71 operators the impl knows is specified declaratively; there is **no**
catch-all constructor deferring to `exec`. Operand decoding is shared with the impl (the
helpers of `Core.Content.Interp`: `nums n` = the last `n` operands, all numbers; `lastName?`,
`lastString?`, `colorIn`, `deviceColor`, `spaceOfName`, `textPart?`): the spec states the
*state transition* for operands of the expected shape, and `skip` covers every other shape.

## Theorems

* `step_iff_exec`: `Step cfg m op m' is ↔ (exec cfg m op).1 = m' ∧ (exec cfg m op).2.1 = is`;
  hence soundness (`exec_step`), determinism (`step_det`) and totality (`step_total`).
* `Steps` is the reflexive-transitive closure over an operator list (items concatenated);
  `steps_iff_runOps`: `Steps cfg {} ops.toList m is ↔ (runOps cfg ops).1 = m ∧
  (interp cfg ops).items.toList = is`; hence `interp_steps` (the run exists) and `steps_det`
  (it is unique).

Not covered: the warning and unknown-operator *counts* of `Result` (only the state and the
display items are specified).

Proof note: `simple_match_fallthrough` names the auxiliary matcher of `Interp.simple`'s operator
dispatch (`Interp.simple.match_33`) and walks its decision tree, because Lean cannot generate
the matcher's equation lemmas or splitter within the default heartbeat budget (57 `List UInt8`
literal patterns). If `Interp.simple` is edited, that name and `simpleKws` may need updating.
-/

set_option autoImplicit false

namespace SafePdf.Spec.Content

open SafePdf SafePdf.Core.Content

/-! ## Operator tables -/

/-- Path-painting operators (ISO 32000-2 §8.5.3.1 Table 59): the paint (`none` for `n`) and
whether the subpath is closed first. -/
inductive PaintKw : List UInt8 → Option Paint → Bool → Prop
  /-- `S` -/
  | S : PaintKw [83] (some .stroke) false
  /-- `s` -/
  | s : PaintKw [115] (some .stroke) true
  /-- `f` -/
  | f : PaintKw [102] (some (.fill .nonzero)) false
  /-- `F` (obsolete synonym of `f`) -/
  | F : PaintKw [70] (some (.fill .nonzero)) false
  /-- `f*` -/
  | fStar : PaintKw [102, 42] (some (.fill .evenOdd)) false
  /-- `B` -/
  | B : PaintKw [66] (some (.fillStroke .nonzero)) false
  /-- `B*` -/
  | BStar : PaintKw [66, 42] (some (.fillStroke .evenOdd)) false
  /-- `b` -/
  | b : PaintKw [98] (some (.fillStroke .nonzero)) true
  /-- `b*` -/
  | bStar : PaintKw [98, 42] (some (.fillStroke .evenOdd)) true
  /-- `n` -/
  | n : PaintKw [110] none false

/-- Clipping operators (§8.5.4 Table 60). -/
inductive ClipKw : List UInt8 → FillRule → Prop
  /-- `W` -/
  | W : ClipKw [87] .nonzero
  /-- `W*` -/
  | WStar : ClipKw [87, 42] .evenOdd

/-- Device colour operators (§8.6.8 Table 73): stroking or not, and the device space. -/
inductive DeviceKw : List UInt8 → Bool → DeviceSpace → Prop
  /-- `G` -/
  | G : DeviceKw [71] true .gray
  /-- `g` -/
  | g : DeviceKw [103] false .gray
  /-- `RG` -/
  | RG : DeviceKw [82, 71] true .rgb
  /-- `rg` -/
  | rg : DeviceKw [114, 103] false .rgb
  /-- `K` -/
  | K : DeviceKw [75] true .cmyk
  /-- `k` -/
  | k : DeviceKw [107] false .cmyk

/-- Colour-space operators `CS` (stroking) and `cs`. -/
inductive SpaceKw : List UInt8 → Bool → Prop
  /-- `CS` -/
  | CS : SpaceKw [67, 83] true
  /-- `cs` -/
  | cs : SpaceKw [99, 115] false

/-- Colour operators in the current space: `SC`, `SCN` (stroking), `sc`, `scn`. -/
inductive ColourKw : List UInt8 → Bool → Prop
  /-- `SC` -/
  | SC : ColourKw [83, 67] true
  /-- `SCN` -/
  | SCN : ColourKw [83, 67, 78] true
  /-- `sc` -/
  | sc : ColourKw [115, 99] false
  /-- `scn` -/
  | scn : ColourKw [115, 99, 110] false

/-- Known operators that change nothing in the state modelled here: `gs` (ExtGState,
resolved in 5.2b), `d0`/`d1` (Type 3 glyph metrics), marked content (§14.6). -/
inductive IgnoredKw : List UInt8 → Prop
  /-- `gs` -/
  | gs : IgnoredKw [103, 115]
  /-- `d0` -/
  | d0 : IgnoredKw [100, 48]
  /-- `d1` -/
  | d1 : IgnoredKw [100, 49]
  /-- `BMC` -/
  | BMC : IgnoredKw [66, 77, 67]
  /-- `BDC` -/
  | BDC : IgnoredKw [66, 68, 67]
  /-- `EMC` -/
  | EMC : IgnoredKw [69, 77, 67]
  /-- `MP` -/
  | MP : IgnoredKw [77, 80]
  /-- `DP` -/
  | DP : IgnoredKw [68, 80]

/-- Operators that save/restore, paint or clip (`q Q S s f F f* B B* b b* n W W*`). -/
def controlKws : List (List UInt8) :=
  [[113], [81], [83], [115], [102], [70], [102, 42], [66], [66, 42], [98], [98, 42], [110],
   [87], [87, 42]]

/-- All other known operators (graphics state, colour, path construction, text, XObjects,
inline images, marked content, compatibility). -/
def simpleKws : List (List UInt8) :=
  [[99, 109], [119], [74], [106], [77], [100], [114, 105], [105], [103, 115], [67, 83],
   [99, 115], [83, 67], [83, 67, 78], [115, 99], [115, 99, 110], [71], [103], [82, 71],
   [114, 103], [75], [107], [109], [108], [99], [118], [121], [104], [114, 101], [66, 84],
   [69, 84], [84, 99], [84, 119], [84, 122], [84, 76], [84, 102], [84, 114], [84, 115],
   [84, 100], [84, 68], [84, 109], [84, 42], [84, 106], [84, 74], [39], [34], [100, 48],
   [100, 49], [68, 111], [115, 104], [66, 73], [66, 77, 67], [66, 68, 67], [69, 77, 67],
   [77, 80], [68, 80], [66, 88], [69, 88]]

/-- The 71 operators the interpreter knows (ISO 32000-2 Annex A Table A.1, except `BI`'s
`ID`/`EI`, which the tokenizer folds into `BI`). -/
def keywords : List (List UInt8) := controlKws ++ simpleKws

/-! ## State vocabulary -/

/-- A user-space point mapped to page space by the CTM. -/
def toPage (c : Core) (x y : Fixed) : Point := Matrix.apply c.gs.ctm ⟨x, y⟩

/-- Append `segs` to the current path and set the current point and subpath start. -/
def extendPath (c : Core) (segs : List Segment) (cur start : Option Point) : Core :=
  { c with path := ⟨c.path.segs ++ segs.toArray⟩, cur := cur, start := start }

/-- `h`: close the current subpath (the current point returns to the subpath start); no-op
without a current point. -/
def closeSubpath (c : Core) : Core :=
  match c.cur with
  | some _ => extendPath c [.closePath] c.start c.start
  | none => c

/-- Close the subpath first (`s`, `b`, `b*`) or not. -/
def closeIf (close : Bool) (c : Core) : Core := if close then closeSubpath c else c

/-- Items of painting operator `p` for `path` in state `g` (§8.5.3.1): a fill, a stroke, or a
fill followed by a stroke; the latter inside a non-isolated knockout group (`groupBegin` …
`groupEnd`, so the stroke composites over the fill's backdrop, not over the fill) unless the
stroke alpha is 0 (the stroke paints nothing) or 1 with blend mode `Normal` (it covers the fill
where it paints) — MuPDF 1.25.1 `pdf-op-run.c` `pdf_show_path` (task 7.3i). -/
def paintItems (p : Paint) (path : Path) (g : GState) : List DisplayItem :=
  match p with
  | .fill r => [.fillPath path r g.fillStyle g.clip]
  | .stroke => [.strokePath path g.strokeStyle g.clip]
  | .fillStroke r =>
    if g.strokeAlpha = Comp.zero ∨ (g.strokeAlpha = Comp.one ∧ g.blendMode = .normal) then
      [.fillPath path r g.fillStyle g.clip, .strokePath path g.strokeStyle g.clip]
    else
      [.groupBegin { isolated := false, knockout := true }, .fillPath path r g.fillStyle g.clip,
        .strokePath path g.strokeStyle g.clip, .groupEnd]

/-- Items of a painting operator for the current path of `c`: nothing for an empty path;
otherwise the paint items (`none` = `n`) then the pending clip. -/
def paintOutput (pending : Option FillRule) (p : Option Paint) (c : Core) :
    List DisplayItem :=
  if c.path.segs.isEmpty then []
  else
    (match p with
      | some p => paintItems p c.path c.gs
      | none => []) ++
    (match pending with
      | some r => [.clip c.path r]
      | none => [])

/-- State after a painting operator: the pending clip (if any, and the path is non-empty) is
intersected into the clip *after* painting; the path and current point are cleared. -/
def afterPaint (pending : Option FillRule) (c : Core) : Core :=
  { c with
    gs := match pending with
      | some r => if c.path.segs.isEmpty then c.gs else { c.gs with clip := ⟨c.path, r⟩ :: c.gs.clip }
      | none => c.gs,
    path := {}, cur := none, start := none }

/-- Set the stroking (`stroke`) or non-stroking colour space and colour. -/
def withColour (c : Core) (stroke : Bool) (sp : ColorSpace) (col : Color) : Core :=
  if stroke then { c with gs := { c.gs with strokeSpace := sp, strokeColor := col } }
  else { c with gs := { c.gs with fillSpace := sp, fillColor := col } }

/-- Replace the line style. -/
def withLine (c : Core) (l : LineStyle) : Core := { c with gs := { c.gs with line := l } }

/-- Replace the text state. -/
def withText (c : Core) (t : TextState) : Core := { c with gs := { c.gs with text := t } }

/-- `"`'s first part: `Tw := aw`, `Tc := ac`. -/
def withSpacing (c : Core) (aw ac : Fixed) : Core :=
  withText c { c.gs.text with wordSpacing := aw, charSpacing := ac }

/-- `Td`: `Tlm := translate(tx, ty) × Tlm` and `Tm := Tlm` (§9.4.2). -/
def moveLine (c : Core) (tx ty : Fixed) : Core :=
  { c with tm := ⟨Matrix.mul (Matrix.translate tx ty) c.tm.tlm,
                  Matrix.mul (Matrix.translate tx ty) c.tm.tlm⟩ }

/-- `T*` = `0 -TL Td`. -/
def nextLine (c : Core) : Core := moveLine c Fixed.zero (Fixed.neg c.gs.text.leading)

/-- Horizontal displacement of one part of a shown run (§9.4.4): a string advances by its
glyph widths (`Config.advance`); a `TJ` number `a` by `-(a / 1000) · Tfs · Th`. -/
def partDisp (cfg : Config) (t : TextState) (size : Fixed) : TextPart → Fixed
  | .str s => cfg.advance t s
  | .adjust a =>
    Fixed.mul (Fixed.mul (Fixed.neg (Fixed.div a (Fixed.ofInt 1000))) size)
      (Fixed.div t.horizScaling (Fixed.ofInt 100))

/-- Total displacement of a run: the sum of its parts, right to left. -/
def displacement (cfg : Config) (t : TextState) (size : Fixed) (parts : List TextPart) :
    Fixed :=
  parts.foldr (fun p acc => Fixed.add (partDisp cfg t size p) acc) Fixed.zero

/-- The glyph run shown by `parts` in state `c` with font `f`. -/
def runOf (c : Core) (f : FontRef) (parts : List TextPart) : GlyphRun :=
  { font := f, tm := c.tm.tm, ctm := c.gs.ctm, charSpacing := c.gs.text.charSpacing,
    wordSpacing := c.gs.text.wordSpacing, horizScaling := c.gs.text.horizScaling,
    rise := c.gs.text.rise, renderMode := c.gs.text.renderMode, parts := parts,
    fill := c.gs.fillStyle, stroke := c.gs.strokeStyle }

/-- State after showing `parts`: `Tm := translate(tx, 0) × Tm` with `tx` the displacement. -/
def afterShow (cfg : Config) (c : Core) (f : FontRef) (parts : List TextPart) : Core :=
  { c with tm := { c.tm with
      tm := Matrix.mul (Matrix.translate (displacement cfg c.gs.text f.size parts) Fixed.zero)
              c.tm.tm } }

/-- The last operand is a nonnegative integer that `f` maps to a value (`J`, `j`, `Tr`). -/
def enumOperand {α : Type} (f : Nat → Option α) (o : List PdfObject) : Option α :=
  (Interp.lastN 1 o).bind List.head? |>.bind Interp.nat? |>.bind f

/-! ## The relation -/

/-- Effect of an operator other than `q Q`, painting and `W`/`W*` on the `Core` state, and the
items it emits. -/
inductive SimpleStep (cfg : Config) : Core → Op → Core → List DisplayItem → Prop
  /-- `a b c d e f cm`: `CTM := M × CTM` (§8.4.4). -/
  | cm {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {a b c' d e f : Fixed}
      (h : Interp.nums 6 o = some [a, b, c', d, e, f]) :
      SimpleStep cfg c ⟨o, [99, 109], off, dat⟩
        { c with gs := { c.gs with ctm := Matrix.mul ⟨a, b, c', d, e, f⟩ c.gs.ctm } } []
  /-- `x w`: line width. -/
  | w {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x : Fixed}
      (h : Interp.nums 1 o = some [x]) :
      SimpleStep cfg c ⟨o, [119], off, dat⟩ (withLine c { c.gs.line with width := x }) []
  /-- `n J`: line cap `0 1 2`. -/
  | J {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {cap : LineCap}
      (h : enumOperand LineCap.ofNat? o = some cap) :
      SimpleStep cfg c ⟨o, [74], off, dat⟩ (withLine c { c.gs.line with cap := cap }) []
  /-- `n j`: line join `0 1 2`. -/
  | j {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {jn : LineJoin}
      (h : enumOperand LineJoin.ofNat? o = some jn) :
      SimpleStep cfg c ⟨o, [106], off, dat⟩ (withLine c { c.gs.line with join := jn }) []
  /-- `x M`: miter limit. -/
  | M {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x : Fixed}
      (h : Interp.nums 1 o = some [x]) :
      SimpleStep cfg c ⟨o, [77], off, dat⟩ (withLine c { c.gs.line with miterLimit := x }) []
  /-- `[a…] p d`: dash array of numbers and phase. -/
  | d {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {xs : List PdfObject}
      {ph : PdfObject} {arr : List Fixed} {phase : Fixed}
      (h : Interp.lastN 2 o = some [.array xs, ph]) (ha : xs.mapM Interp.num? = some arr)
      (hp : Interp.num? ph = some phase) :
      SimpleStep cfg c ⟨o, [100], off, dat⟩ (withLine c { c.gs.line with dash := ⟨arr, phase⟩ })
        []
  /-- `/N ri`: rendering intent. -/
  | ri {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {n : Name}
      (h : Interp.lastName? o = some n) :
      SimpleStep cfg c ⟨o, [114, 105], off, dat⟩
        { c with gs := { c.gs with renderingIntent := n } } []
  /-- `x i`: flatness. -/
  | i {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x : Fixed}
      (h : Interp.nums 1 o = some [x]) :
      SimpleStep cfg c ⟨o, [105], off, dat⟩ { c with gs := { c.gs with flatness := x } } []
  /-- `gs d0 d1 BMC BDC EMC MP DP`: no change. -/
  | ignored {c : Core} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      (hkw : IgnoredKw kw) : SimpleStep cfg c ⟨o, kw, off, dat⟩ c []
  /-- `/N CS`, `/N cs`: set the space and its initial colour (§8.6.8). -/
  | space {c : Core} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {stroke : Bool} {n : Name} (hkw : SpaceKw kw stroke) (h : Interp.lastName? o = some n) :
      SimpleStep cfg c ⟨o, kw, off, dat⟩
        (withColour c stroke (Interp.spaceOfName n) (Interp.spaceOfName n).initialColor) []
  /-- `SC SCN sc scn`: a colour in the current space. -/
  | colour {c : Core} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {stroke : Bool} {col : Color} (hkw : ColourKw kw stroke)
      (h : Interp.colorIn (if stroke then c.gs.strokeSpace else c.gs.fillSpace) o = some col) :
      SimpleStep cfg c ⟨o, kw, off, dat⟩
        (withColour c stroke (if stroke then c.gs.strokeSpace else c.gs.fillSpace) col) []
  /-- `G g RG rg K k`: the device space and a colour of its component count. -/
  | device {c : Core} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {stroke : Bool} {s : DeviceSpace} {xs : List Fixed} {col : Color}
      (hkw : DeviceKw kw stroke s) (h : Interp.nums s.nComps o = some xs)
      (hc : Interp.deviceColor s xs = some col) :
      SimpleStep cfg c ⟨o, kw, off, dat⟩ (withColour c stroke (.device s) col) []
  /-- `x y m`: start a subpath at the point. -/
  | moveTo {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x y : Fixed}
      (h : Interp.nums 2 o = some [x, y]) :
      SimpleStep cfg c ⟨o, [109], off, dat⟩
        (extendPath c [.moveTo (toPage c x y)] (some (toPage c x y)) (some (toPage c x y))) []
  /-- `x y l`: line from the current point. -/
  | lineTo {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x y : Fixed}
      {q : Point} (h : Interp.nums 2 o = some [x, y]) (hc : c.cur = some q) :
      SimpleStep cfg c ⟨o, [108], off, dat⟩
        (extendPath c [.lineTo (toPage c x y)] (some (toPage c x y)) c.start) []
  /-- `x1 y1 x2 y2 x3 y3 c`: Bézier curve from the current point. -/
  | curveTo {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray}
      {x1 y1 x2 y2 x3 y3 : Fixed} {q : Point}
      (h : Interp.nums 6 o = some [x1, y1, x2, y2, x3, y3]) (hc : c.cur = some q) :
      SimpleStep cfg c ⟨o, [99], off, dat⟩
        (extendPath c [.curveTo (toPage c x1 y1) (toPage c x2 y2) (toPage c x3 y3)]
          (some (toPage c x3 y3)) c.start) []
  /-- `x2 y2 x3 y3 v`: the current point is the first control point. -/
  | curveV {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x2 y2 x3 y3 : Fixed}
      {q : Point} (h : Interp.nums 4 o = some [x2, y2, x3, y3]) (hc : c.cur = some q) :
      SimpleStep cfg c ⟨o, [118], off, dat⟩
        (extendPath c [.curveTo q (toPage c x2 y2) (toPage c x3 y3)]
          (some (toPage c x3 y3)) c.start) []
  /-- `x1 y1 x3 y3 y`: the end point is the second control point. -/
  | curveY {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x1 y1 x3 y3 : Fixed}
      {q : Point} (h : Interp.nums 4 o = some [x1, y1, x3, y3]) (hc : c.cur = some q) :
      SimpleStep cfg c ⟨o, [121], off, dat⟩
        (extendPath c [.curveTo (toPage c x1 y1) (toPage c x3 y3) (toPage c x3 y3)]
          (some (toPage c x3 y3)) c.start) []
  /-- `h`: close the current subpath. -/
  | close {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} :
      SimpleStep cfg c ⟨o, [104], off, dat⟩ (closeSubpath c) []
  /-- `x y w h re`: the closed subpath `(x,y) (x+w,y) (x+w,y+h) (x,y+h)`. -/
  | rect {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x y wd ht : Fixed}
      (h : Interp.nums 4 o = some [x, y, wd, ht]) :
      SimpleStep cfg c ⟨o, [114, 101], off, dat⟩
        (extendPath c
          [.moveTo (toPage c x y), .lineTo (toPage c (Fixed.add x wd) y),
           .lineTo (toPage c (Fixed.add x wd) (Fixed.add y ht)),
           .lineTo (toPage c x (Fixed.add y ht)), .closePath]
          (some (toPage c x y)) (some (toPage c x y))) []
  /-- `BT`: begin a text object, `Tm = Tlm = I`. -/
  | BT {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} :
      SimpleStep cfg c ⟨o, [66, 84], off, dat⟩ { c with tm := {}, inText := true } []
  /-- `ET`: end the text object. -/
  | ET {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} :
      SimpleStep cfg c ⟨o, [69, 84], off, dat⟩ { c with inText := false } []
  /-- `x Tc`: character spacing. -/
  | Tc {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x : Fixed}
      (h : Interp.nums 1 o = some [x]) :
      SimpleStep cfg c ⟨o, [84, 99], off, dat⟩ (withText c { c.gs.text with charSpacing := x }) []
  /-- `x Tw`: word spacing. -/
  | Tw {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x : Fixed}
      (h : Interp.nums 1 o = some [x]) :
      SimpleStep cfg c ⟨o, [84, 119], off, dat⟩ (withText c { c.gs.text with wordSpacing := x })
        []
  /-- `x Tz`: horizontal scaling. -/
  | Tz {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x : Fixed}
      (h : Interp.nums 1 o = some [x]) :
      SimpleStep cfg c ⟨o, [84, 122], off, dat⟩
        (withText c { c.gs.text with horizScaling := x }) []
  /-- `x TL`: leading. -/
  | TL {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x : Fixed}
      (h : Interp.nums 1 o = some [x]) :
      SimpleStep cfg c ⟨o, [84, 76], off, dat⟩ (withText c { c.gs.text with leading := x }) []
  /-- `/F size Tf`: font and size. -/
  | Tf {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {n : Name}
      {sz : PdfObject} {s : Fixed} (h : Interp.lastN 2 o = some [.name n, sz])
      (hs : Interp.num? sz = some s) :
      SimpleStep cfg c ⟨o, [84, 102], off, dat⟩ (withText c { c.gs.text with font := some { name := n, size := s } })
        []
  /-- `n Tr`: rendering mode `0…7`. -/
  | Tr {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {mode : TextRenderMode}
      (h : enumOperand TextRenderMode.ofNat? o = some mode) :
      SimpleStep cfg c ⟨o, [84, 114], off, dat⟩ (withText c { c.gs.text with renderMode := mode })
        []
  /-- `x Ts`: rise. -/
  | Ts {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x : Fixed}
      (h : Interp.nums 1 o = some [x]) :
      SimpleStep cfg c ⟨o, [84, 115], off, dat⟩ (withText c { c.gs.text with rise := x }) []
  /-- `tx ty Td`: next line, offset from the start of the current one. -/
  | Td {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x y : Fixed}
      (h : Interp.nums 2 o = some [x, y]) :
      SimpleStep cfg c ⟨o, [84, 100], off, dat⟩ (moveLine c x y) []
  /-- `tx ty TD`: `-ty TL` then `tx ty Td`. -/
  | TD {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {x y : Fixed}
      (h : Interp.nums 2 o = some [x, y]) :
      SimpleStep cfg c ⟨o, [84, 68], off, dat⟩
        (moveLine (withText c { c.gs.text with leading := Fixed.neg y }) x y) []
  /-- `a b c d e f Tm`: `Tm = Tlm = M`. -/
  | Tm {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {a b c' d e f : Fixed}
      (h : Interp.nums 6 o = some [a, b, c', d, e, f]) :
      SimpleStep cfg c ⟨o, [84, 109], off, dat⟩
        { c with tm := ⟨⟨a, b, c', d, e, f⟩, ⟨a, b, c', d, e, f⟩⟩ } []
  /-- `T*`: next line. -/
  | TStar {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} :
      SimpleStep cfg c ⟨o, [84, 42], off, dat⟩ (nextLine c) []
  /-- `(s) Tj`: show a string (a font must be set). -/
  | Tj {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {s : List UInt8}
      {f : FontRef} (h : Interp.lastString? o = some s) (hf : c.gs.text.font = some f) :
      SimpleStep cfg c ⟨o, [84, 106], off, dat⟩ (afterShow cfg c f [.str s])
        [.glyphRun (runOf c f [.str s]) c.gs.clip]
  /-- `[…] TJ`: show strings and adjustments (elements of other types are dropped). -/
  | TJ {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {xs : List PdfObject}
      {f : FontRef} (h : o.getLast? = some (.array xs)) (hf : c.gs.text.font = some f) :
      SimpleStep cfg c ⟨o, [84, 74], off, dat⟩ (afterShow cfg c f (xs.filterMap Interp.textPart?))
        [.glyphRun (runOf c f (xs.filterMap Interp.textPart?)) c.gs.clip]
  /-- `(s) '`: `T*` then `(s) Tj`. -/
  | quote {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {s : List UInt8}
      {f : FontRef} (h : Interp.lastString? o = some s) (hf : c.gs.text.font = some f) :
      SimpleStep cfg c ⟨o, [39], off, dat⟩ (afterShow cfg (nextLine c) f [.str s])
        [.glyphRun (runOf (nextLine c) f [.str s]) c.gs.clip]
  /-- `aw ac (s) "`: `aw Tw ac Tc (s) '`. -/
  | dquote {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {aw ac : PdfObject}
      {s : List UInt8} {w cs : Fixed} {f : FontRef}
      (h : Interp.lastN 3 o = some [aw, ac, .string s]) (hw : Interp.num? aw = some w)
      (hc : Interp.num? ac = some cs) (hf : c.gs.text.font = some f) :
      SimpleStep cfg c ⟨o, [34], off, dat⟩
        (afterShow cfg (nextLine (withSpacing c w cs)) f [.str s])
        [.glyphRun (runOf (nextLine (withSpacing c w cs)) f [.str s]) c.gs.clip]
  /-- `(s) '` without a font: the `T*` part only (showing is skipped). -/
  | quoteNoFont {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {s : List UInt8}
      (h : Interp.lastString? o = some s) (hf : c.gs.text.font = none) :
      SimpleStep cfg c ⟨o, [39], off, dat⟩ (nextLine c) []
  /-- `aw ac (s) "` without a font: the `Tw`, `Tc` and `T*` parts only. -/
  | dquoteNoFont {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray}
      {aw ac : PdfObject} {s : List UInt8} {w cs : Fixed}
      (h : Interp.lastN 3 o = some [aw, ac, .string s]) (hw : Interp.num? aw = some w)
      (hc : Interp.num? ac = some cs) (hf : c.gs.text.font = none) :
      SimpleStep cfg c ⟨o, [34], off, dat⟩ (nextLine (withSpacing c w cs)) []
  /-- `/N Do`: an XObject placeholder (resolved in 5.2b). -/
  | Do {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {n : Name}
      (h : Interp.lastName? o = some n) :
      SimpleStep cfg c ⟨o, [68, 111], off, dat⟩ c
        [.image (.xobject n 0 0) c.gs.ctm c.gs.fillStyle c.gs.clip]
  /-- `/N sh`: paint a shading over the clip. -/
  | sh {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {n : Name}
      (h : Interp.lastName? o = some n) :
      SimpleStep cfg c ⟨o, [115, 104], off, dat⟩ c
        [.shading n .page c.gs.ctm c.gs.fillStyle c.gs.clip]
  /-- `BI … ID … EI`: an inline image with its parameters and raw data. -/
  | BI {c : Core} {dict : Dict} {off : Nat} {dat : ByteArray} :
      SimpleStep cfg c ⟨[.dict dict], [66, 73], off, dat⟩ c
        [.image (.inline dict dat) c.gs.ctm c.gs.fillStyle c.gs.clip]
  /-- `BX`: enter a compatibility section. -/
  | BX {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} :
      SimpleStep cfg c ⟨o, [66, 88], off, dat⟩ { c with bxDepth := c.bxDepth + 1 } []
  /-- `EX`: leave a compatibility section. -/
  | EX {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {n : Nat}
      (h : c.bxDepth = n + 1) :
      SimpleStep cfg c ⟨o, [69, 88], off, dat⟩ { c with bxDepth := n } []

/-- The specified effect of a known operator on the whole machine. -/
inductive Effect (cfg : Config) : Machine → Op → Machine → List DisplayItem → Prop
  /-- `q`: push the current graphics state (below the depth limit). -/
  | save {m : Machine} {o : List PdfObject} {off : Nat} {dat : ByteArray}
      (h : m.stack.depth < cfg.limits.maxGStateDepth) :
      Effect cfg m ⟨o, [113], off, dat⟩ { m with stack := ⟨m.core.gs :: m.stack.saved⟩ } []
  /-- `Q`: restore the most recently saved graphics state and pop it. -/
  | restore {m : Machine} {o : List PdfObject} {off : Nat} {dat : ByteArray} {g : GState}
      {rest : List GState} (h : m.stack.saved = g :: rest) :
      Effect cfg m ⟨o, [81], off, dat⟩ { m with core := { m.core with gs := g }, stack := ⟨rest⟩ }
        []
  /-- A painting operator (see `paintOutput`, `afterPaint`); the pending clip is consumed. -/
  | paint {m : Machine} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {p : Option Paint} {close : Bool} (hkw : PaintKw kw p close) :
      Effect cfg m ⟨o, kw, off, dat⟩
        ⟨afterPaint m.pending (closeIf close m.core), m.stack, none, m.patFill, m.patStroke⟩
        (paintOutput m.pending p (closeIf close m.core))
  /-- `W`, `W*`: the clip rule is pending until the next painting operator. -/
  | clip {m : Machine} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {r : FillRule} (hkw : ClipKw kw r) :
      Effect cfg m ⟨o, kw, off, dat⟩ { m with pending := some r } []
  /-- Any other known operator acts on the `Core` state only. -/
  | simple {m : Machine} {op : Op} {c' : Core} {is : List DisplayItem}
      (h : SimpleStep cfg m.core op c' is) : Effect cfg m op { m with core := c' } is

/-- **The transition relation**: one operator from state `m` yields `m'` and items `is`. -/
inductive Step (cfg : Config) : Machine → Op → Machine → List DisplayItem → Prop
  /-- A specified effect. -/
  | defined {m m' : Machine} {op : Op} {is : List DisplayItem} (h : Effect cfg m op m' is) :
      Step cfg m op m' is
  /-- A known operator none of whose specified forms applies: skipped. -/
  | skip {m : Machine} {op : Op} (hk : op.op ∈ keywords)
      (hn : ¬ ∃ m' is, Effect cfg m op m' is) : Step cfg m op m []
  /-- An unknown operator: an `unsupported` item, nothing else changes. -/
  | unknown {m : Machine} {op : Op} (hk : op.op ∉ keywords) :
      Step cfg m op m [.unsupported op.op]

/-- Runs over an operator list: the items of the steps, concatenated in order. -/
inductive Steps (cfg : Config) : Machine → List Op → Machine → List DisplayItem → Prop
  /-- No operator. -/
  | nil {m : Machine} : Steps cfg m [] m []
  /-- One step, then the rest. -/
  | cons {m m₁ m₂ : Machine} {op : Op} {ops : List Op} {is₁ is₂ : List DisplayItem}
      (h : Step cfg m op m₁ is₁) (t : Steps cfg m₁ ops m₂ is₂) :
      Steps cfg m (op :: ops) m₂ (is₁ ++ is₂)

/-! ## Proofs: the implementation against the relation -/

section Proofs

/-- `List.foldl Array.push` appends. -/
theorem foldl_push {α : Type} (a : Array α) (l : List α) :
    l.foldl Array.push a = a ++ l.toArray := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The impl's segment appending is `extendPath`. -/
theorem addSegs_eq (c : Core) (segs : List Segment) (cur start : Option Point) :
    Interp.addSegs c segs cur start = extendPath c segs cur start := by
  obtain ⟨gs, tm, path, cur0, start0, it, bx⟩ := c
  simp only [Interp.addSegs, extendPath, foldl_push]

/-- The impl's subpath closing is `closeSubpath`. -/
theorem closeCore_eq (c : Core) : Interp.closeCore c = closeSubpath c := by
  unfold Interp.closeCore closeSubpath
  cases c.cur <;> simp only [addSegs_eq]

/-- The impl's run displacement is `displacement`. -/
theorem runTx_eq (cfg : Config) (t : TextState) (size : Fixed) (parts : List TextPart) :
    Interp.runTx cfg t size parts = displacement cfg t size parts := by
  induction parts with
  | nil => rfl
  | cons p rest ih =>
    cases p <;> simp only [Interp.runTx, ih, displacement, List.foldr_cons, partDisp,
      Interp.adjustTx]

/-- Case analysis on a `dite` (used to walk the operator matcher's decision tree). -/
theorem dite_by {α : Sort _} {c : Prop} [inst : Decidable c] {t : c → α} {e : ¬c → α} {r : α}
    (h1 : ∀ h : c, t h = r) (h2 : ∀ h : ¬c, e h = r) : dite c t e = r := by
  cases inst with
  | isFalse h => exact h2 h
  | isTrue h => exact h1 h

/-- The fallthrough of the operator dispatch of `Interp.simple` (its auxiliary matcher, with
abstract alternatives): an operator outside `simpleKws` reaches the last alternative. Proved
by walking the matcher's decision tree (`dite` on each byte, `List` cases on the rest). -/
theorem simple_match_fallthrough {α : Type} (kw : List UInt8) (hk : kw ∉ simpleKws)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 : Unit → α) (f : List UInt8 → α) :
    Interp.simple.match_33 (fun _ => α) kw a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 f = f kw := by
  delta Interp.simple.match_33
  rcases kw with _ | ⟨x, xs⟩
  · rfl
  dsimp only [Interp.deviceColor._sparseCasesOn_1]
  repeat' (first
    | (apply dite_by <;> intro hh <;> (try subst hh) <;>
        (try dsimp only [Eq.ndrec_symm, Interp.deviceColor._sparseCasesOn_1,
          Interp.deviceColor._sparseCasesOn_2]))
    | exact absurd (by decide) hk
    | rfl
    | (cases ‹List UInt8› <;>
        (try dsimp only [Eq.ndrec_symm, Interp.deviceColor._sparseCasesOn_1,
          Interp.deviceColor._sparseCasesOn_2])))

/-- An operator outside `simpleKws` is `unsupported` in `Interp.simple`. -/
theorem simple_unknown (cfg : Config) (c : Core) (o : List PdfObject) (kw : List UInt8)
    (off : Nat) (dat : ByteArray) (hk : kw ∉ simpleKws) :
    Interp.simple cfg c ⟨o, kw, off, dat⟩ =
      (c, some (.unsupported kw), (if c.bxDepth = 0 then 1 else 0), 1) := by
  unfold Interp.simple
  exact simple_match_fallthrough kw hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- An operator outside `controlKws` is dispatched to `Interp.simple`. -/
theorem opKind_of_not_control {kw : List UInt8} (hk : kw ∉ controlKws) :
    Interp.opKind kw = .simple := by
  unfold Interp.opKind
  split <;> first | rfl | exact absurd (by decide) hk

/-- `exec` on a simple operator. -/
theorem exec_simple_eq (cfg : Config) (m : Machine) (op : Op)
    (h : Interp.opKind op.op = .simple) :
    Interp.exec cfg m op =
      ({ m with core := (Interp.simple cfg m.core op).1 },
        (Interp.simple cfg m.core op).2.1.toList, (Interp.simple cfg m.core op).2.2.1,
        (Interp.simple cfg m.core op).2.2.2) := by
  unfold Interp.exec
  rw [h]

/-- **Spec ⇒ impl** for the simple operators: a specified transition is what `Interp.simple`
computes. -/
theorem simple_of_step {cfg : Config} {c : Core} {op : Op} {c' : Core} {is : List DisplayItem}
    (h : SimpleStep cfg c op c' is) :
    (Interp.simple cfg c op).1 = c' ∧ (Interp.simple cfg c op).2.1.toList = is := by
  cases h
  all_goals (try cases ‹IgnoredKw _›)
  all_goals (try cases ‹SpaceKw _ _›)
  all_goals (try cases ‹ColourKw _ _›)
  all_goals (try cases ‹DeviceKw _ _ _›)
  all_goals (try dsimp only [enumOperand] at *)
  all_goals constructor
  all_goals (conv in Interp.simple _ _ _ => whnf)
  all_goals (try simp only [↓reduceIte] at *)
  all_goals (try simp only [*, Interp.showText, Interp.nextLine, Interp.moveText,
    Interp.setText, Interp.setGs, addSegs_eq])
  all_goals (try simp only [runTx_eq])
  all_goals (try rfl)
  all_goals (try (rcases hcur : c.cur with _ | q <;>
    simp only [hcur, closeSubpath, Interp.ok, Option.toList_none] <;> done))
  all_goals (simp only [*, afterShow, nextLine, withSpacing, withText, moveLine, Interp.bad])

/-- **Impl ⇒ spec** for the simple operators: for a known operator, `Interp.simple` either
performs a specified transition or leaves the state unchanged and emits nothing. -/
theorem simple_cases (cfg : Config) (c : Core) (o : List PdfObject) (kw : List UInt8)
    (off : Nat) (dat : ByteArray) (hk : kw ∈ simpleKws) :
    (∃ c' is, SimpleStep cfg c ⟨o, kw, off, dat⟩ c' is) ∨
      ((Interp.simple cfg c ⟨o, kw, off, dat⟩).1 = c ∧
        (Interp.simple cfg c ⟨o, kw, off, dat⟩).2.1 = none) := by
  generalize hs : Interp.simple cfg c ⟨o, kw, off, dat⟩ = r
  simp only [simpleKws, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (conv at hs => lhs; whnf)
  all_goals subst hs
  all_goals (try unfold Interp.showText)
  all_goals (try simp only [Interp.nextLine, Interp.moveText, Interp.setText, Interp.setGs])
  all_goals (repeat' split)
  all_goals first
    | exact Or.inr ⟨rfl, rfl⟩
    | exact Or.inl ⟨_, _, .cm ‹_›⟩
    | exact Or.inl ⟨_, _, .w ‹_›⟩
    | exact Or.inl ⟨_, _, .J ‹_›⟩
    | exact Or.inl ⟨_, _, .j ‹_›⟩
    | exact Or.inl ⟨_, _, .M ‹_›⟩
    | exact Or.inl ⟨_, _, .d ‹_› ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .ri ‹_›⟩
    | exact Or.inl ⟨_, _, .i ‹_›⟩
    | exact Or.inl ⟨_, _, .ignored (by constructor)⟩
    | exact Or.inl ⟨_, _, .space (by constructor) ‹_›⟩
    | exact Or.inl ⟨_, _, .colour (by constructor) ‹_›⟩
    | exact Or.inl ⟨_, _, .device (by constructor) ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .moveTo ‹_›⟩
    | exact Or.inl ⟨_, _, .lineTo ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .curveTo ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .curveV ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .curveY ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .close⟩
    | exact Or.inl ⟨_, _, .rect ‹_›⟩
    | exact Or.inl ⟨_, _, .BT⟩
    | exact Or.inl ⟨_, _, .ET⟩
    | exact Or.inl ⟨_, _, .Tc ‹_›⟩
    | exact Or.inl ⟨_, _, .Tw ‹_›⟩
    | exact Or.inl ⟨_, _, .Tz ‹_›⟩
    | exact Or.inl ⟨_, _, .TL ‹_›⟩
    | exact Or.inl ⟨_, _, .Tf ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .Tr ‹_›⟩
    | exact Or.inl ⟨_, _, .Ts ‹_›⟩
    | exact Or.inl ⟨_, _, .Td ‹_›⟩
    | exact Or.inl ⟨_, _, .TD ‹_›⟩
    | exact Or.inl ⟨_, _, .Tm ‹_›⟩
    | exact Or.inl ⟨_, _, .TStar⟩
    | exact Or.inl ⟨_, _, .Tj ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .TJ ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .quote ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .dquote ‹_› ‹_› ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .quoteNoFont ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .dquoteNoFont ‹_› ‹_› ‹_› ‹_›⟩
    | exact Or.inl ⟨_, _, .Do ‹_›⟩
    | exact Or.inl ⟨_, _, .sh ‹_›⟩
    | exact Or.inl ⟨_, _, .BI⟩
    | exact Or.inl ⟨_, _, .BX⟩
    | exact Or.inl ⟨_, _, .EX ‹_›⟩

/-- The implementation's `Paint.items` is the spec's `paintItems` (task 7.3i). -/
theorem paintItems_eq (p : Paint) (path : Path) (g : GState) :
    p.items path g = paintItems p path g := by
  cases p with
  | fill r => rfl
  | stroke => rfl
  | fillStroke r =>
    simp only [Paint.items, paintItems, Paint.needsKnockout, Paint.knockoutGroup]
    by_cases h0 : g.strokeAlpha = Comp.zero <;> by_cases h1 : g.strokeAlpha = Comp.one <;>
      by_cases h2 : g.blendMode = .normal <;> simp [h0, h1, h2]

/-- The painting step of the impl is `afterPaint` / `paintOutput`. -/
theorem paintStep_eq (m : Machine) (p : Option Paint) (close : Bool) :
    Interp.paintStep m p close =
      (⟨afterPaint m.pending (closeIf close m.core), m.stack, none, m.patFill, m.patStroke⟩,
        paintOutput m.pending p (closeIf close m.core), 0, 0) := by
  obtain ⟨c0, stack, pending, pf, ps⟩ := m
  have hc : (if close = true then Interp.closeCore c0 else c0) = closeIf close c0 := by
    cases close <;> simp [closeIf, closeCore_eq]
  simp only [Interp.paintStep, hc]
  generalize closeIf close c0 = c
  obtain ⟨gs, tm, path, cur, start, it, bx⟩ := c
  cases pending <;> cases p <;> by_cases he : path.segs.isEmpty = true <;>
    simp [he, afterPaint, paintOutput, Interp.paintItemsOf, paintItems_eq]

/-- `exec` on a painting operator. -/
theorem exec_paint_eq (cfg : Config) (m : Machine) (op : Op) (p : Option Paint) (close : Bool)
    (h : Interp.opKind op.op = .paint p close) :
    Interp.exec cfg m op = Interp.paintStep m p close := by
  unfold Interp.exec
  rw [h]

/-- `exec` on `W`/`W*`. -/
theorem exec_clip_eq (cfg : Config) (m : Machine) (op : Op) (r : FillRule)
    (h : Interp.opKind op.op = .clip r) :
    Interp.exec cfg m op = ({ m with pending := some r }, [], 0, 0) := by
  unfold Interp.exec
  rw [h]

/-- The operator of a simple transition is one of `simpleKws`. -/
theorem SimpleStep.mem {cfg : Config} {c : Core} {op : Op} {c' : Core}
    {is : List DisplayItem} (h : SimpleStep cfg c op c' is) : op.op ∈ simpleKws := by
  cases h
  all_goals (try cases ‹IgnoredKw _›)
  all_goals (try cases ‹SpaceKw _ _›)
  all_goals (try cases ‹ColourKw _ _›)
  all_goals (try cases ‹DeviceKw _ _ _›)
  all_goals (dsimp only; decide)

/-- The simple and control operators are disjoint. -/
theorem not_control_of_simple {kw : List UInt8} (h : kw ∈ simpleKws) : kw ∉ controlKws := by
  have : ∀ k ∈ simpleKws, k ∉ controlKws := by decide
  exact this kw h

/-- The operator of a specified effect is one of `keywords`. -/
theorem Effect.mem {cfg : Config} {m : Machine} {op : Op} {m' : Machine}
    {is : List DisplayItem} (h : Effect cfg m op m' is) : op.op ∈ keywords := by
  cases h with
  | simple h => exact List.mem_append_right _ h.mem
  | paint hkw => cases hkw <;> (dsimp only; decide)
  | clip hkw => cases hkw <;> (dsimp only; decide)
  | save => dsimp only; decide
  | restore => dsimp only; decide

/-- **Spec ⇒ impl**: a specified effect is what `exec` computes. -/
theorem exec_of_effect {cfg : Config} {m : Machine} {op : Op} {m' : Machine}
    {is : List DisplayItem} (h : Effect cfg m op m' is) :
    (Interp.exec cfg m op).1 = m' ∧ (Interp.exec cfg m op).2.1 = is := by
  cases h with
  | simple h =>
    rw [exec_simple_eq _ _ _ (opKind_of_not_control (not_control_of_simple h.mem))]
    obtain ⟨h1, h2⟩ := simple_of_step h
    exact ⟨by rw [h1], h2⟩
  | save hd =>
    generalize he : Interp.exec cfg m _ = r
    conv at he => lhs; whnf
    subst he
    simp [GStack.push, hd]
  | restore hs =>
    generalize he : Interp.exec cfg m _ = r
    conv at he => lhs; whnf
    subst he
    simp [GStack.restore, GStack.pop, hs]
  | paint hkw =>
    cases hkw <;>
    · rw [exec_paint_eq cfg m _ _ _ rfl, paintStep_eq]
      exact ⟨rfl, rfl⟩
  | clip hkw =>
    cases hkw <;>
    · rw [exec_clip_eq cfg m _ _ rfl]
      exact ⟨rfl, rfl⟩

/-- **Impl ⇒ spec**: `exec` performs a specified effect, or skips a known operator (no change,
no item), or reports an unknown operator. -/
theorem exec_cases (cfg : Config) (m : Machine) (op : Op) :
    (∃ m' is, Effect cfg m op m' is) ∨
    (op.op ∈ keywords ∧ (Interp.exec cfg m op).1 = m ∧ (Interp.exec cfg m op).2.1 = []) ∨
    (op.op ∉ keywords ∧ (Interp.exec cfg m op).1 = m ∧
      (Interp.exec cfg m op).2.1 = [.unsupported op.op]) := by
  obtain ⟨o, kw, off, dat⟩ := op
  by_cases hc : kw ∈ controlKws
  · have hk : kw ∈ keywords := List.mem_append_left _ hc
    simp only [controlKws, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hd : m.stack.depth < cfg.limits.maxGStateDepth
      · exact Or.inl ⟨_, _, .save hd⟩
      · refine Or.inr (Or.inl ⟨hk, ?_⟩)
        generalize he : Interp.exec cfg m _ = r
        conv at he => lhs; whnf
        subst he
        simp [GStack.push, hd]
    · rcases hs : m.stack.saved with _ | ⟨g, rest⟩
      · refine Or.inr (Or.inl ⟨hk, ?_⟩)
        generalize he : Interp.exec cfg m _ = r
        conv at he => lhs; whnf
        subst he
        obtain ⟨core, ⟨saved⟩, pending⟩ := m
        dsimp only at hs
        subst hs
        exact ⟨rfl, rfl⟩
      · exact Or.inl ⟨_, _, .restore hs⟩
    all_goals first
      | exact Or.inl ⟨_, _, .paint (by constructor)⟩
      | exact Or.inl ⟨_, _, .clip (by constructor)⟩
  · have hs := opKind_of_not_control hc
    rw [exec_simple_eq _ _ _ hs]
    by_cases hk : kw ∈ simpleKws
    · rcases simple_cases cfg m.core o kw off dat hk with ⟨c', is, h⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨_, _, .simple h⟩
      · refine Or.inr (Or.inl ⟨List.mem_append_right _ hk, ?_, ?_⟩)
        · rw [h1]
        · simp only [h2, Option.toList_none]
    · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · simp only [keywords, List.mem_append, not_or]
        exact ⟨hc, hk⟩
      · rw [simple_unknown _ _ _ _ _ _ hk]
      · rw [simple_unknown _ _ _ _ _ _ hk]
        rfl

end Proofs

/-! ## Main theorems -/

/-- **Equivalence**: the relation holds exactly for the state and items `exec` computes. -/
theorem step_iff_exec (cfg : Config) (m : Machine) (op : Op) (m' : Machine)
    (is : List DisplayItem) :
    Step cfg m op m' is ↔ (Interp.exec cfg m op).1 = m' ∧ (Interp.exec cfg m op).2.1 = is := by
  constructor
  · intro h
    cases h with
    | defined h => exact exec_of_effect h
    | skip hk hn =>
      rcases exec_cases cfg m op with hg | ⟨_, h1, h2⟩ | ⟨hk', _, _⟩
      · exact absurd hg hn
      · exact ⟨h1, h2⟩
      · exact absurd hk hk'
    | unknown hk =>
      rcases exec_cases cfg m op with ⟨_, _, hg⟩ | ⟨hk', _, _⟩ | ⟨_, h1, h2⟩
      · exact absurd hg.mem hk
      · exact absurd hk' hk
      · exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    by_cases hg : ∃ m'' is'', Effect cfg m op m'' is''
    · obtain ⟨m'', is'', hg⟩ := hg
      obtain ⟨h1, h2⟩ := exec_of_effect hg
      rw [h1, h2]
      exact .defined hg
    · rcases exec_cases cfg m op with hg' | ⟨hk, h1, h2⟩ | ⟨hk, h1, h2⟩
      · exact absurd hg' hg
      · rw [h1, h2]
        exact .skip hk hg
      · rw [h1, h2]
        exact .unknown hk

/-- **Soundness**: every `exec` result is a transition of the relation. -/
theorem exec_step (cfg : Config) (m : Machine) (op : Op) :
    Step cfg m op (Interp.exec cfg m op).1 (Interp.exec cfg m op).2.1 :=
  (step_iff_exec cfg m op _ _).2 ⟨rfl, rfl⟩

/-- **Determinism** of the relation. -/
theorem step_det {cfg : Config} {m : Machine} {op : Op} {m₁ m₂ : Machine}
    {is₁ is₂ : List DisplayItem} (h₁ : Step cfg m op m₁ is₁) (h₂ : Step cfg m op m₂ is₂) :
    m₁ = m₂ ∧ is₁ = is₂ := by
  obtain ⟨a1, b1⟩ := (step_iff_exec cfg m op _ _).1 h₁
  obtain ⟨a2, b2⟩ := (step_iff_exec cfg m op _ _).1 h₂
  exact ⟨a1 ▸ a2, b1 ▸ b2⟩

/-- **Totality**: every operator has a transition from every state. -/
theorem step_total (cfg : Config) (m : Machine) (op : Op) :
    ∃ m' is, Step cfg m op m' is :=
  ⟨_, _, exec_step cfg m op⟩

/-- `pushAll` appends to the list view. -/
theorem pushAll_toList (a : DisplayList) (l : List DisplayItem) :
    (Interp.pushAll a l).toList = a.toList ++ l := by
  induction l generalizing a with
  | nil => simp [Interp.pushAll]
  | cons x xs ih => simp [Interp.pushAll, ih]

/-- One fold step of the impl, in terms of `exec`. -/
theorem stepAcc_eq (cfg : Config) (acc : Machine × Result) (op : Op) :
    (Interp.stepAcc cfg acc op).1 = (Interp.exec cfg acc.1 op).1 ∧
      (Interp.stepAcc cfg acc op).2.items.toList =
        acc.2.items.toList ++ (Interp.exec cfg acc.1 op).2.1 := by
  obtain ⟨m, items, w, u⟩ := acc
  simp only [Interp.stepAcc]
  generalize Interp.exec cfg m op = r
  obtain ⟨m', its, w', u'⟩ := r
  simp [pushAll_toList]

/-- The impl's fold over a list is a `Steps` run, whose items it appends. -/
theorem foldl_steps (cfg : Config) (l : List Op) (acc : Machine × Result) :
    ∃ is, Steps cfg acc.1 l (l.foldl (Interp.stepAcc cfg) acc).1 is ∧
      (l.foldl (Interp.stepAcc cfg) acc).2.items.toList = acc.2.items.toList ++ is := by
  induction l generalizing acc with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons op rest ih =>
    obtain ⟨is₂, hs, hi⟩ := ih (Interp.stepAcc cfg acc op)
    obtain ⟨e1, e2⟩ := stepAcc_eq cfg acc op
    refine ⟨(Interp.exec cfg acc.1 op).2.1 ++ is₂, ?_, ?_⟩
    · rw [e1] at hs
      exact .cons (exec_step cfg acc.1 op) hs
    · simp only [List.foldl_cons, hi, e2, List.append_assoc]

/-- **Determinism** of runs. -/
theorem steps_det {cfg : Config} {m : Machine} {ops : List Op} {m₁ m₂ : Machine}
    {is₁ is₂ : List DisplayItem} (h₁ : Steps cfg m ops m₁ is₁) (h₂ : Steps cfg m ops m₂ is₂) :
    m₁ = m₂ ∧ is₁ = is₂ := by
  induction h₁ generalizing is₂ with
  | nil => cases h₂; exact ⟨rfl, rfl⟩
  | cons h t ih =>
    cases h₂ with
    | cons h' t' =>
      obtain ⟨rfl, rfl⟩ := step_det h h'
      obtain ⟨rfl, rfl⟩ := ih t'
      exact ⟨rfl, rfl⟩

/-- **Lifted equivalence**: a run from the initial state over the operators ends in `m` with
items `is` exactly when the impl ends in `m` and its display list is `is`. -/
theorem steps_iff_runOps (cfg : Config) (ops : Array Op) (m : Machine)
    (is : List DisplayItem) :
    Steps cfg {} ops.toList m is ↔
      (runOps cfg ops).1 = m ∧ (interp cfg ops).items.toList = is := by
  obtain ⟨is₀, hs, hi⟩ := foldl_steps cfg ops.toList ({}, {})
  have hr : runOps cfg ops = ops.toList.foldl (Interp.stepAcc cfg) ({}, {}) := by
    simp only [runOps, Array.foldl_toList]
  have hi' : (interp cfg ops).items.toList = is₀ := by
    simp only [interp, hr, hi]
    rfl
  rw [← hr] at hs
  rw [hi']
  constructor
  · intro h
    obtain ⟨e1, e2⟩ := steps_det h hs
    exact ⟨e1.symm, e2.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact hs

/-- **`interp` is the unique run**: the impl's display list is the items of a `Steps` run
from the initial state. -/
theorem interp_steps (cfg : Config) (ops : Array Op) :
    Steps cfg {} ops.toList (runOps cfg ops).1 (interp cfg ops).items.toList :=
  (steps_iff_runOps cfg ops _ _).2 ⟨rfl, rfl⟩

/-- Any run from the initial state produces exactly `interp`'s display list. -/
theorem interp_items_of_steps {cfg : Config} {ops : Array Op} {m : Machine}
    {is : List DisplayItem} (h : Steps cfg {} ops.toList m is) :
    (interp cfg ops).items.toList = is :=
  ((steps_iff_runOps cfg ops m is).1 h).2

end SafePdf.Spec.Content
