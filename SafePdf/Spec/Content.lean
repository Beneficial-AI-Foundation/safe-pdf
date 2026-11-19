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
  non-empty path the items are `Paint.items` (fill then stroke for `B`; each with the clip in
  force *before* the operator), followed by a `clip` item if `W`/`W*` was pending; the clip
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
  `'`.
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

/-- The 71 operators the interpreter knows (ISO 32000-2 Annex A, minus none). -/
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

/-- Items of a painting operator for the current path of `c`: nothing for an empty path;
otherwise the paint items (`none` = `n`) then the pending clip. -/
def paintOutput (pending : Option FillRule) (p : Option Paint) (c : Core) :
    List DisplayItem :=
  if c.path.segs.isEmpty then []
  else
    (match p with
      | some p => p.items c.path c.gs
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
      (k : IgnoredKw kw) : SimpleStep cfg c ⟨o, kw, off, dat⟩ c []
  /-- `/N CS`, `/N cs`: set the space and its initial colour (§8.6.8). -/
  | space {c : Core} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {stroke : Bool} {n : Name} (k : SpaceKw kw stroke) (h : Interp.lastName? o = some n) :
      SimpleStep cfg c ⟨o, kw, off, dat⟩
        (withColour c stroke (Interp.spaceOfName n) (Interp.spaceOfName n).initialColor) []
  /-- `SC SCN sc scn`: a colour in the current space. -/
  | colour {c : Core} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {stroke : Bool} {col : Color} (k : ColourKw kw stroke)
      (h : Interp.colorIn (if stroke then c.gs.strokeSpace else c.gs.fillSpace) o = some col) :
      SimpleStep cfg c ⟨o, kw, off, dat⟩
        (withColour c stroke (if stroke then c.gs.strokeSpace else c.gs.fillSpace) col) []
  /-- `G g RG rg K k`: the device space and a colour of its component count. -/
  | device {c : Core} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {stroke : Bool} {s : DeviceSpace} {xs : List Fixed} {col : Color}
      (k : DeviceKw kw stroke s) (h : Interp.nums s.nComps o = some xs)
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
      SimpleStep cfg c ⟨o, [84, 102], off, dat⟩ (withText c { c.gs.text with font := some ⟨n, s⟩ })
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
  /-- `/N Do`: an XObject placeholder (resolved in 5.2b). -/
  | Do {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {n : Name}
      (h : Interp.lastName? o = some n) :
      SimpleStep cfg c ⟨o, [68, 111], off, dat⟩ c
        [.image (.xobject n 0 0) c.gs.ctm c.gs.fillStyle c.gs.clip]
  /-- `/N sh`: paint a shading over the clip. -/
  | sh {c : Core} {o : List PdfObject} {off : Nat} {dat : ByteArray} {n : Name}
      (h : Interp.lastName? o = some n) :
      SimpleStep cfg c ⟨o, [115, 104], off, dat⟩ c [.shading n c.gs.ctm c.gs.clip]
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
      {p : Option Paint} {close : Bool} (k : PaintKw kw p close) :
      Effect cfg m ⟨o, kw, off, dat⟩
        ⟨afterPaint m.pending (closeIf close m.core), m.stack, none⟩
        (paintOutput m.pending p (closeIf close m.core))
  /-- `W`, `W*`: the clip rule is pending until the next painting operator. -/
  | clip {m : Machine} {o : List PdfObject} {kw : List UInt8} {off : Nat} {dat : ByteArray}
      {r : FillRule} (k : ClipKw kw r) :
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

end SafePdf.Spec.Content
