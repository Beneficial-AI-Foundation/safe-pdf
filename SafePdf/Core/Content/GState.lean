import SafePdf.Core.Object
import SafePdf.Core.Limits
import SafePdf.Core.Error

/-!
# Graphics state for the content-stream interpreter (Plan.md §6 Phase 5, §3 rule 2, §4 S3)

The data types and pure state operations the content-stream interpreter (task 5.2) runs on,
the inductive transition spec (5.3) is stated over, and the display list
(`Core.Content.DisplayList`) snapshots. ISO 32000-2 references: §8.3 (coordinate systems,
matrices), §8.4 (graphics state), §8.5 (paths), §8.6 (colour spaces), §9.3 (text state),
§9.4.2 (text matrices).

## Design decisions

* **Numbers are `Fixed`: decimal fixed point with 6 fractional digits, saturating.** A value
  is `raw · 10⁻⁶` with `raw : Int` and `|raw| ≤ 10¹⁸` (so `|value| ≤ 10¹²`), the bound carried
  as proof fields. Content streams multiply matrices (`cm`, `Tm`, text rendering), so the
  object model's exact `Decimal` is unsuitable: its scale grows with every product and an
  adversarial stream of `cm` operators would grow the CTM's digits without bound. ℚ would
  grow the same way. `Fixed` is closed under every operation at constant size.
  - *Decimal, not binary.* PDF writes reals in decimal; `ofDecimal` is exact for every operand
    with at most 6 fractional digits (virtually all real files; ISO 32000-2 Annex C suggests 5
    significant decimal digits for reals) and `toDecimal` prints exactly, so SVG export (5.4)
    loses nothing on input coordinates.
  - *Rounding:* every operation that drops digits (`mul`, `div`, `ofDecimal`, matrix products)
    rounds **half up** (to nearest, ties toward +∞), via `roundDiv p d = (p + d/2) / d` with
    `Int` `/` = `Int.ediv` (floor for positive divisors). Each matrix entry is computed exactly
    (sum of products at scale 10¹²) and rounded **once**.
  - *Saturation:* results outside `±10¹²` are clamped (`Fixed.clamp`). Real pages use
    coordinates below 10⁵; clamping is the defined behaviour for absurd inputs, never an error.
  - *Proven laws:* identity/zero laws for `add`, `mul` and `Matrix.mul`, `Matrix.apply` with
    the identity, commutativity of `add`/`mul`. **Not** proven, because false under rounding:
    associativity of `mul` / `Matrix.mul`. Consumers must therefore fix one evaluation order
    (the interpreter composes exactly as ISO 32000-2 writes the products, left to right).
* **Coordinate space of paths: page space** (the page's default user space, ISO 32000-2
  §8.3.2.3), i.e. path points are transformed by the CTM *when the path is constructed*, as
  §8.5.2.1 specifies. The page-to-device view transform (`/MediaBox`, `/Rotate`, `/UserUnit`,
  zoom) is applied by the renderer, never here. Line widths and dash lengths remain in user
  space, so stroke items also carry the CTM (`DisplayList.StrokeStyle.ctm`).
* **`re`, `v`, `y` are not path segments.** In page space a rectangle under a rotated or
  skewed CTM is no longer axis-aligned, so the interpreter expands `re` into
  `moveTo`/3×`lineTo`/`closePath` (the equivalence §8.5.2.1 Table 58 states) and `v`/`y`
  into `curveTo` with the current point duplicated.
* **Clip = list of clip paths, intersected.** `GState.clip : Clip` (`List ClipPath`, newest
  first); the clip region is the intersection of all entries, `[]` meaning unclipped. `W`/`W*`
  conses one entry; `q`/`Q` save/restore it with the rest of the state. Snapshots are O(1)
  thanks to sharing of the persistent list, so every display item carries its own clip.
* **Colours:** components are `Comp` (a `Fixed` in [0, 1], clamped on entry). Colour spaces
  collapse to the three device spaces: `ICCBased` → its `/Alternate` or by `/N`; `CalGray`/
  `CalRGB` → `DeviceGray`/`DeviceRGB`; `Indexed`, `Separation`, `DeviceN`, `Lab` are kept as
  `ColorSpace.other family nComps alternate` (so `sc`/`scn` operand counts can be checked)
  and their colour is held in the alternate device space (tint transforms are not evaluated
  in Phase 5; the interpreter uses the alternate's initial colour). `Pattern` colours are
  `Color.pattern name`.
* **Text matrices are not graphics state.** `Tm`/`Tlm` live only inside `BT … ET` and are not
  saved by `q`/`Q` (ISO 32000-2 §9.4.1), so they are the separate `TextMatrices`, held by the
  interpreter next to the `GState`; `TextState` holds only the §9.3 parameters.
* **`q`/`Q` stack (`GStack`) is bounded by `Limits.maxGStateDepth`** (already in
  `Limits.lean`): `q` at the bound returns `Error.limitExceeded .gstateDepth`
  (`GStack.push_depth_le`). **`Q` on an empty stack is ignored** (state unchanged,
  `GStack.restore_empty`), as Acrobat, pdf.js and MuPDF do with unbalanced `Q`; the
  interpreter may log it.
-/

namespace SafePdf.Core.Content

open SafePdf

/-! ## Fixed-point numbers -/

/-- Scale of `Fixed`: a value is `raw / fixedScale`, i.e. 6 fractional decimal digits. -/
def fixedScale : Int := 1000000

/-- Bound on `Fixed.raw`: `|raw| ≤ 10¹⁸`, i.e. `|value| ≤ 10¹²`. -/
def fixedMaxRaw : Int := 1000000000000000000

/-- A saturating decimal fixed-point number `raw · 10⁻⁶` with `|raw| ≤ fixedMaxRaw`. -/
structure Fixed where
  /-- The value times `fixedScale`. -/
  raw : Int
  /-- Lower bound. -/
  lo : -fixedMaxRaw ≤ raw
  /-- Upper bound. -/
  hi : raw ≤ fixedMaxRaw
  deriving DecidableEq, Repr

/-- Rounded division for a positive divisor: nearest integer, ties toward +∞
(`Int` `/` is `Int.ediv`, i.e. floor for `d > 0`). -/
def roundDiv (p d : Int) : Int := (p + d / 2) / d

namespace Fixed

/-- Two `Fixed` values are equal when their raw values are. -/
@[ext] theorem ext {x y : Fixed} (h : x.raw = y.raw) : x = y := by
  cases x; cases y; cases h; rfl

/-- Saturate an integer raw value into range. -/
def clamp (r : Int) : Fixed :=
  if h1 : r < -fixedMaxRaw then ⟨-fixedMaxRaw, by unfold fixedMaxRaw; omega, by
    unfold fixedMaxRaw; omega⟩
  else if h2 : fixedMaxRaw < r then ⟨fixedMaxRaw, by unfold fixedMaxRaw; omega, by omega⟩
  else ⟨r, by omega, by omega⟩

/-- `clamp` is the identity on in-range raw values. -/
theorem clamp_raw_of_le {r : Int} (h1 : -fixedMaxRaw ≤ r) (h2 : r ≤ fixedMaxRaw) :
    (clamp r).raw = r := by
  unfold clamp
  split
  · omega
  · split
    · omega
    · rfl

/-- `clamp` of a `Fixed`'s own raw value gives it back. -/
theorem clamp_raw (x : Fixed) : clamp x.raw = x :=
  Fixed.ext (clamp_raw_of_le x.lo x.hi)

/-- Round a raw value at scale `fixedScale²` (a product of two raws) back to scale
`fixedScale`, saturating. -/
def ofScaled2 (p : Int) : Fixed := clamp (roundDiv p fixedScale)

/-- An exact product of a raw value by the scale rounds back to that value. -/
theorem ofScaled2_eq (x : Fixed) {p : Int} (h : p = x.raw * fixedScale) : ofScaled2 p = x := by
  unfold ofScaled2
  have : roundDiv p fixedScale = x.raw := by
    subst h; unfold roundDiv fixedScale; omega
  rw [this, clamp_raw]

/-- Zero. -/
def zero : Fixed := ⟨0, by unfold fixedMaxRaw; omega, by unfold fixedMaxRaw; omega⟩

/-- One. -/
def one : Fixed :=
  ⟨fixedScale, by unfold fixedMaxRaw fixedScale; omega, by unfold fixedMaxRaw fixedScale; omega⟩

/-- `zero.raw = 0`. -/
@[simp] theorem zero_raw : zero.raw = 0 := rfl

/-- `one.raw = fixedScale`. -/
@[simp] theorem one_raw : one.raw = fixedScale := rfl

instance : Inhabited Fixed := ⟨zero⟩

/-- An integer, saturating. -/
def ofInt (n : Int) : Fixed := clamp (n * fixedScale)

/-- Convert an exact decimal operand, rounding half up beyond 6 fractional digits and
saturating. Exact for scales `≤ 6`. (The power of ten is computed with GMP-backed `Nat ^`;
its size is that of the lexed token, whose digits the lexer has already accumulated.) -/
def ofDecimal (d : Decimal) : Fixed :=
  if d.scale ≤ 6 then clamp (d.mantissa * ((10 ^ (6 - d.scale) : Nat) : Int))
  else clamp (roundDiv d.mantissa ((10 ^ (d.scale - 6) : Nat) : Int))

/-- The exact decimal value (canonical form). -/
def toDecimal (x : Fixed) : Decimal := Decimal.normalize ⟨x.raw, 6⟩

/-- Addition, saturating. -/
def add (x y : Fixed) : Fixed := clamp (x.raw + y.raw)

/-- Negation (the range is symmetric, so exact). -/
def neg (x : Fixed) : Fixed := ⟨-x.raw, by have := x.hi; omega, by have := x.lo; omega⟩

/-- Subtraction, saturating. -/
def sub (x y : Fixed) : Fixed := clamp (x.raw - y.raw)

/-- Multiplication, rounded half up and saturating. -/
def mul (x y : Fixed) : Fixed := ofScaled2 (x.raw * y.raw)

/-- Division, rounded half up and saturating; division by zero yields `zero` (the
interpreter treats such operands as malformed before reaching here). -/
def div (x y : Fixed) : Fixed :=
  if y.raw = 0 then zero
  else if 0 < y.raw then clamp (roundDiv (x.raw * fixedScale) y.raw)
  else clamp (roundDiv (-(x.raw * fixedScale)) (-y.raw))

instance : Add Fixed := ⟨add⟩
instance : Sub Fixed := ⟨sub⟩
instance : Mul Fixed := ⟨mul⟩
instance : Div Fixed := ⟨div⟩
instance : Neg Fixed := ⟨neg⟩

/-- `x + 0 = x`. -/
theorem add_zero (x : Fixed) : add x zero = x := by
  simp only [add, zero_raw, Int.add_zero, clamp_raw]

/-- `0 + x = x`. -/
theorem zero_add (x : Fixed) : add zero x = x := by
  simp only [add, zero_raw, Int.zero_add, clamp_raw]

/-- Addition commutes. -/
theorem add_comm (x y : Fixed) : add x y = add y x := by
  simp only [add, Int.add_comm]

/-- `x · 1 = x` exactly. -/
theorem mul_one (x : Fixed) : mul x one = x := ofScaled2_eq x (by simp)

/-- `1 · x = x` exactly. -/
theorem one_mul (x : Fixed) : mul one x = x := ofScaled2_eq x (by simp [Int.mul_comm])

/-- `x · 0 = 0`. -/
theorem mul_zero (x : Fixed) : mul x zero = zero := ofScaled2_eq zero (by simp)

/-- `0 · x = 0`. -/
theorem zero_mul (x : Fixed) : mul zero x = zero := ofScaled2_eq zero (by simp)

/-- Multiplication commutes (the rounding is applied to the exact product). -/
theorem mul_comm (x y : Fixed) : mul x y = mul y x := by
  simp only [mul, Int.mul_comm]

end Fixed

/-! ## Matrices and points -/

/-- A point (in user or page space, per context). -/
structure Point where
  /-- Horizontal coordinate. -/
  x : Fixed
  /-- Vertical coordinate. -/
  y : Fixed
  deriving DecidableEq, Repr, Inhabited

/-- An affine transformation `[a b c d e f]` (ISO 32000-2 §8.3.3), acting on row vectors:
`(x, y) ↦ (a·x + c·y + e, b·x + d·y + f)`. -/
structure Matrix where
  /-- Entry `a`. -/
  a : Fixed
  /-- Entry `b`. -/
  b : Fixed
  /-- Entry `c`. -/
  c : Fixed
  /-- Entry `d`. -/
  d : Fixed
  /-- Entry `e` (x translation). -/
  e : Fixed
  /-- Entry `f` (y translation). -/
  f : Fixed
  deriving DecidableEq, Repr

namespace Matrix

/-- The identity matrix `[1 0 0 1 0 0]`. -/
def identity : Matrix := ⟨Fixed.one, Fixed.zero, Fixed.zero, Fixed.one, Fixed.zero, Fixed.zero⟩

instance : Inhabited Matrix := ⟨identity⟩

/-- The product `m × n` of 3×3 matrices (ISO 32000-2 §8.3.4): apply `m` first, then `n`.
`cm` sets `CTM' = M × CTM`. Each entry is computed exactly and rounded once. -/
def mul (m n : Matrix) : Matrix where
  a := Fixed.ofScaled2 (m.a.raw * n.a.raw + m.b.raw * n.c.raw)
  b := Fixed.ofScaled2 (m.a.raw * n.b.raw + m.b.raw * n.d.raw)
  c := Fixed.ofScaled2 (m.c.raw * n.a.raw + m.d.raw * n.c.raw)
  d := Fixed.ofScaled2 (m.c.raw * n.b.raw + m.d.raw * n.d.raw)
  e := Fixed.ofScaled2 (m.e.raw * n.a.raw + m.f.raw * n.c.raw + n.e.raw * fixedScale)
  f := Fixed.ofScaled2 (m.e.raw * n.b.raw + m.f.raw * n.d.raw + n.f.raw * fixedScale)

/-- Translation `[1 0 0 1 tx ty]`. -/
def translate (tx ty : Fixed) : Matrix := ⟨Fixed.one, Fixed.zero, Fixed.zero, Fixed.one, tx, ty⟩

/-- Scaling `[sx 0 0 sy 0 0]`. -/
def scale (sx sy : Fixed) : Matrix := ⟨sx, Fixed.zero, Fixed.zero, sy, Fixed.zero, Fixed.zero⟩

/-- Apply the matrix to a point; each coordinate computed exactly and rounded once. -/
def apply (m : Matrix) (p : Point) : Point where
  x := Fixed.ofScaled2 (p.x.raw * m.a.raw + p.y.raw * m.c.raw + m.e.raw * fixedScale)
  y := Fixed.ofScaled2 (p.x.raw * m.b.raw + p.y.raw * m.d.raw + m.f.raw * fixedScale)

/-- `I × m = m`. -/
theorem identity_mul (m : Matrix) : mul identity m = m := by
  cases m
  simp only [mul, identity]
  congr 1 <;> apply Fixed.ofScaled2_eq <;> simp [Int.mul_comm]

/-- `m × I = m`. -/
theorem mul_identity (m : Matrix) : mul m identity = m := by
  cases m
  simp only [mul, identity]
  congr 1 <;> apply Fixed.ofScaled2_eq <;> simp

/-- The identity fixes every point. -/
theorem apply_identity (p : Point) : apply identity p = p := by
  cases p
  simp only [apply, identity]
  congr 1 <;> apply Fixed.ofScaled2_eq <;> simp

end Matrix

/-- Text matrix and text line matrix (ISO 32000-2 §9.4.2). Not graphics state: reset by `BT`,
meaningless outside `BT … ET`, not saved by `q`/`Q`. -/
structure TextMatrices where
  /-- `Tm`. -/
  tm : Matrix := Matrix.identity
  /-- `Tlm`. -/
  tlm : Matrix := Matrix.identity
  deriving DecidableEq, Repr, Inhabited

/-! ## Paths and clipping -/

/-- A path segment, in page space (CTM already applied). `re`, `v` and `y` are expanded by
the interpreter (see the module doc). -/
inductive Segment where
  /-- `m`: start a new subpath. -/
  | moveTo (p : Point)
  /-- `l`: straight line. -/
  | lineTo (p : Point)
  /-- `c`: cubic Bézier with control points `c1`, `c2` ending at `p`. -/
  | curveTo (c1 c2 p : Point)
  /-- `h`: close the current subpath. -/
  | closePath
  deriving DecidableEq, Repr, Inhabited

/-- A path in page space. -/
structure Path where
  /-- The segments in construction order. -/
  segs : Array Segment := #[]
  deriving DecidableEq, Repr, Inhabited

/-- Fill rule (ISO 32000-2 §8.5.3.3). -/
inductive FillRule where
  /-- Nonzero winding number (`f`, `B`, `W`). -/
  | nonzero
  /-- Even-odd (`f*`, `B*`, `W*`). -/
  | evenOdd
  deriving DecidableEq, Repr, Inhabited

/-- One clipping path with its fill rule. -/
structure ClipPath where
  /-- The path, in page space. -/
  path : Path
  /-- The rule deciding its inside. -/
  rule : FillRule
  deriving DecidableEq, Repr, Inhabited

/-- The current clip: the intersection of all entries (newest first); `[]` is unclipped. -/
abbrev Clip := List ClipPath

/-! ## Colour -/

/-- A colour component in [0, 1], as `raw / fixedScale`. -/
structure Comp where
  /-- The value times `fixedScale`. -/
  raw : Int
  /-- `0 ≤ value`. -/
  lo : 0 ≤ raw
  /-- `value ≤ 1`. -/
  hi : raw ≤ fixedScale
  deriving DecidableEq, Repr

namespace Comp

/-- Component `0`. -/
def zero : Comp := ⟨0, by omega, by unfold fixedScale; omega⟩

/-- Component `1`. -/
def one : Comp := ⟨fixedScale, by unfold fixedScale; omega, by omega⟩

instance : Inhabited Comp := ⟨zero⟩

/-- Clamp an operand into [0, 1] (ISO 32000-2 §8.6.4: out-of-range values are adjusted to
the nearest valid value). -/
def ofFixed (x : Fixed) : Comp :=
  if h1 : x.raw < 0 then zero
  else if h2 : fixedScale < x.raw then one
  else ⟨x.raw, by omega, by omega⟩

/-- The component as a `Fixed`. -/
def toFixed (c : Comp) : Fixed :=
  ⟨c.raw, by have := c.lo; unfold fixedMaxRaw; omega,
    by have := c.hi; unfold fixedScale at this; unfold fixedMaxRaw; omega⟩

/-- `ofFixed` is the identity on in-range values. -/
theorem ofFixed_toFixed (c : Comp) : ofFixed c.toFixed = c := by
  have h1 := c.lo; have h2 := c.hi
  unfold ofFixed toFixed
  split
  · rename_i h; dsimp only at h; omega
  · split
    · rename_i _ h; dsimp only at h; omega
    · rfl

end Comp

/-- The device colour spaces (ISO 32000-2 §8.6.4). -/
inductive DeviceSpace where
  /-- `DeviceGray`. -/
  | gray
  /-- `DeviceRGB`. -/
  | rgb
  /-- `DeviceCMYK`. -/
  | cmyk
  deriving DecidableEq, Repr, Inhabited

/-- Number of components of a device space. -/
def DeviceSpace.nComps : DeviceSpace → Nat
  | .gray => 1
  | .rgb => 3
  | .cmyk => 4

/-- A colour space as the interpreter tracks it (see the module doc for the collapsing of
CIE-based and special spaces). -/
inductive ColorSpace where
  /-- A device space (also `ICCBased`, `CalGray`, `CalRGB` after fallback). -/
  | device (s : DeviceSpace)
  /-- `Pattern` (ISO 32000-2 §8.7). -/
  | pattern
  /-- `Indexed`, `Separation`, `DeviceN`, `Lab`, …: family name, operand count of
  `sc`/`scn`, and the device space colours are held in. -/
  | other (family : Name) (nComps : Nat) (alternate : DeviceSpace)
  deriving DecidableEq, Repr

instance : Inhabited ColorSpace := ⟨.device .gray⟩

/-- A colour value. Device colours carry their components; a pattern carries its resource
name (rendering falls back to a flat colour until patterns are supported). -/
inductive Color where
  /-- Gray level. -/
  | gray (g : Comp)
  /-- RGB. -/
  | rgb (r g b : Comp)
  /-- CMYK. -/
  | cmyk (c m y k : Comp)
  /-- A pattern resource. -/
  | pattern (name : Name)
  deriving DecidableEq, Repr

instance : Inhabited Color := ⟨.gray Comp.zero⟩

/-- Initial colour of a device space: black (ISO 32000-2 §8.6.4). -/
def DeviceSpace.initialColor : DeviceSpace → Color
  | .gray => .gray Comp.zero
  | .rgb => .rgb Comp.zero Comp.zero Comp.zero
  | .cmyk => .cmyk Comp.zero Comp.zero Comp.zero Comp.one

/-- Initial colour set by `CS`/`cs` (ISO 32000-2 §8.6.8); a pattern space starts with no
pattern, represented here as black. -/
def ColorSpace.initialColor : ColorSpace → Color
  | .device s => s.initialColor
  | .pattern => .gray Comp.zero
  | .other _ _ alt => alt.initialColor

/-! ## Line style -/

/-- Line cap style (`J`, ISO 32000-2 §8.4.3.3). -/
inductive LineCap where
  /-- 0: butt. -/
  | butt
  /-- 1: round. -/
  | round
  /-- 2: projecting square. -/
  | square
  deriving DecidableEq, Repr, Inhabited

/-- Line join style (`j`, ISO 32000-2 §8.4.3.4). -/
inductive LineJoin where
  /-- 0: miter. -/
  | miter
  /-- 1: round. -/
  | round
  /-- 2: bevel. -/
  | bevel
  deriving DecidableEq, Repr, Inhabited

/-- `J` operand → cap; other values are invalid (the interpreter ignores the operator). -/
def LineCap.ofNat? : Nat → Option LineCap
  | 0 => some .butt
  | 1 => some .round
  | 2 => some .square
  | _ => none

/-- `j` operand → join; other values are invalid. -/
def LineJoin.ofNat? : Nat → Option LineJoin
  | 0 => some .miter
  | 1 => some .round
  | 2 => some .bevel
  | _ => none

/-- Dash pattern (`d`, ISO 32000-2 §8.4.3.6), lengths in user space. `[]` is solid. -/
structure DashPattern where
  /-- Alternating dash and gap lengths. -/
  array : List Fixed := []
  /-- Phase. -/
  phase : Fixed := Fixed.zero
  deriving DecidableEq, Repr, Inhabited

/-- Stroke parameters (ISO 32000-2 §8.4.3), in user space. -/
structure LineStyle where
  /-- `w`; initial 1.0. -/
  width : Fixed := Fixed.one
  /-- `J`; initial butt. -/
  cap : LineCap := .butt
  /-- `j`; initial miter. -/
  join : LineJoin := .miter
  /-- `M`; initial 10.0. -/
  miterLimit : Fixed := Fixed.ofInt 10
  /-- `d`; initial solid. -/
  dash : DashPattern := {}
  deriving DecidableEq, Repr, Inhabited

/-! ## Text state -/

/-- Text rendering mode (`Tr`, ISO 32000-2 §9.3.6). -/
inductive TextRenderMode where
  /-- 0 -/
  | fill
  /-- 1 -/
  | stroke
  /-- 2 -/
  | fillStroke
  /-- 3: neither fill nor stroke (invisible text; relevant to C6). -/
  | invisible
  /-- 4 -/
  | fillClip
  /-- 5 -/
  | strokeClip
  /-- 6 -/
  | fillStrokeClip
  /-- 7 -/
  | clip
  deriving DecidableEq, Repr, Inhabited

/-- `Tr` operand → mode; other values are invalid. -/
def TextRenderMode.ofNat? : Nat → Option TextRenderMode
  | 0 => some .fill
  | 1 => some .stroke
  | 2 => some .fillStroke
  | 3 => some .invisible
  | 4 => some .fillClip
  | 5 => some .strokeClip
  | 6 => some .fillStrokeClip
  | 7 => some .clip
  | _ => none

/-- Whether glyphs in this mode paint anything (fill or stroke). -/
def TextRenderMode.paints : TextRenderMode → Bool
  | .invisible | .clip => false
  | _ => true

/-- Font selection by `Tf`: font resource name and size. -/
structure FontRef where
  /-- The `/Font` resource name. -/
  name : Name
  /-- `Tfs` (may be negative or zero; kept as given). -/
  size : Fixed
  deriving DecidableEq, Repr, Inhabited

/-- Text state parameters (ISO 32000-2 §9.3), part of the graphics state. -/
structure TextState where
  /-- `Tc`, unscaled text space units. -/
  charSpacing : Fixed := Fixed.zero
  /-- `Tw`. -/
  wordSpacing : Fixed := Fixed.zero
  /-- `Tz`, in percent; initial 100. -/
  horizScaling : Fixed := Fixed.ofInt 100
  /-- `TL`. -/
  leading : Fixed := Fixed.zero
  /-- `Tf`; none until set. -/
  font : Option FontRef := none
  /-- `Tr`. -/
  renderMode : TextRenderMode := .fill
  /-- `Ts`. -/
  rise : Fixed := Fixed.zero
  deriving DecidableEq, Repr, Inhabited

/-! ## Graphics state -/

/-- The graphics state (ISO 32000-2 §8.4.1 Tables 51–52) — the parameters the display list
needs. Defaults are the initial values at the start of a page. -/
structure GState where
  /-- Current transformation matrix, user → page space. -/
  ctm : Matrix := Matrix.identity
  /-- Current clip (intersection of entries). -/
  clip : Clip := []
  /-- Stroking colour space (`CS`). -/
  strokeSpace : ColorSpace := .device .gray
  /-- Stroking colour (`SC`, `G`, `RG`, `K`, …). -/
  strokeColor : Color := .gray Comp.zero
  /-- Non-stroking colour space (`cs`). -/
  fillSpace : ColorSpace := .device .gray
  /-- Non-stroking colour. -/
  fillColor : Color := .gray Comp.zero
  /-- Stroke parameters. -/
  line : LineStyle := {}
  /-- Text state parameters. -/
  text : TextState := {}
  /-- Stroking alpha (`/CA` in an ExtGState). -/
  strokeAlpha : Comp := Comp.one
  /-- Non-stroking alpha (`/ca`). -/
  fillAlpha : Comp := Comp.one
  /-- Rendering intent (`ri`, `/RI`). -/
  renderingIntent : Name := Name.ofString "RelativeColorimetric"
  /-- Flatness tolerance (`i`); initial 1.0. -/
  flatness : Fixed := Fixed.one
  deriving DecidableEq, Repr, Inhabited

/-! ## Save/restore stack -/

/-- The `q`/`Q` stack of saved graphics states, newest first. Its depth is kept within
`Limits.maxGStateDepth` by `push`. -/
structure GStack where
  /-- Saved states, newest first. -/
  saved : List GState := []
  deriving Repr, Inhabited

namespace GStack

/-- Number of saved states. -/
def depth (s : GStack) : Nat := s.saved.length

/-- The stack stays within the limit. -/
def Bounded (limits : Limits) (s : GStack) : Prop := s.depth ≤ limits.maxGStateDepth

/-- `q`: save `g`. Fails with `limitExceeded .gstateDepth` when the stack is full. -/
def push (limits : Limits) (s : GStack) (g : GState) : Except Error GStack :=
  if s.depth < limits.maxGStateDepth then .ok ⟨g :: s.saved⟩
  else .error (.limitExceeded .gstateDepth)

/-- Pop the newest saved state, if any. -/
def pop (s : GStack) : Option (GState × GStack) :=
  match s.saved with
  | [] => none
  | g :: rest => some (g, ⟨rest⟩)

/-- `Q`: restore the newest saved state; on an empty stack the current state `cur` is kept
and the stack is unchanged (unbalanced `Q` is ignored). -/
def restore (s : GStack) (cur : GState) : GState × GStack :=
  match s.pop with
  | some p => p
  | none => (cur, s)

/-- After a successful `push`, the depth is within the limit. -/
theorem push_depth_le {limits : Limits} {s s' : GStack} {g : GState}
    (h : push limits s g = .ok s') : s'.depth ≤ limits.maxGStateDepth := by
  unfold push at h
  split at h
  · cases h; simp only [depth, List.length_cons]; unfold depth at *; omega
  · cases h

/-- A successful `push` adds exactly one entry. -/
theorem push_depth {limits : Limits} {s s' : GStack} {g : GState}
    (h : push limits s g = .ok s') : s'.depth = s.depth + 1 := by
  unfold push at h
  split at h
  · cases h; simp [depth]
  · cases h

/-- `push` fails exactly when the stack is full. -/
theorem push_error_iff (limits : Limits) (s : GStack) (g : GState) :
    (∃ e, push limits s g = .error e) ↔ limits.maxGStateDepth ≤ s.depth := by
  unfold push
  split
  · constructor
    · rintro ⟨e, h⟩; cases h
    · intro; omega
  · exact ⟨fun _ => by omega, fun _ => ⟨_, rfl⟩⟩

/-- Popping after a successful push returns the saved state and the original stack. -/
theorem pop_push {limits : Limits} {s s' : GStack} {g : GState}
    (h : push limits s g = .ok s') : s'.pop = some (g, s) := by
  unfold push at h
  split at h
  · cases h; rfl
  · cases h

/-- `restore` after a successful push returns the saved state and the original stack. -/
theorem restore_push {limits : Limits} {s s' : GStack} {g : GState}
    (h : push limits s g = .ok s') (cur : GState) : s'.restore cur = (g, s) := by
  simp [restore, pop_push h]

/-- `Q` on an empty stack keeps the current state. -/
theorem restore_empty (cur : GState) : (({} : GStack).restore cur) = (cur, {}) := rfl

/-- `restore` never increases the depth. -/
theorem restore_depth_le (s : GStack) (cur : GState) : (s.restore cur).2.depth ≤ s.depth := by
  cases s with
  | mk saved =>
    cases saved with
    | nil => exact Nat.le_refl _
    | cons g rest => simp [restore, pop, depth]

/-- The empty stack is bounded. -/
theorem bounded_empty (limits : Limits) : Bounded limits {} := Nat.zero_le _

/-- `push` yields a bounded stack. -/
theorem push_bounded {limits : Limits} {s s' : GStack} {g : GState}
    (h : push limits s g = .ok s') : Bounded limits s' := push_depth_le h

/-- `restore` preserves boundedness. -/
theorem restore_bounded {limits : Limits} {s : GStack} (hb : Bounded limits s) (cur : GState) :
    Bounded limits (s.restore cur).2 := Nat.le_trans (restore_depth_le s cur) hb

end GStack

/-! ## Samples -/

#guard (Fixed.ofDecimal ⟨15, 1⟩).raw == 1500000
#guard (Fixed.ofDecimal ⟨-1234567, 7⟩).raw == -123457  -- -0.1234567 → -0.123457 (half up)
#guard (Fixed.ofDecimal ⟨-5, 7⟩).raw == 0              -- -0.0000005 → 0 (tie toward +∞)
#guard (Fixed.mul (Fixed.ofInt 3) (Fixed.ofDecimal ⟨5, 1⟩)).raw == 1500000
#guard (Fixed.div Fixed.one (Fixed.ofInt 3)).raw == 333333
#guard (Fixed.div Fixed.one (Fixed.ofInt (-3))).raw == -333333
#guard (Fixed.ofInt (10 ^ 15)).raw == fixedMaxRaw      -- saturates
#guard (Fixed.ofDecimal ⟨25, 1⟩).toDecimal == ⟨25, 1⟩
#guard (Matrix.apply (Matrix.translate (Fixed.ofInt 10) (Fixed.ofInt 20))
          ⟨Fixed.ofInt 1, Fixed.ofInt 2⟩) == ⟨Fixed.ofInt 11, Fixed.ofInt 22⟩
#guard Matrix.mul (Matrix.scale (Fixed.ofInt 2) (Fixed.ofInt 2))
          (Matrix.translate (Fixed.ofInt 5) Fixed.zero)
        == ⟨Fixed.ofInt 2, Fixed.zero, Fixed.zero, Fixed.ofInt 2, Fixed.ofInt 5, Fixed.zero⟩
#guard Matrix.mul (Matrix.translate (Fixed.ofInt 5) Fixed.zero)
          (Matrix.scale (Fixed.ofInt 2) (Fixed.ofInt 2))
        == ⟨Fixed.ofInt 2, Fixed.zero, Fixed.zero, Fixed.ofInt 2, Fixed.ofInt 10, Fixed.zero⟩
#guard (Comp.ofFixed (Fixed.ofInt 2)) == Comp.one
#guard (Comp.ofFixed (Fixed.ofInt (-1))) == Comp.zero
#guard LineCap.ofNat? 3 == none
#guard TextRenderMode.ofNat? 3 == some .invisible
#guard ((GStack.push {} {} {}).toOption.map GStack.depth) == some 1
#guard ((GStack.push { maxGStateDepth := 0 } {} {}).toOption.map GStack.depth) == none
#guard ((GStack.restore {} ({} : GState)).2.depth) == 0

end SafePdf.Core.Content
