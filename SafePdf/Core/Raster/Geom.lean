import SafePdf.Core.Content.GState
import SafePdf.Core.Doc

/-!
# Exact rational geometry and the page↔screen transform (task 7.1)

Plan.md §4 **C2** ("`toScreen zoom rot ∘ toPage zoom rot = id` for all zoom > 0,
rot ∈ {0,90,180,270} (over ℚ; the float version tested, with proven error bound if
feasible)"), §6 Phase 7 ("Proven: … C2 coordinate round-trips over ℚ"), §8
("Rational-arithmetic geometric model as proof reference; float implementation tested").
ISO 32000-2 references: §8.3 (coordinate systems, transformation matrices), §7.7.3.3
(`/Rotate`), §14.11.2 (page boxes).

This module is the **proof reference** for the rasterizer's geometry. It uses Lean core's
`Rat` (ℚ, in `Init`, no Mathlib); core's `grind` decides the field identities used here.

## Design decisions

* **Row-vector convention, as ISO 32000-2 §8.3.4 writes it.** A matrix `[a b c d e f]` maps
  `(x, y)` to `(a·x + c·y + e, b·x + d·y + f)`, i.e. `[x y 1] × M`. The product `m * n`
  (`Aff.mul`) is the ordinary 3×3 product `m × n`, so **`apply (m * n) p = apply n (apply m p)`**
  (`Aff.apply_mul`): the left factor acts first. This is exactly how the interpreter composes
  `cm` (`CTM' = M × CTM`, `Content.Matrix.mul m n`, same entry formulas); `Aff.ofMatrix_mul_exact`
  states the correspondence entry-wise before rounding. Over ℚ, `Aff.mul` is associative
  (`Aff.mul_assoc`); the `Fixed` product is not (it rounds), which is why the interpreter
  fixes one evaluation order.
* **`Fixed` → ℚ** is exact: `raw / 10⁶` (`Fixed.toRat`). One `Fixed` matrix application
  (`Content.Matrix.apply`) differs from the exact ℚ application of the same (converted)
  operands by at most `1/2 · 10⁻⁶` per coordinate when no saturation occurs
  (`Matrix.apply_x_err`, `Matrix.apply_y_err`): the `Fixed` code computes the exact sum of
  products at scale 10¹² and rounds once, half up.
* **The view transform.** `viewMatrix zoom rot box` maps page space (default user space,
  §8.3.2.3) to screen space: origin at the top-left corner of the *displayed* (rotated) box,
  `x` to the right, `y` **downward**, unit = `1/zoom` page units. `rot` is the page's
  clockwise display rotation (`Doc.Rotation`, already normalised mod 360 by
  `Doc.rotationOfInt`, rule A5: `-90` is `270`). For a box `[llx lly urx ury]`:
  - `r0`:   `(x, y) ↦ (z·(x − llx), z·(ury − y))`
  - `r90`:  `(x, y) ↦ (z·(y − lly), z·(x − llx))`
  - `r180`: `(x, y) ↦ (z·(urx − x), z·(y − lly))`
  - `r270`: `(x, y) ↦ (z·(ury − y), z·(urx − x))`
  Each is a matrix of determinant `−z²` (`viewMatrix_det`), so it is invertible for every
  `zoom ≠ 0`; `toPage` applies the general inverse `Aff.inv`, and the C2 round-trips
  (`toPage_toScreen`, `toScreen_toPage`) follow from `Aff.inv_apply_apply` /
  `Aff.apply_inv_apply`. The box corners land on the corners of the screen rectangle
  `[0, z·W'] × [0, z·H']` with `W'`, `H'` swapped for 90°/270° (`toScreen_corner_*`), and
  every point of the box lands inside that rectangle (`toScreen_mem`).
* **Rotation = page `/Rotate` + user rotation.** The rotation type is the existing
  `Doc.Rotation` (no new `Rot`), so the page's `/Rotate` feeds in unchanged. `rotAdd` adds
  quarter turns mod 4 (a commutative monoid with unit `r0`; it is degree addition mod 360,
  `rotationOfInt_degrees_add`); `toScreenView z pageRot userRot` uses `rotAdd pageRot userRot`
  and inherits C2 (`toPageView_toScreenView`, `toScreenView_toPageView`). Adding a quarter
  turn rotates the screen image clockwise, `(x, y) ↦ (H − y, x)` (`toScreen_rotAdd_r90`).
* **Zero-width boxes** need no special case: the transform is defined for any box; only
  `zoom ≠ 0` matters (the C2 theorems assume `0 < zoom`, as Plan.md states).

## Not done here (left to later Phase-7 tasks)

* The floating-point implementation and its tests (C2's "float version tested").
* An error bound for a *chain* of `Fixed` products (the single-application bound is proven;
  a chain needs a bound on the entries' magnitudes, which depends on the interpreter's CTM).
-/

namespace SafePdf.Core.Raster.Geom

open SafePdf.Core
open SafePdf.Core.Content (Fixed)

/-! ## Points and affine matrices over ℚ -/

/-- A point in the plane, exact rational coordinates. -/
structure Pt where
  /-- Horizontal coordinate. -/
  x : Rat
  /-- Vertical coordinate. -/
  y : Rat
  deriving DecidableEq, Repr, Inhabited

/-- An affine matrix `[a b c d e f]` (ISO 32000-2 §8.3.4), the 3×3 matrix
`[[a, b, 0], [c, d, 0], [e, f, 1]]` acting on row vectors `[x y 1]`. -/
structure Aff where
  /-- Entry `a` (row 1, column 1). -/
  a : Rat
  /-- Entry `b` (row 1, column 2). -/
  b : Rat
  /-- Entry `c` (row 2, column 1). -/
  c : Rat
  /-- Entry `d` (row 2, column 2). -/
  d : Rat
  /-- Entry `e` (horizontal translation). -/
  e : Rat
  /-- Entry `f` (vertical translation). -/
  f : Rat
  deriving DecidableEq, Repr, Inhabited

namespace Aff

/-- Two matrices are equal when their six entries are. -/
theorem ext' {m n : Aff} (ha : m.a = n.a) (hb : m.b = n.b) (hc : m.c = n.c) (hd : m.d = n.d)
    (he : m.e = n.e) (hf : m.f = n.f) : m = n := by
  cases m; cases n; simp_all

/-- The identity matrix `[1 0 0 1 0 0]`. -/
def id : Aff := ⟨1, 0, 0, 1, 0, 0⟩

/-- `p × m` with the row-vector convention: `(a·x + c·y + e, b·x + d·y + f)`. -/
def apply (m : Aff) (p : Pt) : Pt :=
  ⟨m.a * p.x + m.c * p.y + m.e, m.b * p.x + m.d * p.y + m.f⟩

/-- The product `m × n` (3×3 matrix product); `m` acts first (`apply_mul`). -/
def mul (m n : Aff) : Aff where
  a := m.a * n.a + m.b * n.c
  b := m.a * n.b + m.b * n.d
  c := m.c * n.a + m.d * n.c
  d := m.c * n.b + m.d * n.d
  e := m.e * n.a + m.f * n.c + n.e
  f := m.e * n.b + m.f * n.d + n.f

instance : Mul Aff := ⟨mul⟩

/-- `m * n` unfolds to `mul m n`. -/
theorem mul_def (m n : Aff) : m * n = mul m n := rfl

/-- The determinant of the linear part, `a·d − b·c`. -/
def det (m : Aff) : Rat := m.a * m.d - m.b * m.c

/-- The inverse matrix; meaningful when `det m ≠ 0` (`inv_mul`, `mul_inv`). -/
def inv (m : Aff) : Aff :=
  let k := (det m)⁻¹
  ⟨m.d * k, -m.b * k, -m.c * k, m.a * k, (m.c * m.f - m.d * m.e) * k,
    (m.b * m.e - m.a * m.f) * k⟩

/-- A translation by `(tx, ty)`. -/
def translate (tx ty : Rat) : Aff := ⟨1, 0, 0, 1, tx, ty⟩

/-- A scaling by `(sx, sy)`. -/
def scale (sx sy : Rat) : Aff := ⟨sx, 0, 0, sy, 0, 0⟩

/-- **Composition law** (row-vector convention): the left factor acts first. -/
theorem apply_mul (m n : Aff) (p : Pt) : apply (m * n) p = apply n (apply m p) := by
  simp only [mul_def, apply, mul, Pt.mk.injEq]; constructor <;> grind

/-- Matrix product over ℚ is associative. -/
theorem mul_assoc (l m n : Aff) : l * m * n = l * (m * n) := by
  simp only [mul_def, mul]; apply ext' <;> dsimp only <;> grind

/-- The identity is a left unit. -/
theorem id_mul (m : Aff) : id * m = m := by
  simp only [mul_def, mul, id]; apply ext' <;> dsimp only <;> grind

/-- The identity is a right unit. -/
theorem mul_id (m : Aff) : m * id = m := by
  simp only [mul_def, mul, id]; apply ext' <;> dsimp only <;> grind

/-- The identity fixes every point. -/
theorem apply_id (p : Pt) : apply id p = p := by
  simp only [apply, id]; cases p; simp only [Pt.mk.injEq]; constructor <;> grind

/-- The determinant is multiplicative. -/
theorem det_mul (m n : Aff) : det (m * n) = det m * det n := by
  simp only [det, mul_def, mul]; grind

/-- **Left inverse.** -/
theorem inv_mul (m : Aff) (h : det m ≠ 0) : inv m * m = id := by
  simp only [det] at h
  simp only [mul_def, mul, inv, det, id]; apply ext' <;> dsimp only <;> grind

/-- **Right inverse.** -/
theorem mul_inv (m : Aff) (h : det m ≠ 0) : m * inv m = id := by
  simp only [det] at h
  simp only [mul_def, mul, inv, det, id]; apply ext' <;> dsimp only <;> grind

/-- Applying `m` then its inverse is the identity. -/
theorem inv_apply_apply (m : Aff) (h : det m ≠ 0) (p : Pt) : apply (inv m) (apply m p) = p := by
  rw [← apply_mul, mul_inv m h, apply_id]

/-- Applying the inverse then `m` is the identity. -/
theorem apply_inv_apply (m : Aff) (h : det m ≠ 0) (q : Pt) : apply m (apply (inv m) q) = q := by
  rw [← apply_mul, inv_mul m h, apply_id]

/-- An invertible matrix is injective on points. -/
theorem apply_injective (m : Aff) (h : det m ≠ 0) {p q : Pt} (hpq : apply m p = apply m q) :
    p = q := by
  rw [← inv_apply_apply m h p, hpq, inv_apply_apply m h q]

end Aff

/-! ## From the interpreter's `Fixed` and the object model's `Decimal` to ℚ -/

/-- The exact value of a `Fixed`: `raw · 10⁻⁶`. -/
def Fixed.toRat (x : Fixed) : Rat := (x.raw : Rat) / 1000000

/-- The exact value of a `Decimal`: `mantissa · 10^(−scale)`. -/
def decimalToRat (d : Decimal) : Rat := (d.mantissa : Rat) / ((10 ^ d.scale : Nat) : Rat)

/-- A `Content.Point` as an exact point. -/
def ptOfPoint (p : Content.Point) : Pt := ⟨Fixed.toRat p.x, Fixed.toRat p.y⟩

/-- A `Content.Matrix` as an exact matrix. -/
def Aff.ofMatrix (m : Content.Matrix) : Aff :=
  ⟨Fixed.toRat m.a, Fixed.toRat m.b, Fixed.toRat m.c, Fixed.toRat m.d, Fixed.toRat m.e,
    Fixed.toRat m.f⟩

/-- The conversion `Fixed → ℚ` is injective: distinct `Fixed` values denote distinct
rationals (no information is lost). -/
theorem Fixed.toRat_injective {x y : Fixed} (h : Fixed.toRat x = Fixed.toRat y) : x = y := by
  have h2 : (x.raw : Rat) = (y.raw : Rat) := by
    have := congrArg (· * (1000000 : Rat)) h
    simp only [Fixed.toRat, Rat.div_def, Rat.mul_assoc] at this
    rwa [Rat.inv_mul_cancel _ (by decide), Rat.mul_one, Rat.mul_one] at this
  exact Content.Fixed.ext (Rat.intCast_inj.mp h2)

/-- The interpreter's identity matrix is the exact identity. -/
theorem Aff.ofMatrix_identity : Aff.ofMatrix Content.Matrix.identity = Aff.id := by
  simp only [Aff.ofMatrix, Content.Matrix.identity, Fixed.toRat, Content.Fixed.one_raw,
    Content.Fixed.zero_raw, Content.fixedScale, Aff.id]
  apply Aff.ext' <;> dsimp only <;> grind

/-- `Content.Matrix.mul` uses the same entry formulas as `Aff.mul`: each of the six exact
sums it rounds (at scale 10¹², via `Fixed.ofScaled2`) is, divided by 10¹², the corresponding
entry of the ℚ product of the converted operands. So the only difference between the
interpreter's product and the exact one is the final per-entry rounding (`ofScaled2_err`). -/
theorem Aff.ofMatrix_mul_exact (m n : Content.Matrix) :
    ((m.a.raw * n.a.raw + m.b.raw * n.c.raw : Int) : Rat) / 1000000000000 =
      (Aff.ofMatrix m * Aff.ofMatrix n).a ∧
    ((m.a.raw * n.b.raw + m.b.raw * n.d.raw : Int) : Rat) / 1000000000000 =
      (Aff.ofMatrix m * Aff.ofMatrix n).b ∧
    ((m.c.raw * n.a.raw + m.d.raw * n.c.raw : Int) : Rat) / 1000000000000 =
      (Aff.ofMatrix m * Aff.ofMatrix n).c ∧
    ((m.c.raw * n.b.raw + m.d.raw * n.d.raw : Int) : Rat) / 1000000000000 =
      (Aff.ofMatrix m * Aff.ofMatrix n).d ∧
    ((m.e.raw * n.a.raw + m.f.raw * n.c.raw + n.e.raw * Content.fixedScale : Int) : Rat) /
        1000000000000 = (Aff.ofMatrix m * Aff.ofMatrix n).e ∧
    ((m.e.raw * n.b.raw + m.f.raw * n.d.raw + n.f.raw * Content.fixedScale : Int) : Rat) /
        1000000000000 = (Aff.ofMatrix m * Aff.ofMatrix n).f := by
  simp only [Aff.mul_def, Aff.mul, Aff.ofMatrix, Fixed.toRat, Content.fixedScale,
    Rat.intCast_add, Rat.intCast_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- Rounding half up at scale 10⁶ errs by at most half a unit:
`−5·10⁵ < roundDiv p 10⁶ · 10⁶ − p ≤ 5·10⁵`. -/
theorem roundDiv_err (p : Int) :
    -500000 < Content.roundDiv p Content.fixedScale * 1000000 - p ∧
      Content.roundDiv p Content.fixedScale * 1000000 - p ≤ 500000 := by
  simp only [Content.roundDiv, Content.fixedScale]; omega

/-- `ofScaled2 p` without saturation (`|roundDiv p 10⁶| ≤ 10¹⁸`) is within `1/2 · 10⁻⁶` of
the exact value `p / 10¹²`. -/
theorem ofScaled2_err (p : Int)
    (hlo : -Content.fixedMaxRaw ≤ Content.roundDiv p Content.fixedScale)
    (hhi : Content.roundDiv p Content.fixedScale ≤ Content.fixedMaxRaw) :
    -(1 / 2000000 : Rat) ≤ Fixed.toRat (Fixed.ofScaled2 p) - (p : Rat) / 1000000000000 ∧
      Fixed.toRat (Fixed.ofScaled2 p) - (p : Rat) / 1000000000000 ≤ 1 / 2000000 := by
  have hc : (Fixed.ofScaled2 p).raw = Content.roundDiv p Content.fixedScale := by
    simp only [Fixed.ofScaled2]; rw [Fixed.clamp_raw_of_le hlo hhi]
  have ⟨h1, h2⟩ := roundDiv_err p
  generalize Content.roundDiv p Content.fixedScale = q at hc h1 h2
  have h1' : ((-500000 : Int) : Rat) ≤ ((q * 1000000 - p : Int) : Rat) :=
    Rat.intCast_le_intCast.mpr (by omega)
  have h2' : ((q * 1000000 - p : Int) : Rat) ≤ ((500000 : Int) : Rat) :=
    Rat.intCast_le_intCast.mpr h2
  simp only [Fixed.toRat, hc]
  simp only [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg] at h1' h2'
  constructor <;> grind

/-- **Fixed-vs-ℚ error bound, x coordinate.** Without saturation, one `Content.Matrix.apply`
differs from the exact application of the same operands by at most `1/2 · 10⁻⁶`. -/
theorem Matrix.apply_x_err (m : Content.Matrix) (p : Content.Point)
    (hlo : -Content.fixedMaxRaw ≤
      Content.roundDiv (p.x.raw * m.a.raw + p.y.raw * m.c.raw + m.e.raw * Content.fixedScale)
        Content.fixedScale)
    (hhi : Content.roundDiv (p.x.raw * m.a.raw + p.y.raw * m.c.raw + m.e.raw * Content.fixedScale)
        Content.fixedScale ≤ Content.fixedMaxRaw) :
    -(1 / 2000000 : Rat) ≤
        Fixed.toRat (Content.Matrix.apply m p).x - (Aff.apply (Aff.ofMatrix m) (ptOfPoint p)).x ∧
      Fixed.toRat (Content.Matrix.apply m p).x - (Aff.apply (Aff.ofMatrix m) (ptOfPoint p)).x ≤
        1 / 2000000 := by
  have h := ofScaled2_err _ hlo hhi
  have hx : (Aff.apply (Aff.ofMatrix m) (ptOfPoint p)).x =
      ((p.x.raw * m.a.raw + p.y.raw * m.c.raw + m.e.raw * Content.fixedScale : Int) : Rat) /
        1000000000000 := by
    simp only [Aff.apply, Aff.ofMatrix, ptOfPoint, Fixed.toRat, Content.fixedScale,
      Rat.intCast_add, Rat.intCast_mul]
    grind
  rw [hx]; exact h

/-- **Fixed-vs-ℚ error bound, y coordinate** (as `Matrix.apply_x_err`). -/
theorem Matrix.apply_y_err (m : Content.Matrix) (p : Content.Point)
    (hlo : -Content.fixedMaxRaw ≤
      Content.roundDiv (p.x.raw * m.b.raw + p.y.raw * m.d.raw + m.f.raw * Content.fixedScale)
        Content.fixedScale)
    (hhi : Content.roundDiv (p.x.raw * m.b.raw + p.y.raw * m.d.raw + m.f.raw * Content.fixedScale)
        Content.fixedScale ≤ Content.fixedMaxRaw) :
    -(1 / 2000000 : Rat) ≤
        Fixed.toRat (Content.Matrix.apply m p).y - (Aff.apply (Aff.ofMatrix m) (ptOfPoint p)).y ∧
      Fixed.toRat (Content.Matrix.apply m p).y - (Aff.apply (Aff.ofMatrix m) (ptOfPoint p)).y ≤
        1 / 2000000 := by
  have h := ofScaled2_err _ hlo hhi
  have hy : (Aff.apply (Aff.ofMatrix m) (ptOfPoint p)).y =
      ((p.x.raw * m.b.raw + p.y.raw * m.d.raw + m.f.raw * Content.fixedScale : Int) : Rat) /
        1000000000000 := by
    simp only [Aff.apply, Aff.ofMatrix, ptOfPoint, Fixed.toRat, Content.fixedScale,
      Rat.intCast_add, Rat.intCast_mul]
    grind
  rw [hy]; exact h

/-! ## Boxes and rotations -/

/-- A page box over ℚ (`[llx lly urx ury]`, §14.11.2). -/
structure Box where
  /-- Lower-left x. -/
  llx : Rat
  /-- Lower-left y. -/
  lly : Rat
  /-- Upper-right x. -/
  urx : Rat
  /-- Upper-right y. -/
  ury : Rat
  deriving DecidableEq, Repr, Inhabited

/-- The exact box of a resolved page rectangle (CropBox or MediaBox). -/
def Box.ofRect (r : Doc.Rect) : Box :=
  ⟨decimalToRat r.llx, decimalToRat r.lly, decimalToRat r.urx, decimalToRat r.ury⟩

/-- The `/Rotate` value of a rotation in degrees, in `{0, 90, 180, 270}`. -/
def rotDegrees : Doc.Rotation → Int
  | .r0 => 0
  | .r90 => 90
  | .r180 => 180
  | .r270 => 270

/-- `/Rotate` is normalised mod 360 (rule A5, §7.7.3.3): adding a multiple of 360 changes
nothing. -/
theorem rotationOfInt_add_360 (i k : Int) :
    Doc.rotationOfInt (i + 360 * k) = Doc.rotationOfInt i := by
  simp only [Doc.rotationOfInt]
  have : (i + 360 * k) % 360 = i % 360 := by omega
  rw [this]

/-- Every rotation is recovered from its degrees. -/
theorem rotationOfInt_rotDegrees (r : Doc.Rotation) : Doc.rotationOfInt (rotDegrees r) = r := by
  cases r <;> decide

/-- A negative multiple of 90 denotes the clockwise rotation it is congruent to:
`-90 ↦ 270`, `-180 ↦ 180`, `-270 ↦ 90`. -/
theorem rotationOfInt_neg :
    Doc.rotationOfInt (-90) = .r270 ∧ Doc.rotationOfInt (-180) = .r180 ∧
      Doc.rotationOfInt (-270) = .r90 := by
  decide

/-- Number of clockwise quarter turns of a rotation, `0 … 3`. -/
def rotQuarters : Doc.Rotation → Nat
  | .r0 => 0
  | .r90 => 1
  | .r180 => 2
  | .r270 => 3

/-- The rotation of `n` clockwise quarter turns (taken mod 4). -/
def rotOfQuarters (n : Nat) : Doc.Rotation :=
  match n % 4 with
  | 0 => .r0
  | 1 => .r90
  | 2 => .r180
  | _ => .r270

/-- Combine two clockwise rotations, e.g. the page's `/Rotate` with the viewer's user
rotation: the displayed rotation is their sum mod 360°. -/
def rotAdd (a b : Doc.Rotation) : Doc.Rotation := rotOfQuarters (rotQuarters a + rotQuarters b)

/-- `0°` is a right unit of `rotAdd`. -/
theorem rotAdd_r0 (a : Doc.Rotation) : rotAdd a .r0 = a := by cases a <;> decide

/-- `0°` is a left unit of `rotAdd`. -/
theorem r0_rotAdd (a : Doc.Rotation) : rotAdd .r0 a = a := by cases a <;> decide

/-- `rotAdd` is commutative. -/
theorem rotAdd_comm (a b : Doc.Rotation) : rotAdd a b = rotAdd b a := by
  cases a <;> cases b <;> decide

/-- `rotAdd` is associative. -/
theorem rotAdd_assoc (a b c : Doc.Rotation) : rotAdd (rotAdd a b) c = rotAdd a (rotAdd b c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- `rotAdd` is addition of degrees mod 360, as `/Rotate` is normalised (rule A5). -/
theorem rotationOfInt_degrees_add (a b : Doc.Rotation) :
    Doc.rotationOfInt (rotDegrees a + rotDegrees b) = rotAdd a b := by
  cases a <;> cases b <;> decide

/-! ## The view transform and C2 -/

/-- The page→screen matrix for zoom `z`, clockwise display rotation `r` and page box `bx`
(screen origin top-left, `y` downward). See the module doc for the four cases. -/
def viewMatrix (z : Rat) (r : Doc.Rotation) (bx : Box) : Aff :=
  match r with
  | .r0 => ⟨z, 0, 0, -z, -(z * bx.llx), z * bx.ury⟩
  | .r90 => ⟨0, z, z, 0, -(z * bx.lly), -(z * bx.llx)⟩
  | .r180 => ⟨-z, 0, 0, z, z * bx.urx, -(z * bx.lly)⟩
  | .r270 => ⟨0, -z, -z, 0, z * bx.ury, z * bx.urx⟩

/-- Page space → screen space. -/
def toScreen (z : Rat) (r : Doc.Rotation) (bx : Box) (p : Pt) : Pt :=
  (viewMatrix z r bx).apply p

/-- Screen space → page space: the inverse of the view matrix. -/
def toPage (z : Rat) (r : Doc.Rotation) (bx : Box) (q : Pt) : Pt :=
  (viewMatrix z r bx).inv.apply q

/-- The view matrix has determinant `−z²` for every rotation (the y-flip reverses
orientation; the rotations preserve it). -/
theorem viewMatrix_det (z : Rat) (r : Doc.Rotation) (bx : Box) :
    (viewMatrix z r bx).det = -(z * z) := by
  cases r <;> simp only [viewMatrix, Aff.det] <;> grind

/-- The view matrix is invertible for every non-zero zoom. -/
theorem viewMatrix_det_ne_zero {z : Rat} (hz : 0 < z) (r : Doc.Rotation) (bx : Box) :
    (viewMatrix z r bx).det ≠ 0 := by
  rw [viewMatrix_det]
  intro h
  have : z * z = 0 := by grind
  have : z = 0 := by
    rcases Rat.mul_eq_zero.mp this with h | h <;> exact h
  grind

/-- **C2 (page → screen → page).** For all zoom `> 0`, all four rotations and every box,
`toPage ∘ toScreen = id`. -/
theorem toPage_toScreen {z : Rat} (hz : 0 < z) (r : Doc.Rotation) (bx : Box) (p : Pt) :
    toPage z r bx (toScreen z r bx p) = p :=
  Aff.inv_apply_apply _ (viewMatrix_det_ne_zero hz r bx) p

/-- **C2 (screen → page → screen).** For all zoom `> 0`, all four rotations and every box,
`toScreen ∘ toPage = id`. -/
theorem toScreen_toPage {z : Rat} (hz : 0 < z) (r : Doc.Rotation) (bx : Box) (q : Pt) :
    toScreen z r bx (toPage z r bx q) = q :=
  Aff.apply_inv_apply _ (viewMatrix_det_ne_zero hz r bx) q

/-- C2 for a `/Rotate` integer: any multiple of 90 (negative allowed) is normalised by
`Doc.rotationOfInt` and the round-trip holds. -/
theorem toPage_toScreen_int {z : Rat} (hz : 0 < z) (rot : Int) (bx : Box) (p : Pt) :
    toPage z (Doc.rotationOfInt rot) bx (toScreen z (Doc.rotationOfInt rot) bx p) = p :=
  toPage_toScreen hz _ bx p

/-- Distinct page points land on distinct screen points. -/
theorem toScreen_injective {z : Rat} (hz : 0 < z) (r : Doc.Rotation) (bx : Box) {p q : Pt}
    (h : toScreen z r bx p = toScreen z r bx q) : p = q :=
  Aff.apply_injective _ (viewMatrix_det_ne_zero hz r bx) h

/-- Screen width and height of the displayed box at zoom `z` (swapped for 90°/270°). -/
def screenSize (z : Rat) (r : Doc.Rotation) (bx : Box) : Rat × Rat :=
  let w := z * (bx.urx - bx.llx)
  let h := z * (bx.ury - bx.lly)
  match r with
  | .r0 | .r180 => (w, h)
  | .r90 | .r270 => (h, w)

/-- The top-left corner of the displayed page is the screen origin: for `r0` it is the
page's upper-left corner `(llx, ury)`. -/
theorem toScreen_corner_r0 (z : Rat) (bx : Box) :
    toScreen z .r0 bx ⟨bx.llx, bx.ury⟩ = ⟨0, 0⟩ ∧
      toScreen z .r0 bx ⟨bx.urx, bx.lly⟩ =
        ⟨(screenSize z .r0 bx).1, (screenSize z .r0 bx).2⟩ := by
  simp only [toScreen, viewMatrix, Aff.apply, screenSize, Pt.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> grind

/-- For `r90` (clockwise) the page's lower-left corner `(llx, lly)` is the screen origin. -/
theorem toScreen_corner_r90 (z : Rat) (bx : Box) :
    toScreen z .r90 bx ⟨bx.llx, bx.lly⟩ = ⟨0, 0⟩ ∧
      toScreen z .r90 bx ⟨bx.urx, bx.ury⟩ =
        ⟨(screenSize z .r90 bx).1, (screenSize z .r90 bx).2⟩ := by
  simp only [toScreen, viewMatrix, Aff.apply, screenSize, Pt.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> grind

/-- For `r180` the page's lower-right corner `(urx, lly)` is the screen origin. -/
theorem toScreen_corner_r180 (z : Rat) (bx : Box) :
    toScreen z .r180 bx ⟨bx.urx, bx.lly⟩ = ⟨0, 0⟩ ∧
      toScreen z .r180 bx ⟨bx.llx, bx.ury⟩ =
        ⟨(screenSize z .r180 bx).1, (screenSize z .r180 bx).2⟩ := by
  simp only [toScreen, viewMatrix, Aff.apply, screenSize, Pt.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> grind

/-- For `r270` the page's upper-right corner `(urx, ury)` is the screen origin. -/
theorem toScreen_corner_r270 (z : Rat) (bx : Box) :
    toScreen z .r270 bx ⟨bx.urx, bx.ury⟩ = ⟨0, 0⟩ ∧
      toScreen z .r270 bx ⟨bx.llx, bx.lly⟩ =
        ⟨(screenSize z .r270 bx).1, (screenSize z .r270 bx).2⟩ := by
  simp only [toScreen, viewMatrix, Aff.apply, screenSize, Pt.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> grind

/-! ## Page `/Rotate` combined with the viewer's rotation -/

/-- Page → screen for a page with `/Rotate` `pageRot`, shown with an additional clockwise
user rotation `userRot`: the view transform of the combined rotation. -/
def toScreenView (z : Rat) (pageRot userRot : Doc.Rotation) (bx : Box) (p : Pt) : Pt :=
  toScreen z (rotAdd pageRot userRot) bx p

/-- Screen → page, inverse of `toScreenView`. -/
def toPageView (z : Rat) (pageRot userRot : Doc.Rotation) (bx : Box) (q : Pt) : Pt :=
  toPage z (rotAdd pageRot userRot) bx q

/-- **C2 with a user rotation (page → screen → page).** -/
theorem toPageView_toScreenView {z : Rat} (hz : 0 < z) (pageRot userRot : Doc.Rotation)
    (bx : Box) (p : Pt) :
    toPageView z pageRot userRot bx (toScreenView z pageRot userRot bx p) = p :=
  toPage_toScreen hz _ bx p

/-- **C2 with a user rotation (screen → page → screen).** -/
theorem toScreenView_toPageView {z : Rat} (hz : 0 < z) (pageRot userRot : Doc.Rotation)
    (bx : Box) (q : Pt) :
    toScreenView z pageRot userRot bx (toPageView z pageRot userRot bx q) = q :=
  toScreen_toPage hz _ bx q

/-- Adding a quarter turn to the rotation rotates the screen image a quarter turn clockwise:
a point at `(x, y)` in the `W × H` image (y downward) moves to `(H − y, x)`. This is the
geometric meaning of `rotAdd` and of the four `viewMatrix` cases. -/
theorem toScreen_rotAdd_r90 (z : Rat) (r : Doc.Rotation) (bx : Box) (p : Pt) :
    toScreen z (rotAdd r .r90) bx p =
      ⟨(screenSize z r bx).2 - (toScreen z r bx p).y, (toScreen z r bx p).x⟩ := by
  cases r <;>
    simp only [rotAdd, rotQuarters, rotOfQuarters, toScreen, viewMatrix, Aff.apply,
      screenSize, Pt.mk.injEq] <;> constructor <;> grind

/-- `p` lies in the closed box `bx`. -/
def Box.Contains (bx : Box) (p : Pt) : Prop :=
  bx.llx ≤ p.x ∧ p.x ≤ bx.urx ∧ bx.lly ≤ p.y ∧ p.y ≤ bx.ury

/-- Scaling by `z > 0` preserves `0 ≤ d ≤ w`. -/
private theorem scaled_bounds {z d w : Rat} (hz : 0 < z) (h0 : 0 ≤ d) (h1 : d ≤ w) :
    0 ≤ z * d ∧ z * d ≤ z * w :=
  ⟨Rat.mul_nonneg (Rat.le_of_lt hz) h0, Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hz)⟩

/-- **Box mapping.** For zoom `> 0`, every point of the page box lands in the screen
rectangle `[0, W] × [0, H]` (`(W, H) = screenSize z r bx`), for all four rotations. -/
theorem toScreen_mem {z : Rat} (hz : 0 < z) (r : Doc.Rotation) (bx : Box) {p : Pt}
    (hp : bx.Contains p) :
    0 ≤ (toScreen z r bx p).x ∧ (toScreen z r bx p).x ≤ (screenSize z r bx).1 ∧
      0 ≤ (toScreen z r bx p).y ∧ (toScreen z r bx p).y ≤ (screenSize z r bx).2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have bx1 := scaled_bounds (d := p.x - bx.llx) (w := bx.urx - bx.llx) hz (by grind) (by grind)
  have bx2 := scaled_bounds (d := bx.urx - p.x) (w := bx.urx - bx.llx) hz (by grind) (by grind)
  have by1 := scaled_bounds (d := p.y - bx.lly) (w := bx.ury - bx.lly) hz (by grind) (by grind)
  have by2 := scaled_bounds (d := bx.ury - p.y) (w := bx.ury - bx.lly) hz (by grind) (by grind)
  cases r <;> simp only [toScreen, viewMatrix, Aff.apply, screenSize] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-! ## Concrete checks (box `[10 20 210 120]`, zoom 3/2) -/

/-- The example box: 200 wide, 100 tall. -/
private def exBox : Box := ⟨10, 20, 210, 120⟩

/-- An example point near the box's lower-left corner. -/
private def exPt : Pt := ⟨11, 21⟩

-- r0: (11,21) is 1 right of the left edge, 99 below the top: (1.5, 148.5).
#guard toScreen (3/2) .r0 exBox exPt == ⟨3/2, 297/2⟩
-- r90: screen x = z·(y − lly) = 1.5, screen y = z·(x − llx) = 1.5.
#guard toScreen (3/2) .r90 exBox exPt == ⟨3/2, 3/2⟩
-- r180: screen x = z·(urx − x) = 298.5, screen y = z·(y − lly) = 1.5.
#guard toScreen (3/2) .r180 exBox exPt == ⟨597/2, 3/2⟩
-- r270: screen x = z·(ury − y) = 148.5, screen y = z·(urx − x) = 298.5.
#guard toScreen (3/2) .r270 exBox exPt == ⟨297/2, 597/2⟩
-- Round-trips, all four rotations, both directions.
#guard [Doc.Rotation.r0, .r90, .r180, .r270].all fun r =>
  toPage (3/2) r exBox (toScreen (3/2) r exBox exPt) == exPt &&
    toScreen (3/2) r exBox (toPage (3/2) r exBox ⟨7, -5/3⟩) == ⟨7, -5/3⟩
-- Screen sizes: 300 × 150, swapped for 90°/270°.
#guard screenSize (3/2) .r0 exBox == (300, 150) && screenSize (3/2) .r90 exBox == (150, 300)
-- `/Rotate -90` is 270, `/Rotate 450` is 90.
#guard Doc.rotationOfInt (-90) == .r270 && Doc.rotationOfInt 450 == .r90
-- `cm` composition order: scale then translate, as `[x y 1] × S × T`.
#guard Aff.apply (Aff.scale 2 3 * Aff.translate 1 1) ⟨1, 1⟩ == ⟨3, 4⟩
-- Page `/Rotate 270` plus user rotation 180 displays at 90°; same image as `toScreen … .r90`.
#guard rotAdd .r270 .r180 == .r90 && rotAdd .r90 .r270 == .r0
#guard toScreenView (3/2) .r270 .r180 exBox exPt == toScreen (3/2) .r90 exBox exPt
#guard toPageView (3/2) .r270 .r180 exBox (toScreenView (3/2) .r270 .r180 exBox exPt) == exPt
-- A quarter turn on top of r0 maps (x, y) to (H − y, x) with H = 150.
#guard toScreen (3/2) (rotAdd .r0 .r90) exBox exPt == ⟨150 - 297/2, 3/2⟩
-- The inverse of a general invertible matrix.
#guard Aff.apply (Aff.inv ⟨2, 1, 1, 1, 5, -7⟩) (Aff.apply ⟨2, 1, 1, 1, 5, -7⟩ ⟨1/3, 4⟩) == ⟨1/3, 4⟩
-- `Fixed` → ℚ: 1.5 is raw 1 500 000.
#guard Fixed.toRat (Fixed.clamp 1500000) == 3/2

end SafePdf.Core.Raster.Geom
