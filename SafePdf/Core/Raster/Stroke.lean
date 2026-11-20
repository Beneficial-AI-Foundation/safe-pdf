import SafePdf.Core.Raster.Fill
import SafePdf.Core.Content.DisplayList

/-!
# Stroking: path → outline polygons (task 7.2b)

Plan.md §6 Phase 7 ("stroking (width, caps, joins, miter limit, dashes)"; "Proven:
totality, resource bounds (S3)"), §4 **S3**. ISO 32000-2 §8.4.3 (line width §8.4.3.2, cap
§8.4.3.3, join §8.4.3.4, miter limit §8.4.3.5, dash pattern §8.4.3.6), §8.5.3.2 (stroking,
degenerate subpaths).

## Pipeline

The stroke is built as a set of convex polygons in **device subpixel units** (`Fill.FPt`)
that are handed, all together, to 7.2a's scanline filler with the **nonzero** rule.

1. **Centre line.** The page-space path goes through 7.2a's `ofContentPath view` and is
   flattened into subpaths of points (`subpaths`), with 7.2a's chord count `segCount` and
   exact subdivision points `bezAt` (so the centre line is within `tol + ½` subpixel units of
   the curve, `Fill.flatten_err_tol`). Flattening in device space with the device tolerance is
   equivalent to flattening in user space with the tolerance scaled by the CTM's norm, and
   needs no inverse mapping of points. Interior chord vertices of a curve are marked
   `smooth`; they get a miter join with a small fixed limit (`smoothMiterLimit`) instead of the
   path's join style.
2. **The pen.** Stroke geometry is defined in user space: a circular pen of diameter `w`
   under the CTM is an ellipse in device space. Let `L` be the linear part of
   `CTM × view × 256` (user space → device subpixel units). For a device chord `D` the user
   direction is `U = L⁻¹·D`; with `ℓ ≈ |U|` (`sqrtQ`) the device offsets are
   `A = (w/2)/ℓ · D` (along the chord, user length `w/2`) and
   `B = (w/2)/ℓ · L·J·U` (the user-space left normal of length `w/2`, `J` = rotation by 90°).
   Every pen point is `c + α·A + β·B` with `α² + β² = 1`; offsets, caps and joins only use
   `A` and `B`. A non-uniform CTM therefore gives the correct elliptic pen (tested with x
   scaled by 3).
   - **Zero width** (§8.4.3.2, "thinnest line"), and a **degenerate CTM** (`det = 0`), use
     a *hairline* pen: a device-space circle of diameter 1 pixel (`L` replaced by the
     identity on subpixel units, radius 128). With a degenerate CTM user space has no
     lengths, so dashes are ignored (solid hairline); with zero width and an invertible CTM
     dashes still use user-space lengths.
3. **Dashes** (§8.4.3.6) are walked along the polyline in user-space lengths. An array with
   an odd number of elements is doubled (`[3] ≡ [3 3]`) so element parity is on/off; the phase
   is reduced modulo the period (`Rat.floor`, no loop) and restarts at every subpath. A
   negative element or a zero period (all zeros) means **solid**. A zero-length dash is a dot
   (round cap → pen disc, square cap → square oriented along the path, butt → nothing). Each
   dash gets caps at both ends and joins at the vertices it passes.
   **Bound**: the number of dash steps of a path is estimated before walking
   (`dashEstimate`, exact over ℚ); a path whose estimate exceeds `Config.maxDashSteps`
   (`Limits.maxDashSteps`, 100 000) is stroked **solid** instead (MuPDF also ignores dash patterns that are too
   fine). The walk itself runs on fuel `#segments + estimate + 2`.
4. **Pieces.** Each (piece of a) segment is the parallelogram `p ± B … q ± B`; a square cap
   adds `[c − A ± B]`; a round cap and a round join add the full pen polygon at the point (the
   half inside the segment overlaps it); a bevel join adds the triangle `v, v + σB₁, v + σB₂`
   on the outer side `σ`; a miter join adds `v, v + σB₁, tip, v + σB₂` with
   `tip = v + σ(B₁ + B₂)/(1 + cos θ)` when `(1 + cos θ)·ML² ≥ 2` (⇔ `1/sin(φ/2) ≤ ML`, φ the
   angle between the segments, θ = π − φ), else the bevel. The outer side is computed in pen
   space: the turn is left iff `cross(D₁, D₂)·det L > 0`, and the outer side is then the
   right one (`σ = −1`). Closed subpaths get a join at the start vertex and no caps; open
   ones get caps. A degenerate subpath (all points equal) is painted only with round caps, as
   a disc (§8.5.3.2).
5. **Integer frame** (task 7.2i). Per chord, the exact offsets `A`, `B` and the pen-space
   unit tangent `u/ℓ` are rounded once to the frame grid (`gridQ`: multiples of `2⁻¹⁶`,
   `gridQ_err`); so are the pen circle points and the dash centres. Everything after that is
   integer arithmetic: a point `c + α·A + β·B` is one rounded division by `2³²`
   (`off`), the miter test is `⌈2·2³²/ML²⌉ ≤ 2³² + t₁·t₂` (`dminOf`, `miterOK`), the tip uses
   `round(2⁴⁸/(2³² + t₁·t₂))` (`tipPt`), polygon orientation is a shoelace sign (`areaNeg`).
   These run in `Int64` when the frame is small (`SegG.small`: offsets ≤ 2⁴⁴ grid units, i.e.
   pen radii up to 2²⁰ px; chords ≤ 2³⁰ units) and otherwise in exact `Int`, with the same
   result. The chord geometry itself (`mkSeg`) evaluates the exact rationals on
   common-denominator integer forms (`IMat`), normalising only `|u|²` for `sqrtQ`.
   **Specification:** section 10 writes the same pipeline in plain `Rat` arithmetic
   (`strokeEdgesSpec`, `strokeDPathSpec`, `mkSegSpec`); the suite `raster-stroke-spec` checks
   edge-for-edge equality on 8000 pseudo-random cases. Rounding to the grid moves a point by
   at most `2⁻¹⁷` subpixel units per rounded term before the final rounding to `1/256` px.
6. **Fill.** The pen polygon is the ellipse sampled at the exactly-on-circle rational points
   `((m² − j²)/(m² + j²), 2jm/(m² + j²))`, `j < m`, of each quarter (`circleTable`), with `m`
   the least value in `[1, Config.arcCap]` (`Limits.arcSegCap`) such that the chord sagitta bound
   `r·‖L‖_F / (2m²)` is at most `tol`. All pieces are **convex** and every polygon is emitted
   with the **same orientation** (`emit` reverses polygons of negative shoelace area). With
   one orientation, each piece has winding number `+1` (or each `−1`) inside and `0` outside,
   so the winding number of the union is the (non-zero) count of pieces covering a point:
   nonzero filling paints exactly the union, and overlaps (joins over segments, caps over
   pieces, a path crossing itself) are painted once. With *mixed* orientations two
   overlapping pieces could cancel to winding 0 and leave a hole — that is why `emit`
   normalises.

## What is proven

* **Square root** (`sqrtQ_spec`): for `q ≥ 0`, `s = sqrtQ q` satisfies `0 ≤ s`, `s² ≤ q` and
  `q < (s + 1/D)²` with `D = q.den · 2²⁰`; and (`sqrtQ_rel`) for `q > 0`, `1/D ≤ s / 2²⁰`, so
  `s ≤ √q < s·(1 + 2⁻²⁰)`: every length and unit normal is accurate to a relative
  `2⁻²⁰ ≈ 10⁻⁶`, i.e. offsets are within `w/2 · 10⁻⁶` (pen units) of exact before the final
  rounding to `1/256` px (± ½ unit per coordinate); rounding to the frame grid adds at most
  `2⁻¹⁷` subpixel units per offset coordinate (`gridQ_err`).
* **S3 work bound** (`strokeDPath_size_le`): the stroke of a device path has at most
  `3·pen.polyCap·(P + cfg.maxDashSteps + S)` edges, where `P` is the number of flattened
  points and `S` the number of subpaths; `subpaths_bound` gives `P ≤ max 2 cfg.segCap · n`
  and `S ≤ n + 1` for a path of `n` segments (`strokeEdges_size_le` combines them, with
  `pen.polyCap = cfg.polyCap`, `Geo.make_polyCap`). Every emitted polygon has at most
  `polyCap = 4·arcCap` vertices (a runtime guard in `emit`, never hit by construction: the
  largest polygon is the pen with `4·m ≤ 4·arcCap` points). Combined
  with `Fill.fillEdgesCounted_steps_le` this bounds the whole stroke rasterization.
* **Totality** by construction (folds, structural recursion, fuel with proven bounds).

## Tested (`#guard`s below, suites `Tests/RasterStroke.lean`, `Tests/RasterStrokeSpec.lean`)

Width-2 butt line = exact rectangle; square − butt cap area = `w²`; miter vs bevel at a right
angle (exact areas); miter-limit fallback at a sharp angle; round join/cap areas; dash
coverage ratio; non-uniform CTM; zero-width line visible; dots for zero-length dashes; the
fast stroker equals the reference on a few of these.

## Caps

From `SafePdf.Limits` through `Fill.Config` (task 7.2d): `maxDashSteps` (100 000 dash steps
per path; above it the path is stroked solid), `arcSegCap` (64 chords per quarter of the pen
ellipse), `curveSegCap` and `coordLimit` (as for filling). Local constants:
`smoothMiterLimit` (4), `sqrtBits` (20), `frameBits` (16). None raises an error: they only
coarsen absurd inputs (see the `Limits` docstrings).
-/

namespace SafePdf.Core.Raster.Stroke

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill
open SafePdf.Core.Content (LineCap LineJoin LineStyle DashPattern)

/-! ## 1. Square roots over ℚ -/

/-- Bits of relative precision of `sqrtQ`. -/
def sqrtBits : Nat := 20

/-- The denominator `q.den · 2^sqrtBits` of `sqrtQ q`. -/
def sqrtDen (q : Rat) : Nat := q.den * 2 ^ sqrtBits

/-- Lower approximation of `√q` (`0` for `q ≤ 0`): `⌊√(num · den · 4^K)⌋ / (den · 2^K)`. -/
def sqrtQ (q : Rat) : Rat :=
  ((q.num.toNat * q.den * 4 ^ sqrtBits).sqrt : Rat) / (sqrtDen q : Rat)

/-- A non-negative rational is its numerator (as a `Nat`) over its denominator. -/
private theorem rat_eq_div (q : Rat) (hq : 0 ≤ q) : q = (q.num.toNat : Rat) / (q.den : Rat) := by
  have h1 : (q.num.toNat : Int) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have h2 : ((q.num.toNat : Nat) : Rat) = ((q.num : Int) : Rat) := by
    rw [← h1]; rfl
  have h3 := Rat.num_divInt_den q
  rw [Rat.divInt_eq_div] at h3
  rw [h2]; exact h3.symm

/-- For `D > 0`: `(r/D)² ≤ N/D²` iff `r² ≤ N` — the cast step of `sqrtQ_spec`. -/
private theorem sq_div_le {r N D : Nat} (hD : 0 < D) (h : r * r ≤ N) :
    (r : Rat) / D * ((r : Rat) / D) ≤ (N : Rat) / ((D : Rat) * D) := by
  have hD' : (0 : Rat) < D := Rat.natCast_lt_natCast.mpr hD
  have hDD : (0 : Rat) < (D : Rat) * D := Rat.mul_pos hD' hD'
  have hc : ((r * r : Nat) : Rat) ≤ (N : Rat) := Rat.natCast_le_natCast.mpr h
  have e : (r : Rat) / D * ((r : Rat) / D) = ((r * r : Nat) : Rat) / ((D : Rat) * D) := by
    rw [Rat.natCast_mul]; have : (D : Rat) ≠ 0 := Rat.ne_of_gt hD'; grind
  rw [e]
  exact Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt (Rat.inv_pos.mpr hDD))

/-- For `D > 0`: `N < (r+1)²` gives `N/D² < ((r+1)/D)²`. -/
private theorem lt_sq_div {r N D : Nat} (hD : 0 < D) (h : N < (r + 1) * (r + 1)) :
    (N : Rat) / ((D : Rat) * D) < ((r : Rat) / D + 1 / D) * ((r : Rat) / D + 1 / D) := by
  have hD' : (0 : Rat) < D := Rat.natCast_lt_natCast.mpr hD
  have hDD : (0 : Rat) < (D : Rat) * D := Rat.mul_pos hD' hD'
  have hc : (N : Rat) < (((r + 1) * (r + 1) : Nat) : Rat) := Rat.natCast_lt_natCast.mpr h
  have e : ((r : Rat) / D + 1 / D) * ((r : Rat) / D + 1 / D) =
      (((r + 1) * (r + 1) : Nat) : Rat) / ((D : Rat) * D) := by
    rw [Rat.natCast_mul, Rat.natCast_add]; have : (D : Rat) ≠ 0 := Rat.ne_of_gt hD'
    have h1 : ((1 : Nat) : Rat) = 1 := rfl
    rw [h1]; grind
  rw [e]
  exact Rat.mul_lt_mul_of_pos_right hc (Rat.inv_pos.mpr hDD)

/-- `num · den · 4^K / (den · 2^K)² = num / den`. -/
private theorem sqrt_scale (n d : Nat) (hd : 0 < d) :
    ((n * d * 4 ^ sqrtBits : Nat) : Rat) / (((d * 2 ^ sqrtBits : Nat) : Rat) *
      ((d * 2 ^ sqrtBits : Nat) : Rat)) = (n : Rat) / (d : Rat) := by
  have h4 : (4 : Nat) ^ sqrtBits = 2 ^ sqrtBits * 2 ^ sqrtBits := by
    rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_pow]
  rw [h4]
  have hd' : (d : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_lt_natCast.mpr hd)
  have hp : ((2 ^ sqrtBits : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (Rat.natCast_lt_natCast.mpr (Nat.two_pow_pos _))
  simp only [Rat.natCast_mul]
  grind

/-- **Square-root bound.** For `q ≥ 0`, `s = sqrtQ q` satisfies `0 ≤ s`, `s² ≤ q < (s + 1/D)²`
with `D = sqrtDen q = q.den · 2^20`. -/
theorem sqrtQ_spec (q : Rat) (hq : 0 ≤ q) :
    0 ≤ sqrtQ q ∧ sqrtQ q * sqrtQ q ≤ q ∧
      q < (sqrtQ q + 1 / (sqrtDen q : Rat)) * (sqrtQ q + 1 / (sqrtDen q : Rat)) := by
  have hD : 0 < sqrtDen q := Nat.mul_pos q.den_pos (Nat.two_pow_pos _)
  have hD' : (0 : Rat) < (sqrtDen q : Rat) := Rat.natCast_lt_natCast.mpr hD
  have e := sqrt_scale q.num.toNat q.den q.den_pos
  rw [← rat_eq_div q hq] at e
  have hs1 := Nat.sqrt_le (q.num.toNat * q.den * 4 ^ sqrtBits)
  have hs2 := Nat.lt_succ_sqrt (q.num.toNat * q.den * 4 ^ sqrtBits)
  refine ⟨?_, ?_, ?_⟩
  · simp only [sqrtQ]
    exact Rat.mul_nonneg (Rat.natCast_nonneg) (Rat.le_of_lt (Rat.inv_pos.mpr hD'))
  · have h := sq_div_le hD hs1
    have e' : ((q.num.toNat * q.den * 4 ^ sqrtBits : Nat) : Rat) /
        ((sqrtDen q : Rat) * (sqrtDen q : Rat)) = q := e
    rw [e'] at h; exact h
  · have h := lt_sq_div (r := (q.num.toNat * q.den * 4 ^ sqrtBits).sqrt) hD hs2
    have e' : ((q.num.toNat * q.den * 4 ^ sqrtBits : Nat) : Rat) /
        ((sqrtDen q : Rat) * (sqrtDen q : Rat)) = q := e
    rw [e'] at h; exact h

/-- **Relative precision.** For `q > 0` the absolute error bound `1/D` of `sqrtQ_spec` is at
most `s / 2^20`: `s ≤ √q < s·(1 + 2⁻²⁰)`. -/
theorem sqrtQ_rel (q : Rat) (hq : 0 < q) :
    1 / (sqrtDen q : Rat) ≤ sqrtQ q / ((2 ^ sqrtBits : Nat) : Rat) := by
  have hn : 1 ≤ q.num.toNat := by
    have h0 : 0 ≤ q.num := Rat.num_nonneg.mpr (Rat.le_of_lt hq)
    have h1 : q.num ≠ 0 := fun h => Rat.ne_of_gt hq (Rat.num_eq_zero.mp h)
    omega
  -- `N ≥ 4^K`, so `⌊√N⌋ ≥ 2^K`.
  have hN : 4 ^ sqrtBits ≤ q.num.toNat * q.den * 4 ^ sqrtBits :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos hn q.den_pos)
  have hr : 2 ^ sqrtBits ≤ (q.num.toNat * q.den * 4 ^ sqrtBits).sqrt := by
    have h2 := Nat.lt_succ_sqrt (q.num.toNat * q.den * 4 ^ sqrtBits)
    generalize q.num.toNat * q.den * 4 ^ sqrtBits = N at hN h2
    generalize N.sqrt = r at h2
    have h4 : (4 : Nat) ^ sqrtBits = 2 ^ sqrtBits * 2 ^ sqrtBits := by
      rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_pow]
    rw [h4] at hN
    generalize 2 ^ sqrtBits = t at hN ⊢
    refine Nat.le_of_not_lt fun hlt => ?_
    have := Nat.mul_le_mul (Nat.succ_le_of_lt hlt) (Nat.succ_le_of_lt hlt)
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 (Nat.le_trans this hN))
  have hD : 0 < sqrtDen q := Nat.mul_pos q.den_pos (Nat.two_pow_pos _)
  have hD' : (0 : Rat) < (sqrtDen q : Rat) := Rat.natCast_lt_natCast.mpr hD
  have hP' : (0 : Rat) < ((2 ^ sqrtBits : Nat) : Rat) :=
    Rat.natCast_lt_natCast.mpr (Nat.two_pow_pos _)
  have hr' : ((2 ^ sqrtBits : Nat) : Rat) ≤ ((q.num.toNat * q.den * 4 ^ sqrtBits).sqrt : Rat) :=
    Rat.natCast_le_natCast.mpr hr
  simp only [sqrtQ]
  generalize ((q.num.toNat * q.den * 4 ^ sqrtBits).sqrt : Rat) = R at hr'
  generalize ((2 ^ sqrtBits : Nat) : Rat) = P at hP' hr'
  generalize (sqrtDen q : Rat) = D at hD'
  have : 1 / D * P ≤ R / D := by
    have := Rat.mul_le_mul_of_nonneg_right hr' (Rat.le_of_lt (Rat.inv_pos.mpr hD'))
    simp only [Rat.div_def] at this ⊢; grind
  have hPinv : 0 < P⁻¹ := Rat.inv_pos.mpr hP'
  have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hPinv)
  have hP0 : P ≠ 0 := Rat.ne_of_gt hP'
  simp only [Rat.div_def] at this ⊢; grind

/-! ## 2. Vectors and the frame grid -/

/-- Componentwise sum. -/
def padd (u v : Pt) : Pt := ⟨u.x + v.x, u.y + v.y⟩

/-- Scalar multiple. -/
def psc (k : Rat) (v : Pt) : Pt := ⟨k * v.x, k * v.y⟩

/-- The linear part of `m` applied to the vector `v` (row-vector convention, no translation). -/
def lin (m : Aff) (v : Pt) : Pt := ⟨m.a * v.x + m.c * v.y, m.b * v.x + m.d * v.y⟩

/-- Squared Euclidean length. -/
def norm2 (v : Pt) : Rat := v.x * v.x + v.y * v.y

/-- Rotation by +90°: the left normal direction. -/
def perp (v : Pt) : Pt := ⟨-v.y, v.x⟩

/-- A device point as an exact point (subpixel units). -/
def toPt (p : FPt) : Pt := ⟨p.x, p.y⟩

/-- Round to the nearest subpixel unit (halves up), clamped to `±lim` like 7.2a's points. -/
def rnd (lim : Int) (q : Rat) : Int := clampCoord (roundDivI q.num (q.den : Int)) lim

/-- An exact point rounded to a device point, clamped to `±lim`. -/
def fpt (lim : Int) (v : Pt) : FPt := ⟨rnd lim v.x, rnd lim v.y⟩

/-- Fractional bits of the stroke frame grid (task 7.2i): pen offsets, unit tangents, pen
circle points and dash centres are rounded to multiples of `2⁻¹⁶` (subpixel units, or unit
lengths) before they are combined. -/
def frameBits : Nat := 16

/-- `2^frameBits`. -/
def fone : Int := 65536

/-- `round(q · 2¹⁶)`, halves up (the grid coordinate of `q`). -/
def gridQ (q : Rat) : Int := roundDivI (q.num * fone) (q.den : Int)

/-- **Grid rounding error.** `gridQ q` is within `½` of `q · 2¹⁶`:
`−den < 2·(gridQ q · den − num · 2¹⁶) ≤ den`. -/
theorem gridQ_err (q : Rat) :
    -(q.den : Int) < 2 * (gridQ q * q.den - q.num * fone) ∧
      2 * (gridQ q * q.den - q.num * fone) ≤ q.den :=
  roundDivI_err _ _ (by have := q.den_pos; omega)

/-- `q` rounded to the frame grid, as a rational. -/
def gq (q : Rat) : Rat := (gridQ q : Rat) / (fone : Rat)

/-- A point rounded to the frame grid. -/
def gp (v : Pt) : Pt := ⟨gq v.x, gq v.y⟩

/-- `⌊(n + 2³¹) / 2³²⌋`: `n / 2³²` rounded to nearest, halves up (arithmetic shift). -/
@[inline] def rnd32 (n : Int64) : Int64 := (n + 2147483648) >>> 32

/-- `|v| ≤ b` for a 64-bit integer. -/
@[inline] def absLe64 (v b : Int64) : Bool := -b ≤ v && v ≤ b

/-! ## 3. The pen -/

/-- Miter limit used at the interior vertices of a flattened curve (where the true outline
is smooth); larger turns there (cusps) get a bevel. -/
def smoothMiterLimit : Rat := 4

/-- Search the least `m ∈ [m₀, m₀ + fuel]` with `r2 ≤ 4·tol²·m⁴`. -/
def arcCountGo (r2 : Rat) (tol : Nat) : Nat → Nat → Nat
  | m, 0 => m
  | m, fuel + 1 =>
    if r2 ≤ 4 * (tol : Rat) * tol * ((m : Rat) * m * m * m) then m
    else arcCountGo r2 tol (m + 1) fuel

/-- Chords per quarter for a pen whose device radius squared is at most `r2` (subpixel
units²): the least `m ≥ 1` with sagitta bound `√r2 / (2m²) ≤ tol`, capped at `cap`
(`Config.arcCap`). -/
def arcCount (cap : Nat) (r2 : Rat) (tol : Nat) : Nat := min cap (arcCountGo r2 tol 1 (cap - 1))

/-- The `4·m` rational points on the unit circle used for the pen polygon, counter-clockwise
from `(1, 0)`: in each quarter, `((m² − j²)/(m² + j²), 2jm/(m² + j²))` for `j < m`
(rotated by the quarter), exactly on the circle; the angular step is at most `2/m`. -/
def circleTable (m : Nat) : Array Pt :=
  Array.ofFn (n := 4 * m) fun i =>
    let q := i.val / m
    let j : Rat := (i.val % m : Nat)
    let mm : Rat := m
    let den := mm * mm + j * j
    let c := (mm * mm - j * j) / den
    let s := 2 * j * mm / den
    match q with
    | 0 => ⟨c, s⟩
    | 1 => ⟨-s, c⟩
    | 2 => ⟨-c, -s⟩
    | _ => ⟨s, -c⟩

/-- A linear map over a common denominator: `x' = (a·x + c·y)/den`, `y' = (b·x + d·y)/den`
(row-vector convention, as `lin`), `den > 0`. Lets the stroker evaluate `lin m v` on integer
vectors without normalising intermediate fractions. -/
structure IMat where
  /-- `m.a · den`. -/
  a : Int
  /-- `m.b · den`. -/
  b : Int
  /-- `m.c · den`. -/
  c : Int
  /-- `m.d · den`. -/
  d : Int
  /-- The common denominator (lcm of the four denominators). -/
  den : Nat
  deriving Inhabited

/-- The linear part of `m` over the lcm of its four denominators. -/
def IMat.ofAff (m : Aff) : IMat :=
  let dm : Nat := Nat.lcm m.a.den (Nat.lcm m.b.den (Nat.lcm m.c.den m.d.den))
  let sc := fun (q : Rat) => q.num * ((dm / q.den : Nat) : Int)
  ⟨sc m.a, sc m.b, sc m.c, sc m.d, dm⟩

/-- The linear map `v ↦ lin m (perp (lin inv v))` as an `Aff` (rows: images of the unit
vectors; no translation). -/
def normalMap (m inv : Aff) : Aff :=
  let e1 := lin m (perp (lin inv ⟨1, 0⟩))
  let e2 := lin m (perp (lin inv ⟨0, 1⟩))
  ⟨e1.x, e1.y, e2.x, e2.y, 0, 0⟩

/-- The pen: a linear map from pen space to device subpixel units with its inverse, the pen
radius in pen units, the sampled unit circle, and the caps it was made with. -/
structure Pen where
  /-- Pen space → device subpixel units (linear part only). -/
  map : Aff
  /-- The inverse of `map`. -/
  inv : Aff
  /-- Radius (half the line width) in pen units. -/
  r : Rat
  /-- Unit-circle sample points (`circleTable`). -/
  circle : Array Pt
  /-- Upper bound on the vertices of an emitted polygon (`Config.polyCap`). -/
  polyCap : Nat := 4 * Limits.default.arcSegCap
  /-- Device points are clamped to `±lim` subpixel units (`Config.coordLimit`). -/
  lim : Int := (Limits.default.coordLimit : Int)
  /-- `0 < det map` (orientation of the pen map). -/
  detPos : Bool := true
  /-- `circle` on the frame grid (`gridQ` of each coordinate). -/
  circI : Array (Int × Int) := #[]
  /-- `inv` over a common denominator. -/
  invI : IMat := default
  /-- `normalMap map inv` (`d ↦ L·J·L⁻¹·d`) over a common denominator. -/
  nrmI : IMat := default
  deriving Inhabited

/-- How dash lengths are measured: in pen space (the usual case, pen = user space), through a
separate inverse map (zero-width lines with an invertible CTM), or not at all (degenerate
CTM: no dashes). -/
inductive Metric where
  /-- User space is the pen space. -/
  | pen
  /-- Device subpixel units → user space (`im` = `IMat.ofAff inv`). -/
  | user (inv : Aff) (im : IMat)
  /-- No user-space lengths: dashes are ignored. -/
  | none
  deriving Inhabited

/-- Make a pen from its map and radius (tolerance and caps from `cfg`). -/
def Pen.make (map : Aff) (r : Rat) (cfg : Config) : Pen :=
  let fro := map.a * map.a + map.b * map.b + map.c * map.c + map.d * map.d
  let circle := circleTable (arcCount cfg.arcCap (r * r * fro) cfg.tol)
  let inv := map.inv
  { map, inv, r, circle, polyCap := cfg.polyCap, lim := cfg.coordLimit,
    detPos := decide (0 < map.det), circI := circle.map fun p => (gridQ p.x, gridQ p.y),
    invI := IMat.ofAff inv, nrmI := IMat.ofAff (normalMap map inv) }

/-- The hairline pen: a device circle of diameter one pixel. -/
def hairPen (cfg : Config) : Pen := Pen.make Aff.id (subUnit / 2 : Int) cfg

/-! ## 4. Segments -/

/-- The 64-bit copy of a segment's integer frame (valid when `SegG.small`). -/
structure Frame64 where
  /-- `SegG.ax`. -/
  ax : Int64
  /-- `SegG.ay`. -/
  ay : Int64
  /-- `SegG.nx`. -/
  nx : Int64
  /-- `SegG.ny`. -/
  ny : Int64
  /-- `SegG.tx`. -/
  tx : Int64
  /-- `SegG.ty`. -/
  ty : Int64
  /-- `q.x − p.x`. -/
  dx : Int64
  /-- `q.y − p.y`. -/
  dy : Int64
  deriving Inhabited

/-- A non-degenerate device chord with its stroke geometry. The pen frame (`A`, `B` of the
module doc) and the pen-space unit tangent are kept **on the frame grid** (`gridQ`, units of
`2⁻¹⁶` subpixel units resp. `2⁻¹⁶`): every later step is exact integer arithmetic on them. -/
structure SegG where
  /-- Start (device subpixel units). -/
  p : FPt
  /-- End. -/
  q : FPt
  /-- `q − p`, exact. -/
  d : Pt
  /-- Approximate user-space length (for dashes). -/
  len : Rat
  /-- `gridQ` of the x part of the offset `A` (pen-space length `r` along the chord). -/
  ax : Int
  /-- `gridQ` of `A.y`. -/
  ay : Int
  /-- `gridQ` of the x part of the offset `B` (pen-space length `r` along the left normal). -/
  nx : Int
  /-- `gridQ` of `B.y`. -/
  ny : Int
  /-- `gridQ` of the pen-space unit tangent `u/|u|`, x part. -/
  tx : Int
  /-- `gridQ` of the pen-space unit tangent, y part. -/
  ty : Int
  /-- `p` is an interior vertex of a flattened curve. -/
  smooth : Bool
  /-- Clamp for device points (the pen's `lim`). -/
  lim : Int
  /-- The frame fits the 64-bit paths: `|ax|, |ay|, |nx|, |ny| ≤ 2⁴⁴`, `|tx|, |ty| ≤ 2²⁰`,
  `|q − p| ≤ 2³⁰` per coordinate. -/
  small : Bool
  /-- 64-bit copy of the frame (meaningful when `small`). -/
  f : Frame64
  deriving Inhabited

/-- `2⁴⁴`, the 64-bit bound on frame offsets. -/
def bound44 : Nat := 17592186044416

/-- **Reference** geometry of the chord `p → q` (plain `Rat` arithmetic): with `L` the pen map, `u = L⁻¹·d`, `ℓ = sqrtQ |u|²`,
`A = (r/ℓ)·d`, `B = (r/ℓ)·L·J·u`, all exact, then rounded to the frame grid. -/
def mkSegSpec (pen : Pen) (metric : Metric) (p q : FPt) (smooth : Bool) : SegG :=
  let d : Pt := ⟨q.x - p.x, q.y - p.y⟩
  let u := lin pen.inv d
  let pl := sqrtQ (norm2 u)
  let h := pen.r / pl
  let len := match metric with
    | .pen => pl
    | .user inv _ => sqrtQ (norm2 (lin inv d))
    | .none => pl
  let a := psc h d
  let b := psc h (lin pen.map (perp u))
  let ax := gridQ a.x
  let ay := gridQ a.y
  let nx := gridQ b.x
  let ny := gridQ b.y
  let tx := gridQ (u.x / pl)
  let ty := gridQ (u.y / pl)
  let dx := q.x - p.x
  let dy := q.y - p.y
  let small := absLe ax bound44 && absLe ay bound44 && absLe nx bound44 && absLe ny bound44 &&
    absLe tx 1048576 && absLe ty 1048576 && absLe dx 1073741824 && absLe dy 1073741824
  { p, q, d, len, ax, ay, nx, ny, tx, ty, smooth, lim := pen.lim, small,
    f := if small then ⟨ax.toInt64, ay.toInt64, nx.toInt64, ny.toInt64, tx.toInt64,
      ty.toInt64, dx.toInt64, dy.toInt64⟩ else default }

/-- `gridQ (n / d)` for `d > 0`, without normalising the fraction (`roundDivI` only depends
on the value of `n / d`). -/
@[inline] def gridND (n d : Int) : Int := roundDivI (n * fone) d

/-- A segment from its grid frame (computes the 64-bit copy and the `small` flag). -/
def mkFrame (p q : FPt) (len : Rat) (smooth : Bool) (lim : Int)
    (ax ay nx ny tx ty : Int) : SegG :=
  let dx := q.x - p.x
  let dy := q.y - p.y
  let small := absLe ax bound44 && absLe ay bound44 && absLe nx bound44 && absLe ny bound44 &&
    absLe tx 1048576 && absLe ty 1048576 && absLe dx 1073741824 && absLe dy 1073741824
  { p, q, d := ⟨dx, dy⟩, len, ax, ay, nx, ny, tx, ty, smooth, lim, small,
    f := if small then ⟨ax.toInt64, ay.toInt64, nx.toInt64, ny.toInt64, tx.toInt64,
      ty.toInt64, dx.toInt64, dy.toInt64⟩ else default }

/-- `sqrtQ |lin m d|²` for an integer vector `d`, normalising the square once. -/
def lenI (m : IMat) (dx dy : Int) : Rat :=
  let ux := m.a * dx + m.c * dy
  let uy := m.b * dx + m.d * dy
  sqrtQ (mkRat (ux * ux + uy * uy) (m.den * m.den))

/-- The geometry of the chord `p → q`: the values of `mkSegSpec` (equal by construction —
the same exact rationals — and tested in `raster-stroke-spec`), computed on
common-denominator integer forms: `u = L⁻¹·d` via `pen.invI`, `L·J·u` via `pen.nrmI`. Only
`|u|²` is normalised (for `sqrtQ`), and each grid value is one rounded division (`gridND`). -/
def mkSeg (pen : Pen) (metric : Metric) (p q : FPt) (smooth : Bool) : SegG :=
  let dx := q.x - p.x
  let dy := q.y - p.y
  let m := pen.invI
  let ux := m.a * dx + m.c * dy
  let uy := m.b * dx + m.d * dy
  let pl := sqrtQ (mkRat (ux * ux + uy * uy) (m.den * m.den))
  let len := match metric with
    | .pen => pl
    | .user _ im => lenI im dx dy
    | .none => pl
  if pl.num ≤ 0 then mkFrame p q len smooth pen.lim 0 0 0 0 0 0
  else
    -- h = r / pl = hn / hd with hd > 0
    let hn := pen.r.num * (pl.den : Int)
    let hd := (pen.r.den : Int) * pl.num
    let k := pen.nrmI
    let bx := k.a * dx + k.c * dy
    let by' := k.b * dx + k.d * dy
    let hk := hd * (k.den : Int)
    let td := (m.den : Int) * pl.num
    mkFrame p q len smooth pen.lim (gridND (hn * dx) hd) (gridND (hn * dy) hd)
      (gridND (hn * bx) hk) (gridND (hn * by') hk)
      (gridND (ux * (pl.den : Int)) td) (gridND (uy * (pl.den : Int)) td)

/-- The point at user length `s` along the segment. -/
def along (g : SegG) (s : Rat) : Pt := padd (toPt g.p) (psc (s / g.len) g.d)

/-- A centre point on the frame grid: `(x + fx/2¹⁶, y + fy/2¹⁶)` subpixel units, with
`0 ≤ fx, fy < 2¹⁶`. -/
structure Ctr where
  /-- Integer part of x. -/
  x : Int
  /-- Integer part of y. -/
  y : Int
  /-- Fractional part of x, in `2⁻¹⁶` units. -/
  fx : Int
  /-- Fractional part of y, in `2⁻¹⁶` units. -/
  fy : Int
  deriving Inhabited

/-- A device point as a centre (no fraction). -/
def Ctr.ofFPt (p : FPt) : Ctr := ⟨p.x, p.y, 0, 0⟩

/-- An exact point rounded to the frame grid (`gp`). -/
def Ctr.ofPt (c : Pt) : Ctr :=
  let gx := gridQ c.x
  let gy := gridQ c.y
  ⟨gx / fone, gy / fone, gx % fone, gy % fone⟩

/-- One coordinate of `c + fc/2¹⁶ + (α·a + β·n)/2³²` rounded to nearest (halves up) and
clamped to `±lim`; the 64-bit path when the frame is `small` and `|α|, |β| ≤ 2¹⁷` (then every
term is below `2⁶¹`). -/
@[inline] def offCoord (small : Bool) (lim c fc α β a n : Int) (a6 n6 : Int64) : Int :=
  if small && absLe α 131072 && absLe β 131072 then
    clampCoord (c + (rnd32 (fc.toInt64 * 65536 + α.toInt64 * a6 + β.toInt64 * n6)).toInt) lim
  else clampCoord (c + roundDivI (fc * fone + α * a + β * n) (fone * fone)) lim

/-- `c + α·A + β·B` rounded, with the grid coefficients `α`, `β` (units of `2⁻¹⁶`). -/
def off (g : SegG) (c : Ctr) (α β : Int) : FPt :=
  ⟨offCoord g.small g.lim c.x c.fx α β g.ax g.nx g.f.ax g.f.nx,
    offCoord g.small g.lim c.y c.fy α β g.ay g.ny g.f.ay g.f.ny⟩

/-! ## 5. Emitting polygons -/

/-- Twice the signed (shoelace) area of a closed polygon. -/
def area2 (pts : Array FPt) : Int :=
  match pts.back? with
  | none => 0
  | some l =>
    (pts.foldl (fun (acc : Int × FPt) q => (acc.1 + (acc.2.x * q.y - q.x * acc.2.y), q))
      (0, l)).1

/-- `area2 pts < 0`. For at most 256 vertices within `2²⁶` of the first one, the shoelace
sum is taken over coordinates relative to it (the sum is translation invariant) in 64 bits;
otherwise `area2` itself. -/
def areaNeg (pts : Array FPt) : Bool :=
  match pts[0]?, pts.back? with
  | some o, some l =>
    if pts.size ≤ 256 && pts.all (fun p => absLe (p.x - o.x) 67108864 && absLe (p.y - o.y) 67108864)
    then
      let ox := o.x.toInt64
      let oy := o.y.toInt64
      let r := pts.foldl (fun (acc : Int64 × Int64 × Int64) q =>
        let qx := q.x.toInt64 - ox
        let qy := q.y.toInt64 - oy
        (acc.1 + (acc.2.1 * qy - qx * acc.2.2), qx, qy)) (0, l.x.toInt64 - ox, l.y.toInt64 - oy)
      r.1 < 0
    else area2 pts < 0
  | _, _ => false

/-- Append the edges of the closed polygon `pts`. -/
def pushPoly (es : Array Edge) (pts : Array FPt) : Array Edge :=
  match pts.back? with
  | none => es
  | some l => (pts.foldl (fun (acc : Array Edge × FPt) q => (pushLine acc.1 acc.2 q, q)) (es, l)).1

/-- Emit a polygon with the common orientation (non-negative shoelace area); polygons with
more than `pen.polyCap` vertices are dropped (never produced by this module). -/
def emit (pen : Pen) (es : Array Edge) (pts : Array FPt) : Array Edge :=
  if pts.size ≤ pen.polyCap then pushPoly es (if areaNeg pts then pts.reverse else pts) else es

/-- The parallelogram of the segment `g` between the centre points `c0` and `c1`. -/
def quadPts (g : SegG) (c0 c1 : Ctr) : Array FPt :=
  #[off g c0 0 fone, off g c1 0 fone, off g c1 0 (-fone), off g c0 0 (-fone)]

/-- The pen polygon centred at `c` (parametrised by the frame `A`, `B` of `g`). -/
def penPts (pen : Pen) (g : SegG) (c : Ctr) : Array FPt :=
  pen.circI.map fun cs => off g c cs.1 cs.2

/-- Cap at the start of a dash or open subpath (pointing backwards along `g`). -/
def capStart (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Ctr) : Array Edge :=
  match cap with
  | .butt => es
  | .round => emit pen es (penPts pen g c)
  | .square =>
    emit pen es #[off g c (-fone) (-fone), off g c (-fone) fone, off g c 0 fone, off g c 0 (-fone)]

/-- Cap at the end of a dash or open subpath. -/
def capEnd (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Ctr) : Array Edge :=
  match cap with
  | .butt => es
  | .round => emit pen es (penPts pen g c)
  | .square =>
    emit pen es #[off g c 0 (-fone), off g c 0 fone, off g c fone fone, off g c fone (-fone)]

/-- A zero-length dash (or degenerate subpath) at `c`, oriented along `g`. -/
def dot (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Ctr) : Array Edge :=
  match cap with
  | .butt => es
  | .round => emit pen es (penPts pen g c)
  | .square =>
    emit pen es #[off g c (-fone) (-fone), off g c (-fone) fone, off g c fone fone,
      off g c fone (-fone)]

/-- The miter threshold of a miter limit `ml ≥ 1`: `⌈2·2³²/ml²⌉`. With
`D = 2³² + t₁·t₂` (grid unit tangents), `dminOf ml ≤ D` iff `2 ≤ (1 + cos θ)·ml²` for the
grid cosine `cos θ = t₁·t₂ / 2³²`. -/
def dminOf (ml : Rat) : Int := max 1 ((2 * (fone : Rat) * fone / (ml * ml)).ceil)

/-- `dminOf smoothMiterLimit = 2²⁹`. -/
def smoothDmin : Int := 536870912

/-- The sign (`−1`, `0`, `1`) of `cross(d₁, d₂)`. -/
def crossSign (g1 g2 : SegG) : Int :=
  if g1.small && g2.small then
    let c := g1.f.dx * g2.f.dy - g1.f.dy * g2.f.dx
    if c < 0 then -1 else if c = 0 then 0 else 1
  else
    let c := (g1.q.x - g1.p.x) * (g2.q.y - g2.p.y) - (g1.q.y - g1.p.y) * (g2.q.x - g2.p.x)
    if c < 0 then -1 else if c = 0 then 0 else 1

/-- `dm ≤ 2³² + t₁·t₂` (the miter test, see `dminOf`). -/
def miterOK (dm : Int) (g1 g2 : SegG) : Bool :=
  if g1.small && g2.small && absLe dm 1099511627776 then
    dm.toInt64 ≤ 4294967296 + g1.f.tx * g2.f.tx + g1.f.ty * g2.f.ty
  else dm ≤ fone * fone + g1.tx * g2.tx + g1.ty * g2.ty

/-- The miter tip at `v = g2.p`: `v + σ·s·(B₁ + B₂)` rounded, with
`s = gridQ(1/(1 + cos θ))/2¹⁶ = round(2⁴⁸/D)/2¹⁶`, `D = 2³² + t₁·t₂ > 0`. -/
def tipPt (g1 g2 : SegG) (σ : Int) : FPt :=
  let v := g2.p
  let lim := g2.lim
  let slow : Unit → FPt := fun _ =>
    let D := fone * fone + g1.tx * g2.tx + g1.ty * g2.ty
    let si := roundDivI (fone * fone * fone) D
    ⟨clampCoord (v.x + roundDivI (σ * si * (g1.nx + g2.nx)) (fone * fone)) lim,
      clampCoord (v.y + roundDivI (σ * si * (g1.ny + g2.ny)) (fone * fone)) lim⟩
  if g1.small && g2.small then
    let D := 4294967296 + g1.f.tx * g2.f.tx + g1.f.ty * g2.f.ty
    if 0 < D then
      let si := (562949953421312 + D) / (2 * D)
      let sx := g1.f.nx + g2.f.nx
      let sy := g1.f.ny + g2.f.ny
      if si ≤ 4194304 && absLe64 sx 549755813888 && absLe64 sy 549755813888 then
        let s := if σ < 0 then -si else si
        ⟨clampCoord (v.x + (rnd32 (s * sx)).toInt) lim,
          clampCoord (v.y + (rnd32 (s * sy)).toInt) lim⟩
      else slow ()
    else slow ()
  else slow ()

/-- The join at the vertex `g2.p` between `g1` and `g2` (`dm`: the path's miter threshold,
`dminOf`). -/
def join (jn : LineJoin) (dm : Int) (pen : Pen) (es : Array Edge) (g1 g2 : SegG) : Array Edge :=
  let v := Ctr.ofFPt g2.p
  let jn := if g2.smooth then LineJoin.miter else jn
  let dm := if g2.smooth then smoothDmin else dm
  match jn with
  | .round => emit pen es (penPts pen g1 v)
  | _ =>
    let cs := crossSign g1 g2
    if cs = 0 then es
    else
      let σ : Int := if decide (0 < cs) = pen.detPos then -1 else 1
      let p1 := off g1 v 0 (σ * fone)
      let p2 := off g2 v 0 (σ * fone)
      let pv : FPt := ⟨clampCoord g2.p.x g2.lim, clampCoord g2.p.y g2.lim⟩
      if jn = .miter ∧ miterOK dm g1 g2 = true then
        emit pen es #[pv, p1, tipPt g1 g2 σ, p2]
      else emit pen es #[pv, p1, p2]

/-! ## 6. Centre line: subpaths of points -/

/-- A flattened subpath: its points (each with its `smooth` flag), whether it was closed
(the start point is then repeated at the end), and whether any drawing operator touched it. -/
structure Sub where
  /-- Points with the "interior vertex of a curve" flag. -/
  pts : Array (FPt × Bool) := #[]
  /-- Closed by `h`. -/
  closed : Bool := false
  /-- A `lineTo`, `curveTo` or `closePath` belongs to it. -/
  drawn : Bool := false
  deriving Inhabited

/-- Subpath construction state. -/
structure PState where
  /-- Finished subpaths. -/
  done : Array Sub := #[]
  /-- The current subpath. -/
  cur : Sub := {}
  /-- Start of the current subpath. -/
  start : FPt := ⟨0, 0⟩
  /-- Current point. -/
  last : FPt := ⟨0, 0⟩
  deriving Inhabited

/-- Append the subdivision points `B(k/n)` for `fuel` steps (the last is `p3` exactly);
all but the last are interior (`smooth`). -/
def cubicPts (n : Nat) (p0 p1 p2 p3 : FPt) : (fuel k : Nat) → Array (FPt × Bool) →
    Array (FPt × Bool)
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
    let q := if k = n then (p3, false) else (bezAt n k p0 p1 p2 p3, true)
    cubicPts n p0 p1 p2 p3 fuel (k + 1) (acc.push q)

/-- One path segment. The last point of a curve is not smooth. -/
def pSeg (cfg : Config) (st : PState) : DSeg → PState
  | .moveTo p => ⟨st.done.push st.cur, ⟨#[(p, false)], false, false⟩, p, p⟩
  | .lineTo p => ⟨st.done, ⟨st.cur.pts.push (p, false), st.cur.closed, true⟩, st.start, p⟩
  | .curveTo c1 c2 p =>
    let n := segCount cfg.segCap (flatness st.last c1 c2 p) cfg.tol
    ⟨st.done, ⟨cubicPts n st.last c1 c2 p n 1 st.cur.pts, st.cur.closed, true⟩, st.start, p⟩
  | .closePath =>
    ⟨st.done.push ⟨st.cur.pts.push (st.start, false), true, true⟩,
      ⟨#[(st.start, false)], false, false⟩, st.start, st.start⟩

/-- The flattened subpaths of a device path. -/
def subpaths (cfg : Config) (p : DPath) : Array Sub :=
  let st := p.foldl (pSeg cfg) {}
  st.done.push st.cur

/-- The non-degenerate chords of a subpath (consecutive duplicate points dropped). -/
def mkSegs (pen : Pen) (metric : Metric) (pts : Array (FPt × Bool)) : Array SegG :=
  match pts[0]? with
  | none => #[]
  | some (p0, s0) =>
    (pts.foldl (fun (acc : Array SegG × FPt × Bool) (q : FPt × Bool) =>
      if q.1 = acc.2.1 then acc else (acc.1.push (mkSeg pen metric acc.2.1 q.1 acc.2.2), q))
      (#[], p0, s0)).1

/-! ## 7. Solid and dashed subpaths -/

/-- Stroke a subpath without dashes: parallelograms, joins at the vertices, then caps (open)
or the closing join (closed). -/
def solidSub (line : LineStyle) (dm : Int) (pen : Pen) (segs : Array SegG) (closed : Bool)
    (es : Array Edge) : Array Edge :=
  let r := segs.foldl (fun (acc : Array Edge × Option SegG) g =>
    (emit pen (match acc.2 with
      | none => acc.1
      | some g0 => join line.join dm pen acc.1 g0 g) (quadPts g (.ofFPt g.p) (.ofFPt g.q)), some g))
    (es, none)
  match segs[0]?, segs.back? with
  | some g0, some gl =>
    if closed then join line.join dm pen r.1 gl g0
    else capEnd line.cap pen (capStart line.cap pen r.1 g0 (.ofFPt g0.p)) gl (.ofFPt gl.q)
  | _, _ => r.1

/-- Dash walking state. -/
structure DashSt where
  /-- Current segment. -/
  i : Nat := 0
  /-- User length already walked in segment `i`. -/
  s : Rat := 0
  /-- Current dash element (even: on, odd: off). -/
  idx : Nat := 0
  /-- Remaining user length of the element. -/
  rem : Rat := 0
  /-- The current "on" element has drawn nothing yet. -/
  fresh : Bool := true
  deriving Inhabited

/-- The current "on" element ends inside `g` at user length `s + rem`: its piece with caps,
or a dot for a zero-length dash. -/
def dashEnd (line : LineStyle) (pen : Pen) (es : Array Edge) (g : SegG) (d : DashSt) :
    Array Edge :=
  if d.fresh ∧ d.rem = 0 then dot line.cap pen es g (.ofPt (along g d.s))
  else
    let c0 := Ctr.ofPt (along g d.s)
    let c1 := Ctr.ofPt (along g (d.s + d.rem))
    let es1 := if d.fresh then capStart line.cap pen es g c0 else es
    capEnd line.cap pen (emit pen es1 (quadPts g c0 c1)) g c1

/-- The current "on" element runs past the end of `g`: the rest of `g`, then the join to the
next segment or the end cap. -/
def dashThrough (line : LineStyle) (dm : Int) (pen : Pen) (segs : Array SegG) (es : Array Edge)
    (g : SegG) (d : DashSt) : Array Edge :=
  let c0 := Ctr.ofPt (along g d.s)
  let es1 := if d.fresh then capStart line.cap pen es g c0 else es
  let es2 := emit pen es1 (quadPts g c0 (.ofFPt g.q))
  match segs[d.i + 1]? with
  | some g2 => join line.join dm pen es2 g g2
  | none => capEnd line.cap pen es2 g (.ofFPt g.q)

/-- Walk the dash pattern `arr` (even length, non-negative entries) along `segs`. -/
def dashLoop (line : LineStyle) (dm : Int) (pen : Pen) (segs : Array SegG) (arr : Array Rat) :
    Nat → DashSt → Array Edge → Array Edge
  | 0, _, es => es
  | fuel + 1, d, es =>
    match segs[d.i]? with
    | none => es
    | some g =>
      let left := g.len - d.s
      if d.rem ≤ left then
        let es' := if d.idx % 2 = 0 then dashEnd line pen es g d else es
        let idx' := if d.idx + 1 < arr.size then d.idx + 1 else 0
        dashLoop line dm pen segs arr fuel
          { d with s := d.s + d.rem, idx := idx', rem := arr[idx']?.getD 0, fresh := true } es'
      else if left ≤ 0 then
        dashLoop line dm pen segs arr fuel { d with i := d.i + 1, s := 0 } es
      else
        let es' := if d.idx % 2 = 0 then dashThrough line dm pen segs es g d else es
        dashLoop line dm pen segs arr fuel
          { d with i := d.i + 1, s := 0, rem := d.rem - left, fresh := false } es'

/-- A validated dash pattern: the element array (doubled when odd), its period and the
phase reduced to `[0, period)`; `none` means solid (empty array, a negative element, or a
zero period). -/
def dashSetup (dp : DashPattern) : Option (Array Rat × Rat × Rat) :=
  let a := (dp.array.map Fixed.toRat).toArray
  if a.isEmpty || a.any (· < 0) then none
  else
    let a := if a.size % 2 = 1 then a ++ a else a
    let per := a.foldl (· + ·) 0
    if per ≤ 0 then none
    else
      let ph := Fixed.toRat dp.phase
      some (a, per, ph - per * ((ph / per).floor : Rat))

/-- Locate the phase `ph ∈ [0, period)`: the element containing it and the length left in
it. A zero-length element exactly at `ph` is chosen (so phase 0 on `[0 …]` starts with a
dot). -/
def dashStartGo (arr : Array Rat) (ph : Rat) : (fuel idx : Nat) → Rat → Nat × Rat
  | 0, _, _ => (0, arr[0]?.getD 0)
  | fuel + 1, idx, cum =>
    match arr[idx]? with
    | none => (0, arr[0]?.getD 0)
    | some a =>
      if ph < cum + a ∨ (a = 0 ∧ ph = cum) then (idx, cum + a - ph)
      else dashStartGo arr ph fuel (idx + 1) (cum + a)

/-- Total user length of a list of segments. -/
def totalLen (segs : Array SegG) : Rat := segs.foldl (fun t g => t + g.len) 0

/-- Upper estimate of the element steps of a dash walk over `segs`: every period of length
`per` consumes `arr.size` elements, and the walk touches at most `⌊T/per⌋ + 2` periods. -/
def dashEstimate (arr : Array Rat) (per : Rat) (segs : Array SegG) : Nat :=
  arr.size * (((totalLen segs / per).floor).toNat + 2) + 2

/-- Stroke one subpath. `est` is the dash step budget (unused when solid). -/
def strokeSub (line : LineStyle) (dm : Int) (pen : Pen) (dash : Option (Array Rat × Rat × Rat))
    (segs : Array SegG) (sub : Sub) (est : Nat) (es : Array Edge) : Array Edge :=
  if segs.size = 0 then
    match sub.pts[0]?, line.cap with
    | some (p, _), .round =>
      if sub.drawn then dot .round pen es (mkSeg pen .pen p ⟨p.x + 1, p.y⟩ false) (.ofFPt p)
      else es
    | _, _ => es
  else
    match dash with
    | none => solidSub line dm pen segs sub.closed es
    | some (arr, _, ph) =>
      let st := dashStartGo arr ph arr.size 0 0
      dashLoop line dm pen segs arr (segs.size + est + 1) { idx := st.1, rem := st.2 } es

/-- Stroke all subpaths (with their chords and dash budgets). -/
def strokeSubs (line : LineStyle) (dm : Int) (pen : Pen) (dash : Option (Array Rat × Rat × Rat)) :
    List (Array SegG × Sub × Nat) → Array Edge → Array Edge
  | [], es => es
  | (segs, sub, est) :: rest, es =>
    strokeSubs line dm pen dash rest (strokeSub line dm pen dash segs sub est es)

/-! ## 8. The stroker -/

/-- Stroke geometry for a path: the pen and how dash lengths are measured. -/
structure Geo where
  /-- The pen. -/
  pen : Pen
  /-- Dash length metric. -/
  metric : Metric
  deriving Inhabited

/-- The stroke geometry for line width `w` (user units) and the user → device-subpixel map
`L` (only its linear part matters): the elliptic pen `L(disc of radius w/2)`, or the hairline
pen for `w = 0` or a degenerate `L` (see the module doc). -/
def Geo.make (L : Aff) (w : Rat) (cfg : Config := {}) : Geo :=
  let w := if w < 0 then -w else w
  if L.det = 0 then { pen := hairPen cfg, metric := .none }
  else if w = 0 then { pen := hairPen cfg, metric := .user L.inv (IMat.ofAff L.inv) }
  else { pen := Pen.make L (w / 2) cfg, metric := .pen }

/-- The pen of `Geo.make` has the configuration's polygon cap. -/
theorem Geo.make_polyCap (L : Aff) (w : Rat) (cfg : Config) :
    (Geo.make L w cfg).pen.polyCap = cfg.polyCap := by
  unfold Geo.make; dsimp only
  repeat' split
  all_goals rfl

/-- The miter limit of a line style, at least 1. -/
def miterOf (line : LineStyle) : Rat := max 1 (Fixed.toRat line.miterLimit)

/-- **Stroke a device path** into polygon edges (for the nonzero rule). -/
def strokeDPath (cfg : Config) (geo : Geo) (line : LineStyle) (p : DPath) : Array Edge :=
  let subs := (subpaths cfg p).toList
  let sg := subs.map fun s => (mkSegs geo.pen geo.metric s.pts, s)
  let dm := dminOf (miterOf line)
  let dash := match geo.metric with
    | .none => none
    | _ => dashSetup line.dash
  match dash with
  | none => strokeSubs line dm geo.pen none (sg.map fun x => (x.1, x.2, 0)) #[]
  | some dp =>
    let ests := sg.map fun x => (x.1, x.2, dashEstimate dp.1 dp.2.1 x.1)
    if (ests.map (·.2.2)).sum ≤ cfg.maxDashSteps then
      strokeSubs line dm geo.pen (some dp) ests #[]
    else strokeSubs line dm geo.pen none (sg.map fun x => (x.1, x.2, 0)) #[]

/-- The user → device-subpixel map of a stroke: `CTM × view × 256`. -/
def userToSub (view : Aff) (ctm : Content.Matrix) : Aff :=
  Aff.ofMatrix ctm * view * Aff.scale subUnit subUnit

/-- **Stroke a page-space path** (a `DisplayList` `strokePath` item) through the page →
device matrix `view`: polygon edges for the nonzero rule. -/
def strokeEdges (view : Aff) (path : Content.Path) (style : Content.StrokeStyle)
    (cfg : Config := {}) : Array Edge :=
  let geo := Geo.make (userToSub view style.ctm) (Fixed.toRat style.line.width) cfg
  strokeDPath cfg geo style.line (ofContentPath view path cfg)

/-- **Stroke coverage**: the stroke of a page-space path as a coverage mask over
(bounding box ∩ `clip`). -/
def strokePath (view : Aff) (path : Content.Path) (style : Content.StrokeStyle) (clip : IRect)
    (cfg : Config := {}) : Mask :=
  fillEdges (strokeEdges view path style cfg) .nonzero clip cfg

/-! ## 9. Work bound (S3) -/

private theorem pushPoly_fold (pts : List FPt) : ∀ (es : Array Edge) (l : FPt),
    (pts.foldl (fun (acc : Array Edge × FPt) q => (pushLine acc.1 acc.2 q, q)) (es, l)).1.size ≤
      es.size + pts.length := by
  induction pts with
  | nil => intro es l; simp
  | cons q rest ih =>
    intro es l
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (pushLine es l q) q
    have h2 := pushLine_size es l q
    omega

/-- A polygon of `n` vertices adds at most `n` edges. -/
theorem pushPoly_size (es : Array Edge) (pts : Array FPt) :
    (pushPoly es pts).size ≤ es.size + pts.size := by
  unfold pushPoly
  split
  · omega
  · next l _ =>
    rw [← Array.foldl_toList]
    have := pushPoly_fold pts.toList es l
    simp only [Array.length_toList] at this
    exact this

/-- Every emitted polygon adds at most `pen.polyCap` edges. -/
theorem emit_size (pen : Pen) (es : Array Edge) (pts : Array FPt) :
    (emit pen es pts).size ≤ es.size + pen.polyCap := by
  unfold emit
  split
  · rename_i h
    have := pushPoly_size es (if areaNeg pts = true then pts.reverse else pts)
    have hs : (if areaNeg pts = true then pts.reverse else pts).size = pts.size := by
      split <;> simp
    omega
  · omega

/-- A start cap adds at most `pen.polyCap` edges. -/
theorem capStart_size (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Ctr) :
    (capStart cap pen es g c).size ≤ es.size + pen.polyCap := by
  unfold capStart; split
  · omega
  · exact emit_size _ _ _
  · exact emit_size _ _ _

/-- An end cap adds at most `pen.polyCap` edges. -/
theorem capEnd_size (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Ctr) :
    (capEnd cap pen es g c).size ≤ es.size + pen.polyCap := by
  unfold capEnd; split
  · omega
  · exact emit_size _ _ _
  · exact emit_size _ _ _

/-- A dot adds at most `pen.polyCap` edges. -/
theorem dot_size (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Ctr) :
    (dot cap pen es g c).size ≤ es.size + pen.polyCap := by
  unfold dot; split
  · omega
  · exact emit_size _ _ _
  · exact emit_size _ _ _

/-- A join adds at most `pen.polyCap` edges. -/
theorem join_size (jn : LineJoin) (dm : Int) (pen : Pen) (es : Array Edge) (g1 g2 : SegG) :
    (join jn dm pen es g1 g2).size ≤ es.size + pen.polyCap := by
  unfold join
  dsimp only
  repeat' split
  all_goals first | exact emit_size _ _ _ | omega

/-- The end of a dash adds at most `3·pen.polyCap` edges. -/
theorem dashEnd_size (line : LineStyle) (pen : Pen) (es : Array Edge) (g : SegG) (d : DashSt) :
    (dashEnd line pen es g d).size ≤ es.size + 3 * pen.polyCap := by
  unfold dashEnd
  split
  · have := dot_size line.cap pen es g (.ofPt (along g d.s)); omega
  · dsimp only
    have h1 : (if d.fresh = true then capStart line.cap pen es g (.ofPt (along g d.s)) else es).size ≤
        es.size + pen.polyCap := by
      split
      · exact capStart_size _ _ _ _ _
      · omega
    have h2 := emit_size pen (if d.fresh = true then capStart line.cap pen es g (.ofPt (along g d.s)) else es)
      (quadPts g (.ofPt (along g d.s)) (.ofPt (along g (d.s + d.rem))))
    have h3 := capEnd_size line.cap pen
      (emit pen (if d.fresh = true then capStart line.cap pen es g (.ofPt (along g d.s)) else es)
        (quadPts g (.ofPt (along g d.s)) (.ofPt (along g (d.s + d.rem))))) g (.ofPt (along g (d.s + d.rem)))
    omega

/-- A dash running through a vertex adds at most `3·pen.polyCap` edges. -/
theorem dashThrough_size (line : LineStyle) (dm : Int) (pen : Pen) (segs : Array SegG)
    (es : Array Edge) (g : SegG) (d : DashSt) :
    (dashThrough line dm pen segs es g d).size ≤ es.size + 3 * pen.polyCap := by
  unfold dashThrough
  dsimp only
  generalize hE1 : (if d.fresh = true then capStart line.cap pen es g (.ofPt (along g d.s)) else es) = e1
  have h1 : e1.size ≤ es.size + pen.polyCap := by
    rw [← hE1]; split
    · exact capStart_size _ _ _ _ _
    · omega
  generalize hE2 : emit pen e1 (quadPts g (.ofPt (along g d.s)) (.ofFPt g.q)) = e2
  have h2 : e2.size ≤ e1.size + pen.polyCap := by rw [← hE2]; exact emit_size _ _ _
  split
  · have := join_size line.join dm pen e2 g (by assumption); omega
  · have := capEnd_size line.cap pen e2 g (.ofFPt g.q); omega

/-- **Dash walk bound.** Each fuel step adds at most `3·pen.polyCap` edges. -/
theorem dashLoop_size (line : LineStyle) (dm : Int) (pen : Pen) (segs : Array SegG)
    (arr : Array Rat) : ∀ (fuel : Nat) (d : DashSt) (es : Array Edge),
    (dashLoop line dm pen segs arr fuel d es).size ≤ es.size + 3 * pen.polyCap * fuel
  | 0, _, es => by simp [dashLoop]
  | fuel + 1, d, es => by
    simp only [dashLoop]
    split
    · omega
    · rename_i g _
      split
      · generalize hE : (if d.idx % 2 = 0 then dashEnd line pen es g d else es) = e1
        have h1 : e1.size ≤ es.size + 3 * pen.polyCap := by
          rw [← hE]; split
          · exact dashEnd_size _ _ _ _ _
          · omega
        refine Nat.le_trans (dashLoop_size line dm pen segs arr fuel _ e1) ?_
        rw [Nat.mul_succ]; omega
      · split
        · refine Nat.le_trans (dashLoop_size line dm pen segs arr fuel _ es) ?_
          rw [Nat.mul_succ]; omega
        · generalize hE : (if d.idx % 2 = 0 then dashThrough line dm pen segs es g d else es) = e1
          have h1 : e1.size ≤ es.size + 3 * pen.polyCap := by
            rw [← hE]; split
            · exact dashThrough_size _ _ _ _ _ _ _
            · omega
          refine Nat.le_trans (dashLoop_size line dm pen segs arr fuel _ e1) ?_
          rw [Nat.mul_succ]; omega

private theorem solid_fold (jn : LineJoin) (dm : Int) (pen : Pen) : ∀ (l : List SegG)
    (es : Array Edge) (o : Option SegG),
    (l.foldl (fun (acc : Array Edge × Option SegG) g =>
      (emit pen (match acc.2 with
        | none => acc.1
        | some g0 => join jn dm pen acc.1 g0 g) (quadPts g (.ofFPt g.p) (.ofFPt g.q)), some g))
      (es, o)).1.size ≤
      es.size + 2 * pen.polyCap * l.length
  | [], es, o => by simp
  | g :: rest, es, o => by
    simp only [List.foldl_cons, List.length_cons]
    generalize hE : (match o with
      | none => es
      | some g0 => join jn dm pen es g0 g) = e1
    have h1 : e1.size ≤ es.size + pen.polyCap := by
      rw [← hE]; split
      · omega
      · exact join_size _ _ _ _ _ _
    have h2 := emit_size pen e1 (quadPts g (.ofFPt g.p) (.ofFPt g.q))
    have h3 := solid_fold jn dm pen rest (emit pen e1 (quadPts g (.ofFPt g.p) (.ofFPt g.q))) (some g)
    rw [Nat.mul_succ]; omega

/-- A solid subpath of `k` chords adds at most `pen.polyCap·(2k + 2)` edges. -/
theorem solidSub_size (line : LineStyle) (dm : Int) (pen : Pen) (segs : Array SegG)
    (closed : Bool) (es : Array Edge) :
    (solidSub line dm pen segs closed es).size ≤ es.size + pen.polyCap * (2 * segs.size + 2) := by
  unfold solidSub
  dsimp only
  have h0 := solid_fold line.join dm pen segs.toList es none
  rw [Array.foldl_toList, Array.length_toList] at h0
  generalize segs.foldl _ (es, none) = r at h0
  have e : pen.polyCap * (2 * segs.size + 2) = 2 * pen.polyCap * segs.size + 2 * pen.polyCap := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm pen.polyCap 2]
  split
  · next g0 gl _ _ =>
    split
    · have := join_size line.join dm pen r.1 gl g0; omega
    · have h1 := capStart_size line.cap pen r.1 g0 (.ofFPt g0.p)
      have h2 := capEnd_size line.cap pen (capStart line.cap pen r.1 g0 (.ofFPt g0.p)) gl (.ofFPt gl.q)
      omega
  · omega

/-- One subpath adds at most `3·pen.polyCap·(k + est + 1)` edges (`k` chords, dash budget
`est`). -/
theorem strokeSub_size (line : LineStyle) (dm : Int) (pen : Pen)
    (dash : Option (Array Rat × Rat × Rat)) (segs : Array SegG) (sub : Sub) (est : Nat)
    (es : Array Edge) :
    (strokeSub line dm pen dash segs sub est es).size ≤
      es.size + 3 * pen.polyCap * (segs.size + est + 1) := by
  unfold strokeSub
  have hp : pen.polyCap ≤ 3 * pen.polyCap * (segs.size + est + 1) := by
    have : 3 * pen.polyCap * 1 ≤ 3 * pen.polyCap * (segs.size + est + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  split
  · split
    · split
      · exact Nat.le_trans (dot_size _ _ _ _ _) (by omega)
      · omega
    · omega
  · split
    · have := solidSub_size line dm pen segs sub.closed es
      have : pen.polyCap * (2 * segs.size + 2) ≤ 3 * pen.polyCap * (segs.size + est + 1) := by
        rw [Nat.mul_comm 3 pen.polyCap, Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    · exact dashLoop_size line dm pen segs _ _ _ _

/-- The cost measure of a list of planned subpaths: `Σ (k + est + 1)`. -/
def planCost (l : List (Array SegG × Sub × Nat)) : Nat :=
  (l.map fun x => x.1.size + x.2.2 + 1).sum

/-- All subpaths: at most `3·pen.polyCap·planCost` edges. -/
theorem strokeSubs_size (line : LineStyle) (dm : Int) (pen : Pen)
    (dash : Option (Array Rat × Rat × Rat)) :
    ∀ (l : List (Array SegG × Sub × Nat)) (es : Array Edge),
    (strokeSubs line dm pen dash l es).size ≤ es.size + 3 * pen.polyCap * planCost l
  | [], es => by simp [strokeSubs, planCost]
  | (segs, sub, est) :: rest, es => by
    simp only [strokeSubs, planCost, List.map_cons, List.sum_cons]
    have h1 := strokeSub_size line dm pen dash segs sub est es
    have h2 := strokeSubs_size line dm pen dash rest (strokeSub line dm pen dash segs sub est es)
    simp only [planCost] at h2
    rw [Nat.mul_add]; omega

private theorem mkSegs_fold (pen : Pen) (metric : Metric) : ∀ (l : List (FPt × Bool))
    (acc : Array SegG × FPt × Bool),
    (l.foldl (fun (acc : Array SegG × FPt × Bool) (q : FPt × Bool) =>
      if q.1 = acc.2.1 then acc else (acc.1.push (mkSeg pen metric acc.2.1 q.1 acc.2.2), q))
      acc).1.size ≤ acc.1.size + l.length
  | [], acc => by simp
  | q :: rest, acc => by
    simp only [List.foldl_cons, List.length_cons]
    split
    · have := mkSegs_fold pen metric rest acc; omega
    · have := mkSegs_fold pen metric rest (acc.1.push (mkSeg pen metric acc.2.1 q.1 acc.2.2), q)
      simp only [Array.size_push] at this; omega

/-- A subpath of `n` points has at most `n` chords. -/
theorem mkSegs_size (pen : Pen) (metric : Metric) (pts : Array (FPt × Bool)) :
    (mkSegs pen metric pts).size ≤ pts.size := by
  unfold mkSegs
  split
  · simp
  · next p0 s0 _ =>
    rw [← Array.foldl_toList]
    have := mkSegs_fold pen metric pts.toList (#[], p0, s0)
    simp only [Array.length_toList, List.size_toArray, List.length_nil] at this
    simpa using this

/-- Total number of flattened points of a list of subpaths. -/
def ptCount (l : List Sub) : Nat := (l.map fun s => s.pts.size).sum

private theorem planCost_le (pen : Pen) (metric : Metric) (f : Array SegG × Sub → Nat) :
    ∀ l : List Sub,
    planCost ((l.map fun s => (mkSegs pen metric s.pts, s)).map fun x => (x.1, x.2, f x)) ≤
      ptCount l + (l.map fun s => f (mkSegs pen metric s.pts, s)).sum + l.length
  | [] => by simp [planCost, ptCount]
  | s :: rest => by
    have ih := planCost_le pen metric f rest
    have h := mkSegs_size pen metric s.pts
    simp only [planCost, ptCount, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

private theorem sum_ests (pen : Pen) (metric : Metric) (f : Array SegG × Sub → Nat)
    (l : List Sub) :
    (((l.map fun s => (mkSegs pen metric s.pts, s)).map
      fun x => (x.1, x.2, f x)).map (·.2.2)).sum =
      (l.map fun s => f (mkSegs pen metric s.pts, s)).sum := by
  induction l with
  | nil => simp
  | cons s rest ih => simp only [List.map_cons, List.sum_cons]; rw [ih]

/-- **S3 work bound for stroking (flattened form).** For the subpaths `subs` of a device
path, the stroke has at most `3·pen.polyCap·(P + cfg.maxDashSteps + S)` edges, with `P` the
number of flattened points and `S` the number of subpaths. -/
theorem strokeDPath_size_le (cfg : Config) (geo : Geo) (line : LineStyle) (p : DPath) :
    (strokeDPath cfg geo line p).size ≤
      3 * geo.pen.polyCap * (ptCount (subpaths cfg p).toList + cfg.maxDashSteps +
        (subpaths cfg p).toList.length) := by
  unfold strokeDPath
  dsimp only
  generalize (subpaths cfg p).toList = subs
  have hz : (subs.map fun (_ : Sub) => (0 : Nat)).sum = 0 := by
    induction subs with
    | nil => rfl
    | cons s rest ih => simp only [List.map_cons, List.sum_cons]; rw [ih]
  have hsolid := planCost_le geo.pen geo.metric (fun _ => 0) subs
  rw [hz] at hsolid
  have hmono : ∀ c, c ≤ ptCount subs + subs.length →
      3 * geo.pen.polyCap * c ≤
        3 * geo.pen.polyCap * (ptCount subs + cfg.maxDashSteps + subs.length) :=
    fun c hc => Nat.mul_le_mul_left _ (by omega)
  split
  · have := strokeSubs_size line (dminOf (miterOf line)) geo.pen none
      ((subs.map fun s => (mkSegs geo.pen geo.metric s.pts, s)).map fun x => (x.1, x.2, 0)) #[]
    have := hmono _ (by omega)
    simp only [List.size_toArray, List.length_nil] at *
    omega
  · rename_i dp _
    split
    · rename_i hb
      have hd := planCost_le geo.pen geo.metric (fun x => dashEstimate dp.1 dp.2.1 x.1) subs
      have hs := sum_ests geo.pen geo.metric (fun x => dashEstimate dp.1 dp.2.1 x.1) subs
      rw [hs] at hb
      have := strokeSubs_size line (dminOf (miterOf line)) geo.pen (some dp)
        ((subs.map fun s => (mkSegs geo.pen geo.metric s.pts, s)).map
          fun x => (x.1, x.2, dashEstimate dp.1 dp.2.1 x.1)) #[]
      have := Nat.mul_le_mul_left (3 * geo.pen.polyCap)
        (show planCost ((subs.map fun s => (mkSegs geo.pen geo.metric s.pts, s)).map
          fun x => (x.1, x.2, dashEstimate dp.1 dp.2.1 x.1)) ≤
            ptCount subs + cfg.maxDashSteps + subs.length by omega)
      simp only [List.size_toArray, List.length_nil] at *
      omega
    · have := strokeSubs_size line (dminOf (miterOf line)) geo.pen none
        ((subs.map fun s => (mkSegs geo.pen geo.metric s.pts, s)).map fun x => (x.1, x.2, 0)) #[]
      have := hmono _ (by omega)
      simp only [List.size_toArray, List.length_nil] at *
      omega

private theorem cubicPts_size (n : Nat) (p0 p1 p2 p3 : FPt) : ∀ (fuel k : Nat)
    (acc : Array (FPt × Bool)), (cubicPts n p0 p1 p2 p3 fuel k acc).size ≤ acc.size + fuel
  | 0, _, _ => by simp [cubicPts]
  | fuel + 1, k, acc => by
    simp only [cubicPts]
    have := cubicPts_size n p0 p1 p2 p3 fuel (k + 1)
      (acc.push (if k = n then (p3, false) else (bezAt n k p0 p1 p2 p3, true)))
    simp only [Array.size_push] at this
    omega

private theorem ptCount_push (a : Array Sub) (x : Sub) :
    ptCount (a.push x).toList = ptCount a.toList + x.pts.size := by
  simp [ptCount, Array.toList_push, List.map_append, List.sum_append]

/-- The size measure of a subpath construction state: all points so far. -/
private def pMeasure (st : PState) : Nat := ptCount st.done.toList + st.cur.pts.size

private theorem pSeg_measure (cfg : Config) (st : PState) (sg : DSeg) :
    pMeasure (pSeg cfg st sg) ≤ pMeasure st + max 2 cfg.segCap ∧
      (pSeg cfg st sg).done.size ≤ st.done.size + 1 := by
  have hc : 2 ≤ max 2 cfg.segCap := Nat.le_max_left _ _
  have hc' : cfg.segCap ≤ max 2 cfg.segCap := Nat.le_max_right _ _
  cases sg with
  | moveTo p =>
    simp only [pSeg, pMeasure, ptCount_push, Array.size_push]
    simp; omega
  | lineTo p => simp only [pSeg, pMeasure, Array.size_push]; omega
  | curveTo c1 c2 q =>
    simp only [pSeg, pMeasure]
    have h1 := cubicPts_size (segCount cfg.segCap (flatness st.last c1 c2 q) cfg.tol) st.last
      c1 c2 q (segCount cfg.segCap (flatness st.last c1 c2 q) cfg.tol) 1 st.cur.pts
    have h2 := (segCount_spec cfg.segCap (flatness st.last c1 c2 q) cfg.tol
      cfg.one_le_segCap).2.1
    omega
  | closePath =>
    simp only [pSeg, pMeasure, ptCount_push, Array.size_push]
    simp; omega

private theorem pFold_measure (cfg : Config) : ∀ (l : List DSeg) (st : PState),
    pMeasure (l.foldl (pSeg cfg) st) ≤ pMeasure st + max 2 cfg.segCap * l.length ∧
      (l.foldl (pSeg cfg) st).done.size ≤ st.done.size + l.length
  | [], st => by simp
  | sg :: rest, st => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := pFold_measure cfg rest (pSeg cfg st sg)
    have h2 := pSeg_measure cfg st sg
    rw [Nat.mul_succ]; omega

/-- **Flattened size.** A device path of `n` segments flattens to at most
`max 2 cfg.segCap · n` points in at most `n + 1` subpaths (`cfg.segCap` chords per curve; a
`closePath` adds 2 points). -/
theorem subpaths_bound (cfg : Config) (p : DPath) :
    ptCount (subpaths cfg p).toList ≤ max 2 cfg.segCap * p.size ∧
      (subpaths cfg p).toList.length ≤ p.size + 1 := by
  simp only [subpaths]
  rw [← Array.foldl_toList]
  have h := pFold_measure cfg p.toList {}
  have h0 : pMeasure ({} : PState) = 0 := by simp [pMeasure, ptCount]
  simp only [Array.length_toList] at h
  constructor
  · rw [ptCount_push]
    simp only [pMeasure] at h h0
    omega
  · simp only [Array.length_toList, Array.size_push]
    have h3 := h.2
    simp only [List.size_toArray, List.length_nil] at h3
    omega

/-- **S3 work bound for stroking.** The stroke of a page-space path of `n` segments has at
most `3·polyCap·(max 2 segCap·n + maxDashSteps + n + 1)` edges (all caps from `cfg`, i.e.
`Limits.arcSegCap`, `Limits.curveSegCap`, `Limits.maxDashSteps`), whatever the style, CTM,
view or dash pattern. (The fill of these edges is then bounded by
`Fill.fillEdgesCounted_steps_le`.) -/
theorem strokeEdges_size_le (view : Aff) (path : Content.Path) (style : Content.StrokeStyle)
    (cfg : Config) :
    (strokeEdges view path style cfg).size ≤
      3 * cfg.polyCap * (max 2 cfg.segCap * path.segs.size + cfg.maxDashSteps +
        path.segs.size + 1) := by
  unfold strokeEdges
  have h1 := strokeDPath_size_le cfg
    (Geo.make (userToSub view style.ctm) (Fixed.toRat style.line.width) cfg) style.line
    (ofContentPath view path cfg)
  rw [Geo.make_polyCap] at h1
  have h2 := subpaths_bound cfg (ofContentPath view path cfg)
  have hs : (ofContentPath view path cfg).size = path.segs.size := by simp [ofContentPath]
  rw [hs] at h2
  refine Nat.le_trans h1 (Nat.mul_le_mul_left _ ?_)
  omega

/-! ## 10. Reference stroker (`Rat`, task 7.2i)

The specification of sections 4–8: the same pipeline written with plain `Rat` arithmetic on
the grid-rounded frame. Every point is `fpt lim (gp c + gq α · A' + gq β · B')` with
`A' = (ax, ay)/2¹⁶`, `B' = (nx, ny)/2¹⁶` (`frameA`, `frameN`); a miter join compares
`2 ≤ (1 + cos θ)·ml²` with the grid cosine `cos θ = t₁·t₂` (`frameT`) and puts the tip at
`v + σ·gq(1/(1 + cos θ))·(B₁' + B₂')`; segments come from `mkSegSpec`, device paths from
`Fill.ofContentPathSpec`, polygon orientation from `area2`. `strokeEdges` must return exactly
the edges of `strokeEdgesSpec` (suite `raster-stroke-spec`). -/

/-- The grid offset `A'` of a segment, as an exact point. -/
def frameA (g : SegG) : Pt := ⟨(g.ax : Rat) / (fone : Rat), (g.ay : Rat) / (fone : Rat)⟩

/-- The grid offset `B'` of a segment. -/
def frameN (g : SegG) : Pt := ⟨(g.nx : Rat) / (fone : Rat), (g.ny : Rat) / (fone : Rat)⟩

/-- The grid unit tangent of a segment (pen space). -/
def frameT (g : SegG) : Pt := ⟨(g.tx : Rat) / (fone : Rat), (g.ty : Rat) / (fone : Rat)⟩

/-- Reference `off`: `gp c + gq α · A' + gq β · B'`, rounded and clamped. -/
def offR (g : SegG) (c : Pt) (α β : Rat) : FPt :=
  fpt g.lim (padd (gp c) (padd (psc (gq α) (frameA g)) (psc (gq β) (frameN g))))

/-- Reference `emit` (orientation by `area2`). -/
def emitR (pen : Pen) (es : Array Edge) (pts : Array FPt) : Array Edge :=
  if pts.size ≤ pen.polyCap then pushPoly es (if area2 pts < 0 then pts.reverse else pts) else es

/-- Reference `quadPts`. -/
def quadPtsR (g : SegG) (c0 c1 : Pt) : Array FPt :=
  #[offR g c0 0 1, offR g c1 0 1, offR g c1 0 (-1), offR g c0 0 (-1)]

/-- Reference `penPts`. -/
def penPtsR (pen : Pen) (g : SegG) (c : Pt) : Array FPt :=
  pen.circle.map fun cs => offR g c cs.x cs.y

/-- Reference `capStart`. -/
def capStartR (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Pt) : Array Edge :=
  match cap with
  | .butt => es
  | .round => emitR pen es (penPtsR pen g c)
  | .square => emitR pen es #[offR g c (-1) (-1), offR g c (-1) 1, offR g c 0 1, offR g c 0 (-1)]

/-- Reference `capEnd`. -/
def capEndR (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Pt) : Array Edge :=
  match cap with
  | .butt => es
  | .round => emitR pen es (penPtsR pen g c)
  | .square => emitR pen es #[offR g c 0 (-1), offR g c 0 1, offR g c 1 1, offR g c 1 (-1)]

/-- Reference `dot`. -/
def dotR (cap : LineCap) (pen : Pen) (es : Array Edge) (g : SegG) (c : Pt) : Array Edge :=
  match cap with
  | .butt => es
  | .round => emitR pen es (penPtsR pen g c)
  | .square => emitR pen es #[offR g c (-1) (-1), offR g c (-1) 1, offR g c 1 1, offR g c 1 (-1)]

/-- Reference `join` (miter limit `ml` as a rational). -/
def joinR (jn : LineJoin) (ml : Rat) (pen : Pen) (es : Array Edge) (g1 g2 : SegG) : Array Edge :=
  let v := toPt g2.p
  let jn := if g2.smooth then LineJoin.miter else jn
  let ml := if g2.smooth then smoothMiterLimit else ml
  match jn with
  | .round => emitR pen es (penPtsR pen g1 v)
  | _ =>
    let cr := g1.d.x * g2.d.y - g1.d.y * g2.d.x
    if cr = 0 then es
    else
      let σ : Rat := if decide (0 < cr) = decide (0 < pen.map.det) then -1 else 1
      let p1 := offR g1 v 0 σ
      let p2 := offR g2 v 0 σ
      let t1 := frameT g1
      let t2 := frameT g2
      let c := t1.x * t2.x + t1.y * t2.y
      if jn = .miter ∧ 2 ≤ (1 + c) * (ml * ml) then
        let tip := fpt g2.lim (padd v (psc (σ * gq (1 / (1 + c))) (padd (frameN g1) (frameN g2))))
        emitR pen es #[fpt g2.lim v, p1, tip, p2]
      else emitR pen es #[fpt g2.lim v, p1, p2]

/-- Reference `mkSegs` (segments from `mkSegSpec`). -/
def mkSegsSpec (pen : Pen) (metric : Metric) (pts : Array (FPt × Bool)) : Array SegG :=
  match pts[0]? with
  | none => #[]
  | some (p0, s0) =>
    (pts.foldl (fun (acc : Array SegG × FPt × Bool) (q : FPt × Bool) =>
      if q.1 = acc.2.1 then acc else (acc.1.push (mkSegSpec pen metric acc.2.1 q.1 acc.2.2), q))
      (#[], p0, s0)).1

/-- Reference `solidSub`. -/
def solidSubR (line : LineStyle) (ml : Rat) (pen : Pen) (segs : Array SegG) (closed : Bool)
    (es : Array Edge) : Array Edge :=
  let r := segs.foldl (fun (acc : Array Edge × Option SegG) g =>
    (emitR pen (match acc.2 with
      | none => acc.1
      | some g0 => joinR line.join ml pen acc.1 g0 g) (quadPtsR g (toPt g.p) (toPt g.q)), some g))
    (es, none)
  match segs[0]?, segs.back? with
  | some g0, some gl =>
    if closed then joinR line.join ml pen r.1 gl g0
    else capEndR line.cap pen (capStartR line.cap pen r.1 g0 (toPt g0.p)) gl (toPt gl.q)
  | _, _ => r.1

/-- Reference `dashEnd`. -/
def dashEndR (line : LineStyle) (pen : Pen) (es : Array Edge) (g : SegG) (d : DashSt) :
    Array Edge :=
  if d.fresh ∧ d.rem = 0 then dotR line.cap pen es g (along g d.s)
  else
    let c0 := along g d.s
    let c1 := along g (d.s + d.rem)
    let es1 := if d.fresh then capStartR line.cap pen es g c0 else es
    capEndR line.cap pen (emitR pen es1 (quadPtsR g c0 c1)) g c1

/-- Reference `dashThrough`. -/
def dashThroughR (line : LineStyle) (ml : Rat) (pen : Pen) (segs : Array SegG) (es : Array Edge)
    (g : SegG) (d : DashSt) : Array Edge :=
  let c0 := along g d.s
  let es1 := if d.fresh then capStartR line.cap pen es g c0 else es
  let es2 := emitR pen es1 (quadPtsR g c0 (toPt g.q))
  match segs[d.i + 1]? with
  | some g2 => joinR line.join ml pen es2 g g2
  | none => capEndR line.cap pen es2 g (toPt g.q)

/-- Reference `dashLoop`. -/
def dashLoopR (line : LineStyle) (ml : Rat) (pen : Pen) (segs : Array SegG) (arr : Array Rat) :
    Nat → DashSt → Array Edge → Array Edge
  | 0, _, es => es
  | fuel + 1, d, es =>
    match segs[d.i]? with
    | none => es
    | some g =>
      let left := g.len - d.s
      if d.rem ≤ left then
        let es' := if d.idx % 2 = 0 then dashEndR line pen es g d else es
        let idx' := if d.idx + 1 < arr.size then d.idx + 1 else 0
        dashLoopR line ml pen segs arr fuel
          { d with s := d.s + d.rem, idx := idx', rem := arr[idx']?.getD 0, fresh := true } es'
      else if left ≤ 0 then
        dashLoopR line ml pen segs arr fuel { d with i := d.i + 1, s := 0 } es
      else
        let es' := if d.idx % 2 = 0 then dashThroughR line ml pen segs es g d else es
        dashLoopR line ml pen segs arr fuel
          { d with i := d.i + 1, s := 0, rem := d.rem - left, fresh := false } es'

/-- Reference `strokeSub`. -/
def strokeSubR (line : LineStyle) (ml : Rat) (pen : Pen) (dash : Option (Array Rat × Rat × Rat))
    (segs : Array SegG) (sub : Sub) (est : Nat) (es : Array Edge) : Array Edge :=
  if segs.size = 0 then
    match sub.pts[0]?, line.cap with
    | some (p, _), .round =>
      if sub.drawn then dotR .round pen es (mkSegSpec pen .pen p ⟨p.x + 1, p.y⟩ false) (toPt p)
      else es
    | _, _ => es
  else
    match dash with
    | none => solidSubR line ml pen segs sub.closed es
    | some (arr, _, ph) =>
      let st := dashStartGo arr ph arr.size 0 0
      dashLoopR line ml pen segs arr (segs.size + est + 1) { idx := st.1, rem := st.2 } es

/-- Reference `strokeSubs`. -/
def strokeSubsR (line : LineStyle) (ml : Rat) (pen : Pen)
    (dash : Option (Array Rat × Rat × Rat)) :
    List (Array SegG × Sub × Nat) → Array Edge → Array Edge
  | [], es => es
  | (segs, sub, est) :: rest, es =>
    strokeSubsR line ml pen dash rest (strokeSubR line ml pen dash segs sub est es)

/-- **Reference stroker** for a device path (the specification of `strokeDPath`). -/
def strokeDPathSpec (cfg : Config) (geo : Geo) (line : LineStyle) (p : DPath) : Array Edge :=
  let subs := (subpaths cfg p).toList
  let sg := subs.map fun s => (mkSegsSpec geo.pen geo.metric s.pts, s)
  let ml := miterOf line
  let dash := match geo.metric with
    | .none => none
    | _ => dashSetup line.dash
  match dash with
  | none => strokeSubsR line ml geo.pen none (sg.map fun x => (x.1, x.2, 0)) #[]
  | some dp =>
    let ests := sg.map fun x => (x.1, x.2, dashEstimate dp.1 dp.2.1 x.1)
    if (ests.map (·.2.2)).sum ≤ cfg.maxDashSteps then
      strokeSubsR line ml geo.pen (some dp) ests #[]
    else strokeSubsR line ml geo.pen none (sg.map fun x => (x.1, x.2, 0)) #[]

/-- **Reference stroker** for a page-space path (the specification of `strokeEdges`; device
path from `Fill.ofContentPathSpec`). -/
def strokeEdgesSpec (view : Aff) (path : Content.Path) (style : Content.StrokeStyle)
    (cfg : Config := {}) : Array Edge :=
  let geo := Geo.make (userToSub view style.ctm) (Fixed.toRat style.line.width) cfg
  strokeDPathSpec cfg geo style.line (ofContentPathSpec view path cfg)

/-! ## 11. Checks (user space = device pixels, `L = 256·I`, window 100 × 100) -/

/-- A pixel point (test helper). -/
private def tp (x y : Int) : FPt := ⟨x * 256, y * 256⟩

/-- An open polyline through pixel points. -/
private def tline (pts : List (Int × Int)) : DPath :=
  match pts with
  | [] => #[]
  | (x, y) :: rest =>
    #[DSeg.moveTo (tp x y)] ++ (rest.map fun (a, b) => DSeg.lineTo (tp a b)).toArray

/-- Line style with width 1 (the width comes from `Geo.make`). -/
private def tstyle (cap : LineCap := .butt) (jn : LineJoin := .miter) (ml : Int := 10)
    (dash : List Int := []) : LineStyle :=
  { cap, join := jn, miterLimit := Content.Fixed.ofInt ml,
    dash := { array := dash.map Content.Fixed.ofInt } }

/-- Coverage total of a stroke (255 per covered pixel). -/
private def tcov (w sx : Rat) (l : LineStyle) (p : DPath) : Nat :=
  (fillEdges (strokeDPath {} (Geo.make (Aff.scale (256 * sx) 256) w) l p) .nonzero
    ⟨0, 0, 100, 100⟩).total

-- Horizontal line, width 2, butt caps: the exact 20 × 2 rectangle.
#guard tcov 2 1 (tstyle) (tline [(10, 10), (30, 10)]) == 40 * 255
-- Square caps add w/2 at each end: w² = 4 px² more.
#guard tcov 2 1 (tstyle .square) (tline [(10, 10), (30, 10)]) == 44 * 255
-- Right angle, width 4: miter fills the 2 × 2 corner square, bevel half of it.
#guard tcov 4 1 (tstyle) (tline [(10, 10), (30, 10), (30, 30)]) == 160 * 255
#guard
  let b := tcov 4 1 (tstyle (jn := .bevel)) (tline [(10, 10), (30, 10), (30, 30)])
  157 * 255 < b && b < 159 * 255
-- A sharp angle exceeds miter limit 10 (falls back to bevel) but not 100.
#guard tcov 2 1 (tstyle (ml := 10)) (tline [(10, 50), (60, 50), (10, 52)]) ==
  tcov 2 1 (tstyle (jn := .bevel)) (tline [(10, 50), (60, 50), (10, 52)])
#guard tcov 2 1 (tstyle (ml := 100)) (tline [(10, 50), (60, 50), (10, 52)]) >
  tcov 2 1 (tstyle (ml := 10)) (tline [(10, 50), (60, 50), (10, 52)]) + 40 * 255
-- Dashes [3 1] on a 40-long line: on/(on + off) = 3/4 of the 80 px² solid area.
#guard tcov 2 1 (tstyle (dash := [3, 1])) (tline [(10, 10), (50, 10)]) == 60 * 255
-- Non-uniform CTM (x scaled by 3): a vertical line of user width 2 is 6 px wide.
#guard tcov 2 3 (tstyle) (tline [(10, 10), (10, 30)]) == 120 * 255
-- Zero width: a visible hairline about one pixel wide.
#guard
  let t := tcov 0 1 (tstyle) (tline [(10, 10), (30, 10)])
  19 * 255 ≤ t && t ≤ 21 * 255
-- Degenerate subpath: a disc with round caps, nothing with butt caps.
#guard tcov 2 1 (tstyle .round) (tline [(10, 10), (10, 10)]) > 2 * 255
#guard tcov 2 1 (tstyle .butt) (tline [(10, 10), (10, 10)]) == 0
-- Square root: √2 to 20 bits, and exact squares.
#guard sqrtQ 2 * sqrtQ 2 ≤ 2 && 2 < (sqrtQ 2 + 1 / 1048576) * (sqrtQ 2 + 1 / 1048576)
#guard sqrtQ (9 / 4) == 3 / 2 && sqrtQ 0 == 0
-- The pen circle points lie exactly on the unit circle.
#guard (circleTable 5).size == 20 && (circleTable 5).all fun p => p.x * p.x + p.y * p.y == 1
-- The fast stroker equals the reference: round joins and caps, dashes, a curve with miter
-- joins, a non-uniform pen.
#guard
  let p := tline [(10, 10), (30, 10), (30, 30), (12, 40)]
  let g := Geo.make (Aff.scale 256 256) 3
  let l := tstyle .round .round 10 [3, 1]
  strokeDPath {} g l p == strokeDPathSpec {} g l p
#guard
  let p : DPath := #[.moveTo (tp 10 10), .curveTo (tp 40 10) (tp 40 40) (tp 10 50)]
  let g := Geo.make (Aff.scale (3 * 256) 256) 2
  strokeDPath {} g (tstyle .square) p == strokeDPathSpec {} g (tstyle .square) p
-- Grid values: `dminOf 4 = smoothDmin`, `rnd32` rounds halves up, `gridQ` rounds to 2⁻¹⁶.
#guard dminOf smoothMiterLimit == smoothDmin
#guard rnd32 (-2147483648) == 0 && rnd32 2147483648 == 1 && rnd32 (-2147483649) == -1
#guard gridQ (1 / 3) == 21845 && gridQ (-1 / 2) == -32768

end SafePdf.Core.Raster.Stroke
