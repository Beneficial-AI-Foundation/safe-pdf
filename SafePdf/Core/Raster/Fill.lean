import SafePdf.Core.Raster.Geom

/-!
# Fill core: Bézier flattening, polygon edges, scanline coverage (task 7.2a)

Plan.md §6 Phase 7 ("scanline fill (nonzero + even-odd), Bézier flattening with proven error
bound, … anti-aliasing"; "Proven: totality, resource bounds (S3: work ≤ f(area,
display-list size))"), §4 **S3**, §8 ("Rational-arithmetic geometric model as proof
reference; float implementation tested" — here the implementation is exact integer
arithmetic rather than floats). ISO 32000-2 §8.5.3.3 (fill rules), §8.5.2.2 (cubic Bézier
curves).

## Pipeline

1. **Device path** (`DPath = Array DSeg`). `ofContentPath m p` maps a `Content.Path` (page
   space, `Fixed`) through an exact `Geom.Aff` `m` (page → device pixels, e.g. a
   `Geom.viewMatrix`) and rounds each point to **subpixel fixed point**: `Int` in units of
   `1/256` px (`subUnit`), clamped to `±Config.coordLimit` (≈ 4.2 million px). Rational arithmetic
   happens once per path point, never per pixel. Glyph outlines (7.3) build a `DPath`
   directly (a quadratic segment is the cubic with controls `p0 + 2/3(q − p0)`,
   `p2 + 2/3(q − p2)`: degree elevation is exact).
2. **Flattening** (`flatten`) turns the path into polygon edges (`Edge`, oriented
   top-to-bottom with a winding sign; horizontal edges are dropped — they never cross a
   sample row). A cubic is split into `n` uniform parameter steps, its points computed
   exactly in `Int` (`bezNum`, `bezNum_eq`) and rounded once (`roundDivI_err`). `n` is the
   least `n ≥ 1` with `3·M ≤ 4·tol·n²` (`segCount`, `segCount_spec`), where `M` is the
   largest absolute second difference of the control polygon (both coordinates), capped at
   `Config.segCap` (`Limits.curveSegCap`). Curves whose control hull lies entirely on one side of the clip window
   become their chord (exact for the coverage inside the window: the window is outside the
   region between curve and chord).
3. **Coverage** (`fillEdges`): a scanline rasterizer over the mask rectangle
   (path bounding box ∩ clip window). Each pixel row is sampled at `S` sample rows
   (`Config.vSamples`, clamped to `1 … 16`); at each, the crossings of the active edges are
   sorted (`Array.mergeSort`) and swept with the nonzero or even-odd rule; inside spans are
   added with **exact horizontal coverage** (subpixel resolution `1/256`) to a difference
   accumulator, which a prefix sum turns into the pixel coverage of the row, written as a byte
   `0 … 255` (`covByte`). So anti-aliasing is exact-area horizontally and `S`-level
   supersampled vertically. An axis-aligned rectangle with integer corners gets exactly 255
   inside and 0 outside (tested). That description is the **reference** filler
   (`fillEdgesCountedSpec`, section 5); the filler in use (`fillEdgesCounted`, section 6, tasks
   7.2f/7.2j) computes the same bytes either from all crossings bucketed by sample row (small
   masks: glyphs) or with 64-bit active edges whose crossing order is carried across sample
   rows (insertion sort, `mergeSort` fallback), with one reused `UInt32` accumulator; cubics
   are flattened by exact forward differences (`cubicFD_eq`), and `ofContentPath` maps points
   with 64-bit integers when the matrix allows (`IAff`); the fillers and the point mapping are
   tested byte-for-byte against their references (suite `raster-fill-spec`).

## What is proven

* **Flattening error bound over ℚ** (`flatten_err`, from `bez_sub_chord`): for control
  values `p0 … p3` (one coordinate), `M` bounding both absolute second differences, `n > 0`,
  `k < n` and `t ∈ [k/n, (k+1)/n]`, the curve point `B(t)` and the point of the chord from
  `B(k/n)` to `B((k+1)/n)` at the same parameter differ by at most `3·M / (4·n²)`. Applied to
  `x` and `y` this bounds the parametric (hence Hausdorff) distance between the curve and the
  exact polyline per coordinate (L∞; the Euclidean distance is at most `√2` times it).
  `segCount_spec` + `flatten_err_tol`: with the chosen `n` (unless capped), the bound is
  `≤ tol`; `segCount_tol_of_cap` states the cap condition explicitly: whenever
  `3·M ≤ 4·tol·cap²` the chosen `n` satisfies the bound. The implementation's vertices are the exact `B(k/n)` (`bezNum_eq`) rounded to the
  nearest subpixel unit (`roundDivI_err`: error ≤ 1/2 unit per coordinate), so the
  implemented polyline is within `tol + 1/2` subpixel units of the curve per coordinate.
* **Totality** by construction (structural recursion and `Array` folds; no `partial`).
* **S3 work bound**: `flatten_size_le` — at most `cfg.segCap · #segments + 1` edges;
  `fillEdgesCounted_steps_le` — the counted row work (`S` × active edges + mask width + 1
  per row; every active-edge list has at most `E` edges, `rowLoop_inv`) is
  `≤ h · (S · E + w + 1)`, with `h`, `w` the mask height and width (at most the clip window's).
  The per-sample-row ordering of the crossings (≤ `E` elements; reference: `mergeSort`; fast
  filler: insertion sort with a swap budget `8·E + 64`, then `mergeSort`, or for the bucketed
  path an insertion sort of at most 64 crossings) is `O(E log E)` by its algorithm; that factor
  is not part of the counted steps. The fast filler proves the same bound (`rowLoopF_inv`,
  `fillRows_spec`), and its counted steps equal the reference's (tested).
* **Forward differences** (`cubicFD_eq`, from `bezNum_d3`, `bezNum_fd0`): the flattener's
  vertices, computed by additions only, are exactly those of `cubicLoop` (`bezAt`).
* **Buffer shape**: `fillEdges_size` — the coverage buffer has exactly `w · h` bytes; every
  write is a `ByteArray.push` or a bounds-checked `Array.modify` (no `!` indexing).

## Tested (`#guard`s below, suite `Tests/RasterFill.lean`)

Rectangle exactness, triangle and circle (4 cubics) areas within tolerance, nonzero vs
even-odd on a self-overlapping star (and agreement on a simple polygon), empty path, path
outside the window, huge clamped coordinates, coverage of every byte in `[0, 255]`.

## Caps (`SafePdf.Limits`, task 7.2d)

`Config` carries the raster caps, each defaulting from `Limits.default` (`Config.ofLimits`
builds one from any `Limits`): `curveSegCap` (512 chords per cubic) and `coordLimit` (`2³⁰`
subpixel units) here, `arcSegCap` and `maxDashSteps` for the stroker (7.2b), `maxPageSide`
and `clipCacheSize` for page rendering (7.2c). The work-bound theorems are stated over these
fields. None raises an error (see the `Limits` docstrings): the curve cap only coarsens
absurdly large curves, the clamp only moves points beyond ±4 million pixels.
-/

namespace SafePdf.Core.Raster.Fill

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Content (FillRule)

/-! ## 1. The ℚ model of a cubic and the flattening bound -/

/-- One coordinate of the cubic Bézier curve with control values `p0 … p3` at parameter `t`
(Bernstein form, ISO 32000-2 §8.5.2.2). -/
def bez (p0 p1 p2 p3 t : Rat) : Rat :=
  (1 - t) * (1 - t) * (1 - t) * p0 + 3 * (1 - t) * (1 - t) * t * p1 +
    3 * (1 - t) * t * t * p2 + t * t * t * p3

/-- Second derivative of `bez` at `s`: `6·((1 − s)·Δ²₀ + s·Δ²₁)` with the control polygon's
second differences `Δ²₀ = p0 − 2p1 + p2`, `Δ²₁ = p1 − 2p2 + p3`. -/
def bezDD (p0 p1 p2 p3 s : Rat) : Rat :=
  6 * ((1 - s) * (p0 - 2 * p1 + p2) + s * (p1 - 2 * p2 + p3))

/-- Linear interpolation `u + r·(v − u)`. -/
def lerp (u v r : Rat) : Rat := u + r * (v - u)

/-- **Chord identity.** For a cubic `B` and `a ≠ b`, the deviation of `B(t)` from the chord
through `B(a)`, `B(b)` at the same parameter is `(t − a)(t − b)/2 · B''((a + b + t)/3)`
(the divided difference `B[a, b, t]` of a cubic is `B''` at the mean of its nodes over 2). -/
theorem bez_sub_chord (p0 p1 p2 p3 a b t : Rat) (h : b - a ≠ 0) :
    bez p0 p1 p2 p3 t - lerp (bez p0 p1 p2 p3 a) (bez p0 p1 p2 p3 b) ((t - a) / (b - a)) =
      (t - a) * (t - b) / 2 * bezDD p0 p1 p2 p3 ((a + b + t) / 3) := by
  simp only [bez, bezDD, lerp]
  grind

/-- On `[0, 1]`, `|B''| ≤ 6·M` when both second differences are bounded by `M`. -/
theorem bezDD_bound (p0 p1 p2 p3 s M : Rat) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h1 : -M ≤ p0 - 2 * p1 + p2) (h1' : p0 - 2 * p1 + p2 ≤ M)
    (h2 : -M ≤ p1 - 2 * p2 + p3) (h2' : p1 - 2 * p2 + p3 ≤ M) :
    -(6 * M) ≤ bezDD p0 p1 p2 p3 s ∧ bezDD p0 p1 p2 p3 s ≤ 6 * M := by
  have hs : 0 ≤ 1 - s := by grind
  have a1 := Rat.mul_le_mul_of_nonneg_left h1 hs
  have a2 := Rat.mul_le_mul_of_nonneg_left h1' hs
  have b1 := Rat.mul_le_mul_of_nonneg_left h2 hs0
  have b2 := Rat.mul_le_mul_of_nonneg_left h2' hs0
  simp only [bezDD]; constructor <;> grind

/-- Squares are non-negative. -/
private theorem sq_nonneg' (x : Rat) : 0 ≤ x * x := by
  rcases Rat.le_total (a := 0) (b := x) with h | h
  · exact Rat.mul_nonneg h h
  · have := Rat.mul_nonneg (a := -x) (b := -x) (by grind) (by grind)
    grind

/-- `0 ≤ (t − a)(b − t) ≤ (b − a)²/4` on `[a, b]`. -/
private theorem quad_bound (a b t : Rat) (ha : a ≤ t) (hb : t ≤ b) :
    0 ≤ (t - a) * (b - t) ∧ (t - a) * (b - t) ≤ (b - a) * (b - a) / 4 := by
  have h0 := Rat.mul_nonneg (a := t - a) (b := b - t) (by grind) (by grind)
  refine ⟨h0, ?_⟩
  have := sq_nonneg' ((a + b) / 2 - t)
  grind

/-- `|u·v| ≤ U·V` from `0 ≤ u ≤ U`, `|v| ≤ V`. -/
private theorem mul_abs_bound (u U v V : Rat) (hu : 0 ≤ u) (hU : u ≤ U) (hv : -V ≤ v)
    (hv' : v ≤ V) : -(U * V) ≤ u * v ∧ u * v ≤ U * V := by
  have hV : 0 ≤ V := by grind
  have e1 := Rat.mul_le_mul_of_nonneg_left hv' hu
  have e2 := Rat.mul_le_mul_of_nonneg_left hv hu
  have e3 : u * V ≤ U * V := by
    have := Rat.mul_le_mul_of_nonneg_left hU hV; grind
  grind

/-- **Chord error on one parameter interval.** For `0 ≤ a < b ≤ 1` and `t ∈ [a, b]`, the
curve deviates from its chord over `[a, b]` by at most `3/4 · M · (b − a)²`. -/
theorem chord_err (p0 p1 p2 p3 M a b t : Rat) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hat : a ≤ t) (htb : t ≤ b)
    (h1 : -M ≤ p0 - 2 * p1 + p2) (h1' : p0 - 2 * p1 + p2 ≤ M)
    (h2 : -M ≤ p1 - 2 * p2 + p3) (h2' : p1 - 2 * p2 + p3 ≤ M) :
    -(3 / 4 * M * ((b - a) * (b - a))) ≤
        bez p0 p1 p2 p3 t - lerp (bez p0 p1 p2 p3 a) (bez p0 p1 p2 p3 b) ((t - a) / (b - a)) ∧
      bez p0 p1 p2 p3 t - lerp (bez p0 p1 p2 p3 a) (bez p0 p1 p2 p3 b) ((t - a) / (b - a)) ≤
        3 / 4 * M * ((b - a) * (b - a)) := by
  rw [bez_sub_chord _ _ _ _ _ _ _ (by grind)]
  have hdd := bezDD_bound p0 p1 p2 p3 ((a + b + t) / 3) M (by grind) (by grind) h1 h1' h2 h2'
  have hq := quad_bound a b t hat htb
  have hm := mul_abs_bound _ _ _ _ hq.1 hq.2 hdd.1 hdd.2
  have e : (t - a) * (t - b) / 2 * bezDD p0 p1 p2 p3 ((a + b + t) / 3) =
      -((t - a) * (b - t) * bezDD p0 p1 p2 p3 ((a + b + t) / 3)) / 2 := by grind
  rw [e]; constructor <;> grind

/-- **Flattening error bound (uniform subdivision).** Split the parameter range into `n`
equal steps; on step `k` (`k < n`), every curve point `B(t)`, `t ∈ [k/n, (k+1)/n]`, is within
`3·M / (4·n²)` of the point of the chord `B(k/n) → B((k+1)/n)` at the same parameter, and
vice versa (the correspondence is a bijection of the parameter), per coordinate. -/
theorem flatten_err (p0 p1 p2 p3 M : Rat) (n k : Nat) (hk : k < n) (t : Rat)
    (ht0 : (k : Rat) / n ≤ t) (ht1 : t ≤ ((k : Rat) + 1) / n)
    (h1 : -M ≤ p0 - 2 * p1 + p2) (h1' : p0 - 2 * p1 + p2 ≤ M)
    (h2 : -M ≤ p1 - 2 * p2 + p3) (h2' : p1 - 2 * p2 + p3 ≤ M) :
    -(3 * M / (4 * ((n : Rat) * n))) ≤
        bez p0 p1 p2 p3 t -
          lerp (bez p0 p1 p2 p3 ((k : Rat) / n)) (bez p0 p1 p2 p3 (((k : Rat) + 1) / n))
            (n * t - k) ∧
      bez p0 p1 p2 p3 t -
          lerp (bez p0 p1 p2 p3 ((k : Rat) / n)) (bez p0 p1 p2 p3 (((k : Rat) + 1) / n))
            (n * t - k) ≤ 3 * M / (4 * ((n : Rat) * n)) := by
  have hn : (0 : Rat) < n := by
    have : ((0 : Nat) : Rat) < ((n : Nat) : Rat) := Rat.natCast_lt_natCast.mpr (by omega)
    simpa using this
  have hkn : ((k : Rat) + 1) ≤ n := by
    have : ((k + 1 : Nat) : Rat) ≤ ((n : Nat) : Rat) := Rat.natCast_le_natCast.mpr (by omega)
    simpa using this
  have hk0 : (0 : Rat) ≤ k := by
    have : ((0 : Nat) : Rat) ≤ ((k : Nat) : Rat) := Rat.natCast_le_natCast.mpr (by omega)
    simpa using this
  have hne : (n : Rat) ≠ 0 := by grind
  have ha0 : (0 : Rat) ≤ (k : Rat) / n := by
    rw [Rat.div_def]; exact Rat.mul_nonneg hk0 (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  have hab : (k : Rat) / n < ((k : Rat) + 1) / n := by
    rw [Rat.lt_div_iff hn]; grind
  have hb1 : ((k : Rat) + 1) / n ≤ 1 := by
    apply Rat.not_lt.mp; rw [Rat.lt_div_iff hn]; grind
  have h := chord_err p0 p1 p2 p3 M ((k : Rat) / n) (((k : Rat) + 1) / n) t ha0 hab hb1
    ht0 ht1 h1 h1' h2 h2'
  have e1 : (t - (k : Rat) / n) / (((k : Rat) + 1) / n - (k : Rat) / n) = n * t - k := by
    grind
  have e2 : 3 / 4 * M * ((((k : Rat) + 1) / n - (k : Rat) / n) *
      (((k : Rat) + 1) / n - (k : Rat) / n)) = 3 * M / (4 * ((n : Rat) * n)) := by
    grind
  rw [e1, e2] at h; exact h

/-- With `3·M ≤ 4·tol·n²` (the choice made by `segCount`), the flattening error bound of
`flatten_err` is at most `tol`. -/
theorem flatten_err_tol (M tol : Rat) (n : Nat) (hn : 0 < n)
    (h : 3 * M ≤ 4 * tol * ((n : Rat) * n)) : 3 * M / (4 * ((n : Rat) * n)) ≤ tol := by
  have hn' : (0 : Rat) < n := by
    have : ((0 : Nat) : Rat) < ((n : Nat) : Rat) := Rat.natCast_lt_natCast.mpr hn
    simpa using this
  have hpos : (0 : Rat) < 4 * ((n : Rat) * n) := by
    have := Rat.mul_pos hn' hn'; grind
  apply Rat.not_lt.mp; rw [Rat.lt_div_iff hpos]; grind

/-! ## 2. Exact integer evaluation of the subdivision points -/

/-- `n³ · B(k/n)` as an integer: `(n−k)³p0 + 3(n−k)²k·p1 + 3(n−k)k²·p2 + k³p3`. -/
def bezNum (n k : Nat) (p0 p1 p2 p3 : Int) : Int :=
  let j : Int := (n : Int) - k
  let k : Int := k
  j * j * j * p0 + 3 * j * j * k * p1 + 3 * j * k * k * p2 + k * k * k * p3

/-- `bezNum` is exact: divided by `n³` it is the ℚ curve point at `k/n`. -/
theorem bezNum_eq (n k : Nat) (hn : 0 < n) (p0 p1 p2 p3 : Int) :
    ((bezNum n k p0 p1 p2 p3 : Int) : Rat) / ((n : Rat) * n * n) =
      bez p0 p1 p2 p3 ((k : Rat) / n) := by
  have : (n : Rat) ≠ 0 := by
    intro h
    have h2 : ((n : Nat) : Rat) = ((0 : Nat) : Rat) := by simpa using h
    have := Rat.natCast_inj.mp h2; omega
  simp only [bezNum, bez, Rat.intCast_add, Rat.intCast_mul, Rat.intCast_sub,
    Rat.intCast_natCast, Rat.intCast_ofNat]
  grind

/-- `a / d` rounded to the nearest integer (halves up), for `d > 0`. -/
def roundDivI (a d : Int) : Int := (2 * a + d) / (2 * d)

/-- Rounding error of `roundDivI`: `|q·d − a| ≤ d/2`. -/
theorem roundDivI_err (a d : Int) (hd : 0 < d) :
    -d < 2 * (roundDivI a d * d - a) ∧ 2 * (roundDivI a d * d - a) ≤ d := by
  have h1 := Int.mul_ediv_add_emod (2 * a + d) (2 * d)
  have h2 := Int.emod_nonneg (2 * a + d) (b := 2 * d) (by omega)
  have h3 := Int.emod_lt_of_pos (2 * a + d) (b := 2 * d) (by omega)
  simp only [roundDivI]
  generalize (2 * a + d) / (2 * d) = q at *
  generalize (2 * a + d) % (2 * d) = r at *
  have : 2 * d * q = 2 * (q * d) := by grind
  constructor <;> omega

/-! ## 3. Device paths in subpixel fixed point -/

/-- Subpixel units per pixel (8 fractional bits). -/
def subUnit : Int := 256

/-- A device point, in `1/256` pixel units (y downward, as `Geom.toScreen`). -/
structure FPt where
  /-- Horizontal coordinate, subpixel units. -/
  x : Int
  /-- Vertical coordinate, subpixel units. -/
  y : Int
  deriving DecidableEq, Repr, Inhabited

/-- A device path segment (the `Content.Segment` shape, in subpixel units). -/
inductive DSeg where
  /-- Start a new subpath (implicitly closing the previous one, as filling does). -/
  | moveTo (p : FPt)
  /-- Straight line to `p`. -/
  | lineTo (p : FPt)
  /-- Cubic Bézier with controls `c1`, `c2`, ending at `p`. -/
  | curveTo (c1 c2 p : FPt)
  /-- Close the current subpath. -/
  | closePath
  deriving DecidableEq, Repr, Inhabited

/-- A device path. -/
abbrev DPath := Array DSeg

/-- Clamp to `[−lim, lim]` (`lim` = `Limits.coordLimit`, default `2³⁰` subpixel units). -/
def clampCoord (v : Int) (lim : Int := (Limits.default.coordLimit : Int)) : Int :=
  max (-lim) (min lim v)

/-- A rational pixel coordinate in subpixel units, rounded to nearest (halves up). -/
def toSub (q : Rat) : Int := roundDivI (q.num * subUnit) (q.den : Int)

/-- A device point (pixels, exact) in subpixel units clamped to `±lim`. -/
def FPt.ofPt (p : Pt) (lim : Int := (Limits.default.coordLimit : Int)) : FPt :=
  ⟨clampCoord (toSub p.x) lim, clampCoord (toSub p.y) lim⟩

/-- Map one content-stream segment (page space) through `m` (page → device pixels),
clamping to `±lim` subpixel units. -/
def DSeg.ofSegment (lim : Int) (m : Aff) : Content.Segment → DSeg
  | .moveTo p => .moveTo (FPt.ofPt (m.apply (ptOfPoint p)) lim)
  | .lineTo p => .lineTo (FPt.ofPt (m.apply (ptOfPoint p)) lim)
  | .curveTo c1 c2 p =>
    .curveTo (FPt.ofPt (m.apply (ptOfPoint c1)) lim) (FPt.ofPt (m.apply (ptOfPoint c2)) lim)
      (FPt.ofPt (m.apply (ptOfPoint p)) lim)
  | .closePath => .closePath

/-- Device pixel rectangle `[x0, x1) × [y0, y1)` (the clip window / target area). -/
structure IRect where
  /-- Left pixel column (inclusive). -/
  x0 : Int
  /-- Top pixel row (inclusive). -/
  y0 : Int
  /-- Right pixel column (exclusive). -/
  x1 : Int
  /-- Bottom pixel row (exclusive). -/
  y1 : Int
  deriving DecidableEq, Repr, Inhabited

/-! ## 4. Flattening to edges -/

/-- A non-horizontal polygon edge, `y0 < y1` (subpixel units), with winding `+1` if the
path runs downward (increasing `y`) along it, `−1` otherwise. -/
structure Edge where
  /-- Upper endpoint x. -/
  x0 : Int
  /-- Upper endpoint y. -/
  y0 : Int
  /-- Lower endpoint x. -/
  x1 : Int
  /-- Lower endpoint y (`> y0`). -/
  y1 : Int
  /-- Winding contribution, `±1`. -/
  wind : Int
  deriving DecidableEq, Repr, Inhabited

/-- Append the edge `a → b` (dropped when horizontal). -/
def pushLine (es : Array Edge) (a b : FPt) : Array Edge :=
  if a.y < b.y then es.push ⟨a.x, a.y, b.x, b.y, 1⟩
  else if b.y < a.y then es.push ⟨b.x, b.y, a.x, a.y, -1⟩
  else es

/-- `pushLine` adds at most one edge. -/
theorem pushLine_size (es : Array Edge) (a b : FPt) : (pushLine es a b).size ≤ es.size + 1 := by
  unfold pushLine; split
  · simp
  · split <;> simp

/-- The closed polygon through `pts` as edges (for stroking, 7.2b). -/
def polygonEdges (pts : Array FPt) : Array Edge :=
  match pts[0]? with
  | none => #[]
  | some p0 =>
    let r := pts.foldl (fun (acc : Array Edge × FPt) q => (pushLine acc.1 acc.2 q, q)) (#[], p0)
    pushLine r.1 r.2 p0

/-- Raster configuration: flattening tolerance, anti-aliasing quality, and the raster caps
of `SafePdf.Limits` (task 7.2d; each defaults from `Limits.default`, `Config.ofLimits` copies
them from any `Limits`). Shared by the filler, the stroker (7.2b) and page rendering
(7.2c). -/
structure Config where
  /-- Flattening tolerance per coordinate, in subpixel units (default 26 ≈ 0.1 px: chords lie
  inside convex arcs, so a coarser tolerance visibly thins small glyphs — 0.2 px loses 4.5% of
  the area of a radius-5 disc, 0.1 px 1.6%). -/
  tol : Nat := 26
  /-- Sample rows per pixel row (vertical anti-aliasing levels), clamped to `1 … 16`. -/
  vSamples : Nat := 4
  /-- `Limits.curveSegCap`: chords per cubic (values below 1 act as 1, `segCap`). -/
  curveSegCap : Nat := Limits.default.curveSegCap
  /-- `Limits.coordLimit`: device coordinates are clamped to `±coordLimit` subpixel units. -/
  coordLimit : Nat := Limits.default.coordLimit
  /-- `Limits.arcSegCap`: chords per quarter of the pen ellipse (stroker; below 1 acts as 1). -/
  arcSegCap : Nat := Limits.default.arcSegCap
  /-- `Limits.maxDashSteps`: dash steps per stroked path (above it: solid). -/
  maxDashSteps : Nat := Limits.default.maxDashSteps
  /-- `Limits.maxPageSide`: page width and height in pixels (larger pages are cropped). -/
  maxPageSide : Nat := Limits.default.maxPageSide
  /-- `Limits.clipCacheSize`: cached clip masks per page. -/
  clipCacheSize : Nat := Limits.default.clipCacheSize
  /-- `Limits.renderStepFactor`: render work allowance per page pixel (task 13.4b). -/
  renderStepFactor : Nat := Limits.default.renderStepFactor
  /-- `Limits.renderStepFloor`: floor of the render work allowance (task 13.4b). -/
  renderStepFloor : Nat := Limits.default.renderStepFloor
  deriving Repr, Inhabited

/-- The raster configuration with the caps of `l` (tolerance and sampling from `base`). -/
def Config.ofLimits (l : Limits) (base : Config := {}) : Config :=
  { base with curveSegCap := l.curveSegCap, coordLimit := l.coordLimit,
              arcSegCap := l.arcSegCap, maxDashSteps := l.maxDashSteps,
              maxPageSide := l.maxPageSide, clipCacheSize := l.clipCacheSize,
              renderStepFactor := l.renderStepFactor, renderStepFloor := l.renderStepFloor }

/-- The render work allowance in counted steps of a `W × H` pixel page (task 13.4b), as
`Limits.renderAllowance`: `max renderStepFloor (renderStepFactor · W · H)`. -/
def Config.renderAllowance (cfg : Config) (W H : Nat) : Nat :=
  max cfg.renderStepFloor (cfg.renderStepFactor * (W * H))

/-- `Config.ofLimits` computes the allowance of `Limits.renderAllowance`. -/
theorem Config.ofLimits_renderAllowance (l : Limits) (base : Config) (W H : Nat) :
    (Config.ofLimits l base).renderAllowance W H = l.renderAllowance W H := rfl

/-- The effective chord cap per cubic: `max 1 curveSegCap`. -/
def Config.segCap (cfg : Config) : Nat := max 1 cfg.curveSegCap

/-- The effective chord cap is positive. -/
theorem Config.one_le_segCap (cfg : Config) : 1 ≤ cfg.segCap := Nat.le_max_left _ _

/-- The effective chord cap per quarter of the pen ellipse (stroker): `max 1 arcSegCap`. -/
def Config.arcCap (cfg : Config) : Nat := max 1 cfg.arcSegCap

/-- Upper bound on the vertices of one emitted stroke polygon: `4 · arcCap` (the pen). -/
def Config.polyCap (cfg : Config) : Nat := 4 * cfg.arcCap

/-- `⌊n / d⌋` for `d > 0` (`Int64` division truncates). -/
@[inline] def fdiv64 (n d : Int64) : Int64 :=
  let q := n / d
  if n % d < 0 then q - 1 else q

/-- An affine map over a common denominator, for exact 64-bit point mapping (task 7.2f):
`x' = (a·X + c·Y + e·10⁶) / (dm·10⁶)`, `y' = (b·X + d·Y + f·10⁶) / (dm·10⁶)` for a
`Content.Point` with raw `Fixed` values `X`, `Y` (units of `10⁻⁶`). -/
structure IAff where
  /-- `Aff.a · dm`. -/
  a : Int64
  /-- `Aff.b · dm`. -/
  b : Int64
  /-- `Aff.c · dm`. -/
  c : Int64
  /-- `Aff.d · dm`. -/
  d : Int64
  /-- `Aff.e · dm · 10⁶`. -/
  e : Int64
  /-- `Aff.f · dm · 10⁶`. -/
  f : Int64
  /-- The denominator `dm · 10⁶`. -/
  den : Int64

/-- `|v| ≤ b` (on `natAbs`: no big-integer arithmetic for small `v`). -/
@[inline] def absLe (v : Int) (b : Nat) : Bool := v.natAbs ≤ b

/-- `m` over its common denominator `dm` (lcm of the six denominators), when every scaled
entry is small enough for `IAff.sub` to be exact in 64 bits: `dm ≤ 2²⁰`, the linear entries
`≤ 2²⁰` and the translations `≤ 2³⁰` in absolute value (after scaling by `dm`). -/
def IAff.ofAff? (m : Aff) : Option IAff :=
  let dm : Nat := Nat.lcm m.a.den (Nat.lcm m.b.den (Nat.lcm m.c.den (Nat.lcm m.d.den
    (Nat.lcm m.e.den m.f.den))))
  let sc := fun (q : Rat) => q.num * ((dm / q.den : Nat) : Int)
  let a := sc m.a
  let b := sc m.b
  let c := sc m.c
  let d := sc m.d
  let e := sc m.e
  let f := sc m.f
  if 0 < dm && dm ≤ 1048576 && absLe a 1048576 && absLe b 1048576 && absLe c 1048576 &&
      absLe d 1048576 && absLe e 1073741824 && absLe f 1073741824 then
    some ⟨a.toInt64, b.toInt64, c.toInt64, d.toInt64, (e * 1000000).toInt64,
      (f * 1000000).toInt64, ((dm : Int) * 1000000).toInt64⟩
  else none

/-- `toSub (N / D)` for `D > 0`: `round(256·N / D)`, halves up, computed as
`256·⌊N/D⌋ + ⌊(512·r + D) / (2·D)⌋` with `r = N mod D` (no overflow for `|N| < 2⁶²`,
`D ≤ 2⁴⁰`). -/
@[inline] def IAff.sub (n den : Int64) : Int64 :=
  let q := fdiv64 n den
  let r := n - q * den
  256 * q + (512 * r + den) / (2 * den)

/-- `2³⁶`, the bound on raw point coordinates of the 64-bit path of `FPt.ofPoint`. Out of line
(`noinline`): a literal of `2³²` or more in a function body is parsed from its decimal string
through GMP on every call (`scripts/check-codegen.sh`, task 13.18). -/
@[noinline] def ptCap36 : Nat := 68719476736

/-- A page point through `m` in subpixel units clamped to `±lim`: the 64-bit path when `im`
is available and `|X|, |Y| ≤ 2³⁶` (then `|N| ≤ 2⁵⁸`), else the exact `Rat` path
(`FPt.ofPt`). Both compute `toSub` of the same rational, so they agree (tested,
suite `raster-fill-spec`). -/
def FPt.ofPoint (lim : Int) (m : Aff) (im : Option IAff) (p : Content.Point) : FPt :=
  match im with
  | some i =>
    if absLe p.x.raw ptCap36 && absLe p.y.raw ptCap36 then
      let X := p.x.raw.toInt64
      let Y := p.y.raw.toInt64
      ⟨clampCoord (IAff.sub (i.a * X + i.c * Y + i.e) i.den).toInt lim,
        clampCoord (IAff.sub (i.b * X + i.d * Y + i.f) i.den).toInt lim⟩
    else FPt.ofPt (m.apply (ptOfPoint p)) lim
  | none => FPt.ofPt (m.apply (ptOfPoint p)) lim

/-- `DSeg.ofSegment` through `FPt.ofPoint` (64-bit fast path). -/
def DSeg.ofSegmentF (lim : Int) (m : Aff) (im : Option IAff) : Content.Segment → DSeg
  | .moveTo p => .moveTo (FPt.ofPoint lim m im p)
  | .lineTo p => .lineTo (FPt.ofPoint lim m im p)
  | .curveTo c1 c2 p =>
    .curveTo (FPt.ofPoint lim m im c1) (FPt.ofPoint lim m im c2) (FPt.ofPoint lim m im p)
  | .closePath => .closePath

/-- A page-space path as a device path (affine maps commute with Bézier curves, so mapping
the control points is exact before rounding), clamped to `±cfg.coordLimit`. Points go
through 64-bit integer arithmetic when the matrix allows it (`IAff.ofAff?`), else through
`Rat`; the results are the same (`ofContentPathSpec`, tested). -/
def ofContentPath (m : Aff) (p : Content.Path) (cfg : Config := {}) : DPath :=
  p.segs.map (DSeg.ofSegmentF (cfg.coordLimit : Int) m (IAff.ofAff? m))

/-- Reference for `ofContentPath`: every point through `Rat` (`DSeg.ofSegment`). -/
def ofContentPathSpec (m : Aff) (p : Content.Path) (cfg : Config := {}) : DPath :=
  p.segs.map (DSeg.ofSegment (cfg.coordLimit : Int) m)

/-- Search for the least `n ∈ [n₀, n₀ + fuel]` with `3·m ≤ 4·tol·n²` (else `n₀ + fuel`). -/
def segCountGo (m tol : Nat) : Nat → Nat → Nat
  | n, 0 => n
  | n, fuel + 1 => if 3 * m ≤ 4 * tol * (n * n) then n else segCountGo m tol (n + 1) fuel

/-- Number of chords for a cubic whose second differences are bounded by `m`: the least
`n ≥ 1` with `3·m ≤ 4·tol·n²`, capped at `cap` (callers pass `Config.segCap ≥ 1`). -/
def segCount (cap m tol : Nat) : Nat := segCountGo m tol 1 (cap - 1)

private theorem segCountGo_spec (m tol : Nat) : ∀ fuel n,
    n ≤ segCountGo m tol n fuel ∧ segCountGo m tol n fuel ≤ n + fuel ∧
      (3 * m ≤ 4 * tol * (segCountGo m tol n fuel * segCountGo m tol n fuel) ∨
        segCountGo m tol n fuel = n + fuel)
  | 0, n => by simp [segCountGo]
  | fuel + 1, n => by
    simp only [segCountGo]
    split
    · rename_i h; exact ⟨Nat.le_refl _, by omega, Or.inl h⟩
    · have ih := segCountGo_spec m tol fuel (n + 1)
      refine ⟨by omega, by omega, ?_⟩
      rcases ih.2.2 with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)

/-- **Chord count.** For a cap `≥ 1`: `1 ≤ n ≤ cap`, and either the flattening bound
`3·m ≤ 4·tol·n²` holds (so the error is `≤ tol`, `flatten_err_tol`) or the cap was hit. -/
theorem segCount_spec (cap m tol : Nat) (hcap : 1 ≤ cap) :
    1 ≤ segCount cap m tol ∧ segCount cap m tol ≤ cap ∧
      (3 * m ≤ 4 * tol * (segCount cap m tol * segCount cap m tol) ∨
        segCount cap m tol = cap) := by
  have h := segCountGo_spec m tol (cap - 1) 1
  simp only [segCount]
  have hc : 1 + (cap - 1) = cap := by omega
  rw [hc] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **The cap condition.** If the cap itself is fine enough for the curve
(`3·m ≤ 4·tol·cap²`), the chosen chord count meets the flattening bound `3·m ≤ 4·tol·n²`, so
the per-coordinate error is `≤ tol` (`flatten_err_tol`). Without that condition the curve is
flattened with `cap` chords and the error is only `≤ 3·m / (4·cap²)` (`flatten_err`): the
documented degradation of `Limits.curveSegCap`. -/
theorem segCount_tol_of_cap (cap m tol : Nat) (hcap : 1 ≤ cap)
    (h : 3 * m ≤ 4 * tol * (cap * cap)) :
    3 * m ≤ 4 * tol * (segCount cap m tol * segCount cap m tol) := by
  rcases (segCount_spec cap m tol hcap).2.2 with h' | h'
  · exact h'
  · rw [h']; exact h

/-- Absolute second difference `|a − 2b + c|`. -/
def dd2 (a b c : Int) : Nat := (a - 2 * b + c).natAbs

/-- The flatness measure `M` of a cubic: the largest absolute second difference of its
control polygon over both coordinates. -/
def flatness (p0 p1 p2 p3 : FPt) : Nat :=
  max (max (dd2 p0.x p1.x p2.x) (dd2 p1.x p2.x p3.x))
    (max (dd2 p0.y p1.y p2.y) (dd2 p1.y p2.y p3.y))

/-- The `k`-th of `n` uniform subdivision points, rounded to subpixel units. -/
def bezAt (n k : Nat) (p0 p1 p2 p3 : FPt) : FPt :=
  let d : Int := (n : Int) * n * n
  ⟨roundDivI (bezNum n k p0.x p1.x p2.x p3.x) d, roundDivI (bezNum n k p0.y p1.y p2.y p3.y) d⟩

/-- Emit the chords `B((k−1)/n) → B(k/n)` for the remaining `fuel` steps; the last point is
`p3` exactly. -/
def cubicLoop (n : Nat) (p0 p1 p2 p3 : FPt) : (fuel k : Nat) → FPt → Array Edge → Array Edge
  | 0, _, _, es => es
  | fuel + 1, k, prev, es =>
    let q := if k = n then p3 else bezAt n k p0 p1 p2 p3
    cubicLoop n p0 p1 p2 p3 fuel (k + 1) q (pushLine es prev q)

private theorem cubicLoop_size (n : Nat) (p0 p1 p2 p3 : FPt) : ∀ fuel k prev es,
    (cubicLoop n p0 p1 p2 p3 fuel k prev es).size ≤ es.size + fuel
  | 0, _, _, _ => by simp [cubicLoop]
  | fuel + 1, k, prev, es => by
    simp only [cubicLoop]
    have := cubicLoop_size n p0 p1 p2 p3 fuel (k + 1)
      (if k = n then p3 else bezAt n k p0 p1 p2 p3)
      (pushLine es prev (if k = n then p3 else bezAt n k p0 p1 p2 p3))
    have := pushLine_size es prev (if k = n then p3 else bezAt n k p0 p1 p2 p3)
    omega

/-- `cubicLoop` by **forward differences** (task 7.2j): `bezNum n k` is a cubic polynomial in
`k`, so its value, first, second and third differences (`f`, `d1`, `d2`, `d3`; `d3` constant)
advance by additions only, exactly (`Int`). Same vertices as `cubicLoop` (`cubicLoopFD_eq`). -/
def cubicLoopFD (n : Nat) (p3 : FPt) (d : Int) :
    (fuel k : Nat) → FPt → (fx d1x d2x d3x fy d1y d2y d3y : Int) → Array Edge → Array Edge
  | 0, _, _, _, _, _, _, _, _, _, _, es => es
  | fuel + 1, k, prev, fx, d1x, d2x, d3x, fy, d1y, d2y, d3y, es =>
    let fx := fx + d1x
    let fy := fy + d1y
    let q : FPt := if k = n then p3 else ⟨roundDivI fx d, roundDivI fy d⟩
    cubicLoopFD n p3 d fuel (k + 1) q fx (d1x + d2x) (d2x + d3x) d3x fy (d1y + d2y) (d2y + d3y) d3y
      (pushLine es prev q)

/-- The third difference of `bezNum n k` in `k` is the constant `6·(p3 − p0 + 3·(p1 − p2))`. -/
theorem bezNum_d3 (n k : Nat) (p0 p1 p2 p3 : Int) :
    bezNum n (k + 3) p0 p1 p2 p3 - 3 * bezNum n (k + 2) p0 p1 p2 p3 +
      3 * bezNum n (k + 1) p0 p1 p2 p3 - bezNum n k p0 p1 p2 p3 =
        6 * (p3 - p0 + 3 * (p1 - p2)) := by
  simp only [bezNum, Int.natCast_add]
  grind

/-- The forward-difference start values at `k = 0`: `bezNum n 0 = n³·p0`, and the first and
second differences in closed form. -/
theorem bezNum_fd0 (n : Nat) (p0 p1 p2 p3 : Int) :
    bezNum n 0 p0 p1 p2 p3 = (n : Int) * n * n * p0 ∧
    bezNum n 1 p0 p1 p2 p3 - bezNum n 0 p0 p1 p2 p3 =
      3 * ((n : Int) * n) * (p1 - p0) + 3 * (n : Int) * (p0 - 2 * p1 + p2) +
        (p3 - p0 + 3 * (p1 - p2)) ∧
    bezNum n 2 p0 p1 p2 p3 - 2 * bezNum n 1 p0 p1 p2 p3 + bezNum n 0 p0 p1 p2 p3 =
      6 * (n : Int) * (p0 - 2 * p1 + p2) + 6 * (p3 - p0 + 3 * (p1 - p2)) := by
  simp only [bezNum]
  refine ⟨by grind, by grind, by grind⟩

/-- **Forward differences are exact**: started with the differences of `bezNum` at `m`,
`cubicLoopFD` emits exactly the edges of `cubicLoop` from vertex `m + 1` on. -/
theorem cubicLoopFD_eq (n : Nat) (p0 p1 p2 p3 : FPt) : ∀ fuel m prev es fx d1x d2x fy d1y d2y,
    fx = bezNum n m p0.x p1.x p2.x p3.x →
    d1x = bezNum n (m + 1) p0.x p1.x p2.x p3.x - bezNum n m p0.x p1.x p2.x p3.x →
    d2x = bezNum n (m + 2) p0.x p1.x p2.x p3.x - 2 * bezNum n (m + 1) p0.x p1.x p2.x p3.x +
      bezNum n m p0.x p1.x p2.x p3.x →
    fy = bezNum n m p0.y p1.y p2.y p3.y →
    d1y = bezNum n (m + 1) p0.y p1.y p2.y p3.y - bezNum n m p0.y p1.y p2.y p3.y →
    d2y = bezNum n (m + 2) p0.y p1.y p2.y p3.y - 2 * bezNum n (m + 1) p0.y p1.y p2.y p3.y +
      bezNum n m p0.y p1.y p2.y p3.y →
    cubicLoopFD n p3 ((n : Int) * n * n) fuel (m + 1) prev fx d1x d2x
        (6 * (p3.x - p0.x + 3 * (p1.x - p2.x))) fy d1y d2y (6 * (p3.y - p0.y + 3 * (p1.y - p2.y)))
        es =
      cubicLoop n p0 p1 p2 p3 fuel (m + 1) prev es
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, m, prev, es, fx, d1x, d2x, fy, d1y, d2y, hf, h1, h2, hfy, h1y, h2y => by
    simp only [cubicLoopFD, cubicLoop]
    have ex : fx + d1x = bezNum n (m + 1) p0.x p1.x p2.x p3.x := by omega
    have ey : fy + d1y = bezNum n (m + 1) p0.y p1.y p2.y p3.y := by omega
    have hq : (if m + 1 = n then p3 else
        (⟨roundDivI (fx + d1x) ((n : Int) * n * n), roundDivI (fy + d1y) ((n : Int) * n * n)⟩ :
          FPt)) = (if m + 1 = n then p3 else bezAt n (m + 1) p0 p1 p2 p3) := by
      rw [ex, ey]; rfl
    rw [hq]
    have t3x := bezNum_d3 n m p0.x p1.x p2.x p3.x
    have t3y := bezNum_d3 n m p0.y p1.y p2.y p3.y
    refine cubicLoopFD_eq n p0 p1 p2 p3 fuel (m + 1) _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (try simp only [Nat.add_assoc, Nat.reduceAdd]) <;> omega

/-- The control hull of the cubic lies entirely on one side of the window (in subpixel
units `[cx0, cx1) × [cy0, cy1)`): then the chord replaces the curve exactly as far as
coverage inside the window is concerned. -/
def hullOutside (cx0 cy0 cx1 cy1 : Int) (p0 p1 p2 p3 : FPt) : Bool :=
  (p0.x ≤ cx0 && p1.x ≤ cx0 && p2.x ≤ cx0 && p3.x ≤ cx0) ||
  (cx1 ≤ p0.x && cx1 ≤ p1.x && cx1 ≤ p2.x && cx1 ≤ p3.x) ||
  (p0.y ≤ cy0 && p1.y ≤ cy0 && p2.y ≤ cy0 && p3.y ≤ cy0) ||
  (cy1 ≤ p0.y && cy1 ≤ p1.y && cy1 ≤ p2.y && cy1 ≤ p3.y)

/-- All `n` chords of a cubic by forward differences (`cubicLoopFD` started at `k = 0`);
equal to `cubicLoop n p0 p1 p2 p3 n 1 p0` (`cubicFD_eq`). -/
def cubicFD (n : Nat) (p0 p1 p2 p3 : FPt) (es : Array Edge) : Array Edge :=
  let N : Int := n
  let ax := p0.x - 2 * p1.x + p2.x
  let cx := p3.x - p0.x + 3 * (p1.x - p2.x)
  let ay := p0.y - 2 * p1.y + p2.y
  let cy := p3.y - p0.y + 3 * (p1.y - p2.y)
  cubicLoopFD n p3 (N * N * N) n 1 p0
    (N * N * N * p0.x) (3 * (N * N) * (p1.x - p0.x) + 3 * N * ax + cx) (6 * N * ax + 6 * cx) (6 * cx)
    (N * N * N * p0.y) (3 * (N * N) * (p1.y - p0.y) + 3 * N * ay + cy) (6 * N * ay + 6 * cy) (6 * cy)
    es

/-- `cubicFD` emits exactly the chords of `cubicLoop`. -/
theorem cubicFD_eq (n : Nat) (p0 p1 p2 p3 : FPt) (es : Array Edge) :
    cubicFD n p0 p1 p2 p3 es = cubicLoop n p0 p1 p2 p3 n 1 p0 es := by
  have hx := bezNum_fd0 n p0.x p1.x p2.x p3.x
  have hy := bezNum_fd0 n p0.y p1.y p2.y p3.y
  refine cubicLoopFD_eq n p0 p1 p2 p3 n 0 p0 es _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Nat.zero_add]) <;> omega

/-- Flatten one cubic into at most `cfg.segCap` edges. -/
def flattenCubic (cfg : Config) (clip : IRect) (es : Array Edge) (p0 p1 p2 p3 : FPt) :
    Array Edge :=
  if hullOutside (clip.x0 * subUnit) (clip.y0 * subUnit) (clip.x1 * subUnit)
      (clip.y1 * subUnit) p0 p1 p2 p3 then
    pushLine es p0 p3
  else
    let n := segCount cfg.segCap (flatness p0 p1 p2 p3) cfg.tol
    cubicFD n p0 p1 p2 p3 es

/-- A cubic adds at most `cfg.segCap` edges. -/
theorem flattenCubic_size (cfg : Config) (clip : IRect) (es : Array Edge) (p0 p1 p2 p3 : FPt) :
    (flattenCubic cfg clip es p0 p1 p2 p3).size ≤ es.size + cfg.segCap := by
  unfold flattenCubic; split
  · have := pushLine_size es p0 p3
    have := cfg.one_le_segCap
    omega
  · dsimp only
    rw [cubicFD_eq]
    have h1 := cubicLoop_size (segCount cfg.segCap (flatness p0 p1 p2 p3) cfg.tol) p0 p1 p2 p3
      (segCount cfg.segCap (flatness p0 p1 p2 p3) cfg.tol) 1 p0 es
    have h2 := (segCount_spec cfg.segCap (flatness p0 p1 p2 p3) cfg.tol cfg.one_le_segCap).2.1
    omega

/-- Flattening state: edges so far, subpath start, current point. -/
structure FState where
  /-- Edges emitted so far. -/
  edges : Array Edge := #[]
  /-- Start of the current subpath. -/
  start : FPt := ⟨0, 0⟩
  /-- Current point. -/
  cur : FPt := ⟨0, 0⟩
  deriving Inhabited

/-- Flatten one segment. Every subpath is closed for filling (ISO 32000-2 §8.5.3.1). -/
def flattenSeg (cfg : Config) (clip : IRect) (st : FState) : DSeg → FState
  | .moveTo p => { edges := pushLine st.edges st.cur st.start, start := p, cur := p }
  | .lineTo p => { st with edges := pushLine st.edges st.cur p, cur := p }
  | .curveTo c1 c2 p => { st with edges := flattenCubic cfg clip st.edges st.cur c1 c2 p, cur := p }
  | .closePath => { st with edges := pushLine st.edges st.cur st.start, cur := st.start }

private theorem flattenSeg_size (cfg : Config) (clip : IRect) (st : FState) (s : DSeg) :
    (flattenSeg cfg clip st s).edges.size ≤ st.edges.size + cfg.segCap := by
  have := cfg.one_le_segCap
  cases s with
  | moveTo p => have := pushLine_size st.edges st.cur st.start; simp only [flattenSeg]; omega
  | lineTo p => have := pushLine_size st.edges st.cur p; simp only [flattenSeg]; omega
  | curveTo c1 c2 p => exact flattenCubic_size cfg clip st.edges st.cur c1 c2 p
  | closePath => have := pushLine_size st.edges st.cur st.start; simp only [flattenSeg]; omega

/-- **Flattening.** The polygon edges of a device path (all subpaths closed). The window
`clip` only lets curves outside it be replaced by their chords. -/
def flatten (cfg : Config) (clip : IRect) (p : DPath) : Array Edge :=
  let st := p.foldl (flattenSeg cfg clip) {}
  pushLine st.edges st.cur st.start

private theorem foldl_flattenSeg_size (cfg : Config) (clip : IRect) :
    ∀ (l : List DSeg) (st : FState),
      (l.foldl (flattenSeg cfg clip) st).edges.size ≤ st.edges.size + cfg.segCap * l.length
  | [], st => by simp
  | s :: l, st => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := foldl_flattenSeg_size cfg clip l (flattenSeg cfg clip st s)
    have h2 := flattenSeg_size cfg clip st s
    rw [Nat.mul_succ]; omega

/-- **S3, edge count.** A path of `s` segments flattens to at most `cfg.segCap · s + 1`
edges (`cfg.segCap = max 1 cfg.curveSegCap`, `Limits.curveSegCap`). -/
theorem flatten_size_le (cfg : Config) (clip : IRect) (p : DPath) :
    (flatten cfg clip p).size ≤ cfg.segCap * p.size + 1 := by
  simp only [flatten]
  rw [← Array.foldl_toList]
  have h1 := foldl_flattenSeg_size cfg clip p.toList {}
  have h2 := pushLine_size (p.toList.foldl (flattenSeg cfg clip) {}).edges
    (p.toList.foldl (flattenSeg cfg clip) {}).cur (p.toList.foldl (flattenSeg cfg clip) {}).start
  simp only [Array.length_toList] at h1
  have : ({} : FState).edges.size = 0 := rfl
  rw [this] at h1
  omega

/-! ## 5. Scanline coverage -/

/-- A coverage mask: `w × h` bytes (row-major, `0 … 255`) for the device pixels
`[x0, x0 + w) × [y0, y0 + h)`. Pixels outside the rectangle have coverage 0. -/
structure Mask where
  /-- Left pixel column. -/
  x0 : Int := 0
  /-- Top pixel row. -/
  y0 : Int := 0
  /-- Width in pixels. -/
  w : Nat := 0
  /-- Height in pixels. -/
  h : Nat := 0
  /-- Coverage bytes, row-major (`fillEdges_size`: exactly `w · h` of them). -/
  data : ByteArray := ByteArray.empty
  deriving Inhabited

/-- Coverage of device pixel `(x, y)` (0 outside the mask). -/
def Mask.get (m : Mask) (x y : Int) : UInt8 :=
  if m.x0 ≤ x ∧ x < m.x0 + m.w ∧ m.y0 ≤ y ∧ y < m.y0 + m.h then
    (m.data[((y - m.y0) * m.w + (x - m.x0)).toNat]?).getD 0
  else 0

/-- Sum of all coverage bytes (`255` per fully covered pixel). -/
def Mask.total (m : Mask) : Nat := m.data.foldl (fun s b => s + b.toNat) 0

/-- Is winding number `wn` inside under `rule`? -/
def inside (rule : FillRule) (wn : Int) : Bool :=
  match rule with
  | .nonzero => wn != 0
  | .evenOdd => wn % 2 != 0

/-- Effective sample rows per pixel, `1 … 16`. -/
def Config.samples (cfg : Config) : Nat := min 16 (max 1 cfg.vSamples)

/-- Add the span `[xa, xb)` (subpixel units, relative to the mask's left edge, clamped to
`[0, 256·w]`) to the difference accumulator `acc` (size `w + 2`): after a prefix sum, pixel
`i` receives the length of `[xa, xb) ∩ [256·i, 256·(i+1))`. -/
def addSpan (acc : Array Int) (w : Nat) (xa xb : Int) : Array Int :=
  let lim : Int := (w : Int) * subUnit
  let a := max 0 (min lim xa)
  let b := max 0 (min lim xb)
  if a < b then
    let ia := (a / subUnit).toNat
    let fa := a % subUnit
    let ib := (b / subUnit).toNat
    let fb := b % subUnit
    if ia = ib then
      (acc.modify ia (· + (b - a))).modify (ia + 1) (· - (b - a))
    else
      (((acc.modify ia (· + (subUnit - fa))).modify (ia + 1) (· + fa)).modify ib
        (· + (fb - subUnit))).modify (ib + 1) (· - fb)
  else acc

/-- `x` of the edge at height `ys` (`y0 ≤ ys < y1`), rounded down. -/
def Edge.xAt (e : Edge) (ys : Int) : Int := e.x0 + (ys - e.y0) * (e.x1 - e.x0) / (e.y1 - e.y0)

/-- Crossings `(x, winding)` of the active edges with the sample row `ys`, sorted by `x`. -/
def crossings (act : Array Edge) (ys : Int) : Array (Int × Int) :=
  let cs := act.foldl (fun (cs : Array (Int × Int)) e =>
    if e.y0 ≤ ys ∧ ys < e.y1 then cs.push (e.xAt ys, e.wind) else cs) #[]
  cs.mergeSort (fun a b => a.1 ≤ b.1)

/-- Sweep sorted crossings left to right, adding the inside spans to `acc`. `bx` is the
mask's left edge in subpixel units. -/
def sweep (rule : FillRule) (w : Nat) (bx : Int) (cs : Array (Int × Int)) (acc : Array Int) :
    Array Int :=
  let r := cs.foldl (fun (st : Int × Int × Array Int) c =>
    let (wn, px, acc) := st
    let acc := if inside rule wn then addSpan acc w (px - bx) (c.1 - bx) else acc
    (wn + c.2, c.1, acc)) (0, 0, acc)
  r.2.2

/-- Accumulate the `fuel` sample rows `j, j+1, …` of the pixel row starting at `top`. -/
def sampleLoop (rule : FillRule) (S w : Nat) (bx top : Int) (act : Array Edge) :
    (fuel j : Nat) → Array Int → Array Int
  | 0, _, acc => acc
  | fuel + 1, j, acc =>
    let ys := top + ((2 * (j : Int) + 1) * (subUnit / 2)) / (S : Int)
    sampleLoop rule S w bx top act fuel (j + 1) (sweep rule w bx (crossings act ys) acc)

/-- Accumulated coverage (`0 … 256·S`) as a byte: `round(255 · c / (256·S))`, clamped. -/
def covByte (S : Nat) (c : Int) : UInt8 :=
  let full : Nat := 256 * S
  (min 255 ((c.toNat * 255 + full / 2) / full)).toUInt8

/-- A full pixel (accumulated `256·S`, `S ≥ 1`) has coverage exactly 255. -/
theorem covByte_full (S : Nat) (hS : 1 ≤ S) : covByte S ((256 * S : Nat) : Int) = 255 := by
  simp only [covByte, Int.toNat_natCast]
  have : ((256 * S) * 255 + 256 * S / 2) / (256 * S) = 255 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [this]; rfl

/-- An empty pixel (accumulated `0`, `S ≥ 1`) has coverage 0. -/
theorem covByte_zero (S : Nat) (hS : 1 ≤ S) : covByte S 0 = 0 := by
  simp only [covByte]
  have : (Int.toNat 0 * 255 + 256 * S / 2) / (256 * S) = 0 := Nat.div_eq_of_lt (by simp; omega)
  rw [this]; rfl

/-- Prefix-sum the accumulator into `fuel` coverage bytes appended to `out`. -/
def pushRow (acc : Array Int) (S : Nat) : (fuel i : Nat) → Int → ByteArray → ByteArray
  | 0, _, _, out => out
  | fuel + 1, i, cum, out =>
    let c := cum + acc.getD i 0
    pushRow acc S fuel (i + 1) c (out.push (covByte S c))

private theorem pushRow_size (acc : Array Int) (S : Nat) : ∀ fuel i cum out,
    (pushRow acc S fuel i cum out).size = out.size + fuel
  | 0, _, _, _ => by simp [pushRow]
  | fuel + 1, i, cum, out => by
    simp only [pushRow]
    rw [pushRow_size acc S fuel, ByteArray.size_push]; omega

/-- Move the edges starting above `bot` (sorted by `y0`) from `es[idx …]` to `act`. -/
def activate (es : Array Edge) (bot : Int) : (fuel idx : Nat) → Array Edge → Nat × Array Edge
  | 0, idx, act => (idx, act)
  | fuel + 1, idx, act =>
    match es[idx]? with
    | some e => if e.y0 < bot then activate es bot fuel (idx + 1) (act.push e) else (idx, act)
    | none => (idx, act)

private theorem activate_inv (es : Array Edge) (bot : Int) : ∀ fuel idx act,
    act.size ≤ idx → idx ≤ es.size →
      (activate es bot fuel idx act).2.size ≤ (activate es bot fuel idx act).1 ∧
        (activate es bot fuel idx act).1 ≤ es.size
  | 0, idx, act, h1, h2 => by simp [activate]; omega
  | fuel + 1, idx, act, h1, h2 => by
    simp only [activate]
    split
    · rename_i e he
      have hlt : idx < es.size := by
        rcases Nat.lt_or_ge idx es.size with h | h
        · exact h
        · rw [Array.getElem?_eq_none h] at he; cases he
      split
      · exact activate_inv es bot fuel (idx + 1) (act.push e) (by simp; omega) (by omega)
      · exact ⟨h1, h2⟩
    · exact ⟨h1, h2⟩

/-- Rasterizer state across pixel rows. -/
structure RState where
  /-- Next edge (in `y0` order) not yet activated. -/
  idx : Nat := 0
  /-- Active edges. -/
  active : Array Edge := #[]
  /-- Coverage bytes so far. -/
  out : ByteArray := ByteArray.empty
  /-- Counted work (S3 cost model: `S · |active| + w + 1` per row). -/
  steps : Nat := 0
  deriving Inhabited

/-- Rasterize one pixel row `r` (absolute device row). -/
def rowStep (rule : FillRule) (es : Array Edge) (S w : Nat) (bx : Int) (r : Int) (st : RState) :
    RState :=
  let top := r * subUnit
  let ev := activate es (top + subUnit) es.size st.idx st.active
  let act := ev.2.filter (fun e => top < e.y1)
  let acc := sampleLoop rule S w bx top act S 0 (Array.replicate (w + 2) 0)
  { idx := ev.1, active := act, out := pushRow acc S w 0 0 st.out,
    steps := st.steps + (S * act.size + w + 1) }

/-- Rasterize `fuel` pixel rows starting at row `r`. -/
def rowLoop (rule : FillRule) (es : Array Edge) (S w : Nat) (bx : Int) :
    (fuel : Nat) → Int → RState → RState
  | 0, _, st => st
  | fuel + 1, r, st => rowLoop rule es S w bx fuel (r + 1) (rowStep rule es S w bx r st)

private theorem rowStep_inv (rule : FillRule) (es : Array Edge) (S w : Nat) (bx r : Int)
    (st : RState) (h1 : st.active.size ≤ st.idx) (h2 : st.idx ≤ es.size) :
    (rowStep rule es S w bx r st).active.size ≤ (rowStep rule es S w bx r st).idx ∧
      (rowStep rule es S w bx r st).idx ≤ es.size ∧
      (rowStep rule es S w bx r st).out.size = st.out.size + w ∧
      (rowStep rule es S w bx r st).steps ≤ st.steps + (S * es.size + w + 1) := by
  have ha := activate_inv es (r * subUnit + subUnit) es.size st.idx st.active h1 h2
  simp only [rowStep]
  generalize activate es (r * subUnit + subUnit) es.size st.idx st.active = ev at ha
  have hf := Array.size_filter_le (p := fun e => decide (r * subUnit < e.y1)) (xs := ev.2)
  refine ⟨by omega, ha.2, pushRow_size _ _ _ _ _ _, ?_⟩
  have : S * (ev.2.filter (fun e => decide (r * subUnit < e.y1))).size ≤ S * es.size :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Row-loop invariant and S3 work bound.** Starting from a state whose active list is no
longer than the number of edges consumed, after `fuel` rows: the active list stays within the
`E = es.size` edges, the output grew by exactly `fuel · w` bytes, and the counted work grew
by at most `fuel · (S · E + w + 1)`. -/
theorem rowLoop_inv (rule : FillRule) (es : Array Edge) (S w : Nat) (bx : Int) :
    ∀ (fuel : Nat) (r : Int) (st : RState), st.active.size ≤ st.idx → st.idx ≤ es.size →
      (rowLoop rule es S w bx fuel r st).active.size ≤ es.size ∧
      (rowLoop rule es S w bx fuel r st).out.size = st.out.size + fuel * w ∧
      (rowLoop rule es S w bx fuel r st).steps ≤ st.steps + fuel * (S * es.size + w + 1)
  | 0, _, st, h1, h2 => by simp [rowLoop]; omega
  | fuel + 1, r, st, h1, h2 => by
    simp only [rowLoop]
    have hs := rowStep_inv rule es S w bx r st h1 h2
    have ih := rowLoop_inv rule es S w bx fuel (r + 1) (rowStep rule es S w bx r st) hs.1 hs.2.1
    refine ⟨ih.1, ?_, ?_⟩
    · rw [ih.2.1, hs.2.2.1, Nat.succ_mul]; omega
    · have := ih.2.2; rw [Nat.succ_mul]; omega

/-- `⌊a / 256⌋`. -/
def floorSub (a : Int) : Int := a / subUnit

/-- `⌈a / 256⌉`. -/
def ceilSub (a : Int) : Int := (a + subUnit - 1) / subUnit

/-- Bounding box of the edges in subpixel units `(minx, miny, maxx, maxy)`. The start value
uses the default `Limits.coordLimit` only as a sentinel: for edges beyond it the box is a
superset, which `maskRect` then cuts to the window. -/
def edgeBBox (es : Array Edge) : Int × Int × Int × Int :=
  go es.size 0 (Limits.default.coordLimit : Int) (Limits.default.coordLimit : Int)
    (-(Limits.default.coordLimit : Int)) (-(Limits.default.coordLimit : Int))
where
  /-- The box of `es[i …]` widened from `(a, b, c, d)` (four accumulators: no tuple per edge,
  task 7.2j). -/
  go : (fuel i : Nat) → (a b c d : Int) → Int × Int × Int × Int
    | 0, _, a, b, c, d => (a, b, c, d)
    | fuel + 1, i, a, b, c, d =>
      if h : i < es.size then
        let e := es[i]
        go fuel (i + 1) (min a (min e.x0 e.x1)) (min b e.y0) (max c (max e.x0 e.x1)) (max d e.y1)
      else (a, b, c, d)

/-- The mask rectangle: bounding box of the edges (in whole pixels) ∩ `clip`, as
`(x0, y0, w, h)`. -/
def maskRect (es : Array Edge) (clip : IRect) : Int × Int × Nat × Nat :=
  let (minx, miny, maxx, maxy) := edgeBBox es
  let px0 := max clip.x0 (floorSub minx)
  let py0 := max clip.y0 (floorSub miny)
  let px1 := min clip.x1 (ceilSub maxx)
  let py1 := min clip.y1 (ceilSub maxy)
  (px0, py0, (px1 - px0).toNat, (py1 - py0).toNat)

/-- **Reference rasterizer** (the 7.2a scanline filler, kept as the specification of the fast
one, task 7.2f) with its counted work: fill the polygon `edges` with `rule` into a coverage
mask over (bounding box ∩ `clip`). `fillEdgesCounted` produces byte-identical masks (suite
`raster-fill-spec`). -/
def fillEdgesCountedSpec (edges : Array Edge) (rule : FillRule) (clip : IRect)
    (cfg : Config := {}) : Mask × Nat :=
  let es := edges.mergeSort (fun a b => a.y0 ≤ b.y0)
  let S := cfg.samples
  let rc := maskRect es clip
  let st := rowLoop rule es S rc.2.2.1 (rc.1 * subUnit) rc.2.2.2 rc.2.1 {}
  ({ x0 := rc.1, y0 := rc.2.1, w := rc.2.2.1, h := rc.2.2.2, data := st.out }, st.steps)

/-- **Reference rasterizer** (specification of `fillEdges`): the mask of
`fillEdgesCountedSpec`. -/
def fillEdgesSpec (edges : Array Edge) (rule : FillRule) (clip : IRect) (cfg : Config := {}) :
    Mask :=
  (fillEdgesCountedSpec edges rule clip cfg).1

/-- The mask is never wider or taller than the clip window. -/
theorem maskRect_le (es : Array Edge) (clip : IRect) :
    ((maskRect es clip).2.2.1 : Int) ≤ max 0 (clip.x1 - clip.x0) ∧
      ((maskRect es clip).2.2.2 : Int) ≤ max 0 (clip.y1 - clip.y0) := by
  simp only [maskRect]
  constructor <;> omega

/-- **Buffer shape** of the reference rasterizer: exactly `w · h` bytes. -/
theorem fillEdgesSpec_size (edges : Array Edge) (rule : FillRule) (clip : IRect) (cfg : Config) :
    (fillEdgesSpec edges rule clip cfg).data.size =
      (fillEdgesSpec edges rule clip cfg).w * (fillEdgesSpec edges rule clip cfg).h := by
  simp only [fillEdgesSpec, fillEdgesCountedSpec]
  have := (rowLoop_inv rule (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) cfg.samples
    (maskRect (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) clip).2.2.1
    ((maskRect (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) clip).1 * subUnit)
    (maskRect (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) clip).2.2.2
    (maskRect (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) clip).2.1 {}
    (by simp) (by simp)).2.1
  rw [this, Nat.mul_comm]; exact Nat.zero_add _

/-- **S3 work bound for the reference rasterizer**: at most `h · (S · E + w + 1)`. -/
theorem fillEdgesCountedSpec_steps_le (edges : Array Edge) (rule : FillRule) (clip : IRect)
    (cfg : Config) :
    (fillEdgesCountedSpec edges rule clip cfg).2 ≤
      (fillEdgesCountedSpec edges rule clip cfg).1.h *
        (cfg.samples * edges.size + (fillEdgesCountedSpec edges rule clip cfg).1.w + 1) := by
  simp only [fillEdgesCountedSpec]
  have := (rowLoop_inv rule (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) cfg.samples
    (maskRect (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) clip).2.2.1
    ((maskRect (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) clip).1 * subUnit)
    (maskRect (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) clip).2.2.2
    (maskRect (edges.mergeSort (fun a b => a.y0 ≤ b.y0)) clip).2.1 {}
    (by simp) (by simp)).2.2
  rw [Array.size_mergeSort] at this
  simpa using this

/-! ## 6. The fast rasterizer (tasks 7.2f, 7.2j)

Same sampling, same crossings, same spans as the reference (`rowLoop`), organised for speed.
Two fast paths share the guard `fastOK`; `fillRows` picks one.

**Bucketed crossings** (7.2j; masks of at most `2²⁰` sample rows and `2²⁰` pixels across, at
most `2²⁰` crossings and at most 64 per sample row — every glyph, most small fills): see
"Bucketed crossings" below. No active-edge list, no comparison sort of the edges.

**Active edges** (7.2f, everything else under `fastOK`):

* the edges are ordered by first pixel row with a counting sort (`ySort`, 7.2j; the reference
  sorts by `y0` with `Array.mergeSort`, but only the row of `y0` matters for activation);
* the active edges live in one array (`AEdge`, all fields `Int64`, so no big-integer
  arithmetic: under the fast-path guard `fastOK` every product stays below `2⁶³`) whose order
  is carried from sample row to sample row and repaired by an **insertion sort** (`sortAct`,
  one tail-recursive loop, linear on the nearly sorted input; a swap budget of `8·n + 64` per
  sample row falls back to `Array.mergeSort`, so the worst case stays `O(n log n)`); finished
  edges are dropped in place (`keepLive`);
* an edge that does not cross the current sample row stays in the array (flag `on` false,
  stale `cx`) and the sweep skips it, so the sweep sees exactly the reference's sorted
  crossings (ties in `x` are harmless: they only produce empty spans);
* one `UInt32` difference accumulator of `w + 2` cells is reused for every row (the prefix
  sum zeroes it as it reads; per-pixel sums are `≤ 256·S`, so wrapping arithmetic is exact).

Inputs outside the guard (coordinates beyond `±2³⁰` subpixel units, windings other than
`−1, 0, 1`, absurd mask rectangles) take the reference path. Equality with the reference is
tested on random paths, raw edge sets and glyph-like runs of tiny contours, with both fast
paths exercised (suite `raster-fill-spec`); the buffer shape and the S3 work bound are proved
for the combined rasterizer (`fillRows_spec`, `fillEdges_size`, `fillEdgesCounted_steps_le`). -/


/-- An active edge of the fast rasterizer: the edge in 64-bit subpixel units plus its
crossing with the current sample row (`cx`, meaningful when `on`). -/
structure AEdge where
  /-- Upper endpoint x. -/
  x0 : Int64
  /-- Upper endpoint y. -/
  y0 : Int64
  /-- Lower endpoint y. -/
  y1 : Int64
  /-- `x1 − x0`. -/
  dx : Int64
  /-- `y1 − y0` (`> 0`). -/
  dy : Int64
  /-- Winding contribution. -/
  wind : Int64
  /-- Crossing x at the current sample row (stale when not `on`). -/
  cx : Int64
  /-- Does the edge cross the current sample row? -/
  on : Bool
  deriving Inhabited

/-- An edge in fast form (64-bit wrap-around conversion; `fastOK` guarantees it is exact). -/
def AEdge.ofEdge (e : Edge) : AEdge :=
  ⟨e.x0.toInt64, e.y0.toInt64, e.y1.toInt64, (e.x1 - e.x0).toInt64, (e.y1 - e.y0).toInt64,
    e.wind.toInt64, e.x0.toInt64, false⟩

/-- The edge's crossing with sample row `ys` (`Edge.xAt` in 64 bits), if it crosses it (a
non-crossing edge keeps its stale `cx`, so the sort order stays nearly right). -/
@[inline] def AEdge.atRow (ys : Int64) (e : AEdge) : AEdge :=
  let on := e.y0 ≤ ys && ys < e.y1
  let cx := if on then (if e.dx == 0 then e.x0 else e.x0 + fdiv64 ((ys - e.y0) * e.dx) e.dy)
    else e.cx
  -- one constructor site, so the compiled code updates the edge in place (task 7.2j)
  { e with cx := cx, on := on }

/-- Update the crossings of `a[i …]` for the sample row `ys`. -/
def crossAll (ys : Int64) : (fuel i : Nat) → Array AEdge → Array AEdge
  | 0, _, a => a
  | fuel + 1, i, a => crossAll ys fuel (i + 1) (a.modify i (AEdge.atRow ys))

private theorem crossAll_size (ys : Int64) : ∀ fuel i (a : Array AEdge),
    (crossAll ys fuel i a).size = a.size
  | 0, _, _ => rfl
  | fuel + 1, i, a => by simp only [crossAll]; rw [crossAll_size]; simp

/-- Insertion sort of the active edges by crossing (task 7.2j: one tail-recursive loop, no
intermediate pairs). Element `i` is being inserted and sits at position `j`; it is swapped
left while its left neighbour has a larger crossing, spending one unit of the swap budget
`bud` per swap; when the budget runs out the array is finished with `Array.mergeSort`. With
`fuel ≥ size + bud + 1` the loop always ends by itself (each step inserts an element or
spends a swap). -/
def insSort : (fuel : Nat) → (a : Array AEdge) → (i j bud : Nat) → Array AEdge
  | 0, a, _, _, _ => a
  | fuel + 1, a, i, j, bud =>
    if hj : j < a.size then
      match j, hj with
      | 0, _ => insSort fuel a (i + 1) (i + 1) bud
      | j' + 1, hj =>
        if a[j' + 1].cx < a[j'].cx then
          match bud with
          | 0 => a.mergeSort (fun x y => x.cx ≤ y.cx)
          | bud' + 1 => insSort fuel (a.swapIfInBounds j' (j' + 1)) i j' bud'
        else insSort fuel a (i + 1) (i + 1) bud
    else a

private theorem insSort_size : ∀ fuel (a : Array AEdge) i j bud,
    (insSort fuel a i j bud).size = a.size
  | 0, _, _, _, _ => rfl
  | fuel + 1, a, i, j, bud => by
    simp only [insSort]
    split
    · split
      · exact insSort_size fuel a _ _ _
      · split
        · split
          · exact Array.size_mergeSort
          · rw [insSort_size]; simp
        · exact insSort_size fuel a _ _ _
    · rfl

/-- Are the crossings of `a[i …]` (with `prev` before them) in non-decreasing order? -/
def sortedFrom (a : Array AEdge) : (fuel i : Nat) → Int64 → Bool
  | 0, _, _ => true
  | fuel + 1, i, prev =>
    if h : i < a.size then prev ≤ a[i].cx && sortedFrom a fuel (i + 1) a[i].cx else true

/-- Sort the active edges by crossing: insertion sort (the order of the previous sample row
is nearly right) with a swap budget of `8·n + 64`, falling back to `Array.mergeSort` when it
runs out, so the worst case stays `O(n log n)`. -/
def sortAct (a : Array AEdge) : Array AEdge :=
  insSort (9 * a.size + 66) a 0 0 (8 * a.size + 64)

/-- Sorting keeps every active edge: `sortAct` preserves the array size. -/
theorem sortAct_size (a : Array AEdge) : (sortAct a).size = a.size := insSort_size _ _ _ _ _

/-- `addSpan` on the `UInt32` accumulator: add `[xa, xb)` (relative subpixel units, clamped
to `[0, lim]`, `lim = 256·w`). -/
@[inline] def addSpanF (acc : Array UInt32) (lim xa xb : Int64) : Array UInt32 :=
  let a := max 0 (min lim xa)
  let b := max 0 (min lim xb)
  if a < b then
    let ia := (a / 256).toUInt64.toNat
    let fa := (a % 256).toUInt64.toUInt32
    let ib := (b / 256).toUInt64.toNat
    let fb := (b % 256).toUInt64.toUInt32
    if ia = ib then
      let d := (b - a).toUInt64.toUInt32
      (acc.modify ia (· + d)).modify (ia + 1) (· - d)
    else
      (((acc.modify ia (· + (256 - fa))).modify (ia + 1) (· + fa)).modify ib
        (· + (fb - 256))).modify (ib + 1) (· - fb)
  else acc

/-- Sweep the sorted active edges left to right (winding `wn`, previous crossing `px`),
adding inside spans to `acc` (`eo`: even-odd rule, else nonzero). -/
def sweepF (eo : Bool) (lim bx : Int64) (act : Array AEdge) :
    (fuel i : Nat) → (wn px : Int64) → Array UInt32 → Array UInt32
  | 0, _, _, _, acc => acc
  | fuel + 1, i, wn, px, acc =>
    if h : i < act.size then
      let e := act[i]
      if !e.on then sweepF eo lim bx act fuel (i + 1) wn px acc
      else
        let ins := if eo then wn % 2 != 0 else wn != 0
        let acc := if ins then addSpanF acc lim (px - bx) (e.cx - bx) else acc
        sweepF eo lim bx act fuel (i + 1) (wn + e.wind) e.cx acc
    else acc

/-- Accumulate the `fuel` sample rows `j, j+1, …` of the pixel row starting at `top`. -/
def sampleLoopF (eo : Bool) (S : Nat) (lim bx top : Int64) :
    (fuel j : Nat) → Array AEdge → Array UInt32 → Array AEdge × Array UInt32
  | 0, _, act, acc => (act, acc)
  | fuel + 1, j, act, acc =>
    let ys := top + ((2 * j.toInt64 + 1) * 128) / S.toInt64
    let act := sortAct (crossAll ys act.size 0 act)
    sampleLoopF eo S lim bx top fuel (j + 1) act (sweepF eo lim bx act act.size 0 0 0 acc)

private theorem sampleLoopF_size (eo : Bool) (S : Nat) (lim bx top : Int64) : ∀ fuel j act acc,
    (sampleLoopF eo S lim bx top fuel j act acc).1.size = act.size
  | 0, _, _, _ => rfl
  | fuel + 1, j, act, acc => by
    simp only [sampleLoopF]; rw [sampleLoopF_size, sortAct_size, crossAll_size]

/-- Coverage byte from the accumulated `c` (`full = 256·S`): `covByte` in 32 bits. -/
@[inline] def covByteF (full c : UInt32) : UInt8 :=
  (min 255 ((c * 255 + full / 2) / full)).toUInt8

/-- Prefix-sum `acc[i …]` into `fuel` coverage bytes appended to `out`, zeroing the cells it
reads (and the two guard cells after the row), so the accumulator is ready for the next row. -/
def pushRowF (full : UInt32) : (fuel i : Nat) → UInt32 → Array UInt32 → ByteArray →
    Array UInt32 × ByteArray
  | 0, i, _, acc, out => ((acc.setIfInBounds i 0).setIfInBounds (i + 1) 0, out)
  | fuel + 1, i, cum, acc, out =>
    let c := cum + acc.getD i 0
    pushRowF full fuel (i + 1) c (acc.setIfInBounds i 0) (out.push (covByteF full c))

private theorem pushRowF_size (full : UInt32) : ∀ fuel i cum acc out,
    (pushRowF full fuel i cum acc out).2.size = out.size + fuel
  | 0, _, _, _, _ => rfl
  | fuel + 1, i, cum, acc, out => by
    simp only [pushRowF]; rw [pushRowF_size, ByteArray.size_push]; omega

/-- Move the edges starting above `bot` (sorted by `y0`) from `es[idx …]` to `act`. -/
def activateF (es : Array AEdge) (bot : Int64) :
    (fuel idx : Nat) → Array AEdge → Nat × Array AEdge
  | 0, idx, act => (idx, act)
  | fuel + 1, idx, act =>
    if h : idx < es.size then
      if es[idx].y0 < bot then activateF es bot fuel (idx + 1) (act.push es[idx])
      else (idx, act)
    else (idx, act)

private theorem activateF_inv (es : Array AEdge) (bot : Int64) : ∀ fuel idx act,
    act.size ≤ idx → idx ≤ es.size →
      (activateF es bot fuel idx act).2.size ≤ (activateF es bot fuel idx act).1 ∧
        (activateF es bot fuel idx act).1 ≤ es.size
  | 0, idx, act, h1, h2 => by simp [activateF]; omega
  | fuel + 1, idx, act, h1, h2 => by
    simp only [activateF]
    split
    · split
      · exact activateF_inv es bot fuel (idx + 1) _ (by simp; omega) (by omega)
      · exact ⟨h1, h2⟩
    · exact ⟨h1, h2⟩

/-- Fast rasterizer state across pixel rows. -/
structure FRow where
  /-- Next edge (in `y0` order) not yet activated. -/
  idx : Nat := 0
  /-- Active edges, in the crossing order of the last sample row. -/
  act : Array AEdge := #[]
  /-- The reused difference accumulator (`w + 2` cells, all zero between rows). -/
  acc : Array UInt32 := #[]
  /-- Coverage bytes so far. -/
  out : ByteArray := ByteArray.empty
  /-- Counted work (the reference's cost model: `S · |active| + w + 1` per row). -/
  steps : Nat := 0
  deriving Inhabited

/-- Pop `a` down to `k` elements (in place). -/
def popTo (k : Nat) : (fuel : Nat) → Array AEdge → Array AEdge
  | 0, a => a
  | fuel + 1, a => if k < a.size then popTo k fuel a.pop else a

private theorem popTo_size_le (k : Nat) : ∀ fuel (a : Array AEdge), (popTo k fuel a).size ≤ a.size
  | 0, _ => Nat.le_refl _
  | fuel + 1, a => by
    simp only [popTo]
    split
    · have := popTo_size_le k fuel a.pop; simp at this; omega
    · exact Nat.le_refl _

/-- Keep the active edges that reach below `top` (`top < y1`), in their order, in place:
`a[i …]` is scanned, the kept edges are swapped down to `a[k …]`, the rest popped (the
reference's `filter`, without a new array per row; task 7.2j). -/
def keepLive (top : Int64) : (fuel : Nat) → (a : Array AEdge) → (i k : Nat) → Array AEdge
  | 0, a, _, k => popTo k a.size a
  | fuel + 1, a, i, k =>
    if h : i < a.size then
      if top < a[i].y1 then keepLive top fuel (a.swapIfInBounds k i) (i + 1) (k + 1)
      else keepLive top fuel a (i + 1) k
    else popTo k a.size a

private theorem keepLive_size_le (top : Int64) : ∀ fuel (a : Array AEdge) i k,
    (keepLive top fuel a i k).size ≤ a.size
  | 0, a, _, k => popTo_size_le k _ a
  | fuel + 1, a, i, k => by
    simp only [keepLive]
    split
    · split
      · have := keepLive_size_le top fuel (a.swapIfInBounds k i) (i + 1) (k + 1)
        simp at this; exact this
      · exact keepLive_size_le top fuel a (i + 1) k
    · exact popTo_size_le k _ a

/-- Rasterize one pixel row `r` (absolute device row) — `rowStep`, fast. -/
def rowStepF (eo : Bool) (es : Array AEdge) (S w : Nat) (lim bx : Int64) (r : Int64)
    (st : FRow) : FRow :=
  let top := r * 256
  let ev := activateF es (top + 256) es.size st.idx st.act
  let act := keepLive top ev.2.size ev.2 0 0
  let sa := sampleLoopF eo S lim bx top S 0 act st.acc
  let pr := pushRowF (256 * S).toUInt32 w 0 0 sa.2 st.out
  { idx := ev.1, act := sa.1, acc := pr.1, out := pr.2,
    steps := st.steps + (S * act.size + w + 1) }

/-- Rasterize `fuel` pixel rows starting at row `r` — `rowLoop`, fast. -/
def rowLoopF (eo : Bool) (es : Array AEdge) (S w : Nat) (lim bx : Int64) :
    (fuel : Nat) → Int64 → FRow → FRow
  | 0, _, st => st
  | fuel + 1, r, st => rowLoopF eo es S w lim bx fuel (r + 1) (rowStepF eo es S w lim bx r st)

/-- **Row-loop invariant and S3 work bound** of the fast rasterizer (as `rowLoop_inv`). -/
theorem rowLoopF_inv (eo : Bool) (es : Array AEdge) (S w : Nat) (lim bx : Int64) :
    ∀ (fuel : Nat) (r : Int64) (st : FRow), st.act.size ≤ st.idx → st.idx ≤ es.size →
      (rowLoopF eo es S w lim bx fuel r st).out.size = st.out.size + fuel * w ∧
      (rowLoopF eo es S w lim bx fuel r st).steps ≤ st.steps + fuel * (S * es.size + w + 1)
  | 0, _, st, h1, h2 => by simp [rowLoopF]
  | fuel + 1, r, st, h1, h2 => by
    simp only [rowLoopF]
    have ha := activateF_inv es (r * 256 + 256) es.size st.idx st.act h1 h2
    have hf := keepLive_size_le (r * 256)
      (activateF es (r * 256 + 256) es.size st.idx st.act).2.size
      (activateF es (r * 256 + 256) es.size st.idx st.act).2 0 0
    have ih := rowLoopF_inv eo es S w lim bx fuel (r + 1) (rowStepF eo es S w lim bx r st)
      (by simp only [rowStepF]; rw [sampleLoopF_size]; omega) (by simp only [rowStepF]; omega)
    have hm : S * (keepLive (r * 256)
        (activateF es (r * 256 + 256) es.size st.idx st.act).2.size
        (activateF es (r * 256 + 256) es.size st.idx st.act).2 0 0).size ≤ S * es.size :=
      Nat.mul_le_mul_left _ (by omega)
    have hs1 : (rowStepF eo es S w lim bx r st).out.size = st.out.size + w := by
      simp only [rowStepF]; rw [pushRowF_size]
    have hs2 : (rowStepF eo es S w lim bx r st).steps ≤ st.steps + (S * es.size + w + 1) := by
      simp only [rowStepF]; omega
    refine ⟨?_, ?_⟩
    · rw [ih.1, hs1, Nat.succ_mul]; omega
    · have := ih.2; rw [Nat.succ_mul]; omega


/-- Fast-path bound on coordinates: `|v| ≤ 2³⁰` subpixel units (`Limits.coordLimit`). -/
def fastCoord (v : Int) : Bool := -1073741824 ≤ v && v ≤ 1073741824

/-- **Fast-path guard**: every edge coordinate within `±2³⁰`, windings in `{−1, 0, 1}`, and a
mask rectangle `(x0, y0, w, h)` with `|x0|, |y0| ≤ 2³⁰`, `w ≤ 2²³`. Then all 64-bit
arithmetic of the fast rasterizer is exact: sample rows lie within `2³⁰ + 256` of 0, so
`(ys − y0)·dx` is below `(2³¹ + 512)·2³¹ < 2⁶³`. -/
def fastOK (es : Array Edge) (rc : Int × Int × Nat × Nat) : Bool :=
  es.all (fun e => fastCoord e.x0 && fastCoord e.y0 && fastCoord e.x1 && fastCoord e.y1 &&
    (-1 ≤ e.wind && e.wind ≤ 1)) &&
  fastCoord rc.1 && fastCoord rc.2.1 && rc.2.2.1 ≤ 8388608

/-- Bucket of an edge for the fast path's activation order (task 7.2j): its first pixel row
`⌊y0 / 256⌋` relative to the mask's top row `ym`, clamped to `[0, h]` (`h`: never activated
inside the mask). -/
@[inline] def rowKey (ym : Int64) (h : Nat) (e : Edge) : Nat :=
  let k := fdiv64 e.y0.toInt64 256 - ym
  if k < 0 then 0 else min h k.toInt.toNat

/-- Count the edges `es[i …]` per bucket (`c[k + 1]` counts bucket `k`). -/
def countKeys (ym : Int64) (h : Nat) (es : Array Edge) :
    (fuel i : Nat) → Array Nat → Array Nat
  | 0, _, c => c
  | fuel + 1, i, c =>
    if hi : i < es.size then countKeys ym h es fuel (i + 1) (c.modify (rowKey ym h es[i] + 1) (· + 1))
    else c

/-- Running sums `c[i] += c[i − 1]` for `i = i₀ …`: bucket starts. -/
def runSums : (fuel i : Nat) → Nat → Array Nat → Array Nat
  | 0, _, _, c => c
  | fuel + 1, i, prev, c =>
    let v := prev + c.getD i 0
    runSums fuel (i + 1) v (c.setIfInBounds i v)

/-- Place the edges `es[i …]` (in fast form) at their bucket's next free slot. -/
def placeKeys (ym : Int64) (h : Nat) (es : Array Edge) :
    (fuel i : Nat) → Array Nat → Array AEdge → Array AEdge
  | 0, _, _, out => out
  | fuel + 1, i, st, out =>
    if hi : i < es.size then
      let k := rowKey ym h es[i]
      placeKeys ym h es fuel (i + 1) (st.modify k (· + 1))
        (out.setIfInBounds (st.getD k 0) (AEdge.ofEdge es[i]))
    else out

private theorem placeKeys_size (ym : Int64) (h : Nat) (es : Array Edge) :
    ∀ fuel i st (out : Array AEdge), (placeKeys ym h es fuel i st out).size = out.size
  | 0, _, _, _ => rfl
  | fuel + 1, i, st, out => by
    simp only [placeKeys]
    split
    · rw [placeKeys_size]; simp
    · rfl

/-- The edges in fast form, ordered by first pixel row (a counting sort over the `h + 1`
buckets of `rowKey`, `O(E + h)`, no comparisons; task 7.2j). Any order with non-decreasing
`⌊y0 / 256⌋` activates the same edges on every row as the reference's `y0`-sorted list. -/
def ySort (ym : Int64) (h : Nat) (es : Array Edge) : Array AEdge :=
  let c := countKeys ym h es es.size 0 (Array.replicate (h + 2) 0)
  let st := runSums (h + 2) 0 0 c
  placeKeys ym h es es.size 0 st (Array.replicate es.size default)

/-- `ySort` keeps every edge. -/
theorem ySort_size (ym : Int64) (h : Nat) (es : Array Edge) : (ySort ym h es).size = es.size := by
  simp only [ySort]; rw [placeKeys_size]; simp

/-! ### Bucketed crossings (task 7.2j)

For masks of modest size (glyphs above all: one small fill per glyph after
`Glyph.columnGroups`) the fast path skips the active-edge list altogether. Every edge's
crossings with the mask's sample rows are computed once, in one pass, and written into one
`UInt32` array bucketed by sample row (a counting sort: count per sample row, running sums,
scatter). A crossing is packed as `4·x + (wind + 1)` with `x` the crossing relative to the
mask's left edge **clamped to `[0, 256·w]`**: `addSpanF` clamps both ends of every span to
that range anyway, and clamping is monotone, so sorting the clamped values gives a valid
sorted order of the crossings as far as the spans are concerned (ties only make empty spans).
Each bucket is then insertion-sorted and swept exactly as in `sweepF`. The counted work is
computed per edge (the rows on which the reference has it active: `⌊y0/256⌋ ≤ r < ⌈y1/256⌉`
inside the mask), so it equals the reference's sum of `S·|active| + w + 1` per row.

Taken when the mask has at most `2²⁰` sample rows and is at most `2²⁰` pixels wide, there
are at most `2²⁰` crossings and no sample row has more than 64 of them (so each bucket's
insertion sort is bounded); otherwise the active-edge rasterizer above runs. -/

/-- `#{j' ∈ [j, S) : ((2j' + 1)·128) / S < rel}` (sample rows of a pixel row above offset
`rel`; offsets increase with `j'`). -/
def offCount (S rel : Int64) : (fuel : Nat) → Int64 → Nat → Nat
  | 0, _, n => n
  | fuel + 1, j, n =>
    if j < S && ((2 * j + 1) * 128) / S < rel then offCount S rel fuel (j + 1) (n + 1) else n

/-- `offCount S rel S 0 0` in closed form for `rel ∈ [0, 256)`, `S ∈ [1, 16]`:
`⌊(2j+1)·128 / S⌋ < rel` iff `256·j + 128 < rel·S`, so the count is
`min S ⌈(rel·S − 128) / 256⌉ = min S ⌊(rel·S + 127) / 256⌋` (checked exhaustively below). -/
@[inline] def offBelow (Si rel : Int64) : Int64 :=
  min Si ((rel * Si + 127) >>> 8)

#guard (List.range 16).all fun s => (List.range 256).all fun rel =>
  (offBelow (s + 1).toInt64 rel.toInt64).toInt ==
    (offCount (s + 1).toInt64 rel.toInt64 (s + 1) 0 0 : Int)

/-- The number of the mask's sample rows (pixel rows `ym …`, `hI` of them, `Si` sample rows
each) whose sample height `ys` is below `y` (`ys < y`). -/
@[inline] def belowS (Si hI ym y : Int64) : Int64 :=
  let t := y >>> 8
  let r := t - ym
  if r < 0 then 0
  else if hI ≤ r then hI * Si
  else r * Si + offBelow Si (y - t * 256)

/-- First pass of the bucketed path: the difference counts of the buckets (an edge's
sample-row range `[a, b)` adds `cur[a] += 1`, `cur[b] −= 1`, wrapping `UInt32`), the number of
crossings `n`, and the counted active rows `act`. -/
structure ScanB where
  /-- Difference counts per sample row. -/
  cur : Array UInt32
  /-- Total number of crossings. -/
  n : Nat
  /-- Sum over the edges of the rows on which the reference has them active. -/
  act : Nat

/-- Scan the edges `es[i …]` (see `ScanB`; `Si = S`, `hI = h` as `Int64`, `ym` the mask's
top row). The active rows of an edge are `⌊y0/256⌋ ≤ r < ⌈y1/256⌉` within the mask. -/
def scanB (h : Nat) (Si hI ym : Int64) (es : Array Edge) :
    (fuel i : Nat) → (cur : Array UInt32) → (n act : Nat) → ScanB
  | 0, _, cur, n, act => ⟨cur, n, act⟩
  | fuel + 1, i, cur, n, act =>
    if hi : i < es.size then
      let e := es[i]
      let y0 := e.y0.toInt64
      let y1 := e.y1.toInt64
      let a := belowS Si hI ym y0
      let b := belowS Si hI ym y1
      let lo := max (y0 >>> 8) ym
      let up := min ((y1 + 255) >>> 8) (ym + hI)
      let rows := if lo < up then min h (up - lo).toUInt64.toNat else 0
      if a < b then
        scanB h Si hI ym es fuel (i + 1)
          ((cur.modify a.toUInt64.toNat (· + 1)).modify b.toUInt64.toNat (· - 1))
          (n + (b - a).toUInt64.toNat) (act + rows)
      else scanB h Si hI ym es fuel (i + 1) cur n (act + rows)
    else ⟨cur, n, act⟩

private theorem scanB_act (h : Nat) (Si hI ym : Int64) (es : Array Edge) :
    ∀ fuel i cur n act, (scanB h Si hI ym es fuel i cur n act).act ≤ act + fuel * h
  | 0, _, _, _, _ => by simp [scanB]
  | fuel + 1, i, cur, n, act => by
    simp only [scanB]
    split
    · skip
      split
      · refine Nat.le_trans (scanB_act h Si hI ym es fuel _ _ _ _) ?_
        rw [Nat.succ_mul]; split <;> omega
      · refine Nat.le_trans (scanB_act h Si hI ym es fuel _ _ _ _) ?_
        rw [Nat.succ_mul]; split <;> omega
    · simp only [Nat.succ_mul]; omega

/-- Running sums over the difference counts: `cur[s]` becomes the start of bucket `s`; also
returns the largest bucket. -/
def prefB : (fuel s : Nat) → (cov st mx : UInt32) → Array UInt32 → Array UInt32 × UInt32
  | 0, _, _, _, mx, c => (c, mx)
  | fuel + 1, s, cov, st, mx, c =>
    let cov := cov + c.getD s 0
    prefB fuel (s + 1) cov (st + cov) (max mx cov) (c.setIfInBounds s st)

/-- Scatter every crossing into its bucket: edge `i − 1`'s remaining sample rows `[s, b)`
(`j`: sample row within pixel row `r`, relative to `ym`), then the edges `es[i …]`. `cur[s]`
is bucket `s`'s next free slot (afterwards: the end of bucket `s`).

The crossing `x0 + ⌊(ys − y0)·dx / dy⌋` is computed exactly at an edge's first sample row;
when `S` divides 256 (`dd = 256 / S`, else `dd = 0`) the sample rows are `dd` apart and the
next crossings follow by exact stepping (`cx` with remainder `rem ∈ [0, dy)`, step
`⌊dd·dx / dy⌋ = sq` with remainder `sr`), otherwise each crossing is divided out. -/
def emitB (es : Array Edge) (S : Nat) (Si hI ym bx lim dd : Int64) :
    (fuel i s b j : Nat) → (r x0 y0 dx dy wc cx rem sq sr : Int64) → (cur xs : Array UInt32) →
      Array UInt32 × Array UInt32
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, cur, xs => (cur, xs)
  | fuel + 1, i, s, b, j, r, x0, y0, dx, dy, wc, cx, rem, sq, sr, cur, xs =>
    if s < b then
      let cx := if dd == 0 then
          (if dx == 0 then x0
           else x0 + fdiv64 (((ym + r) * 256 + ((2 * j.toInt64 + 1) * 128) / Si - y0) * dx) dy)
        else cx
      let xr := cx - bx
      let xc := if xr < 0 then 0 else if lim < xr then lim else xr
      let v : UInt32 := xc.toUInt64.toUInt32 * 4 + wc.toUInt64.toUInt32
      let p := cur.getD s 0
      let xs := xs.setIfInBounds p.toNat v
      let cur := cur.setIfInBounds s (p + 1)
      let rs := rem + sr
      let carry := dy ≤ rs
      let cx' := if carry then cx + sq + 1 else cx + sq
      let rem' := if carry then rs - dy else rs
      if j + 1 < S then
        emitB es S Si hI ym bx lim dd fuel i (s + 1) b (j + 1) r x0 y0 dx dy wc cx' rem' sq sr cur xs
      else emitB es S Si hI ym bx lim dd fuel i (s + 1) b 0 (r + 1) x0 y0 dx dy wc cx' rem' sq sr cur xs
    else if h : i < es.size then
      let e := es[i]
      let y0 := e.y0.toInt64
      let a := (belowS Si hI ym y0).toUInt64.toNat
      let j := a % S
      let r := (a / S).toInt64
      let x0 := e.x0.toInt64
      let dx := (e.x1 - e.x0).toInt64
      let dy := (e.y1 - e.y0).toInt64
      let num := ((ym + r) * 256 + ((2 * j.toInt64 + 1) * 128) / Si - y0) * dx
      let q := fdiv64 num dy
      let stp := dd * dx
      let sq := fdiv64 stp dy
      emitB es S Si hI ym bx lim dd fuel (i + 1) a (belowS Si hI ym e.y1.toInt64).toUInt64.toNat j r x0
        y0 dx dy
        (e.wind + 1).toInt64 (x0 + q) (num - q * dy) sq (stp - sq * dy) cur xs
    else (cur, xs)

/-- Insertion sort of `xs[lo, hi)`: element `i` is being inserted, now at `j`. -/
def insU : (fuel : Nat) → (xs : Array UInt32) → (lo i j hi : Nat) → Array UInt32
  | 0, xs, _, _, _, _ => xs
  | fuel + 1, xs, lo, i, j, hi =>
    if lo < j && xs.getD j 0 < xs.getD (j - 1) 0 then
      insU fuel (xs.swapIfInBounds (j - 1) j) lo i (j - 1) hi
    else if i + 1 < hi then insU fuel xs lo (i + 1) (i + 1) hi
    else xs

/-- Sort every bucket (`cur[s]`: end of bucket `s`; bucket `s` starts at `lo`). -/
def sortB (cur : Array UInt32) : (fuel s lo : Nat) → Array UInt32 → Array UInt32
  | 0, _, _, xs => xs
  | fuel + 1, s, lo, xs =>
    let hi := (cur.getD s 0).toNat
    sortB cur fuel (s + 1) hi (if lo + 1 < hi then insU ((hi - lo) * (hi - lo) + 2) xs lo lo lo hi
      else xs)

/-- Add `d` to `acc[i]` (wrapping; no-op out of bounds): one read, one in-place write. -/
@[inline] def bump (acc : Array UInt32) (i : Nat) (d : UInt32) : Array UInt32 :=
  acc.setIfInBounds i (acc.getD i 0 + d)

/-- `addSpanF` for clamped relative ends `a, b ∈ [0, 256·w]`. -/
@[inline] def addSpanU (acc : Array UInt32) (a b : UInt32) : Array UInt32 :=
  if a < b then
    let ia := (a >>> 8).toNat
    let fa := a &&& 255
    let ib := (b >>> 8).toNat
    let fb := b &&& 255
    if ia = ib then
      bump (bump acc ia (b - a)) (ia + 1) (a - b)
    else
      bump (bump (bump (bump acc ia (256 - fa)) (ia + 1) fa) ib (fb - 256)) (ib + 1) (0 - fb)
  else acc


/-- Sweep the sorted packed crossings `xs[i …]` (`fuel` of them) as `sweepF` does. -/
def sweepB (eo : Bool) (xs : Array UInt32) :
    (fuel i : Nat) → (wn : Int64) → (px : UInt32) → Array UInt32 → Array UInt32
  | 0, _, _, _, acc => acc
  | fuel + 1, i, wn, px, acc =>
    let v := xs.getD i 0
    let x := v >>> 2
    let ins := if eo then wn % 2 != 0 else wn != 0
    let acc := if ins then addSpanU acc px x else acc
    sweepB eo xs fuel (i + 1) (wn + ((v &&& 3).toUInt64.toInt64 - 1)) x acc

/-- Sweep the buckets of sample rows `s, s+1, …` (`fuel` of them) into `acc`. -/
def sampB (eo : Bool) (xs cur : Array UInt32) : (fuel s : Nat) → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | fuel + 1, s, acc =>
    let lo := if s = 0 then 0 else (cur.getD (s - 1) 0).toNat
    let hi := (cur.getD s 0).toNat
    sampB eo xs cur fuel (s + 1) (sweepB eo xs (hi - lo) lo 0 0 acc)

/-- The coverage rows `r, r+1, …` (`fuel` of them) of the bucketed path. -/
def rowsB (eo : Bool) (S w : Nat) (full : UInt32) (xs cur : Array UInt32) :
    (fuel r : Nat) → Array UInt32 → ByteArray → ByteArray
  | 0, _, _, out => out
  | fuel + 1, r, acc, out =>
    let pr := pushRowF full w 0 0 (sampB eo xs cur S (r * S) acc) out
    rowsB eo S w full xs cur fuel (r + 1) pr.1 pr.2

private theorem rowsB_size (eo : Bool) (S w : Nat) (full : UInt32) (xs cur : Array UInt32) :
    ∀ fuel r acc out, (rowsB eo S w full xs cur fuel r acc out).size = out.size + fuel * w
  | 0, _, _, _ => by simp [rowsB]
  | fuel + 1, r, acc, out => by
    simp only [rowsB]; rw [rowsB_size, pushRowF_size, Nat.succ_mul]; omega

/-- The active-edge fast rasterizer (7.2f, with the 7.2j changes): coverage rows and counted
work. -/
def fillActive (eo : Bool) (es : Array Edge) (S : Nat) (rc : Int × Int × Nat × Nat) :
    ByteArray × Nat :=
  let st := rowLoopF eo (ySort rc.2.1.toInt64 rc.2.2.2 es) S rc.2.2.1
    (rc.2.2.1.toInt64 * 256) (rc.1 * subUnit).toInt64 rc.2.2.2 rc.2.1.toInt64
    { acc := Array.replicate (rc.2.2.1 + 2) 0,
      out := ByteArray.emptyWithCapacity (rc.2.2.2 * rc.2.2.1) }
  (st.out, st.steps)

private theorem fillActive_spec (eo : Bool) (es : Array Edge) (S : Nat)
    (rc : Int × Int × Nat × Nat) :
    (fillActive eo es S rc).1.size = rc.2.2.2 * rc.2.2.1 ∧
      (fillActive eo es S rc).2 ≤ rc.2.2.2 * (S * es.size + rc.2.2.1 + 1) := by
  have h := rowLoopF_inv eo (ySort rc.2.1.toInt64 rc.2.2.2 es) S rc.2.2.1
    (rc.2.2.1.toInt64 * 256) (rc.1 * subUnit).toInt64 rc.2.2.2 rc.2.1.toInt64
    { acc := Array.replicate (rc.2.2.1 + 2) 0,
      out := ByteArray.emptyWithCapacity (rc.2.2.2 * rc.2.2.1) } (by simp) (by simp)
  rw [ySort_size] at h
  have h0 : (ByteArray.emptyWithCapacity (rc.2.2.2 * rc.2.2.1)).size = 0 := rfl
  rw [h0] at h
  simp only [fillActive]
  simpa using h

/-- Is the bucketed path's shape guard met (`h·S ≤ 2²⁰` sample rows, `w ≤ 2²⁰`)? -/
def bucketShape (S : Nat) (rc : Int × Int × Nat × Nat) : Bool :=
  rc.2.2.2 * S ≤ 1048576 && rc.2.2.1 ≤ 1048576

/-- The coverage rows of the mask rectangle `rc` with their counted work: under `fastOK`, the
bucketed path when its guards hold (`bucketShape`, at most `2²⁰` crossings, at most 64 per
sample row), else the active-edge fast rasterizer (`fillActive`); without `fastOK` the
reference `rowLoop` (edges sorted by `y0`). -/
def fillRows (rule : FillRule) (es : Array Edge) (S : Nat) (rc : Int × Int × Nat × Nat) :
    ByteArray × Nat :=
  if fastOK es rc then
    let eo := match rule with | .evenOdd => true | .nonzero => false
    if bucketShape S rc then
      let h := rc.2.2.2
      let w := rc.2.2.1
      let ym := rc.2.1.toInt64
      let sc := scanB h S.toInt64 h.toInt64 ym es es.size 0 (Array.replicate (h * S + 1) 0) 0 0
      if sc.n ≤ 1048576 then
        let pr := prefB (h * S) 0 0 0 0 sc.cur
        if pr.2 ≤ 64 then
          let dd : Int64 := if 256 % S = 0 then (256 / S).toInt64 else 0
          let em := emitB es S S.toInt64 h.toInt64 ym (rc.1 * subUnit).toInt64 (w.toInt64 * 256) dd
            (es.size + sc.n + 1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 pr.1 (Array.replicate sc.n 0)
          let xs := sortB em.1 (h * S) 0 0 em.2
          (rowsB eo S w (256 * S).toUInt32 xs em.1 h 0 (Array.replicate (w + 2) 0)
            (ByteArray.emptyWithCapacity (h * w)), h * (w + 1) + S * sc.act)
        else fillActive eo es S rc
      else fillActive eo es S rc
    else fillActive eo es S rc
  else
    let st := rowLoop rule (es.mergeSort (fun a b => a.y0 ≤ b.y0)) S rc.2.2.1 (rc.1 * subUnit)
      rc.2.2.2 rc.2.1 {}
    (st.out, st.steps)

/-- `fillRows` writes exactly `h · w` bytes and counts at most `h · (S · E + w + 1)` steps. -/
theorem fillRows_spec (rule : FillRule) (es : Array Edge) (S : Nat)
    (rc : Int × Int × Nat × Nat) :
    (fillRows rule es S rc).1.size = rc.2.2.2 * rc.2.2.1 ∧
      (fillRows rule es S rc).2 ≤ rc.2.2.2 * (S * es.size + rc.2.2.1 + 1) := by
  simp only [fillRows]
  split
  · split
    · skip
      split
      · split
        · constructor
          · rw [rowsB_size]
            have h0 : (ByteArray.emptyWithCapacity (rc.2.2.2 * rc.2.2.1)).size = 0 := rfl
            rw [h0]; omega
          · have ha := scanB_act rc.2.2.2 S.toInt64 rc.2.2.2.toInt64 rc.2.1.toInt64 es es.size 0
              (Array.replicate (rc.2.2.2 * S + 1) 0) 0 0
            generalize (scanB rc.2.2.2 S.toInt64 rc.2.2.2.toInt64 rc.2.1.toInt64 es es.size 0
              (Array.replicate (rc.2.2.2 * S + 1) 0) 0 0).act
              = A at ha ⊢
            have h1 : S * A ≤ S * (es.size * rc.2.2.2) := Nat.mul_le_mul_left _ (by omega)
            have h2 : S * (es.size * rc.2.2.2) = rc.2.2.2 * (S * es.size) := by
              rw [Nat.mul_comm rc.2.2.2, Nat.mul_assoc]
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
            omega
        · exact fillActive_spec _ _ _ _
      · exact fillActive_spec _ _ _ _
    · exact fillActive_spec _ _ _ _
  · have h := rowLoop_inv rule (es.mergeSort (fun a b => a.y0 ≤ b.y0)) S rc.2.2.1
      (rc.1 * subUnit) rc.2.2.2 rc.2.1 {} (by simp) (by simp)
    rw [Array.size_mergeSort] at h
    simpa using And.intro h.2.1 h.2.2

/-- **Coverage rasterizer** with its counted work: fill the polygon `edges` with `rule` into a
coverage mask over (bounding box ∩ `clip`). Byte-identical to `fillEdgesCountedSpec`
(tested); fast path of tasks 7.2f/7.2j (the bounding box does not depend on the edge order, so
only the reference fallback sorts the edges by `y0`). -/
def fillEdgesCounted (edges : Array Edge) (rule : FillRule) (clip : IRect) (cfg : Config := {}) :
    Mask × Nat :=
  let S := cfg.samples
  let rc := maskRect edges clip
  let st := fillRows rule edges S rc
  ({ x0 := rc.1, y0 := rc.2.1, w := rc.2.2.1, h := rc.2.2.2, data := st.1 }, st.2)

/-- **Coverage rasterizer**: fill the polygon `edges` with `rule` into a coverage mask over
(bounding box of the edges ∩ `clip`). -/
def fillEdges (edges : Array Edge) (rule : FillRule) (clip : IRect) (cfg : Config := {}) :
    Mask :=
  (fillEdgesCounted edges rule clip cfg).1

/-- **Buffer shape.** The coverage buffer has exactly `w · h` bytes. -/
theorem fillEdges_size (edges : Array Edge) (rule : FillRule) (clip : IRect) (cfg : Config) :
    (fillEdges edges rule clip cfg).data.size =
      (fillEdges edges rule clip cfg).w * (fillEdges edges rule clip cfg).h := by
  simp only [fillEdges, fillEdgesCounted]
  rw [(fillRows_spec rule _ cfg.samples _).1, Nat.mul_comm]

/-- **S3 work bound for the rasterizer.** The counted work is at most
`h · (S · E + w + 1)` for `E` edges, mask height `h`, width `w`, `S` sample rows per pixel. -/
theorem fillEdgesCounted_steps_le (edges : Array Edge) (rule : FillRule) (clip : IRect)
    (cfg : Config) :
    (fillEdgesCounted edges rule clip cfg).2 ≤
      (fillEdgesCounted edges rule clip cfg).1.h *
        (cfg.samples * edges.size + (fillEdgesCounted edges rule clip cfg).1.w + 1) := by
  simp only [fillEdgesCounted]
  exact (fillRows_spec rule edges cfg.samples (maskRect edges clip)).2

/-- **Fill a device path**: flatten then rasterize. -/
def fillDPath (p : DPath) (rule : FillRule) (clip : IRect) (cfg : Config := {}) : Mask :=
  fillEdges (flatten cfg clip p) rule clip cfg

/-- **Fill a page-space path** through the page → device matrix `m`
(e.g. `Geom.viewMatrix zoom rot box`). -/
def fillPath (m : Aff) (p : Content.Path) (rule : FillRule) (clip : IRect) (cfg : Config := {}) :
    Mask :=
  fillDPath (ofContentPath m p cfg) rule clip cfg

/-! ## 7. Checks -/

/-- Device path from pixel-unit integer points (test helper). -/
private def px (x y : Int) : FPt := ⟨x * 256, y * 256⟩

/-- A closed polygon through pixel points. -/
private def poly (pts : List (Int × Int)) : DPath :=
  match pts with
  | [] => #[]
  | (x, y) :: rest =>
    (#[DSeg.moveTo (px x y)] ++ (rest.map fun (a, b) => DSeg.lineTo (px a b)).toArray).push
      .closePath

private def win : IRect := ⟨0, 0, 20, 20⟩

-- Rectangle with integer corners [3,8)×[5,9): exactly 255 inside, 0 outside, area 20 px.
#guard
  let m := fillDPath (poly [(3, 5), (8, 5), (8, 9), (3, 9)]) .nonzero win
  m.x0 == 3 && m.y0 == 5 && m.w == 5 && m.h == 4 && m.total == 20 * 255 &&
    m.data.toList.all (· == 255) && m.get 2 5 == 0 && m.get 8 6 == 0 && m.get 3 5 == 255
-- Even-odd agrees with nonzero on the simple rectangle.
#guard (fillDPath (poly [(3, 5), (8, 5), (8, 9), (3, 9)]) .evenOdd win).total == 20 * 255
-- Opposite orientation gives the same coverage.
#guard (fillDPath (poly [(3, 5), (3, 9), (8, 9), (8, 5)]) .nonzero win).total == 20 * 255
-- Triangle (0,0),(10,0),(0,10): area 50 px² (within 1%).
#guard
  let t := (fillDPath (poly [(0, 0), (10, 0), (0, 10)]) .nonzero win).total
  50 * 255 * 99 ≤ t * 100 && t * 100 ≤ 50 * 255 * 101
-- Empty path, path outside the window: empty masks.
#guard (fillDPath #[] .nonzero win).w * (fillDPath #[] .nonzero win).h == 0
#guard (fillDPath (poly [(30, 30), (40, 30), (40, 40)]) .nonzero win).total == 0
-- Huge (clamped) coordinates: the whole 20×20 window is covered.
#guard
  let big := (Limits.default.coordLimit : Int) / 256 + 1000000
  let m := fillDPath (poly [(-big, -big), (big, -big), (big, big), (-big, big)]) .nonzero win
  m.w == 20 && m.h == 20 && m.total == 400 * 255
-- Exact subdivision points: B(1/2) of (0, 0, 256, 256) is (0 + 0 + 768 + 256)/8 = 128.
#guard bezNum 2 1 0 0 256 256 == 1024 && (bezAt 2 1 ⟨0, 0⟩ ⟨0, 0⟩ ⟨256, 256⟩ ⟨256, 256⟩).x == 128
#guard segCount 512 0 51 == 1 && segCount 512 1000000 51 ≤ 512 && segCount 0 5 1 == 1
-- A smaller cap from `Limits` coarsens: a 16-chord cap gives at most 16 + 1 edges per cubic.
#guard
  let cfg := Config.ofLimits { curveSegCap := 16 }
  let p : DPath := #[.moveTo ⟨0, 0⟩, .curveTo ⟨0, 100000⟩ ⟨100000, 100000⟩ ⟨100000, 0⟩]
  (flatten cfg win p).size ≤ 17 && (flatten {} win p).size > 17

end SafePdf.Core.Raster.Fill
