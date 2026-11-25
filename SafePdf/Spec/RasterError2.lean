import SafePdf.Spec.RasterError
import SafePdf.Core.Raster.Type3

/-!
# Raster error bounds, part 2 (task 12.8b)

Plan.md §6 Phase 12, "Proof gaps" (targeted numeric error bounds for the raster's rounded
surfaces); continues `SafePdf/Spec/RasterError.lean` (12.8), whose inventory in
`docs/raster.md` ("Error bounds") lists the surfaces left open there.

## (a) Type 3 stencil weights: `weightsAtI` vs `weightsAt`

`Type3.weightsAtI` evaluates MuPDF's smoothstep filter in `2⁻²⁴` fixed point with natural
numbers. `weightsAtI_eq` restates it with its per-weight kernel factored out (`weightI`),
by `rfl`. For that kernel:

* `smoothI_near`: the integer smoothstep `s` of the truncated distance `⌊P·2²⁴/Q⌋` satisfies
  `0 ≤ s/2²⁴ − simpleFilter (P/Q) < 17/2²⁶` (`P < Q`): one-sided, the integer filter never
  undershoots.
* `weightI_near`: with `M = 256·F = mulN·2²⁴/den ≤ 256` (the scale both branches of
  `weightsAtI` use), the integer weight `wI` and the exact `wR = ⌊M·simpleFilter(P/Q) + ½⌋`
  (`weightsAt`'s formula) satisfy `wR ≤ wI ≤ wR + 1`, and `wI = wR` unless
  `M·simpleFilter(P/Q) + ½` lies within `17/2¹⁸` below an integer (a near tie).
* `dist_down`, `dist_up`: `weightsAt`'s filter distance for source sample `i` is exactly
  `P/Q` with `weightsAtI`'s `P` and `Q`, on the grid inputs `x = X/2²⁰`, `dstW = N/2²⁰`, in
  both the downscaling and the upscaling branch, and `256·F = mulN·2²⁴/den` there.
* `sum_near`: two weight lists that agree index by index up to `1` have sums within the
  list length; `checkWeightsB_sum`: whenever `checkWeightsB` adjusts, the result sums to 256.

## (b) Per-pixel stepping of axial and radial shadings

`axialRows` starts each row at `t₀ = ⌊T₀·2²⁴⌋` and adds `dt = roundQ(α·2²⁴)` per pixel.
`step_near`: after `k` steps the integer parameter is within `1 + k/2` units (`2⁻²⁴`) of the
exact `(T₀ + k·α)·2²⁴` (no clamp, no overflow). `isqrtFrom`'s Newton steps:
`isqrt_go_ge` (never below `⌊√n⌋`) and `isqrt_go_eq` (exact when it stops by convergence),
on the natural-number model of the step.

## (c) Integer powers of function arithmetic

`powNat_near`: square-and-multiply with every product rounded to `2⁻²⁴` (`Shading.powNat`)
is within `n·2⁻²⁵` of `xⁿ` for `|x| ≤ 1`, `n < 2¹⁷`. `exp_component_near`: one output of a
type 2 function with a natural exponent `n ≤ 2¹⁶` is within `2⁻²⁵ + n·2⁻²⁵·|c₁ − c₀|` of
`c₀ + xⁿ·(c₁ − c₀)`.

## (d) Image bilinear interpolation

`lerpU_toNat` (no 32-bit wrap), `lerpN_near` (one 12-bit lerp truncates by less than 1),
`bil_near`: the two-level lerp of `Image.bil` lies in `(E − 2, E]` of the exact bilinear
value `E` at the 12-bit weights.

## Still open

The list-level identity of the `weightsAt`/`weightsAtI` index ranges (`l`, `r`), non-natural
exponents (`log2Q`/`exp2Q`), sampled (type 0) and stitched (type 3) functions and the
256-entry LUTs, the 12-bit truncation of the image fraction and the image stepping, the box
filter, and the stroke pen-chord distance (see `docs/raster.md`).
-/

namespace SafePdf.Spec.RasterError2

open SafePdf.Core
open SafePdf.Core.Raster
open SafePdf.Spec.RasterError (Near)

/-! ## (a) Type 3 weights -/

/-- `0 ≤ z²`. -/
theorem sq_nonneg' (z : Rat) : 0 ≤ z * z := by
  rcases (Rat.le_total : (0 : Rat) ≤ z ∨ z ≤ 0) with h | h
  · exact Rat.mul_nonneg h h
  · have := Rat.mul_nonneg (show 0 ≤ -z by grind) (show 0 ≤ -z by grind); grind

/-- The smoothstep `f(u) = 1 + (2u − 3)u²` is decreasing on `[0, 1]` with slope at most
`9/4` in absolute value: `0 ≤ f(u) − f(t) ≤ 9/4·(t − u)` for `0 ≤ u ≤ t ≤ 1`. -/
theorem smooth_lip (u t : Rat) (hu0 : 0 ≤ u) (hut : u ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 + (2 * u - 3) * u * u) - (1 + (2 * t - 3) * t * t) ∧
    (1 + (2 * u - 3) * u * u) - (1 + (2 * t - 3) * t * t) ≤ 9 / 4 * (t - u) := by
  have e : (1 + (2 * u - 3) * u * u) - (1 + (2 * t - 3) * t * t) =
      (t - u) * (3 * (u + t) - 2 * (u * u + u * t + t * t)) := by grind
  have hd : 0 ≤ t - u := by grind
  have h1 : u * u ≤ u := by
    have := Rat.mul_le_mul_of_nonneg_left (show u ≤ 1 by grind) hu0; grind
  have h2 : t * t ≤ t := by
    have := Rat.mul_le_mul_of_nonneg_left ht1 (show 0 ≤ t by grind); grind
  have h3 : u * t ≤ t := by
    have := Rat.mul_le_mul_of_nonneg_right (show u ≤ 1 by grind) (show 0 ≤ t by grind); grind
  have h5 : u * t ≤ u := by
    have := Rat.mul_le_mul_of_nonneg_left (show t ≤ 1 by grind) hu0; grind
  have h4 : 0 ≤ u * t := Rat.mul_nonneg hu0 (by grind)
  have q1 := sq_nonneg' (u - 3 / 4)
  have q2 := sq_nonneg' (t - 3 / 4)
  have hh0 : 0 ≤ 3 * (u + t) - 2 * (u * u + u * t + t * t) := by grind
  have hh1 : 3 * (u + t) - 2 * (u * u + u * t + t * t) ≤ 9 / 4 := by grind
  rw [e]
  constructor
  · exact Rat.mul_nonneg hd hh0
  · have := Rat.mul_le_mul_of_nonneg_left hh1 hd; grind

/-- The integer smoothstep of `weightsAtI` at `d` (`2⁻²⁴` units):
`2²⁴ − ⌊⌊(3·2²⁴ − 2d)·d / 2²⁴⌋·d / 2²⁴⌋`. -/
def smoothI (d : Nat) : Nat :=
  let one : Nat := 1 <<< 24
  one - (((((3 * one - 2 * d) * d) >>> 24) * d) >>> 24)

/-- The per-weight kernel of `weightsAtI`: distance `P/Q`, scale `mulN/den`. -/
def weightI (P Q mulN den : Nat) : Nat :=
  let one : Nat := 1 <<< 24
  let d := (P <<< 24) / Q
  let s := one - (((((3 * one - 2 * d) * d) >>> 24) * d) >>> 24)
  (mulN * s + den / 2) / den

/-- `weightI` through `smoothI`. -/
theorem weightI_def (P Q mulN den : Nat) :
    weightI P Q mulN den = (mulN * smoothI (P * 16777216 / Q) + den / 2) / den := by
  simp only [weightI, smoothI, Nat.shiftLeft_eq]

/-- `Type3.weightsAtI` with its per-weight kernel factored out as `weightI` (same text
otherwise; `weightsAtI_eq`). -/
def weightsAtI' (srcW : Nat) (X N : Nat) (dstWInt j : Nat) : List (Nat × Int) :=
  let K : Nat := 1 <<< Type3.wBits
  let sw : Nat := srcW
  let down := N < sw * K
  let c : Nat := 2 * K * sw
  let Ac : Nat := ((2 * j + 3) * K - 2 * X) * sw
  let A : Int := (Ac : Int) - c
  let win2 : Int := if down then 2 * (sw : Int) * K else 2 * (N : Int)
  let l : Int := -Int.fdiv (-(A - N - win2)) (2 * (N : Int))
  let r : Int := Int.fdiv (A - N + win2) (2 * (N : Int))
  let Q : Nat := if down then 2 * sw * K else 2 * N
  let one : Nat := 1 <<< 24
  let den : Nat := if down then K * sw * one else one
  let mulN : Nat := if down then 256 * N else 256
  let ws := (List.range (r - l + 1).toNat).filterMap fun (k : Nat) =>
    let i : Int := l + (k : Int)
    if i < 0 ∨ (sw : Int) ≤ i then none else
    let B := (2 * i.toNat + 1) * N + c
    let P := if B ≤ Ac then Ac - B else B - Ac
    if Q ≤ P then none else
    let wt := weightI P Q mulN den
    if wt = 0 then none else some (i.toNat, (wt : Int))
  let ws := if ws.isEmpty then
      [((max 0 (min (Int.fdiv (A - N) (2 * (N : Int))) ((sw : Int) - 1))).toNat, 1)]
    else ws
  Type3.checkWeightsB ws j dstWInt (X * 10000 < K) (((dstWInt : Int) * K - N) * 10000 < K)

/-- **`weightsAtI` is `weightsAtI'`**: every weight it emits is `weightI P Q mulN den`. -/
theorem weightsAtI_eq (srcW X N dstWInt j : Nat) :
    Type3.weightsAtI srcW X N dstWInt j = weightsAtI' srcW X N dstWInt j := rfl

/-- **The integer smoothstep never undershoots and overshoots by less than `17/2²⁶`**:
for `P < Q`, `0 ≤ smoothI ⌊P·2²⁴/Q⌋ / 2²⁴ − simpleFilter (P/Q) < 17/2²⁶`. -/
theorem smoothI_near (P Q : Nat) (hPQ : P < Q) :
    0 ≤ (smoothI (P * 16777216 / Q) : Rat) / 16777216 - Type3.simpleFilter ((P : Rat) / Q) ∧
    (smoothI (P * 16777216 / Q) : Rat) / 16777216 - Type3.simpleFilter ((P : Rat) / Q) <
      17 / 67108864 := by
  have hQ : 0 < Q := by omega
  generalize hd : P * 16777216 / Q = d
  have nd1 : d * Q ≤ P * 16777216 := by rw [← hd]; exact Nat.div_mul_le_self _ _
  have nd2 : P * 16777216 < (d + 1) * Q := by
    have := Nat.lt_div_mul_add (a := P * 16777216) hQ
    rw [hd] at this; rw [Nat.add_mul, Nat.one_mul]; exact this
  have hdS : d < 16777216 := by
    have : d * Q < 16777216 * Q := by
      have := Nat.mul_lt_mul_of_pos_right hPQ (show 0 < 16777216 by omega); omega
    exact Nat.lt_of_mul_lt_mul_right this
  simp only [smoothI, Nat.shiftRight_eq_div_pow]
  generalize ha : (3 * (1 <<< 24) - 2 * d) * d = a
  have ha' : a + 2 * d * d = 3 * 16777216 * d := by
    rw [← ha]; simp only [show (1 <<< 24 : Nat) = 16777216 from rfl]
    rw [Nat.sub_mul]; have : 2 * d * d ≤ 3 * 16777216 * d := by
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  generalize ha1 : a / 2 ^ 24 = a1
  have na1 : a1 * 16777216 ≤ a := by rw [← ha1]; exact Nat.div_mul_le_self _ _
  have na2 : a < a1 * 16777216 + 16777216 := by
    rw [← ha1]; have := Nat.lt_div_mul_add (a := a) (show 0 < 2 ^ 24 by decide)
    simp only [show (2 ^ 24 : Nat) = 16777216 from rfl] at this ⊢; omega
  generalize hb1 : a1 * d / 2 ^ 24 = b1
  have nb1 : b1 * 16777216 ≤ a1 * d := by rw [← hb1]; exact Nat.div_mul_le_self _ _
  have nb2 : a1 * d < b1 * 16777216 + 16777216 := by
    rw [← hb1]; have := Nat.lt_div_mul_add (a := a1 * d) (show 0 < 2 ^ 24 by decide)
    simp only [show (2 ^ 24 : Nat) = 16777216 from rfl] at this ⊢; omega
  -- to `Rat`
  have rd1 : (d : Rat) * Q ≤ P * 16777216 := by exact_mod_cast nd1
  have rd2 : (P : Rat) * 16777216 < (d + 1) * Q := by exact_mod_cast nd2
  have ra : (a : Rat) + 2 * d * d = 3 * 16777216 * d := by exact_mod_cast ha'
  have ra1 : (a1 : Rat) * 16777216 ≤ a := by exact_mod_cast na1
  have ra2 : (a : Rat) < a1 * 16777216 + 16777216 := by exact_mod_cast na2
  have rb1 : (b1 : Rat) * 16777216 ≤ a1 * d := by exact_mod_cast nb1
  have rb2 : (a1 : Rat) * d < b1 * 16777216 + 16777216 := by exact_mod_cast nb2
  have rdS : (d : Rat) < 16777216 := by exact_mod_cast hdS
  have rd0 : (0 : Rat) ≤ d := Rat.natCast_nonneg
  have rQ : (0 : Rat) < Q := by exact_mod_cast hQ
  -- `a1·d` against `(3S − 2d)·d²`
  have m1 := Rat.mul_le_mul_of_nonneg_right ra1 rd0
  have m2 := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ra2) rd0
  -- `u = d/S ≤ t = P/Q < u + 1/S`
  generalize ht : (P : Rat) / Q = t
  have htQ : t * Q = P := by rw [← ht]; exact Rat.div_mul_cancel (by grind)
  have hut : (d : Rat) / 16777216 ≤ t := by
    have : (d : Rat) * Q ≤ (t * 16777216) * Q := by grind
    have := Rat.le_of_mul_le_mul_right this rQ; grind
  have htu : t < (d : Rat) / 16777216 + 1 / 16777216 := by
    have h' : (t * 16777216) * Q < ((d : Rat) + 1) * Q := by grind
    have : t * 16777216 < (d : Rat) + 1 := by
      apply Decidable.byContradiction; intro hc
      have h : (d : Rat) + 1 ≤ t * 16777216 := by grind
      have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt rQ); grind
    grind
  have ht1 : t < 1 := by
    rw [← ht]; exact (Rat.div_lt_iff rQ).mpr (by rw [Rat.one_mul]; exact_mod_cast hPQ)
  have hsf : Type3.simpleFilter t = 1 + (2 * t - 3) * t * t := by
    simp only [Type3.simpleFilter]; split
    · grind
    · rfl
  rw [hsf]
  have lip := smooth_lip ((d : Rat) / 16777216) t (by grind) hut (by grind)
  have ra' : (a : Rat) * d + 2 * d * d * d = 3 * 16777216 * d * d := by
    have e : ((a : Rat) + 2 * d * d) * d = 3 * 16777216 * d * d := by rw [ra]
    grind
  -- `b1·S² ≤ (3S − 2d)·d² < b1·S² + 2S²`
  have g1 : (b1 : Rat) * 16777216 * 16777216 ≤ 3 * 16777216 * d * d - 2 * d * d * d := by
    clear lip hsf htu hut ht1 htQ ht rd1 rd2 nd1 nd2 hd ha ha' ha1 na1 na2 hb1 nb1 nb2; grind
  have g2 : 3 * 16777216 * d * d - 2 * d * d * d <
      (b1 : Rat) * 16777216 * 16777216 + 2 * 16777216 * 16777216 := by
    clear lip hsf htu hut ht1 htQ ht rd1 rd2 nd1 nd2 hd ha ha' ha1 na1 na2 hb1 nb1 nb2; grind
  -- `b1 ≤ S`
  have hb1S : (b1 : Rat) ≤ 16777216 := by
    have q := sq_nonneg' ((d : Rat) - 16777216)
    have q2 := Rat.mul_nonneg q (show (0 : Rat) ≤ 2 * d + 16777216 by grind)
    clear lip hsf htu hut ht1 htQ ht rd1 rd2 nd1 nd2 hd ha ha' ha1 na1 na2 hb1 nb1 nb2; grind
  have nb1S : b1 ≤ 16777216 := by exact_mod_cast hb1S
  have hsub : (((1 <<< 24 : Nat) - b1 : Nat) : Rat) = 16777216 - b1 := by
    rw [show (1 <<< 24 : Nat) = 16777216 from rfl]
    have : ((16777216 - b1 : Nat) : Rat) + b1 = 16777216 := by
      rw [← Rat.natCast_add, Nat.sub_add_cancel nb1S]; rfl
    grind
  rw [hsub]
  have e : (16777216 - (b1 : Rat)) / 16777216 - (1 + (2 * ((d : Rat) / 16777216) - 3) *
      ((d : Rat) / 16777216) * ((d : Rat) / 16777216)) =
      ((3 * 16777216 * d * d - 2 * d * d * d) - (b1 : Rat) * 16777216 * 16777216) /
        (16777216 * 16777216 * 16777216) := by grind
  clear hsub nb1S hb1S ra' rdS ra ra1 ra2 rb1 rb2 m1 m2 rd1 rd2 nd1 nd2 hd ha ha' ha1 na1 na2 hb1 nb1 nb2
  constructor <;> grind

/-- **Per-weight bound of `weightsAtI` against `weightsAt`.** With `256·F = mulN·2²⁴/den`
(`F ≤ 1`, `den` even, as in both branches of `weightsAtI`; `dist_down`, `dist_up`), the
integer weight `wI = weightI P Q mulN den` and `weightsAt`'s exact
`wR = ⌊simpleFilter(P/Q)·F·256 + ½⌋` satisfy `wR ≤ wI ≤ wR + 1`, and they differ only when
`simpleFilter(P/Q)·F·256 + ½` is within `17/2¹⁸` below the integer `wR + 1` (a near tie). -/
theorem weightI_near (P Q mulN den : Nat) (F : Rat) (hPQ : P < Q) (hden : 0 < den)
    (hev : den % 2 = 0) (hF : (mulN : Rat) * 16777216 / den = F * 256) (hF1 : F ≤ 1) :
    (Type3.simpleFilter ((P : Rat) / Q) * F * 256 + 1 / 2).floor ≤ (weightI P Q mulN den : Int) ∧
    (weightI P Q mulN den : Int) ≤ (Type3.simpleFilter ((P : Rat) / Q) * F * 256 + 1 / 2).floor + 1 ∧
    ((weightI P Q mulN den : Int) ≠ (Type3.simpleFilter ((P : Rat) / Q) * F * 256 + 1 / 2).floor →
      (((Type3.simpleFilter ((P : Rat) / Q) * F * 256 + 1 / 2).floor : Int) : Rat) + 1 - 17 / 262144 ≤
        Type3.simpleFilter ((P : Rat) / Q) * F * 256 + 1 / 2) := by
  have hs := smoothI_near P Q hPQ
  rw [weightI_def]
  generalize smoothI (P * 16777216 / Q) = sI at *
  generalize Type3.simpleFilter ((P : Rat) / Q) = f at *
  generalize hw : (mulN * sI + den / 2) / den = w
  have nw1 : w * den ≤ mulN * sI + den / 2 := by rw [← hw]; exact Nat.div_mul_le_self _ _
  have nw2 : mulN * sI + den / 2 < w * den + den := by
    rw [← hw]; exact Nat.lt_div_mul_add hden
  have nh : den / 2 * 2 = den := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hev)
  have rw1 : (w : Rat) * den ≤ mulN * sI + ((den / 2 : Nat) : Rat) := by exact_mod_cast nw1
  have rw2 : (mulN : Rat) * sI + ((den / 2 : Nat) : Rat) < w * den + den := by exact_mod_cast nw2
  have rh : ((den / 2 : Nat) : Rat) * 2 = den := by exact_mod_cast nh
  have rden : (0 : Rat) < den := by exact_mod_cast hden
  -- `mulN·sI/den = F·256·sI/2²⁴`
  have e : (mulN : Rat) * 16777216 = F * 256 * den := by
    rw [← hF]; exact (Rat.div_mul_cancel (by grind)).symm
  have hY : (mulN : Rat) * sI = F * 256 * (sI / 16777216) * den := by grind
  have hF0 : 0 ≤ F := by
    apply Decidable.byContradiction; intro hc
    have h := Rat.mul_lt_mul_of_pos_right (show F < 0 by grind) rden
    have : (0 : Rat) ≤ mulN := Rat.natCast_nonneg
    grind
  -- `Y = w`-ish: `w ≤ F·256·sI/2²⁴ + ½ < w + 1`
  generalize hu : (sI : Rat) / 16777216 = u at *
  have y1 : (w : Rat) ≤ F * 256 * u + 1 / 2 := by
    have : (w : Rat) * den ≤ (F * 256 * u + 1 / 2) * den := by grind
    exact Rat.le_of_mul_le_mul_right this rden
  have y2 : F * 256 * u + 1 / 2 < (w : Rat) + 1 := by
    apply Decidable.byContradiction; intro hc
    have h : (w : Rat) + 1 ≤ F * 256 * u + 1 / 2 := by grind
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt rden); grind
  -- `0 ≤ F·256·(u − f) < 17/2¹⁸`
  have d1 := Rat.mul_le_mul_of_nonneg_left hs.1 (show 0 ≤ F * 256 by grind)
  have d2 := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hs.2) (show 0 ≤ F * 256 by grind)
  have d3 := Rat.mul_le_mul_of_nonneg_right hF1 (show (0 : Rat) ≤ 256 * (17 / 67108864) by grind)
  generalize hX : f * F * 256 + 1 / 2 = X
  have fl1 := Rat.floor_le X
  have fl2 := Rat.lt_floor_add_one X
  generalize X.floor = wR at *
  have c1 : (wR : Rat) < ((w : Int) : Rat) + 1 := by
    rw [Rat.intCast_natCast]; clear nw1 nw2 nh rw1 rw2 rh hw; grind
  have c2 : ((w : Int) : Rat) < (wR : Rat) + 2 := by
    rw [Rat.intCast_natCast]; clear nw1 nw2 nh rw1 rw2 rh hw; grind
  have i1 : wR < (w : Int) + 1 := by
    have : ((wR : Int) : Rat) < (((w : Int) + 1 : Int) : Rat) := by
      rw [Rat.intCast_add, Rat.intCast_one]; exact c1
    exact Rat.intCast_lt_intCast.mp this
  have i2 : (w : Int) < wR + 2 := by
    have : (((w : Int) : Int) : Rat) < ((wR + 2 : Int) : Rat) := by
      rw [Rat.intCast_add]; exact c2
    exact Rat.intCast_lt_intCast.mp this
  refine ⟨by omega, by omega, fun hne => ?_⟩
  have hw1 : (w : Int) = wR + 1 := by omega
  have : ((w : Int) : Rat) = (wR : Rat) + 1 := by rw [hw1, Rat.intCast_add, Rat.intCast_one]
  rw [Rat.intCast_natCast] at this
  clear nw1 nw2 nh rw1 rw2 rh hw; grind

/-- `weightsAtI`'s `P = |Ac − B|` (natural numbers) as a rational absolute value. -/
theorem natDist_cast (Ac B : Nat) :
    (((if B ≤ Ac then Ac - B else B - Ac : Nat)) : Rat) = Type3.absQ ((Ac : Rat) - B) := by
  simp only [Type3.absQ]
  split
  · rename_i h
    have e : ((Ac - B : Nat) : Rat) + B = Ac := by rw [← Rat.natCast_add, Nat.sub_add_cancel h]
    have : ¬ ((Ac : Rat) - B < 0) := by
      have : (B : Rat) ≤ Ac := by exact_mod_cast h
      grind
    simp only [this, ↓reduceIte]; grind
  · rename_i h
    have h' : Ac ≤ B := by omega
    have e : ((B - Ac : Nat) : Rat) + Ac = B := by rw [← Rat.natCast_add, Nat.sub_add_cancel h']
    have : (Ac : Rat) - B < 0 := by
      have : (Ac : Rat) < B := by exact_mod_cast (show Ac < B by omega)
      grind
    simp only [this, ↓reduceIte]; grind

/-- `absQ (y / c) = absQ y / c` for `c > 0`. -/
theorem absQ_div (y c : Rat) (hc : 0 < c) : Type3.absQ (y / c) = Type3.absQ y / c := by
  simp only [Type3.absQ]
  have hc' : c ≠ 0 := by grind
  by_cases h : y < 0
  · have : y / c < 0 := by
      have := (Rat.div_lt_iff hc).mpr (show y < 0 * c by grind); exact this
    simp only [this, h, ↓reduceIte]; grind
  · have : ¬ y / c < 0 := by
      intro h2; have := (Rat.div_lt_iff hc).mp h2; grind
    simp only [this, h, ↓reduceIte]

/-- `weightsAtI`'s shifted numerator, as a rational: `Ac − B = ((2j+1)·2²⁰ − 2X)·srcW − (2i+1)·N`
(`X < 2²⁰`). -/
theorem acb_cast (srcW X N j i : Nat) (hX : X < 1048576) :
    ((((2 * j + 3) * 1048576 - 2 * X) * srcW : Nat) : Rat) - (((2 * i + 1) * N + 2 * 1048576 * srcW : Nat) : Rat) =
      (((2 * (j : Rat) + 1) * 1048576 - 2 * X) * srcW - (2 * (i : Rat) + 1) * N) := by
  have h : 2 * X ≤ (2 * j + 3) * 1048576 := by omega
  have e : (((2 * j + 3) * 1048576 - 2 * X : Nat) : Rat) + ((2 * X : Nat) : Rat) =
      (((2 * j + 3) * 1048576 : Nat) : Rat) := by rw [← Rat.natCast_add, Nat.sub_add_cancel h]
  simp only [Rat.natCast_mul, Rat.natCast_add] at e ⊢
  have e2 : ((((2 * j + 3) * 1048576 - 2 * X : Nat)) : Rat) = (2 * (j : Rat) + 3) * 1048576 - 2 * X := by
    have h3 : ((3 : Nat) : Rat) = 3 := rfl
    have h2 : ((2 : Nat) : Rat) = 2 := rfl
    have h1 : ((1048576 : Nat) : Rat) = 1048576 := rfl
    rw [h3, h2, h1] at e; grind
  rw [e2]
  have h2 : ((2 : Nat) : Rat) = 2 := rfl
  have h1 : ((1048576 : Nat) : Rat) = 1048576 := rfl
  have h1' : ((1 : Nat) : Rat) = 1 := rfl
  rw [h2, h1, h1']; grind

/-- **Downscaling branch** (`N < srcW·2²⁰`, `G = 1`, `F = dstW/srcW`): `weightsAt`'s distance
of source sample `i` from destination pixel `j`, on the grid inputs `x = X/2²⁰`,
`dstW = N/2²⁰`, is `P/Q` with `weightsAtI`'s `P` and `Q = 2·srcW·2²⁰`; and its scale
`mulN·2²⁴/den = 256·N·2²⁴/(2²⁰·srcW·2²⁴)` is `F·256`. -/
theorem dist_down (srcW X N j i : Nat) (hX : X < 1048576) (hsw : 0 < srcW) :
    Type3.absQ (((j : Rat) - (X : Rat) / 1048576 + 1 / 2 -
        (((i : Int) : Rat) + 1 / 2) * ((N : Rat) / 1048576) / (srcW : Rat)) * 1) =
      ((if (2 * i + 1) * N + 2 * 1048576 * srcW ≤ ((2 * j + 3) * 1048576 - 2 * X) * srcW
        then ((2 * j + 3) * 1048576 - 2 * X) * srcW - ((2 * i + 1) * N + 2 * 1048576 * srcW)
        else ((2 * i + 1) * N + 2 * 1048576 * srcW) - ((2 * j + 3) * 1048576 - 2 * X) * srcW
        : Nat) : Rat) / ((2 * srcW * 1048576 : Nat) : Rat) ∧
    ((256 * N : Nat) : Rat) * 16777216 / ((1048576 * srcW * 16777216 : Nat) : Rat) =
      (N : Rat) / 1048576 / (srcW : Rat) * 256 := by
  have hs : (0 : Rat) < srcW := by exact_mod_cast hsw
  rw [natDist_cast, acb_cast srcW X N j i hX]
  constructor
  · have hc : (0 : Rat) < ((2 * srcW * 1048576 : Nat) : Rat) := by
      exact_mod_cast (show 0 < 2 * srcW * 1048576 by omega)
    rw [← absQ_div _ _ hc]
    congr 1
    simp only [Rat.natCast_mul, Rat.intCast_natCast]
    have h2 : ((2 : Nat) : Rat) = 2 := rfl
    have h1 : ((1048576 : Nat) : Rat) = 1048576 := rfl
    rw [h2, h1]; grind
  · simp only [Rat.natCast_mul]
    have h2 : ((256 : Nat) : Rat) = 256 := rfl
    have h1 : ((1048576 : Nat) : Rat) = 1048576 := rfl
    have h3 : ((16777216 : Nat) : Rat) = 16777216 := rfl
    rw [h2, h1, h3]; grind

/-- **Upscaling branch** (`G = srcW/dstW`, `F = 1`): the distance is `P/Q` with
`Q = 2N`, and the scale `256·2²⁴/2²⁴` is `1·256`. -/
theorem dist_up (srcW X N j i : Nat) (hX : X < 1048576) (hsw : 0 < srcW) (hN : 0 < N) :
    Type3.absQ (((j : Rat) - (X : Rat) / 1048576 + 1 / 2 -
        (((i : Int) : Rat) + 1 / 2) * ((N : Rat) / 1048576) / (srcW : Rat)) *
        ((srcW : Rat) / ((N : Rat) / 1048576))) =
      ((if (2 * i + 1) * N + 2 * 1048576 * srcW ≤ ((2 * j + 3) * 1048576 - 2 * X) * srcW
        then ((2 * j + 3) * 1048576 - 2 * X) * srcW - ((2 * i + 1) * N + 2 * 1048576 * srcW)
        else ((2 * i + 1) * N + 2 * 1048576 * srcW) - ((2 * j + 3) * 1048576 - 2 * X) * srcW
        : Nat) : Rat) / ((2 * N : Nat) : Rat) ∧
    ((256 : Nat) : Rat) * 16777216 / ((16777216 : Nat) : Rat) = 1 * 256 := by
  have hs : (0 : Rat) < srcW := by exact_mod_cast hsw
  have hn : (0 : Rat) < N := by exact_mod_cast hN
  rw [natDist_cast, acb_cast srcW X N j i hX]
  constructor
  · have hc : (0 : Rat) < ((2 * N : Nat) : Rat) := by
      exact_mod_cast (show 0 < 2 * N by omega)
    rw [← absQ_div _ _ hc]
    congr 1
    simp only [Rat.natCast_mul, Rat.intCast_natCast]
    have h2 : ((2 : Nat) : Rat) = 2 := rfl
    rw [h2]; grind
  · have h2 : ((256 : Nat) : Rat) = 256 := rfl
    have h3 : ((16777216 : Nat) : Rat) = 16777216 := rfl
    rw [h2, h3]; grind

/-- The weight sum `checkWeightsB` computes. -/
def wsum (ws : List (Nat × Int)) : Int := ws.foldl (fun s p => s + p.2) 0

/-- The sum fold from any start. -/
theorem foldl_wsum (ws : List (Nat × Int)) (a : Int) :
    ws.foldl (fun s p => s + p.2) a = a + wsum ws := by
  induction ws generalizing a with
  | nil => simp [wsum]
  | cons p ws ih =>
    simp only [wsum, List.foldl_cons]; rw [ih, ih (0 + p.2)]; omega

/-- Adding `c` to one weight adds `c` to the sum. -/
theorem wsum_modify (ws : List (Nat × Int)) (i : Nat) (c : Int) (hi : i < ws.length) :
    wsum (ws.modify i (fun p => (p.1, p.2 + c))) = wsum ws + c := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons p ws ih =>
    cases i with
    | zero =>
      rw [List.modify_zero_cons]; simp only [wsum, List.foldl_cons]
      rw [foldl_wsum, foldl_wsum]; omega
    | succ i =>
      rw [List.modify_succ_cons]; simp only [wsum, List.foldl_cons]
      rw [foldl_wsum, foldl_wsum]
      have := ih i (by simp at hi; omega)
      omega

/-- A scan step that moves the index by one and keeps the position or sets it to the old
index (the first-maximum scan of `checkWeightsB`). -/
def ScanStep (f : Nat × Int × Nat → Nat × Int → Nat × Int × Nat) : Prop :=
  ∀ acc p, (f acc p).1 = acc.1 + 1 ∧ ((f acc p).2.2 = acc.2.2 ∨ (f acc p).2.2 = acc.1)

/-- The scan's invariant: index `k + length`, position `0` or below the index. -/
theorem scan_idx (f : Nat × Int × Nat → Nat × Int → Nat × Int × Nat) (hf : ScanStep f)
    (ws : List (Nat × Int)) : ∀ (acc : Nat × Int × Nat), (acc.2.2 = 0 ∨ acc.2.2 < acc.1) →
    (ws.foldl f acc).1 = acc.1 + ws.length ∧
      ((ws.foldl f acc).2.2 = 0 ∨ (ws.foldl f acc).2.2 < (ws.foldl f acc).1) := by
  induction ws with
  | nil => intro acc h; simp only [List.foldl_nil, List.length_nil]; omega
  | cons p ws ih =>
    intro acc h
    simp only [List.foldl_cons, List.length_cons]
    have := hf acc p
    have := ih (f acc p) (by omega)
    omega

/-- The position the scan returns on a non-empty list is an index of the list. -/
theorem scan_lt (f : Nat × Int × Nat → Nat × Int → Nat × Int × Nat) (hf : ScanStep f)
    (ws : List (Nat × Int)) (b : Int) (hne : ws ≠ []) : (ws.foldl f (0, b, 0)).2.2 < ws.length := by
  have := scan_idx f hf ws (0, b, 0) (Or.inl rfl)
  have hl : 0 < ws.length := by cases ws <;> simp_all
  simp only at this; omega

/-- **`checkWeightsB` normalises**: whenever it adjusts (its condition holds) a non-empty
weight list, the result sums to exactly 256. Both `weightsAt` and `weightsAtI` end with it. -/
theorem checkWeightsB_sum (ws : List (Nat × Int)) (j w : Nat) (xs ws' : Bool)
    (hne : ws ≠ []) (hadj : ((j ≠ 0 ∧ j + 1 ≠ w) ∨ 256 < wsum ws) ∨
      (j = 0 ∧ xs = true ∧ wsum ws ≠ 256) ∨ (j + 1 = w ∧ ws' = true ∧ wsum ws ≠ 256)) :
    wsum (Type3.checkWeightsB ws j w xs ws') = 256 := by
  simp only [Type3.checkWeightsB]
  have hs : ws.foldl (fun s p => s + p.2) 0 = wsum ws := rfl
  rw [hs]
  split
  case isFalse hn => exact absurd (by simpa [decide_eq_true_eq] using hadj) hn
  rw [wsum_modify _ _ _ ?_]
  · omega
  · apply scan_lt _ ?_ ws _ hne
    intro acc p; simp only []; split <;> simp

/-- The value an optional weight contributes to a sum (`0` when dropped). -/
def optW (o : Option (Nat × Int)) : Int := match o with | none => 0 | some p => p.2

/-- A `filterMap`ped weight list sums to the sum of the contributions (dropped = 0). -/
theorem wsum_filterMap (L : List Nat) (g : Nat → Option (Nat × Int)) :
    wsum (L.filterMap g) = (L.map (fun k => optW (g k))).foldl (· + ·) 0 := by
  have gen : ∀ (a : Int), (L.filterMap g).foldl (fun s p => s + p.2) a =
      (L.map (fun k => optW (g k))).foldl (· + ·) a := by
    induction L with
    | nil => intro a; rfl
    | cons k L ih =>
      intro a
      simp only [List.filterMap_cons, List.map_cons, List.foldl_cons]
      cases h : g k with
      | none => rw [ih]; simp [optW]
      | some p => simp only [List.foldl_cons]; rw [ih]; rfl
  exact gen 0

/-- A sum fold from any start. -/
theorem foldl_off (l : List Int) (a : Int) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih => simp only [List.foldl_cons]; rw [ih, ih (0 + y)]; omega

/-- **Sum bound**: if, index by index, the contribution of `g2` is that of `g1` or one more
(`weightI_near`), the sums of the two `filterMap`ped weight lists differ by at most the number
of indices: `Σ₁ ≤ Σ₂ ≤ Σ₁ + |L|`. -/
theorem sum_near (L : List Nat) (g1 g2 : Nat → Option (Nat × Int))
    (h : ∀ k ∈ L, optW (g1 k) ≤ optW (g2 k) ∧ optW (g2 k) ≤ optW (g1 k) + 1) :
    wsum (L.filterMap g1) ≤ wsum (L.filterMap g2) ∧
      wsum (L.filterMap g2) ≤ wsum (L.filterMap g1) + L.length := by
  rw [wsum_filterMap, wsum_filterMap]
  induction L with
  | nil => simp
  | cons k L ih =>
    simp only [List.map_cons, List.foldl_cons, List.length_cons]
    rw [foldl_off _ (0 + optW (g1 k)), foldl_off _ (0 + optW (g2 k))]
    have hk := h k (by simp)
    have ih' := ih (fun k hk => h k (by simp [hk]))
    omega

/-! ## (b) Per-pixel stepping of axial and radial shadings -/

/-- **Stepping drift.** A row starts at `⌊T₀⌋` and adds the rounded step `roundQ α` per
pixel; after `k` steps the integer is within `1 + k/2` of the exact `T₀ + k·α` (two-sided:
`−1 − k/2 < error ≤ k/2`). Axial rows (`axialRows`): `T₀ = T·2²⁴`, `α = alpha·2²⁴`, units
`2⁻²⁴` of the shading parameter. Radial rows (`radialRows`): `T₀`, `α` are the
normalised-unit coordinates `· 2¹⁸` of the row start and `B.a`/`B.b`. No clamp
(`clampI64` inactive) and no overflow (`stepI_toInt`) assumed. -/
theorem step_near (T0 α : Rat) (k : Nat) :
    Near (((T0.floor + (k : Int) * Shading.roundQ α : Int)) : Rat) (T0 + k * α) (1 + k / 2) := by
  simp only [Shading.roundQ]
  have f1 := Rat.floor_le T0
  have f2 := Rat.lt_floor_add_one T0
  have g1 := Rat.floor_le (α + 1 / 2)
  have g2 := Rat.lt_floor_add_one (α + 1 / 2)
  generalize T0.floor = t0 at *
  generalize (α + 1 / 2).floor = dt at *
  have hk : (0 : Rat) ≤ k := Rat.natCast_nonneg
  have m1 := Rat.mul_le_mul_of_nonneg_left g1 hk
  have m2 := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt g2) hk
  simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_natCast] at *
  unfold Near; constructor <;> grind

/-- `k` steps of `+ dt` on a machine integer (the per-pixel recurrence of `axialRow` and of
each coordinate of `radialRow`: pixel `k` of a row sees `stepI dt k t₀`). -/
def stepI (dt : Int64) : Nat → Int64 → Int64
  | 0, t => t
  | k + 1, t => stepI dt k (t + dt)

/-- **No wrap-around**: if every partial sum `t₀ + j·dt` (`j ≤ k`) fits in 64 bits, the
machine recurrence computes it exactly. -/
theorem stepI_toInt (dt : Int64) (k : Nat) : ∀ (t : Int64),
    (∀ j ≤ k, -2 ^ 63 ≤ t.toInt + (j : Int) * dt.toInt ∧ t.toInt + (j : Int) * dt.toInt < 2 ^ 63) →
    (stepI dt k t).toInt = t.toInt + (k : Int) * dt.toInt := by
  induction k with
  | zero => intro t _; simp [stepI]
  | succ k ih =>
    intro t h
    have h1 := h 1 (by omega)
    have e : (t + dt).toInt = t.toInt + dt.toInt := by
      rw [Int64.toInt_add]; apply Int.bmod_eq_of_le <;> simp at h1 ⊢ <;> omega
    simp only [stepI]
    rw [ih (t + dt) (fun j hj => by
      have := h (j + 1) (by omega); rw [e]
      simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul] at this
      constructor <;> omega), e]
    simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]; omega

/-- The clamps of `axialRows`/`radialRows` (`|t₀| ≤ 2⁴⁰`, `|dt| ≤ 2³⁰`) keep every row of up
to `2³²` pixels free of wrap-around. -/
theorem stepI_toInt_clamped (t dt : Int64) (k : Nat) (ht : -2 ^ 40 ≤ t.toInt ∧ t.toInt ≤ 2 ^ 40)
    (hdt : -2 ^ 30 ≤ dt.toInt ∧ dt.toInt ≤ 2 ^ 30) (hk : k ≤ 2 ^ 32) :
    (stepI dt k t).toInt = t.toInt + (k : Int) * dt.toInt := by
  apply stepI_toInt
  intro j hj
  have hj' : (j : Int) ≤ 2 ^ 32 := by omega
  have hj0 : (0 : Int) ≤ j := by omega
  have a1 : (j : Int) * dt.toInt ≤ 2 ^ 32 * 2 ^ 30 := by
    rcases Int.le_total 0 dt.toInt with h | h
    · exact Int.mul_le_mul hj' hdt.2 h (by decide)
    · have := Int.mul_nonpos_of_nonneg_of_nonpos hj0 h; omega
  have a2 : -(2 ^ 32 * 2 ^ 30) ≤ (j : Int) * dt.toInt := by
    rcases Int.le_total 0 dt.toInt with h | h
    · have := Int.mul_nonneg hj0 h; omega
    · have := Int.mul_le_mul hj' (show -dt.toInt ≤ 2 ^ 30 by omega) (by omega) (by decide)
      rw [Int.mul_neg] at this; omega
  constructor <;> omega

/-- The Newton step of `isqrtFrom` on natural numbers. -/
def newton (n x : Nat) : Nat := (x + n / x) / 2

/-- `isqrtFrom.go` on natural numbers (no 64-bit wrap; `isqrt_go_toNat`). -/
def goN (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | f + 1, x => if x = 0 then x else if newton n x < x then goN n f (newton n x) else x

/-- **Integer AM–GM**: one Newton step from any positive guess lands at or above `⌊√n⌋`. -/
theorem sqrt_le_newton (n x : Nat) (hx : 0 < x) : Nat.sqrt n ≤ newton n x := by
  unfold newton
  generalize hs : Nat.sqrt n = s
  have hsn : s * s ≤ n := hs ▸ Nat.sqrt_le n
  by_cases h : 2 * s ≤ x
  · have := Nat.zero_le (n / x); omega
  · -- `(2s − x)·x = s² − (x − s)² ≤ n`
    have key : (2 * s - x) * x ≤ n := by
      have hi : ((2 * s - x : Nat) : Int) * x ≤ (s : Int) * s := by
        have e : ((2 * s - x : Nat) : Int) = 2 * s - x := by omega
        rw [e]
        have sq : 0 ≤ ((x : Int) - s) * ((x : Int) - s) := by
          rcases Int.le_total 0 ((x : Int) - s) with h | h
          · exact Int.mul_nonneg h h
          · have := Int.mul_nonneg (show 0 ≤ -((x : Int) - s) by omega)
              (show 0 ≤ -((x : Int) - s) by omega)
            rw [Int.neg_mul_neg] at this; exact this
        have e2 : ((x : Int) - s) * ((x : Int) - s) = (s : Int) * s - (2 * s - x) * x := by
          grind
        omega
      have : (2 * s - x) * x ≤ s * s := by exact_mod_cast hi
      omega
    have := (Nat.le_div_iff_mul_le hx).mpr key
    omega

/-- Above `⌊√n⌋` a Newton step strictly decreases. -/
theorem newton_lt (n x : Nat) (hx : Nat.sqrt n < x) : newton n x < x := by
  unfold newton
  have h1 := Nat.lt_succ_sqrt n
  have h2 : n < x * x := Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul hx hx)
  have : n / x < x := (Nat.div_lt_iff_lt_mul (by omega)).mpr h2
  omega

/-- **`isqrtFrom` never under-estimates**: from a guess at or above `⌊√n⌋` the decreasing
Newton steps stay at or above it. -/
theorem goN_ge (n : Nat) (hn : 0 < n) : ∀ (f x : Nat), Nat.sqrt n ≤ x → Nat.sqrt n ≤ goN n f x
  | 0, x, h => h
  | f + 1, x, h => by
    simp only [goN]
    have hx : 0 < x := by
      have := Nat.lt_succ_sqrt n
      by_cases h0 : Nat.sqrt n = 0
      · rw [h0] at this; omega
      · omega
    have hx0 : ¬ x = 0 := by omega
    simp only [hx0, ↓reduceIte]
    split
    · exact goN_ge n hn f _ (sqrt_le_newton n x hx)
    · exact h

/-- **A converged result is exact**: a value at or above `⌊√n⌋` that one more Newton step
would not decrease is `⌊√n⌋`. So `goN` returns `⌊√n⌋` whenever it stops by convergence, and
an over-estimate only when its 8 steps run out. -/
theorem eq_sqrt_of_stable (n x : Nat) (h : Nat.sqrt n ≤ x) (hs : ¬ newton n x < x) :
    x = Nat.sqrt n := by
  by_cases hlt : Nat.sqrt n < x
  · exact absurd (newton_lt n x hlt) hs
  · omega

/-- One machine Newton step is the natural-number step when nothing wraps. -/
theorem newton_toNat (n x : UInt64) (hn : n.toNat < 2 ^ 63) (hx : x.toNat < 2 ^ 63) :
    ((x + n / x) / 2).toNat = newton n.toNat x.toNat := by
  simp only [newton, UInt64.toNat_div, UInt64.toNat_add]
  have : n.toNat / x.toNat ≤ n.toNat := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt (by omega)]; rfl

/-- **`isqrtFrom.go` is `goN`** for `n, x < 2⁶³` (every intermediate below `2⁶⁴`). -/
theorem isqrt_go_toNat (n : UInt64) (hn : n.toNat < 2 ^ 63) :
    ∀ (f : Nat) (x : UInt64), x.toNat < 2 ^ 63 →
      (Shading.isqrtFrom.go n f x).toNat = goN n.toNat f x.toNat
  | 0, x, _ => rfl
  | f + 1, x, hx => by
    simp only [Shading.isqrtFrom.go, goN]
    have hz : (x = 0) ↔ (x.toNat = 0) := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact UInt64.toNat_inj.mp (by rw [h]; rfl)
    by_cases h0 : x.toNat = 0
    · simp only [hz.mpr h0]; rfl
    · have h0' : ¬ x = 0 := fun h => h0 (hz.mp h)
      simp only [h0, h0', ↓reduceIte]
      have e := newton_toNat n x hn hx
      have hlt : ((x + n / x) / 2 < x) ↔ newton n.toNat x.toNat < x.toNat := by
        rw [UInt64.lt_iff_toNat_lt, e]
      by_cases hl : newton n.toNat x.toNat < x.toNat
      · simp only [hlt.mpr hl, hl, ↓reduceIte]
        rw [isqrt_go_toNat n hn f _ (by omega), e]
      · have : ¬ ((x + n / x) / 2 < x) := fun h => hl (hlt.mp h)
        simp only [this, hl, ↓reduceIte]

/-- **`isqrtFrom` over-estimates or is exact** (radial shadings, `n, g < 2⁶³`): its result
`r` satisfies `⌊√n⌋ ≤ r`, and `r = ⌊√n⌋` whenever one more Newton step would not decrease
`r` (it stopped by convergence, not by running out of its 8 steps). -/
theorem isqrtFrom_bound (n g : UInt64) (hn : n.toNat < 2 ^ 63) (hg : g.toNat < 2 ^ 63) :
    Nat.sqrt n.toNat ≤ (Shading.isqrtFrom n g).toNat ∧
    (¬ newton n.toNat (Shading.isqrtFrom n g).toNat < (Shading.isqrtFrom n g).toNat →
      (Shading.isqrtFrom n g).toNat = Nat.sqrt n.toNat) := by
  have main : Nat.sqrt n.toNat ≤ (Shading.isqrtFrom n g).toNat := by
    simp only [Shading.isqrtFrom]
    have hz : ∀ x : UInt64, (x = 0) ↔ (x.toNat = 0) := fun x => by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact UInt64.toNat_inj.mp (by rw [h]; rfl)
    by_cases hn0 : n.toNat = 0
    · simp only [(hz n).mpr hn0, ↓reduceIte]; decide
    · have hn0' : ¬ n = 0 := fun h => hn0 ((hz n).mp h)
      simp only [hn0', ↓reduceIte]
      by_cases hg0 : g.toNat = 0
      · simp only [(hz g).mpr hg0, ↓reduceIte]
        have : Nat.sqrt n.toNat < 2 ^ 64 := by
          have := Nat.sqrt_le n.toNat
          apply Decidable.byContradiction; intro hc
          have := Nat.mul_le_mul (Nat.le_of_not_lt hc) (Nat.le_of_not_lt hc); omega
        simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt this, Nat.le_refl]
      · have hg0' : ¬ g = 0 := fun h => hg0 ((hz g).mp h)
        simp only [hg0', ↓reduceIte]
        have e := newton_toNat n g hn hg
        have hb : newton n.toNat g.toNat < 2 ^ 63 := by
          have : n.toNat / g.toNat ≤ n.toNat := Nat.div_le_self _ _
          unfold newton; omega
        rw [isqrt_go_toNat n hn 8 _ (by rw [e]; exact hb), e]
        exact goN_ge _ (by omega) 8 _ (sqrt_le_newton _ _ (by omega))
  exact ⟨main, fun hs => eq_sqrt_of_stable _ _ main hs⟩

/-! ## (c) Integer powers of function arithmetic (`Shading.powNat`) -/

/-- Half a step of the function-arithmetic grid: `2⁻²⁵`. -/
def η : Rat := 1 / 33554432

/-- `0 ≤ η`. -/
theorem η_nonneg : 0 ≤ η := by unfold η; grind

/-- `|p·q − P·Q| ≤ e₁ + e₂` when `|p − P| ≤ e₁`, `|q − Q| ≤ e₂`, `|p| ≤ 1`, `|Q| ≤ 1`. -/
theorem near_mul (p q P Q e1 e2 : Rat) (hp : Near p 0 1) (hQ : Near Q 0 1)
    (h1 : Near p P e1) (h2 : Near q Q e2) : Near (p * q) (P * Q) (e1 + e2) := by
  have a := SafePdf.Spec.RasterError.mul_near p (q - Q) e2 h2.sub_zero
  have b := SafePdf.Spec.RasterError.mul_near Q (p - P) e1 h1.sub_zero
  have rp := SafePdf.Spec.RasterError.rabs_bound p
  have rQ := SafePdf.Spec.RasterError.rabs_bound Q
  have e1n : 0 ≤ e1 := by unfold Near at h1; grind
  have e2n : 0 ≤ e2 := by unfold Near at h2; grind
  have rp1 : SafePdf.Spec.RasterError.rabs p ≤ 1 := by
    unfold SafePdf.Spec.RasterError.rabs; unfold Near at hp; split <;> grind
  have rQ1 : SafePdf.Spec.RasterError.rabs Q ≤ 1 := by
    unfold SafePdf.Spec.RasterError.rabs; unfold Near at hQ; split <;> grind
  have m1 := Rat.mul_le_mul_of_nonneg_right rp1 e2n
  have m2 := Rat.mul_le_mul_of_nonneg_right rQ1 e1n
  unfold Near at *; constructor <;> grind

/-- The unit interval is closed under products. -/
theorem unit_mul (p q : Rat) (hp : Near p 0 1) (hq : Near q 0 1) : Near (p * q) 0 1 := by
  have a := SafePdf.Spec.RasterError.mul_near p q 1 hq
  have rp1 : SafePdf.Spec.RasterError.rabs p ≤ 1 := by
    unfold SafePdf.Spec.RasterError.rabs; unfold Near at hp; split <;> grind
  unfold Near at *; constructor <;> grind

/-- `|xᵐ| ≤ 1` for `|x| ≤ 1`. -/
theorem pow_unit (x : Rat) (hx : Near x 0 1) : ∀ m : Nat, Near (x ^ m) 0 1
  | 0 => by rw [Rat.pow_zero]; unfold Near; grind
  | m + 1 => by rw [Rat.pow_succ]; exact unit_mul _ _ (pow_unit x hx m) hx

/-- Rounding to the grid keeps the unit interval (`±1` are grid points). -/
theorem qd_unit (y : Rat) (hy : Near y 0 1) : Near (Shading.qd y) 0 1 := by
  have n1 : ¬ Shading.qMax < y := by unfold Near at hy; simp only [Shading.qMax]; grind
  have n2 : ¬ y < -Shading.qMax := by unfold Near at hy; simp only [Shading.qMax]; grind
  have hc : (if Shading.qMax < y then Shading.qMax
      else if y < -Shading.qMax then -Shading.qMax else y) = y := by
    simp only [n1, n2, ↓reduceIte]
  simp only [Shading.qd, hc, Shading.qScale]
  have f1 := Rat.floor_le (y * ((16777216 : Int) : Rat) + 1 / 2)
  have f2 := Rat.lt_floor_add_one (y * ((16777216 : Int) : Rat) + 1 / 2)
  generalize hF : (y * ((16777216 : Int) : Rat) + 1 / 2).floor = F at *
  have hS : ((16777216 : Int) : Rat) = 16777216 := rfl
  rw [hS] at f1 f2 ⊢
  unfold Near at hy
  have u1 : F ≤ 16777216 := by
    apply Decidable.byContradiction; intro hc
    have : ((16777217 : Int) : Rat) ≤ (F : Rat) := Rat.intCast_le_intCast.mpr (by omega)
    have h17 : ((16777217 : Int) : Rat) = 16777217 := rfl
    rw [h17] at this; grind
  have u2 : -16777216 ≤ F := by
    apply Decidable.byContradiction; intro hc
    have : (F : Rat) ≤ ((-16777217 : Int) : Rat) := Rat.intCast_le_intCast.mpr (by omega)
    have h17 : ((-16777217 : Int) : Rat) = -16777217 := rfl
    rw [h17] at this; grind
  have v1 : (F : Rat) ≤ ((16777216 : Int) : Rat) := Rat.intCast_le_intCast.mpr u1
  have v2 : ((-16777216 : Int) : Rat) ≤ (F : Rat) := Rat.intCast_le_intCast.mpr u2
  have h1 : ((16777216 : Int) : Rat) = 16777216 := rfl
  have h2 : ((-16777216 : Int) : Rat) = -16777216 := rfl
  rw [h1] at v1; rw [h2] at v2
  unfold Near; constructor <;> grind

/-- One rounding of a unit-interval value errs by at most `η` (`qd_err`). -/
theorem qd_near_unit (y : Rat) (hy : Near y 0 1) : Near (Shading.qd y) y η := by
  have := SafePdf.Spec.RasterError.qd_err y (by unfold Near at hy; simp only [Shading.qMax]; grind)
    (by unfold Near at hy; simp only [Shading.qMax]; grind)
  unfold η; exact this

/-- The square-and-multiply loop: `b ≈ xᵐ` within `(m − 1)·η`, `acc ≈ xᵃ` within `a·η`,
everything in the unit interval, `n < 2^fuel`: the result is within `(a + m·n)·η` of
`x^(a + m·n)`. -/
theorem powNat_go_near (x : Rat) (hx : Near x 0 1) : ∀ (fuel : Nat) (b : Rat) (n : Nat)
    (acc : Rat) (m a : Nat), n < 2 ^ fuel → 1 ≤ m → Near b 0 1 → Near acc 0 1 →
    Near b (x ^ m) (((m : Rat) - 1) * η) → Near acc (x ^ a) ((a : Rat) * η) →
    Near (Shading.powNat.go fuel b n acc) (x ^ (a + m * n)) (((a + m * n : Nat) : Rat) * η)
  | 0, b, n, acc, m, a, hn, _, _, _, _, hacc => by
    have : n = 0 := by simp at hn; omega
    subst this; simpa [Shading.powNat.go] using hacc
  | fuel + 1, b, n, acc, m, a, hn, hm, hb1, hacc1, hb, hacc => by
    simp only [Shading.powNat.go]
    by_cases hn0 : n = 0
    · subst hn0; simpa using hacc
    simp only [hn0, ↓reduceIte]
    have xm := pow_unit x hx m
    have xa := pow_unit x hx a
    -- the new base: `qd(b·b) ≈ x^(2m)` within `(2m − 1)·η`
    have bb := near_mul b b (x ^ m) (x ^ m) _ _ hb1 xm hb hb
    have bb1 := unit_mul b b hb1 hb1
    have b' := (qd_near_unit (b * b) bb1).trans bb
    have hpow2 : x ^ m * x ^ m = x ^ (2 * m) := by
      rw [← Lean.Grind.Semiring.pow_add]; congr 1; omega
    rw [hpow2] at b'
    have b'' : Near (Shading.qd (b * b)) (x ^ (2 * m)) ((((2 * m : Nat) : Rat) - 1) * η) := by
      apply b'.mono; simp only [Rat.natCast_mul]
      have : ((2 : Nat) : Rat) = 2 := rfl
      rw [this]; grind
    have hn2 : n / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hn; omega
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte]
      have ab := near_mul acc b (x ^ a) (x ^ m) _ _ hacc1 xm hacc hb
      have ab1 := unit_mul acc b hacc1 hb1
      have a' := (qd_near_unit (acc * b) ab1).trans ab
      rw [← Lean.Grind.Semiring.pow_add] at a'
      have a'' : Near (Shading.qd (acc * b)) (x ^ (a + m)) (((a + m : Nat) : Rat) * η) := by
        apply a'.mono; simp only [Rat.natCast_add]; grind
      have := powNat_go_near x hx fuel _ (n / 2) _ (2 * m) (a + m) hn2 (by omega)
        (qd_unit _ bb1) (qd_unit _ ab1) b'' a''
      have e : a + m + 2 * m * (n / 2) = a + m * n := by
        have h3 : n = 2 * (n / 2) + 1 := by omega
        generalize n / 2 = q at h3 ⊢
        rw [h3]; grind
      rw [e] at this; exact this
    · simp only [hodd, ↓reduceIte]
      have := powNat_go_near x hx fuel _ (n / 2) acc (2 * m) a hn2 (by omega)
        (qd_unit _ bb1) hacc1 b'' hacc
      have e : a + 2 * m * (n / 2) = a + m * n := by
        have h3 : n = 2 * (n / 2) := by omega
        generalize n / 2 = q at h3 ⊢
        rw [h3]; grind
      rw [e] at this; exact this

/-- **`powNat` error**: for `|x| ≤ 1` and `n < 2¹⁷` (`rpow` caps integer exponents at
`2¹⁶`), the rounded square-and-multiply power is within `n·2⁻²⁵` of the exact `xⁿ`. Type 2
(exponential) functions with an integral exponent and inputs in `[0, 1]` evaluate this. -/
theorem powNat_near (x : Rat) (n : Nat) (hx : Near x 0 1) (hn : n < 2 ^ 17) :
    Near (Shading.powNat x n) (x ^ n) ((n : Rat) * η) := by
  have := powNat_go_near x hx 17 x n 1 1 0 hn (Nat.le_refl 1) hx (by unfold Near; grind)
    (by rw [Rat.pow_succ, Rat.pow_zero]; unfold Near; grind)
    (by rw [Rat.pow_zero]; unfold Near; grind)
  simp only [Nat.zero_add, Nat.one_mul] at this
  exact this

/-- `rpow` at a natural exponent `n ≤ 2¹⁶` is `powNat`. -/
theorem rpow_nat (x : Rat) (n : Nat) (hn : n ≤ 65536) : Shading.rpow x (n : Rat) = Shading.powNat x n := by
  have hd : ((n : Rat)).den = 1 := by simp
  have hnum : ((n : Rat)).num = (n : Int) := by simp
  simp only [Shading.rpow, hd, hnum, ↓reduceIte, Int.natCast_nonneg, Int.toNat_natCast]
  rw [Nat.min_eq_left hn]

/-- **One output of a type 2 (exponential) function** with a natural exponent `n ≤ 2¹⁶`
(`Fn.evalD`, `.exp`): for a clamped input `|x| ≤ 1` and no saturation, the implemented
`qd(c₀ + rpow x n · (c₁ − c₀))` is within `η + n·η·|c₁ − c₀|` (`η = 2⁻²⁵`) of the exact
`c₀ + xⁿ·(c₁ − c₀)`. (The optional `/Range` clip is 1-Lipschitz and does not add error.) -/
theorem exp_component_near (x c0 c1 : Rat) (n : Nat) (hx : Near x 0 1) (hn : n ≤ 65536)
    (hsat : -Shading.qMax ≤ c0 + Shading.rpow x n * (c1 - c0) ∧
      c0 + Shading.rpow x n * (c1 - c0) ≤ Shading.qMax) :
    Near (Shading.qd (c0 + Shading.rpow x n * (c1 - c0))) (c0 + x ^ n * (c1 - c0))
      (η + SafePdf.Spec.RasterError.rabs (c1 - c0) * ((n : Rat) * η)) := by
  have q := SafePdf.Spec.RasterError.qd_err _ hsat.1 hsat.2
  rw [rpow_nat x n hn] at q ⊢
  have p := powNat_near x n hx (by omega)
  have m := SafePdf.Spec.RasterError.mul_near (c1 - c0) (Shading.powNat x n - x ^ n) _ p.sub_zero
  have q' : Near (Shading.qd (c0 + Shading.powNat x n * (c1 - c0)))
      (c0 + Shading.powNat x n * (c1 - c0)) η := by unfold η; exact q
  apply q'.trans
  unfold Near at m ⊢; constructor <;> grind

/-! ## (d) Image bilinear interpolation (`Image.lerpU`, `Image.bil`, `Image.bilPre`) -/

/-- `Image.lerpU` on natural numbers: `⌊(a·(4096 − f) + b·f) / 4096⌋`. -/
def lerpN (a b f : Nat) : Nat := (a * (4096 - f) + b * f) / 4096

/-- **`lerpU` does not wrap** for samples below `2¹⁶` (bytes, or `bilPre`'s premultiplied
`c·a ≤ 255²`) and a weight `f ≤ 4096`. -/
theorem lerpU_toNat (a b f : UInt32) (ha : a.toNat < 2 ^ 16) (hb : b.toNat < 2 ^ 16)
    (hf : f.toNat ≤ 4096) : (Image.lerpU a b f).toNat = lerpN a.toNat b.toNat f.toNat := by
  simp only [Image.lerpU, lerpN, UInt32.toNat_shiftRight, UInt32.toNat_add, UInt32.toNat_mul]
  have hle : f ≤ 4096 := UInt32.le_iff_toNat_le.mpr (by simpa using hf)
  rw [UInt32.toNat_sub_of_le _ _ hle]
  have h4 : (4096 : UInt32).toNat = 4096 := rfl
  have h12 : (12 : UInt32).toNat % 32 = 12 := rfl
  rw [h4, h12, Nat.shiftRight_eq_div_pow]
  have m1 : a.toNat * (4096 - f.toNat) ≤ 2 ^ 16 * 4096 :=
    Nat.mul_le_mul (by omega) (by omega)
  have m2 : b.toNat * f.toNat ≤ 2 ^ 16 * 4096 := Nat.mul_le_mul (by omega) hf
  rw [Nat.mod_eq_of_lt (a := a.toNat * (4096 - f.toNat)) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat * f.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **One 12-bit lerp truncates by less than one unit**: with `t = f/4096`,
`a + (b − a)·t − 1 < lerpN a b f ≤ a + (b − a)·t`. -/
theorem lerpN_near (a b f : Nat) (hf : f ≤ 4096) :
    ((a : Rat) + ((b : Rat) - a) * ((f : Rat) / 4096)) - 1 < (lerpN a b f : Rat) ∧
      (lerpN a b f : Rat) ≤ (a : Rat) + ((b : Rat) - a) * ((f : Rat) / 4096) := by
  unfold lerpN
  generalize hq : (a * (4096 - f) + b * f) / 4096 = q
  have n1 : q * 4096 ≤ a * (4096 - f) + b * f := by rw [← hq]; exact Nat.div_mul_le_self _ _
  have n2 : a * (4096 - f) + b * f < q * 4096 + 4096 := by
    rw [← hq]; exact Nat.lt_div_mul_add (by decide)
  have e : (((4096 - f : Nat)) : Rat) = 4096 - f := by
    have : ((4096 - f : Nat) : Rat) + f = 4096 := by
      rw [← Rat.natCast_add, Nat.sub_add_cancel hf]; rfl
    grind
  have r1 : (q : Rat) * 4096 ≤ a * ((4096 - f : Nat) : Rat) + b * f := by exact_mod_cast n1
  have r2 : (a : Rat) * ((4096 - f : Nat) : Rat) + b * f < q * 4096 + 4096 := by exact_mod_cast n2
  rw [e] at r1 r2
  constructor <;> grind

/-- `lerpN` stays below a common bound of its endpoints. -/
theorem lerpN_le (a b f B : Nat) (hf : f ≤ 4096) (ha : a ≤ B) (hb : b ≤ B) : lerpN a b f ≤ B := by
  unfold lerpN
  apply (Nat.div_le_iff_le_mul_add_pred (by decide)).mpr
  have m1 : a * (4096 - f) ≤ B * (4096 - f) := Nat.mul_le_mul_right _ ha
  have m2 : b * f ≤ B * f := Nat.mul_le_mul_right _ hb
  have : B * (4096 - f) + B * f = 4096 * B := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hf, Nat.mul_comm]
  omega

/-- **Bilinear interpolation error** (`Image.bil`; `bilPre` before its division): for
samples `aᵢⱼ < 2¹⁶` and 12-bit weights `fu, fv ≤ 4095`, the two-level truncating lerp `r`
lies in `(E − 2, E]`, where `E` is the exact bilinear interpolation of the same samples at
`(t, s) = (fu/4096, fv/4096)`: `E = (1−s)·((1−t)a₀₀ + t·a₁₀) + s·((1−t)a₀₁ + t·a₁₁)`. -/
theorem bil_near (a00 a10 a01 a11 fu fv : UInt32) (h00 : a00.toNat < 2 ^ 16)
    (h10 : a10.toNat < 2 ^ 16) (h01 : a01.toNat < 2 ^ 16) (h11 : a11.toNat < 2 ^ 16)
    (hu : fu.toNat ≤ 4095) (hv : fv.toNat ≤ 4095) :
    let t : Rat := (fu.toNat : Rat) / 4096
    let s : Rat := (fv.toNat : Rat) / 4096
    let e0 : Rat := (a00.toNat : Rat) + ((a10.toNat : Rat) - a00.toNat) * t
    let e1 : Rat := (a01.toNat : Rat) + ((a11.toNat : Rat) - a01.toNat) * t
    let E : Rat := e0 + (e1 - e0) * s
    E - 2 < ((Image.lerpU (Image.lerpU a00 a10 fu) (Image.lerpU a01 a11 fu) fv).toNat : Rat) ∧
      ((Image.lerpU (Image.lerpU a00 a10 fu) (Image.lerpU a01 a11 fu) fv).toNat : Rat) ≤ E := by
  intro t s e0 e1 E
  have i0 := lerpU_toNat a00 a10 fu h00 h10 (by omega)
  have i1 := lerpU_toNat a01 a11 fu h01 h11 (by omega)
  have b0 : (Image.lerpU a00 a10 fu).toNat < 2 ^ 16 := by
    rw [i0]; have := lerpN_le a00.toNat a10.toNat fu.toNat (2 ^ 16 - 1) (by omega) (by omega) (by omega); omega
  have b1 : (Image.lerpU a01 a11 fu).toNat < 2 ^ 16 := by
    rw [i1]; have := lerpN_le a01.toNat a11.toNat fu.toNat (2 ^ 16 - 1) (by omega) (by omega) (by omega); omega
  rw [lerpU_toNat _ _ _ b0 b1 (by omega), i0, i1]
  have n0 := lerpN_near a00.toNat a10.toNat fu.toNat (by omega)
  have n1 := lerpN_near a01.toNat a11.toNat fu.toNat (by omega)
  have no := lerpN_near (lerpN a00.toNat a10.toNat fu.toNat) (lerpN a01.toNat a11.toNat fu.toNat)
    fv.toNat (by omega)
  generalize (lerpN a00.toNat a10.toNat fu.toNat : Rat) = x0 at *
  generalize (lerpN a01.toNat a11.toNat fu.toNat : Rat) = x1 at *
  have hv0 : (0 : Rat) ≤ (fv.toNat : Rat) := Rat.natCast_nonneg
  have hv1 : (fv.toNat : Rat) ≤ 4095 := by exact_mod_cast hv
  have hs0 : (0 : Rat) ≤ s := by simp only [s]; grind
  have hs1 : s ≤ 1 := by simp only [s]; grind
  -- `(1 − s)·(x0 − e0) + s·(x1 − e1) ∈ (−1, 0]`
  have d0 : -1 < x0 - e0 ∧ x0 - e0 ≤ 0 := by
    simp only [e0, t]; constructor <;> grind
  have d1 : -1 < x1 - e1 ∧ x1 - e1 ≤ 0 := by
    simp only [e1, t]; constructor <;> grind
  have p1 := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt d0.1) (show 0 ≤ 1 - s by grind)
  have p2 := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt d1.1) hs0
  have p3 := Rat.mul_le_mul_of_nonneg_left d0.2 (show 0 ≤ 1 - s by grind)
  have p4 := Rat.mul_le_mul_of_nonneg_left d1.2 hs0
  have eq : x0 + (x1 - x0) * s - E = (1 - s) * (x0 - e0) + s * (x1 - e1) := by
    simp only [E]; grind
  simp only [E] at eq ⊢
  constructor <;> grind

end SafePdf.Spec.RasterError2
