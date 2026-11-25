import SafePdf.Core.Raster.Fill
import SafePdf.Core.Raster.Shading

/-!
# Numeric error bounds of the raster's rounded surfaces against the ℚ model (task 12.8)

Plan.md §6 Phase 12, "Proof gaps": "targeted numeric error bounds for the raster float
surfaces (fill/stroke are already integer fixed-point)"; Plan.md §4 **C2**, §8
("Rational-arithmetic geometric model as proof reference"). `docs/raster.md`, section
"Error bounds", lists what is proved here and what stays open.

There is **no IEEE `Float`** anywhere in `SafePdf/Core` (or `Spec`, `Repair`): every
"float surface" of the renderer is a rounding fixed-point approximation of an exact `Rat`
quantity. This file bounds the two that every page goes through.

## (a) The transform pipeline

The interpreter keeps the CTM as a `Content.Matrix` of `Fixed` numbers (`raw · 10⁻⁶`);
`cm` sets `CTM' = M × CTM`, each entry computed exactly at scale 10¹² and rounded once
(`Content.Matrix.mul`). Path points are mapped by `Content.Matrix.apply` (rounded once).
The ℚ model is `Geom.Aff` (`Aff.mul`, `Aff.apply`), exact.

* `mul_err`: one rounded product differs from the exact product of the same operands by at
  most `δ = 1/2 · 10⁻⁶` in every entry (no saturation).
* `ctm_err` / `ctm_err_linear`: for a chain of `k` `cm` operators, the rounded CTM differs
  entrywise from the exact product by at most `δ · Σⱼ ‖Pⱼ‖`, where `Pⱼ` are the exact
  products of the matrices concatenated *after* step `j` (the rounding error of step `j` is
  carried to the end by them) and `‖·‖` is the row-sum norm `rowNorm` of the
  row-vector convention. If every such `‖Pⱼ‖ ≤ K`, the error is `≤ k · K · δ`: linear in `k`.
  (Without a bound on the later products no bound is possible: a scale by 10⁶ after a
  rounding magnifies that rounding by 10⁶.)
* `ctm_apply_err`: the device-independent end of the pipeline: a point mapped by the
  rounded CTM is within `δ + (|x| + |y| + 1) · ε` of the exact image of the point under the
  exact CTM, per coordinate, where `ε` is the CTM bound above.
* `ofDecimal_err`: the operand conversion `Decimal → Fixed` errs by at most `δ`.

## (b) Curve flattening

`Fill.flatten_err` (already proved, 7.2a) bounds the exact-ℚ chord polyline; new here is the
link to the **implemented** polyline, whose vertices are rounded (`Fill.bezAt`) and whose
control points are themselves rounded to subpixels (`Fill.toSub`):

* `vertex_err`: an implemented vertex is within `1/2` subpixel unit of the exact curve point.
* `polyline_err`: on parameter step `k`, the curve is within `3M/(4n²) + 1/2` of the
  implemented polyline (rounded vertices, same parameter).
* `polyline_tol`: with the chord count `segCount` chooses and the cap condition of
  `Fill.segCount_tol_of_cap`, that is `≤ tol + 1/2`, both coordinates.
* `toSub_err`, `bez_near`, `device_curve_err`: rounding the control points moves the curve
  by at most `1/2` unit (Bernstein weights are a convex combination), so the exact device
  curve (exact ℚ control points, times 256) is within `tol + 1` subpixel units of the
  implemented polyline, per coordinate, when no point is clamped.

## Also

* `qd_err`: one rounding step of shading-function arithmetic (`Shading.qd`, grid `2⁻²⁴`)
  errs by at most `2⁻²⁵` inside the saturation range.

Open (see `docs/raster.md`): whole `Fn.eval` evaluations and the `log2Q`/`exp2Q` routines,
per-pixel fixed-point stepping of shadings and images, image resampling filters, the stroke
outline vs the exact offset curve, and `weightsAtI` vs `weightsAt`.

All bounds are two-sided (`Near x y ε := −ε ≤ x − y ≤ ε`); core `Rat` has no `|·|`, so
`rabs` is defined here.
-/

namespace SafePdf.Spec.RasterError

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill

/-! ## Basics -/

/-- `x` is within `ε` of `y`: `−ε ≤ x − y ≤ ε`. -/
def Near (x y ε : Rat) : Prop := -ε ≤ x - y ∧ x - y ≤ ε

/-- Absolute value on `Rat` (core has none). -/
def rabs (x : Rat) : Rat := if x < 0 then -x else x

/-- `0 ≤ |x|`. -/
theorem rabs_nonneg (x : Rat) : 0 ≤ rabs x := by
  unfold rabs; split <;> grind

/-- `−|x| ≤ x ≤ |x|`. -/
theorem rabs_bound (x : Rat) : -rabs x ≤ x ∧ x ≤ rabs x := by
  unfold rabs; split <;> grind

/-- `|p · r| ≤ |p| · δ` when `|r| ≤ δ`. -/
theorem mul_near (p r δ : Rat) (h : Near r 0 δ) : Near (p * r) 0 (rabs p * δ) := by
  unfold Near at *
  unfold rabs
  split
  · have hp : 0 ≤ -p := by grind
    have e1 := Rat.mul_le_mul_of_nonneg_left h.2 hp
    have e2 := Rat.mul_le_mul_of_nonneg_left h.1 hp
    constructor <;> grind
  · have hp : 0 ≤ p := by grind
    have e1 := Rat.mul_le_mul_of_nonneg_left h.2 hp
    have e2 := Rat.mul_le_mul_of_nonneg_left h.1 hp
    constructor <;> grind

/-- `Near` is symmetric. -/
theorem Near.symm {x y ε : Rat} (h : Near x y ε) : Near y x ε := by
  unfold Near at *; constructor <;> grind

/-- `Near` composes: errors add. -/
theorem Near.trans {x y z ε η : Rat} (h1 : Near x y ε) (h2 : Near y z η) : Near x z (ε + η) := by
  unfold Near at *; constructor <;> grind

/-- `Near x y ε` as a bound on the difference. -/
theorem Near.sub_zero {x y ε : Rat} (h : Near x y ε) : Near (x - y) 0 ε := by
  unfold Near at *; constructor <;> grind

/-- A larger bound. -/
theorem Near.mono {x y ε η : Rat} (h : Near x y ε) (hle : ε ≤ η) : Near x y η := by
  unfold Near at *; constructor <;> grind

/-! ## (a) Matrices: entrywise bounds and the rounding residual -/

/-- Entrywise difference of two exact matrices. -/
def Aff.sub (m n : Aff) : Aff := ⟨m.a - n.a, m.b - n.b, m.c - n.c, m.d - n.d, m.e - n.e, m.f - n.f⟩

/-- Every entry of `m` lies in `[−ε, ε]`. -/
def EntryLe (m : Aff) (ε : Rat) : Prop :=
  Near m.a 0 ε ∧ Near m.b 0 ε ∧ Near m.c 0 ε ∧ Near m.d 0 ε ∧ Near m.e 0 ε ∧ Near m.f 0 ε

/-- The row-sum norm for the row-vector convention, with the translation row counting the
`1` an error matrix's (zero) corner contributes when it is the right factor: every entry of
`P * R` is at most `rowNorm P · ε` when every entry of `R` is at most `ε` (`mul_entryLe`). -/
def rowNorm (P : Aff) : Rat :=
  max (max (rabs P.a + rabs P.b) (rabs P.c + rabs P.d)) (rabs P.e + rabs P.f + 1)

/-- `rowNorm` is at least 1. -/
theorem one_le_rowNorm (P : Aff) : 1 ≤ rowNorm P := by
  have := rabs_nonneg P.e; have := rabs_nonneg P.f
  unfold rowNorm; grind

/-- The identity has `rowNorm` 1. -/
theorem rowNorm_id : rowNorm Aff.id = 1 := by
  have h1 : rabs 1 = 1 := by unfold rabs; grind
  have h0 : rabs 0 = 0 := by unfold rabs; grind
  simp only [rowNorm, Aff.id, h1, h0]; grind

/-- Two-term bound: `|p·r + q·s| ≤ (|p| + |q|)·ε ≤ N·ε`. -/
private theorem two_term (p q r s ε N : Rat) (hε : 0 ≤ ε) (hN : rabs p + rabs q ≤ N)
    (hr : Near r 0 ε) (hs : Near s 0 ε) : Near (p * r + q * s) 0 (N * ε) := by
  have h1 := mul_near p r ε hr
  have h2 := mul_near q s ε hs
  have h3 := Rat.mul_le_mul_of_nonneg_right hN hε
  unfold Near at *; constructor <;> grind

/-- Three-term bound for the translation row: `|p·r + q·s + u| ≤ (|p| + |q| + 1)·ε`. -/
private theorem three_term (p q r s u ε N : Rat) (hε : 0 ≤ ε) (hN : rabs p + rabs q + 1 ≤ N)
    (hr : Near r 0 ε) (hs : Near s 0 ε) (hu : Near u 0 ε) : Near (p * r + q * s + u) 0 (N * ε) := by
  have h1 := mul_near p r ε hr
  have h2 := mul_near q s ε hs
  have h3 := Rat.mul_le_mul_of_nonneg_right hN hε
  unfold Near at *; constructor <;> grind

/-- **Propagation of an entrywise bound** through a left factor: `‖P * R‖ ≤ rowNorm P · ε`. -/
theorem mul_entryLe (P R : Aff) (ε : Rat) (hε : 0 ≤ ε) (h : EntryLe R ε) :
    EntryLe (P * R) (rowNorm P * ε) := by
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  have r1 : rabs P.a + rabs P.b ≤ rowNorm P := by unfold rowNorm; grind
  have r2 : rabs P.c + rabs P.d ≤ rowNorm P := by unfold rowNorm; grind
  have r3 : rabs P.e + rabs P.f + 1 ≤ rowNorm P := by unfold rowNorm; grind
  simp only [EntryLe, Aff.mul_def, Aff.mul]
  exact ⟨two_term _ _ _ _ _ _ hε r1 ha hc, two_term _ _ _ _ _ _ hε r1 hb hd,
    two_term _ _ _ _ _ _ hε r2 ha hc, two_term _ _ _ _ _ _ hε r2 hb hd,
    three_term _ _ _ _ _ _ _ hε r3 ha hc he, three_term _ _ _ _ _ _ _ hε r3 hb hd hf⟩

/-- The zero matrix satisfies every non-negative bound. -/
theorem entryLe_sub_self (m : Aff) (ε : Rat) (hε : 0 ≤ ε) : EntryLe (Aff.sub m m) ε := by
  simp only [EntryLe, Aff.sub, Near]; grind

/-- Entrywise bounds add. -/
theorem entryLe_add (X Y : Aff) (ε η : Rat) (hX : EntryLe X ε) (hY : EntryLe Y η) :
    EntryLe ⟨X.a + Y.a, X.b + Y.b, X.c + Y.c, X.d + Y.d, X.e + Y.e, X.f + Y.f⟩ (ε + η) := by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := hX
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := hY
  simp only [EntryLe, Near] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> constructor <;> grind

/-- The rounding grid of `Fixed`: `δ = 1/2 · 10⁻⁶`. -/
def δ : Rat := 1 / 2000000

/-- `0 ≤ δ`. -/
theorem δ_nonneg : 0 ≤ δ := by unfold δ; grind

/-- `ofScaled2 p` does not saturate: `|roundDiv p 10⁶| ≤ 10¹⁸`. -/
def NoSat (p : Int) : Prop :=
  -Content.fixedMaxRaw ≤ Content.roundDiv p Content.fixedScale ∧
    Content.roundDiv p Content.fixedScale ≤ Content.fixedMaxRaw

/-- A sufficient condition for `NoSat`: the exact value (`p / 10¹²`) is at most `10¹²` minus
half a grid step in absolute value. -/
theorem noSat_of_le (p : Int) (h1 : -1000000000000000000000000 ≤ p)
    (h2 : p ≤ 999999999999999999500000) : NoSat p := by
  simp only [NoSat, Content.roundDiv, Content.fixedScale, Content.fixedMaxRaw]; omega

/-- None of the six entries of `Content.Matrix.mul m n` saturates. -/
def MulNoSat (m n : Content.Matrix) : Prop :=
  NoSat (m.a.raw * n.a.raw + m.b.raw * n.c.raw) ∧ NoSat (m.a.raw * n.b.raw + m.b.raw * n.d.raw) ∧
  NoSat (m.c.raw * n.a.raw + m.d.raw * n.c.raw) ∧ NoSat (m.c.raw * n.b.raw + m.d.raw * n.d.raw) ∧
  NoSat (m.e.raw * n.a.raw + m.f.raw * n.c.raw + n.e.raw * Content.fixedScale) ∧
  NoSat (m.e.raw * n.b.raw + m.f.raw * n.d.raw + n.f.raw * Content.fixedScale)

/-- `ofScaled2_err` as `Near`. -/
private theorem ofScaled2_near (p : Int) (h : NoSat p) :
    Near (Fixed.toRat (Content.Fixed.ofScaled2 p)) ((p : Rat) / 1000000000000) δ :=
  ofScaled2_err p h.1 h.2

/-- **One rounded matrix product.** Without saturation, `Content.Matrix.mul m n` (as ℚ)
differs from the exact product of the same operands by at most `δ` in every entry. -/
theorem mul_err (m n : Content.Matrix) (h : MulNoSat m n) :
    EntryLe (Aff.sub (Aff.ofMatrix (Content.Matrix.mul m n)) (Aff.ofMatrix m * Aff.ofMatrix n)) δ := by
  obtain ⟨ea, eb, ec, ed, ee, ef⟩ := Aff.ofMatrix_mul_exact m n
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  have za := ofScaled2_near _ ha
  have zb := ofScaled2_near _ hb
  have zc := ofScaled2_near _ hc
  have zd := ofScaled2_near _ hd
  have ze := ofScaled2_near _ he
  have zf := ofScaled2_near _ hf
  rw [ea] at za; rw [eb] at zb; rw [ec] at zc; rw [ed] at zd; rw [ee] at ze; rw [ef] at zf
  exact ⟨Near.sub_zero za, Near.sub_zero zb, Near.sub_zero zc, Near.sub_zero zd,
    Near.sub_zero ze, Near.sub_zero zf⟩

/-! ## (a) Chains of `cm` operators -/

/-- The interpreter's CTM after the `cm` matrices `ms`, **newest first**, starting from `c0`:
`CTM' = M × CTM`, rounded at every step (`Content.Interp`, operator `cm`). For matrices in
content-stream order `ss`, this is `ctmF c0 ss.reverse` (`ctmF_reverse`). -/
def ctmF (c0 : Content.Matrix) : List Content.Matrix → Content.Matrix
  | [] => c0
  | m :: ms => Content.Matrix.mul m (ctmF c0 ms)

/-- The exact ℚ model of `ctmF`: the same products without rounding. -/
def ctmQ (c0 : Aff) : List Aff → Aff
  | [] => c0
  | m :: ms => m * ctmQ c0 ms

/-- No product along the chain saturates. -/
def ChainNoSat (c0 : Content.Matrix) : List Content.Matrix → Prop
  | [] => True
  | m :: ms => MulNoSat m (ctmF c0 ms) ∧ ChainNoSat c0 ms

/-- The error bound of a chain seen through a left factor `P`:
`δ · (rowNorm P + rowNorm (P·Mₖ) + rowNorm (P·Mₖ·Mₖ₋₁) + …)`, one term per rounding. -/
def chainBound (P : Aff) : List Aff → Rat
  | [] => 0
  | m :: ms => rowNorm P * δ + chainBound (P * m) ms

/-- Content-stream order: folding `cm` left to right is `ctmF` of the reversed list. -/
theorem ctmF_reverse (c0 : Content.Matrix) (ss : List Content.Matrix) :
    ss.foldl (fun ctm m => Content.Matrix.mul m ctm) c0 = ctmF c0 ss.reverse := by
  induction ss generalizing c0 with
  | nil => rfl
  | cons s ss ih =>
    rw [List.foldl_cons, ih, List.reverse_cons]
    clear ih
    induction ss.reverse with
    | nil => rfl
    | cons t ts ih2 => simp only [List.cons_append, ctmF, ih2]

/-- The one-step error identity: `P·(X' − M·C) = P·(X' − M·Y) + (P·M)·(Y − C)`. -/
private theorem step_identity (P M X' Y C : Aff) :
    P * Aff.sub X' (M * C) =
      ⟨(P * Aff.sub X' (M * Y)).a + (P * M * Aff.sub Y C).a,
        (P * Aff.sub X' (M * Y)).b + (P * M * Aff.sub Y C).b,
        (P * Aff.sub X' (M * Y)).c + (P * M * Aff.sub Y C).c,
        (P * Aff.sub X' (M * Y)).d + (P * M * Aff.sub Y C).d,
        (P * Aff.sub X' (M * Y)).e + (P * M * Aff.sub Y C).e,
        (P * Aff.sub X' (M * Y)).f + (P * M * Aff.sub Y C).f⟩ := by
  simp only [Aff.mul_def, Aff.mul, Aff.sub]
  apply Aff.ext' <;> dsimp only <;> grind

/-- `chainBound` is non-negative. -/
theorem chainBound_nonneg (P : Aff) (ms : List Aff) : 0 ≤ chainBound P ms := by
  induction ms generalizing P with
  | nil => simp [chainBound]
  | cons m ms ih =>
    have h1 := one_le_rowNorm P
    have h2 := ih (P * m)
    have h3 : 0 ≤ rowNorm P * δ := Rat.mul_nonneg (by grind) δ_nonneg
    simp only [chainBound]; grind

/-- **Chain error, through any left factor.** For every `P`, the rounded CTM's error matrix,
multiplied by `P`, is entrywise within `chainBound P`. -/
theorem ctm_err_through (c0 : Content.Matrix) (ms : List Content.Matrix)
    (h : ChainNoSat c0 ms) (P : Aff) :
    EntryLe (P * Aff.sub (Aff.ofMatrix (ctmF c0 ms)) (ctmQ (Aff.ofMatrix c0) (ms.map Aff.ofMatrix)))
      (chainBound P (ms.map Aff.ofMatrix)) := by
  induction ms generalizing P with
  | nil =>
    have : P * Aff.sub (Aff.ofMatrix c0) (Aff.ofMatrix c0) = Aff.sub (Aff.ofMatrix c0) (Aff.ofMatrix c0) := by
      simp only [Aff.mul_def, Aff.mul, Aff.sub]
      apply Aff.ext' <;> dsimp only <;> grind
    simp only [ctmF, ctmQ, List.map_nil, chainBound]
    rw [this]; exact entryLe_sub_self _ 0 (by decide)
  | cons m ms ih =>
    obtain ⟨hm, hms⟩ := h
    simp only [ctmF, ctmQ, List.map_cons, chainBound]
    rw [step_identity P (Aff.ofMatrix m) _ (Aff.ofMatrix (ctmF c0 ms))]
    have r := mul_entryLe P _ δ δ_nonneg (mul_err m (ctmF c0 ms) hm)
    have i := ih hms (P * Aff.ofMatrix m)
    exact entryLe_add _ _ _ _ r i

/-- **Chain error.** The rounded CTM after the `cm` matrices `ms` (newest first, from an
exact start `c0`) differs from the exact product entrywise by at most
`δ · Σⱼ rowNorm(Pⱼ)`, `Pⱼ` the exact products of the matrices after step `j`. -/
theorem ctm_err (c0 : Content.Matrix) (ms : List Content.Matrix) (h : ChainNoSat c0 ms) :
    EntryLe (Aff.sub (Aff.ofMatrix (ctmF c0 ms)) (ctmQ (Aff.ofMatrix c0) (ms.map Aff.ofMatrix)))
      (chainBound Aff.id (ms.map Aff.ofMatrix)) := by
  have := ctm_err_through c0 ms h Aff.id
  rwa [Aff.id_mul] at this

/-- Every partial product `P·Mₖ·…·Mⱼ₊₁` the chain bound visits has `rowNorm ≤ K`. -/
def PartialNormLe (K : Rat) (P : Aff) : List Aff → Prop
  | [] => True
  | m :: ms => rowNorm P ≤ K ∧ PartialNormLe K (P * m) ms

/-- Under `PartialNormLe K`, the chain bound is at most `k · K · δ`. -/
theorem chainBound_le (K : Rat) (P : Aff) (ms : List Aff) (h : PartialNormLe K P ms) :
    chainBound P ms ≤ ms.length * K * δ := by
  induction ms generalizing P with
  | nil => simp [chainBound]
  | cons m ms ih =>
    obtain ⟨h1, h2⟩ := h
    have i := ih (P * m) h2
    have e := Rat.mul_le_mul_of_nonneg_right h1 δ_nonneg
    have hc : ((ms.length + 1 : Nat) : Rat) = (ms.length : Rat) + 1 := by simp
    simp only [chainBound, List.length_cons, hc]
    grind

/-- **Linear growth.** If every partial product of the later matrices has `rowNorm ≤ K`, the
rounded CTM after `k` `cm` operators is entrywise within `k · K · δ` of the exact one. -/
theorem ctm_err_linear (c0 : Content.Matrix) (ms : List Content.Matrix) (K : Rat)
    (h : ChainNoSat c0 ms) (hK : PartialNormLe K Aff.id (ms.map Aff.ofMatrix)) :
    EntryLe (Aff.sub (Aff.ofMatrix (ctmF c0 ms)) (ctmQ (Aff.ofMatrix c0) (ms.map Aff.ofMatrix)))
      (ms.length * K * δ) := by
  have e := ctm_err c0 ms h
  have b := chainBound_le K Aff.id _ hK
  rw [List.length_map] at b
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := e
  exact ⟨ha.mono b, hb.mono b, hc.mono b, hd.mono b, he.mono b, hf.mono b⟩

/-- The `x` coordinate of `Content.Matrix.apply m p` does not saturate. -/
def ApplyNoSat (m : Content.Matrix) (p : Content.Point) : Prop :=
  NoSat (p.x.raw * m.a.raw + p.y.raw * m.c.raw + m.e.raw * Content.fixedScale) ∧
    NoSat (p.x.raw * m.b.raw + p.y.raw * m.d.raw + m.f.raw * Content.fixedScale)

/-- **Point through a rounded matrix.** If the rounded matrix `F` is entrywise within `ε` of an
exact `C`, a point mapped by `F` (rounded once) is within `δ + (|x| + |y| + 1)·ε` of its exact
image under `C`, per coordinate. -/
theorem apply_err (F : Content.Matrix) (C : Aff) (p : Content.Point) (ε : Rat)
    (hF : EntryLe (Aff.sub (Aff.ofMatrix F) C) ε) (hs : ApplyNoSat F p) :
    Near (Fixed.toRat (Content.Matrix.apply F p).x) (Aff.apply C (ptOfPoint p)).x
        (δ + (rabs (ptOfPoint p).x + rabs (ptOfPoint p).y + 1) * ε) ∧
      Near (Fixed.toRat (Content.Matrix.apply F p).y) (Aff.apply C (ptOfPoint p)).y
        (δ + (rabs (ptOfPoint p).x + rabs (ptOfPoint p).y + 1) * ε) := by
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := hF
  have hx := Matrix.apply_x_err F p hs.1.1 hs.1.2
  have hy := Matrix.apply_y_err F p hs.2.1 hs.2.2
  have ma := mul_near (ptOfPoint p).x _ _ ha
  have mb := mul_near (ptOfPoint p).x _ _ hb
  have mc := mul_near (ptOfPoint p).y _ _ hc
  have md := mul_near (ptOfPoint p).y _ _ hd
  have dist : (rabs (ptOfPoint p).x + rabs (ptOfPoint p).y + 1) * ε =
      rabs (ptOfPoint p).x * ε + rabs (ptOfPoint p).y * ε + ε := by grind
  simp only [Aff.apply, Aff.sub, Near, δ] at *
  rw [dist]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> grind

/-- **The transform pipeline end to end.** A point mapped by the interpreter's rounded CTM
after `k` `cm` operators is, per coordinate, within `δ + (|x| + |y| + 1)·k·K·δ` of its image
under the exact product, when nothing saturates and every partial product of the later
matrices has `rowNorm ≤ K`. -/
theorem ctm_apply_err (c0 : Content.Matrix) (ms : List Content.Matrix) (K : Rat)
    (p : Content.Point) (h : ChainNoSat c0 ms) (hK : PartialNormLe K Aff.id (ms.map Aff.ofMatrix))
    (hs : ApplyNoSat (ctmF c0 ms) p) :
    Near (Fixed.toRat (Content.Matrix.apply (ctmF c0 ms) p).x)
        (Aff.apply (ctmQ (Aff.ofMatrix c0) (ms.map Aff.ofMatrix)) (ptOfPoint p)).x
        (δ + (rabs (ptOfPoint p).x + rabs (ptOfPoint p).y + 1) * (ms.length * K * δ)) ∧
      Near (Fixed.toRat (Content.Matrix.apply (ctmF c0 ms) p).y)
        (Aff.apply (ctmQ (Aff.ofMatrix c0) (ms.map Aff.ofMatrix)) (ptOfPoint p)).y
        (δ + (rabs (ptOfPoint p).x + rabs (ptOfPoint p).y + 1) * (ms.length * K * δ)) :=
  apply_err _ _ p _ (ctm_err_linear c0 ms K h hK) hs

/-! ## Rounding to an integer grid -/

/-- An integer `q` with `|q·d − a| ≤ d/2` is within `1/2` of `a / d`. -/
theorem int_round_near (q a d : Int) (hd : 0 < d) (h1 : -d ≤ 2 * (q * d - a))
    (h2 : 2 * (q * d - a) ≤ d) : Near (q : Rat) ((a : Rat) / d) (1 / 2) := by
  have hD : (0 : Rat) < d := by
    have : ((0 : Int) : Rat) < ((d : Int) : Rat) := Rat.intCast_lt_intCast.mpr hd
    simpa using this
  have h1' : ((-d : Int) : Rat) ≤ ((2 * (q * d - a) : Int) : Rat) := Rat.intCast_le_intCast.mpr h1
  have h2' : ((2 * (q * d - a) : Int) : Rat) ≤ ((d : Int) : Rat) := Rat.intCast_le_intCast.mpr h2
  simp only [Rat.intCast_neg, Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_ofNat] at h1' h2'
  have hne : (d : Rat) ≠ 0 := by grind
  have e : ((q : Rat) - (a : Rat) / d) * d = (q : Rat) * d - a := by grind
  unfold Near
  constructor
  · apply Rat.not_lt.mp; intro hlt
    have := Rat.mul_lt_mul_of_pos_right hlt hD
    grind
  · apply Rat.not_lt.mp; intro hlt
    have := Rat.mul_lt_mul_of_pos_right hlt hD
    grind

/-- `Fill.roundDivI a d` is within `1/2` of `a / d`. -/
theorem roundDivI_near (a d : Int) (hd : 0 < d) :
    Near (roundDivI a d : Rat) ((a : Rat) / d) (1 / 2) := by
  have h := roundDivI_err a d hd
  exact int_round_near _ _ _ hd (by omega) h.2

/-- **Subpixel rounding.** `Fill.toSub q` is within `1/2` of `256·q`. -/
theorem toSub_err (q : Rat) : Near (toSub q : Rat) (q * 256) (1 / 2) := by
  have h := roundDivI_near (q.num * subUnit) (q.den : Int) (by have := q.den_pos; omega)
  have hq : (q.num : Rat) / ((q.den : Int) : Rat) = q := by
    rw [← Rat.divInt_eq_div]; exact Rat.num_divInt_den q
  have hne : ((q.den : Int) : Rat) ≠ 0 := by
    intro h0
    have h1 : ((q.den : Int) : Rat) = ((0 : Int) : Rat) := by simpa using h0
    have := Rat.intCast_inj.mp h1
    have := q.den_pos; omega
  have e : ((q.num * subUnit : Int) : Rat) / ((q.den : Int) : Rat) = q * 256 := by
    rw [← hq, Rat.intCast_mul]
    simp only [subUnit]
    grind
  rw [e] at h; exact h

/-- The raw value `Fixed.ofDecimal` computes before saturating. -/
def decRaw (d : Decimal) : Int :=
  if d.scale ≤ 6 then d.mantissa * ((10 ^ (6 - d.scale) : Nat) : Int)
  else Content.roundDiv d.mantissa ((10 ^ (d.scale - 6) : Nat) : Int)

/-- `ofDecimal` is the clamp of `decRaw`. -/
theorem ofDecimal_eq (d : Decimal) :
    Content.Fixed.ofDecimal d = Content.Fixed.clamp (decRaw d) := by
  unfold Content.Fixed.ofDecimal decRaw; split <;> rfl

/-- `roundDiv` by an even positive divisor `2E` errs by at most `E`. -/
private theorem roundDiv_even (m : Int) (E : Nat) (hE : 0 < E) :
    -((2 * E : Nat) : Int) ≤ 2 * (Content.roundDiv m ((2 * E : Nat) : Int) * ((2 * E : Nat) : Int) - m) ∧
      2 * (Content.roundDiv m ((2 * E : Nat) : Int) * ((2 * E : Nat) : Int) - m) ≤
        ((2 * E : Nat) : Int) := by
  simp only [Content.roundDiv]
  have c1 : ((2 * E : Nat) : Int) = 2 * (E : Int) := by simp
  rw [c1]
  have hdiv : (2 * (E : Int)) / 2 = E := by omega
  rw [hdiv]
  have h1 := Int.mul_ediv_add_emod (m + E) (2 * E)
  have h2 := Int.emod_nonneg (m + E) (b := 2 * (E : Int)) (by omega)
  have h3 := Int.emod_lt_of_pos (m + E) (b := 2 * (E : Int)) (by omega)
  generalize (m + E) / (2 * E) = q at *
  generalize (m + E) % (2 * E) = r at *
  have : 2 * (E : Int) * q = q * (2 * E) := by grind
  constructor <;> omega

/-- **Operand conversion error.** Without saturation, `Fixed.ofDecimal d` is within `δ` of the
exact decimal value (and equal to it for at most 6 fractional digits). -/
theorem ofDecimal_err (d : Decimal) (hlo : -Content.fixedMaxRaw ≤ decRaw d)
    (hhi : decRaw d ≤ Content.fixedMaxRaw) :
    Near (Fixed.toRat (Content.Fixed.ofDecimal d)) (decimalToRat d) δ := by
  have hraw : (Content.Fixed.ofDecimal d).raw = decRaw d := by
    rw [ofDecimal_eq]; exact Content.Fixed.clamp_raw_of_le hlo hhi
  simp only [Fixed.toRat, hraw, decimalToRat, δ]
  unfold decRaw
  split
  · rename_i hs
    have hp : (10 ^ (6 - d.scale) * 10 ^ d.scale : Nat) = 1000000 := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hs]
    have hp' : ((10 ^ (6 - d.scale) : Nat) : Rat) * ((10 ^ d.scale : Nat) : Rat) = 1000000 := by
      rw [← Rat.natCast_mul, hp]; rfl
    simp only [Rat.intCast_mul, Rat.intCast_natCast]
    generalize ((10 ^ (6 - d.scale) : Nat) : Rat) = A at *
    generalize ((10 ^ d.scale : Nat) : Rat) = B at *
    have hB : B ≠ 0 := by intro h0; rw [h0] at hp'; grind
    have hA : A ≠ 0 := by intro h0; rw [h0] at hp'; grind
    have e : (d.mantissa : Rat) * A / 1000000 = (d.mantissa : Rat) / B := by
      rw [← hp']; grind
    rw [e]; unfold Near; constructor <;> grind
  · rename_i hs
    have hE : 0 < 5 * 10 ^ (d.scale - 7) := by
      have := Nat.pow_pos (n := d.scale - 7) (by omega : 0 < 10); omega
    have hD : (10 ^ (d.scale - 6) : Nat) = 2 * (5 * 10 ^ (d.scale - 7)) := by
      have : d.scale - 6 = (d.scale - 7) + 1 := by omega
      rw [this, Nat.pow_succ]; omega
    have hP : (10 ^ d.scale : Nat) = 10 ^ (d.scale - 6) * 1000000 := by
      have : d.scale = (d.scale - 6) + 6 := by omega
      conv => lhs; rw [this]
      rw [Nat.pow_add]
    have hq := roundDiv_even d.mantissa _ hE
    rw [← hD] at hq
    have hDpos : (0 : Int) < ((10 ^ (d.scale - 6) : Nat) : Int) := by rw [hD]; omega
    have hn := int_round_near _ _ _ hDpos hq.1 hq.2
    rw [hP]
    have hDne : ((10 ^ (d.scale - 6) : Nat) : Rat) ≠ 0 := by
      intro h0
      have h1 : ((10 ^ (d.scale - 6) : Nat) : Rat) = ((0 : Nat) : Rat) := by simpa using h0
      have := Rat.natCast_inj.mp h1; omega
    simp only [Rat.natCast_mul, Rat.intCast_natCast] at hn ⊢
    generalize ((Content.roundDiv d.mantissa ((10 ^ (d.scale - 6) : Nat) : Int) : Int) : Rat) = q
      at hn ⊢
    generalize ((10 ^ (d.scale - 6) : Nat) : Rat) = D at hn hDne ⊢
    have e : (d.mantissa : Rat) / (D * ((1000000 : Nat) : Rat)) =
        ((d.mantissa : Rat) / D) / 1000000 := by
      have : ((1000000 : Nat) : Rat) = 1000000 := rfl
      rw [this]; grind
    rw [e]
    generalize (d.mantissa : Rat) / D = x at hn ⊢
    unfold Near at hn ⊢
    constructor <;> grind

/-! ## (b) Curve flattening: the implemented polyline -/

/-- Convex combinations preserve closeness: `lerp` of `ε`-close endpoints at `r ∈ [0, 1]`. -/
theorem lerp_near (u v u' v' r ε : Rat) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hu : Near u u' ε)
    (hv : Near v v' ε) : Near (lerp u v r) (lerp u' v' r) ε := by
  have h1r : 0 ≤ 1 - r := by grind
  unfold Near at *
  have a1 := Rat.mul_le_mul_of_nonneg_left hu.1 h1r
  have a2 := Rat.mul_le_mul_of_nonneg_left hu.2 h1r
  have b1 := Rat.mul_le_mul_of_nonneg_left hv.1 hr0
  have b2 := Rat.mul_le_mul_of_nonneg_left hv.2 hr0
  simp only [lerp]; constructor <;> grind

/-- The implemented vertex `k` of `n` (one coordinate, integer controls), as in `Fill.bezAt`. -/
def vertex (n k : Nat) (a b c e : Int) : Int := roundDivI (bezNum n k a b c e) ((n : Int) * n * n)

/-- `Fill.bezAt` is `vertex` per coordinate. -/
theorem bezAt_eq (n k : Nat) (p0 p1 p2 p3 : FPt) :
    bezAt n k p0 p1 p2 p3 = ⟨vertex n k p0.x p1.x p2.x p3.x, vertex n k p0.y p1.y p2.y p3.y⟩ :=
  rfl

/-- **Vertex error.** An implemented vertex is within `1/2` subpixel unit of the exact curve
point `B(k/n)`. -/
theorem vertex_err (n k : Nat) (hn : 0 < n) (a b c e : Int) :
    Near (vertex n k a b c e : Rat) (bez a b c e ((k : Rat) / n)) (1 / 2) := by
  have hn' : (0 : Int) < n := by omega
  have h := roundDivI_near (bezNum n k a b c e) ((n : Int) * n * n)
    (Int.mul_pos (Int.mul_pos hn' hn') hn')
  have e1 : (((n : Int) * n * n : Int) : Rat) = (n : Rat) * n * n := by
    simp only [Rat.intCast_mul, Rat.intCast_natCast]
  rw [e1, bezNum_eq n k hn] at h
  exact h

/-- **Polyline error.** On step `k` of `n`, the exact curve point `B(t)` is within
`3M/(4n²) + 1/2` of the implemented polyline (rounded vertices) at the same parameter. -/
theorem polyline_err (n k : Nat) (hk : k < n) (a b c e : Int) (M t : Rat)
    (ht0 : (k : Rat) / n ≤ t) (ht1 : t ≤ ((k : Rat) + 1) / n)
    (h1 : -M ≤ (a : Rat) - 2 * b + c) (h1' : (a : Rat) - 2 * b + c ≤ M)
    (h2 : -M ≤ (b : Rat) - 2 * c + e) (h2' : (b : Rat) - 2 * c + e ≤ M) :
    Near (bez a b c e t)
      (lerp (vertex n k a b c e) (vertex n (k + 1) a b c e) (n * t - k))
      (3 * M / (4 * ((n : Rat) * n)) + 1 / 2) := by
  have hn : 0 < n := by omega
  have hnr : (0 : Rat) < n := by
    have : ((0 : Nat) : Rat) < ((n : Nat) : Rat) := Rat.natCast_lt_natCast.mpr hn
    simpa using this
  have hf := flatten_err a b c e M n k hk t ht0 ht1 h1 h1' h2 h2'
  have v0 := vertex_err n k hn a b c e
  have v1 := vertex_err n (k + 1) hn a b c e
  have ek : (((k + 1 : Nat) : Rat)) = (k : Rat) + 1 := by simp
  rw [ek] at v1
  have hne : (n : Rat) ≠ 0 := by grind
  have hr0 : 0 ≤ (n : Rat) * t - k := by
    have := Rat.mul_le_mul_of_nonneg_left ht0 (Rat.le_of_lt hnr)
    have e : (n : Rat) * ((k : Rat) / n) = k := by grind
    grind
  have hr1 : (n : Rat) * t - k ≤ 1 := by
    have := Rat.mul_le_mul_of_nonneg_left ht1 (Rat.le_of_lt hnr)
    have e : (n : Rat) * (((k : Rat) + 1) / n) = k + 1 := by grind
    grind
  have hl := lerp_near _ _ _ _ _ _ hr0 hr1 v0.symm v1.symm
  exact Near.trans hf hl

/-- `|z| ≤ M` from `z.natAbs ≤ M`, over `ℚ`. -/
private theorem natAbs_bound (z : Int) (M : Nat) (h : z.natAbs ≤ M) :
    -(M : Rat) ≤ (z : Rat) ∧ (z : Rat) ≤ M := by
  have hz1 : -(M : Int) ≤ z := by
    have := Int.le_natAbs (a := -z); rw [Int.natAbs_neg] at this; omega
  have hz2 : z ≤ (M : Int) := by have := Int.le_natAbs (a := z); omega
  have c1 : ((-(M : Int) : Int) : Rat) ≤ (z : Rat) := Rat.intCast_le_intCast.mpr hz1
  have c2 : (z : Rat) ≤ ((M : Int) : Rat) := Rat.intCast_le_intCast.mpr hz2
  simp only [Rat.intCast_neg, Rat.intCast_natCast] at c1 c2
  exact ⟨c1, c2⟩

/-- A second difference bounded by `Fill.flatness`, over `ℚ`. -/
private theorem dd2_bound (a b c : Int) (M : Nat) (h : dd2 a b c ≤ M) :
    -(M : Rat) ≤ (a : Rat) - 2 * b + c ∧ (a : Rat) - 2 * b + c ≤ M := by
  have e : ((a - 2 * b + c : Int) : Rat) = (a : Rat) - 2 * b + c := by
    simp only [Rat.intCast_add, Rat.intCast_sub, Rat.intCast_mul]; rfl
  rw [← e]; exact natAbs_bound _ _ h

/-- **Flattening within tolerance.** With the chord count `segCount` chooses (as `Fill.flatten`
does) and the cap condition `3·M ≤ 4·tol·cap²` (`Fill.segCount_tol_of_cap`), on every step
`k` the exact curve with the (integer) control points is within `tol + 1/2` subpixel units of
the implemented polyline, both coordinates. -/
theorem polyline_tol (cap tol : Nat) (hcap : 1 ≤ cap) (p0 p1 p2 p3 : FPt)
    (hc : 3 * flatness p0 p1 p2 p3 ≤ 4 * tol * (cap * cap)) (k : Nat)
    (hk : k < segCount cap (flatness p0 p1 p2 p3) tol) (t : Rat)
    (ht0 : (k : Rat) / (segCount cap (flatness p0 p1 p2 p3) tol : Nat) ≤ t)
    (ht1 : t ≤ ((k : Rat) + 1) / (segCount cap (flatness p0 p1 p2 p3) tol : Nat)) :
    Near (bez p0.x p1.x p2.x p3.x t)
        (lerp (bezAt (segCount cap (flatness p0 p1 p2 p3) tol) k p0 p1 p2 p3).x
          (bezAt (segCount cap (flatness p0 p1 p2 p3) tol) (k + 1) p0 p1 p2 p3).x
          ((segCount cap (flatness p0 p1 p2 p3) tol : Nat) * t - k))
        (tol + 1 / 2) ∧
      Near (bez p0.y p1.y p2.y p3.y t)
        (lerp (bezAt (segCount cap (flatness p0 p1 p2 p3) tol) k p0 p1 p2 p3).y
          (bezAt (segCount cap (flatness p0 p1 p2 p3) tol) (k + 1) p0 p1 p2 p3).y
          ((segCount cap (flatness p0 p1 p2 p3) tol : Nat) * t - k))
        (tol + 1 / 2) := by
  have hN := segCount_tol_of_cap cap (flatness p0 p1 p2 p3) tol hcap hc
  have hn : 0 < segCount cap (flatness p0 p1 p2 p3) tol :=
    (segCount_spec cap (flatness p0 p1 p2 p3) tol hcap).1
  generalize segCount cap (flatness p0 p1 p2 p3) tol = n at *
  have hfl : dd2 p0.x p1.x p2.x ≤ flatness p0 p1 p2 p3 ∧ dd2 p1.x p2.x p3.x ≤ flatness p0 p1 p2 p3 ∧
      dd2 p0.y p1.y p2.y ≤ flatness p0 p1 p2 p3 ∧ dd2 p1.y p2.y p3.y ≤ flatness p0 p1 p2 p3 := by
    simp only [flatness]; omega
  generalize flatness p0 p1 p2 p3 = M at *
  have hNr : 3 * (M : Rat) ≤ 4 * (tol : Rat) * ((n : Rat) * n) := by
    have := Rat.natCast_le_natCast.mpr hN
    simpa only [Rat.natCast_mul, Rat.natCast_ofNat] using this
  have ht := flatten_err_tol _ _ n hn hNr
  have ⟨x1, x1'⟩ := dd2_bound _ _ _ _ hfl.1
  have ⟨x2, x2'⟩ := dd2_bound _ _ _ _ hfl.2.1
  have ⟨y1, y1'⟩ := dd2_bound _ _ _ _ hfl.2.2.1
  have ⟨y2, y2'⟩ := dd2_bound _ _ _ _ hfl.2.2.2
  have hx := polyline_err n k hk p0.x p1.x p2.x p3.x _ t ht0 ht1 x1 x1' x2 x2'
  have hy := polyline_err n k hk p0.y p1.y p2.y p3.y _ t ht0 ht1 y1 y1' y2 y2'
  have hle : 3 * (M : Rat) / (4 * ((n : Rat) * n)) + 1 / 2 ≤ tol + 1 / 2 := by grind
  exact ⟨hx.mono hle, hy.mono hle⟩

/-- **Control-point rounding.** On `[0, 1]` the cubic is a convex combination of its control
values, so moving each control value by at most `ε` moves the curve by at most `ε`. -/
theorem bez_near (p0 p1 p2 p3 q0 q1 q2 q3 t ε : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h0 : Near p0 q0 ε) (h1 : Near p1 q1 ε) (h2 : Near p2 q2 ε) (h3 : Near p3 q3 ε) :
    Near (bez p0 p1 p2 p3 t) (bez q0 q1 q2 q3 t) ε := by
  have hs : 0 ≤ 1 - t := by grind
  have h3' : (0 : Rat) ≤ 3 := by decide
  have w0 : 0 ≤ (1 - t) * (1 - t) * (1 - t) := Rat.mul_nonneg (Rat.mul_nonneg hs hs) hs
  have w1 : 0 ≤ 3 * (1 - t) * (1 - t) * t :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg h3' hs) hs) ht0
  have w2 : 0 ≤ 3 * (1 - t) * t * t :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg h3' hs) ht0) ht0
  have w3 : 0 ≤ t * t * t := Rat.mul_nonneg (Rat.mul_nonneg ht0 ht0) ht0
  unfold Near at *
  have a0 := Rat.mul_le_mul_of_nonneg_left h0.1 w0
  have a0' := Rat.mul_le_mul_of_nonneg_left h0.2 w0
  have a1 := Rat.mul_le_mul_of_nonneg_left h1.1 w1
  have a1' := Rat.mul_le_mul_of_nonneg_left h1.2 w1
  have a2 := Rat.mul_le_mul_of_nonneg_left h2.1 w2
  have a2' := Rat.mul_le_mul_of_nonneg_left h2.2 w2
  have a3 := Rat.mul_le_mul_of_nonneg_left h3.1 w3
  have a3' := Rat.mul_le_mul_of_nonneg_left h3.2 w3
  simp only [bez]; constructor <;> grind

/-- **Device curve vs implemented polyline.** Let `c₀ … c₃` be the exact (ℚ, pixel) control
points of a device cubic and `p₀ … p₃` the subpixel control points the renderer uses, each
coordinate within `1/2` of `256·cᵢ` (`toSub_err`, `ofPt_near`). Under the cap condition, on
every step `k` the exact curve (in subpixel units) is within `tol + 1` of the implemented
polyline, both coordinates. -/
theorem device_curve_err (cap tol : Nat) (hcap : 1 ≤ cap) (c0 c1 c2 c3 : Pt) (p0 p1 p2 p3 : FPt)
    (hx0 : Near (p0.x : Rat) (256 * c0.x) (1 / 2)) (hx1 : Near (p1.x : Rat) (256 * c1.x) (1 / 2))
    (hx2 : Near (p2.x : Rat) (256 * c2.x) (1 / 2)) (hx3 : Near (p3.x : Rat) (256 * c3.x) (1 / 2))
    (hy0 : Near (p0.y : Rat) (256 * c0.y) (1 / 2)) (hy1 : Near (p1.y : Rat) (256 * c1.y) (1 / 2))
    (hy2 : Near (p2.y : Rat) (256 * c2.y) (1 / 2)) (hy3 : Near (p3.y : Rat) (256 * c3.y) (1 / 2))
    (hc : 3 * flatness p0 p1 p2 p3 ≤ 4 * tol * (cap * cap)) (k : Nat)
    (hk : k < segCount cap (flatness p0 p1 p2 p3) tol) (t : Rat)
    (ht0 : (k : Rat) / (segCount cap (flatness p0 p1 p2 p3) tol : Nat) ≤ t)
    (ht1 : t ≤ ((k : Rat) + 1) / (segCount cap (flatness p0 p1 p2 p3) tol : Nat)) :
    Near (256 * bez c0.x c1.x c2.x c3.x t)
        (lerp (bezAt (segCount cap (flatness p0 p1 p2 p3) tol) k p0 p1 p2 p3).x
          (bezAt (segCount cap (flatness p0 p1 p2 p3) tol) (k + 1) p0 p1 p2 p3).x
          ((segCount cap (flatness p0 p1 p2 p3) tol : Nat) * t - k)) (tol + 1) ∧
      Near (256 * bez c0.y c1.y c2.y c3.y t)
        (lerp (bezAt (segCount cap (flatness p0 p1 p2 p3) tol) k p0 p1 p2 p3).y
          (bezAt (segCount cap (flatness p0 p1 p2 p3) tol) (k + 1) p0 p1 p2 p3).y
          ((segCount cap (flatness p0 p1 p2 p3) tol : Nat) * t - k)) (tol + 1) := by
  have ⟨px, py⟩ := polyline_tol cap tol hcap p0 p1 p2 p3 hc k hk t ht0 ht1
  generalize segCount cap (flatness p0 p1 p2 p3) tol = n at *
  have hnr : (0 : Rat) < n := by
    have : ((0 : Nat) : Rat) < ((n : Nat) : Rat) := Rat.natCast_lt_natCast.mpr (by omega)
    simpa using this
  have hk0 : (0 : Rat) ≤ k := by
    have : ((0 : Nat) : Rat) ≤ ((k : Nat) : Rat) := Rat.natCast_le_natCast.mpr (by omega)
    simpa using this
  have hkn : (k : Rat) + 1 ≤ n := by
    have : ((k + 1 : Nat) : Rat) ≤ ((n : Nat) : Rat) := Rat.natCast_le_natCast.mpr (by omega)
    simpa using this
  have t0 : 0 ≤ t := by
    have : (0 : Rat) ≤ (k : Rat) / n := by
      rw [Rat.div_def]; exact Rat.mul_nonneg hk0 (Rat.le_of_lt (Rat.inv_pos.mpr hnr))
    grind
  have t1 : t ≤ 1 := by
    have : ((k : Rat) + 1) / n ≤ 1 := by
      apply Rat.not_lt.mp; rw [Rat.lt_div_iff hnr]; grind
    grind
  have sx : 256 * bez c0.x c1.x c2.x c3.x t =
      bez (256 * c0.x) (256 * c1.x) (256 * c2.x) (256 * c3.x) t := by
    simp only [bez]; grind
  have sy : 256 * bez c0.y c1.y c2.y c3.y t =
      bez (256 * c0.y) (256 * c1.y) (256 * c2.y) (256 * c3.y) t := by
    simp only [bez]; grind
  have bx := bez_near _ _ _ _ _ _ _ _ t _ t0 t1 hx0 hx1 hx2 hx3
  have by' := bez_near _ _ _ _ _ _ _ _ t _ t0 t1 hy0 hy1 hy2 hy3
  have e : (1 / 2 : Rat) + (tol + 1 / 2) = tol + 1 := by grind
  rw [sx, sy]
  refine ⟨?_, ?_⟩
  · have := Near.trans bx.symm px; rw [e] at this; exact this
  · have := Near.trans by'.symm py; rw [e] at this; exact this

/-- `FPt.ofPt` without clamping is `toSub` per coordinate, so `toSub_err` gives the
hypotheses of `device_curve_err`. -/
theorem ofPt_near (p : Pt) (lim : Int) (hx : -lim ≤ toSub p.x ∧ toSub p.x ≤ lim)
    (hy : -lim ≤ toSub p.y ∧ toSub p.y ≤ lim) :
    Near ((FPt.ofPt p lim).x : Rat) (256 * p.x) (1 / 2) ∧
      Near ((FPt.ofPt p lim).y : Rat) (256 * p.y) (1 / 2) := by
  have ex : (FPt.ofPt p lim).x = toSub p.x := by
    simp only [FPt.ofPt, clampCoord]; omega
  have ey : (FPt.ofPt p lim).y = toSub p.y := by
    simp only [FPt.ofPt, clampCoord]; omega
  have a := toSub_err p.x
  have b := toSub_err p.y
  rw [ex, ey]
  unfold Near at *
  exact ⟨⟨by grind, by grind⟩, ⟨by grind, by grind⟩⟩

/-! ## Shading function arithmetic -/

/-- **One rounding step of function arithmetic** (`Shading.qd`, used after every operation
of `Fn.eval`): within the saturation range `±2⁴⁰`, `qd x` is within `2⁻²⁵` of `x`. (A
bound for a whole function evaluation would compose these per operation; not done here.) -/
theorem qd_err (x : Rat) (hlo : -Raster.Shading.qMax ≤ x) (hhi : x ≤ Raster.Shading.qMax) :
    Near (Raster.Shading.qd x) x (1 / 33554432) := by
  have hc : (if Raster.Shading.qMax < x then Raster.Shading.qMax
      else if x < -Raster.Shading.qMax then -Raster.Shading.qMax else x) = x := by
    split
    · grind
    · split
      · grind
      · rfl
  simp only [Raster.Shading.qd, hc, Raster.Shading.qScale]
  have f1 := Rat.floor_le (x * ((16777216 : Int) : Rat) + 1 / 2)
  have f2 := Rat.lt_floor_add_one (x * ((16777216 : Int) : Rat) + 1 / 2)
  generalize (x * ((16777216 : Int) : Rat) + 1 / 2).floor = F at *
  simp only [Rat.intCast_add, Rat.intCast_one] at f2
  have hS : ((16777216 : Int) : Rat) = 16777216 := rfl
  rw [hS] at f1 f2 ⊢
  unfold Near; constructor <;> grind

end SafePdf.Spec.RasterError
