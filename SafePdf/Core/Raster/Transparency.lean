import SafePdf.Core.Raster.Clip

/-!
# Transparency: blend modes, transparency groups, soft masks (task 7.3c)

Plan.md §6 Phase 7 ("soft masks + transparency groups + shadings (Tier 1 — matplotlib needs
them)"; "Proven: totality, resource bounds"). ISO 32000-2 §11 (transparency): §11.3.5 (blend
modes), §11.3.7 (shape and opacity), §11.4.7 / §11.6.6 (transparency groups), §11.5 / §11.6.5
(soft masks).

## What the display list gives us (task 7.3c in `Core.Content`)

Every fill/stroke snapshot carries a blend mode and a soft-mask reference
(`FillStyle.blend`/`.smask`, also in glyph runs and images); a soft mask is defined by a nested
`DisplayItem.softMask id info items` item; a transparency group is bracketed by `groupBegin g`
… `groupEnd`.

## Model: every buffer is an opaque page-size RGBA buffer

The page renderer (`Clip`, `Glyph`, `Image`) composites onto an **opaque** RGBA buffer of the
page size. Rather than teaching every painter about alpha, transparency here only ever uses
buffers of the same shape (`4 · W · H` bytes, opaque), so all existing painters work unchanged
on them; each construct is "save the backdrop `B`, paint into a scratch buffer `R`, combine":

* **Layers** (`beginLayer` / `endLayer`, stack `TxState.stack`): `beginLayer` saves `B` and
  starts the scratch buffer as a copy of `B` (blend mode `Normal`; a persistent `ByteArray`,
  so the copy happens on the first write) or, for a separable non-`Normal` blend mode, as a
  buffer filled with the mode's **neutral** source value `n` (`neutral`: `B(cb, n) = cb`, e.g.
  white for `Multiply`, black for `Screen`, 128 for `Overlay`/`HardLight`/`SoftLight`, within
  one byte). `endLayer` combines per pixel with factor `f = alpha · mask / 255`:
  - `Normal`: `out = lerp(B, R, f)`. **Exact** for everything painted with `Normal` inside: a
    group's result over an opaque backdrop is `R = (1 − αg)·B + αg·C`, and compositing the
    group with opacity `f` gives `(1 − f·αg)·B + f·αg·C = lerp(B, R, f)`.
  - other modes: `out = lerp(B, Blend(B, R), f)` with `R` the content over the neutral colour
    (`R = (1 − αg)·n + αg·C`). Exact where the content is opaque or absent (`αg ∈ {0, 1}`) and,
    for modes affine in the source (`Multiply`, `Screen`, `Exclusion`), everywhere; elsewhere
    (anti-aliased edges, translucent content) the error is that of applying `Blend` to the
    pre-mixed colour. The non-separable modes start from a copy of `B` (`Blend(B, B) = B`
    for all four).
* **Painting items with a blend mode or soft mask** (`itemFx`): one layer around the item
  (alpha 255, the item's own alpha and coverage are applied by its painter). With a soft mask
  `M` and `Normal`, `lerp(B, R, M)` with `R = (1 − a)·B + a·C` is `(1 − M·a)·B + M·a·C`:
  **exact** (§11.6.5.1: the mask multiplies the item's shape × opacity).
* **Transparency groups** (`beginGroup`): one layer, alpha `ca` at the `Do`, the group's blend
  mode and soft mask. A group with alpha 1, `Normal` and no mask is painted directly (a
  `.skipped` frame): without knockout this is exact. So overlapping items of a group with
  alpha 0.5 are composited **once** (no double darkening). Approximations: **isolated** groups
  whose content itself uses non-`Normal` blend modes blend that content with the page
  instead of with transparent black (non-isolated semantics; exact for `Normal` content);
  **knockout** (`/K`) is ignored (items composite over each other, not over the group's
  initial backdrop); the group colour space `/CS` is ignored (device RGB).
* **Soft masks** (`maskFrom`): the mask group's items are drawn into a fresh buffer, then
  - `/Luminosity`: backdrop = `/BC` (opaque), mask = `Y = round((30 R + 59 G + 11 B) / 100)`
    of the result (§11.5.3, the 0.30/0.59/0.11 weights of `Lum`);
  - `/Alpha`: drawn twice, over black (`R₀ = α·C`) and over white (`R₁ = 1 − α + α·C`),
    `α = 255 − (ΣR₁ − ΣR₀)/3` (8-bit rounding: ±1);
  outside the mask group's `/BBox` (its items are clipped to it) this yields `Y(BC)`
  (luminosity) and 0 (alpha), as §11.6.5.2 requires. `/TR` is ignored (identity).
  Masks are stored by identifier in `TxState.masks` (at most `maxMasks`, most recent first;
  a mask that was evicted or never defined is ignored: the item paints unmasked).

## Arithmetic (§11.3.5, bytes `0 … 255` standing for `0 … 1`)

`blendSep` evaluates the separable formulas in integers with round-half-up divisions
(`mul255 a b = round(a·b/255)`):
`Multiply = mul255 cb cs`; `Screen = cb + cs − mul255 cb cs`; `HardLight` =
`mul255 cb (2cs)` if `cs ≤ 127`, else `Screen(cb, 2cs − 255)`; `Overlay(cb, cs) =
HardLight(cs, cb)`; `Darken`/`Lighten` = `min`/`max`; `ColorDodge` = 0 if `cb = 0`, 255 if
`cs = 255`, else `min(255, round(255·cb/(255 − cs)))`; `ColorBurn` = 255 if `cb = 255`, 0 if
`cs = 0`, else `255 − min(255, round(255·(255 − cb)/cs))`; `SoftLight` with
`D(x) = ((16x − 12)x + 4)x` for `x ≤ 1/4` (exact rational, rounded once) else `√x` (integer
square root of `255·cb`, rounded to nearest); `Difference = |cb − cs|`;
`Exclusion = cb + cs − 2·mul255 cb cs`. Every result is clamped to 255 (`blendSep_le`), so
the byte bound holds by construction. The non-separable modes (`Hue`, `Saturation`, `Color`,
`Luminosity`) follow §11.3.5.3 (`Lum`, `ClipColor`, `SetLum`, `Sat`, `SetSat`) exactly over
`ℚ`, rounded once per channel (`blendRGB_le`).

## Bounds

* At most `maxLayerDepth` (8) layers are open at once (`beginLayer_open_le`): each holds one
  saved page buffer, so offscreen memory is `≤ 8 · 4 · W · H` bytes plus `maxMasks` (8) masks of
  `W · H` bytes (`addMask_length_le`). Deeper layers are `.skipped` (painted directly, the
  layer's alpha/blend/mask ignored — documented degradation, never an error).
* Soft-mask nesting (a mask group whose content sets another mask) is bounded by the fuel of
  `renderTx` (`maxMaskDepth`, 4; deeper mask definitions are ignored).
* Buffer sizes: `combine_size`, `beginLayer_size`, `endLayer_size`, `maskFrom_size`, and for the
  driver `renderTx_inv` (a page buffer of `4 · W · H` bytes stays so, given a painter that
  preserves sizes). The combine pass is `O(W · H)` per layer.

## Wiring

`renderTx P W H fuel` is the transparency driver over any renderer state `S` given a
`Painter S` (lenses to the page buffer and the `TxState`, and the plain item painter, e.g.
`Glyph.renderItemG`); see the task report for the exact `Glyph` change.
-/

namespace SafePdf.Core.Raster.Transparency

open SafePdf.Core
open SafePdf.Core.Raster.Fill (IRect)
open SafePdf.Core.Raster.Clip (mul255 getB setB setB_size compByte deviceRGB)
open SafePdf.Core.Content (BlendMode Comp Color DisplayItem GroupInfo SoftMaskInfo SoftMaskKind)

/-! ## 1. Separable blend modes on bytes -/

/-- `Screen` on bytes: `cb + cs − round(cb·cs/255)`. -/
def screenB (cb cs : Nat) : Nat := cb + cs - mul255 cb cs

/-- `HardLight` on bytes (§11.3.5.2). -/
def hardLightB (cb cs : Nat) : Nat :=
  if cs ≤ 127 then mul255 cb (2 * cs) else screenB cb (2 * cs - 255)

/-- `round(√n)`: the integer square root, rounded to nearest. -/
def roundSqrt (n : Nat) : Nat :=
  let r := Nat.sqrt n
  if n - r * r > r then r + 1 else r

/-- `255 · D(cb/255)` of `SoftLight` (§11.3.5.2): the cubic for `cb ≤ 63` (exact rational,
rounded once), else `round(√(255·cb))`. -/
def softD (cb : Nat) : Nat :=
  if 4 * cb ≤ 255 then (cb * (16 * cb * cb + 260100 - 3060 * cb) + 32512) / 65025
  else roundSqrt (cb * 255)

/-- `SoftLight` on bytes (§11.3.5.2). -/
def softLightB (cb cs : Nat) : Nat :=
  if cs ≤ 127 then cb - ((255 - 2 * cs) * cb * (255 - cb) + 32512) / 65025
  else cb + ((2 * cs - 255) * (softD cb - cb) + 127) / 255

/-- `ColorDodge` on bytes (ISO 32000-2 form: 0 on a black backdrop). -/
def dodgeB (cb cs : Nat) : Nat :=
  if cb = 0 then 0 else if 255 ≤ cs then 255
  else min 255 ((cb * 255 + (255 - cs) / 2) / (255 - cs))

/-- `ColorBurn` on bytes (ISO 32000-2 form: 255 on a white backdrop). -/
def burnB (cb cs : Nat) : Nat :=
  if 255 ≤ cb then 255 else if cs = 0 then 0
  else 255 - min 255 (((255 - cb) * 255 + cs / 2) / cs)

/-- The unclamped separable blend function `B(cb, cs)` on bytes (non-separable modes: `cs`). -/
def blendRaw : BlendMode → Nat → Nat → Nat
  | .normal, _, cs => cs
  | .multiply, cb, cs => mul255 cb cs
  | .screen, cb, cs => screenB cb cs
  | .overlay, cb, cs => hardLightB cs cb
  | .darken, cb, cs => min cb cs
  | .lighten, cb, cs => max cb cs
  | .colorDodge, cb, cs => dodgeB cb cs
  | .colorBurn, cb, cs => burnB cb cs
  | .hardLight, cb, cs => hardLightB cb cs
  | .softLight, cb, cs => softLightB cb cs
  | .difference, cb, cs => if cb ≤ cs then cs - cb else cb - cs
  | .exclusion, cb, cs => cb + cs - 2 * mul255 cb cs
  | _, _, cs => cs

/-- **Separable blend** of backdrop byte `cb` and source byte `cs`, clamped to a byte. -/
def blendSep (m : BlendMode) (cb cs : Nat) : Nat := min 255 (blendRaw m cb cs)

/-- Blend results are bytes. -/
theorem blendSep_le (m : BlendMode) (cb cs : Nat) : blendSep m cb cs ≤ 255 :=
  Nat.min_le_left _ _

/-- `Normal` returns the source. -/
theorem blendSep_normal (cb cs : Nat) (h : cs ≤ 255) : blendSep .normal cb cs = cs := by
  simp [blendSep, blendRaw]; omega

/-- The neutral source byte of a separable mode: `B(cb, neutral m) = cb` (within one byte for
`Overlay`/`HardLight`/`SoftLight`, whose exact neutral 127.5 is not a byte; tested). -/
def neutral : BlendMode → Nat
  | .multiply | .darken | .colorBurn => 255
  | .overlay | .hardLight | .softLight => 128
  | _ => 0

/-! ## 2. Non-separable blend modes (§11.3.5.3), exact over ℚ -/

/-- An RGB triple over ℚ, components in `0 … 255`. -/
abbrev QRGB := Rat × Rat × Rat

/-- `Lum(C) = 0.3 R + 0.59 G + 0.11 B`. -/
def lum (c : QRGB) : Rat := (30 * c.1 + 59 * c.2.1 + 11 * c.2.2) / 100

/-- Smallest component. -/
def cmin (c : QRGB) : Rat := min c.1 (min c.2.1 c.2.2)

/-- Largest component. -/
def cmax (c : QRGB) : Rat := max c.1 (max c.2.1 c.2.2)

/-- Map each component. -/
def cmap (f : Rat → Rat) (c : QRGB) : QRGB := (f c.1, f c.2.1, f c.2.2)

/-- `ClipColor` (§11.3.5.3), with 255 standing for 1. -/
def clipColor (c : QRGB) : QRGB :=
  let l := lum c
  let n := cmin c
  let x := cmax c
  let c := if n < 0 ∧ l - n ≠ 0 then cmap (fun v => l + (v - l) * l / (l - n)) c else c
  if 255 < x ∧ x - l ≠ 0 then cmap (fun v => l + (v - l) * (255 - l) / (x - l)) c else c

/-- `SetLum(C, l)`. -/
def setLum (c : QRGB) (l : Rat) : QRGB := clipColor (cmap (· + (l - lum c)) c)

/-- `Sat(C) = max − min`. -/
def sat (c : QRGB) : Rat := cmax c - cmin c

/-- `SetSat(C, s)`: the largest component becomes `s`, the smallest 0, the middle one scaled
proportionally (all 0 for a grey `C`). -/
def setSat (c : QRGB) (s : Rat) : QRGB :=
  let mx := cmax c
  let mn := cmin c
  if mn < mx then cmap (fun v => (v - mn) * s / (mx - mn)) c else (0, 0, 0)

/-- A ℚ component in `0 … 255` rounded to a byte (clamped). -/
def toByte (q : Rat) : Nat := min 255 (q + 1 / 2).floor.toNat

/-- A byte triple as ℚ. -/
def toQ (c : Nat × Nat × Nat) : QRGB := ((c.1 : Rat), (c.2.1 : Rat), (c.2.2 : Rat))

/-- The non-separable blend functions. -/
def blendNonSep (m : BlendMode) (cb cs : QRGB) : QRGB :=
  match m with
  | .hue => setLum (setSat cs (sat cb)) (lum cb)
  | .saturation => setLum (setSat cb (sat cs)) (lum cb)
  | .color => setLum cs (lum cb)
  | .luminosity => setLum cb (lum cs)
  | _ => cs

/-- **Blend an RGB pixel**: backdrop `cb`, source `cs` (bytes) → bytes. -/
def blendRGB (m : BlendMode) (cb cs : Nat × Nat × Nat) : Nat × Nat × Nat :=
  if m.separable then (blendSep m cb.1 cs.1, blendSep m cb.2.1 cs.2.1, blendSep m cb.2.2 cs.2.2)
  else
    let r := blendNonSep m (toQ cb) (toQ cs)
    (toByte r.1, toByte r.2.1, toByte r.2.2)

/-- Every channel of a blended pixel is a byte. -/
theorem blendRGB_le (m : BlendMode) (cb cs : Nat × Nat × Nat) :
    (blendRGB m cb cs).1 ≤ 255 ∧ (blendRGB m cb cs).2.1 ≤ 255 ∧ (blendRGB m cb cs).2.2 ≤ 255 := by
  unfold blendRGB toByte
  split
  · exact ⟨blendSep_le _ _ _, blendSep_le _ _ _, blendSep_le _ _ _⟩
  · exact ⟨Nat.min_le_left _ _, Nat.min_le_left _ _, Nat.min_le_left _ _⟩

/-! ## 3. Combining a layer with its backdrop -/

/-- How a layer is composited onto its backdrop: constant alpha (byte), blend mode, soft mask
(`W · H` coverage bytes, row-major; `none` = 255 everywhere). -/
structure Fx where
  /-- Constant alpha, `0 … 255`. -/
  alpha : Nat := 255
  /-- Blend mode. -/
  blend : BlendMode := .normal
  /-- Soft mask bytes. -/
  mask : Option ByteArray := none

/-- RGB bytes of pixel `i` of an RGBA buffer. -/
@[inline] def px (b : ByteArray) (i : Nat) : Nat × Nat × Nat :=
  (getB b (4 * i), getB b (4 * i + 1), getB b (4 * i + 2))

/-- The mask byte of pixel `i` (255 without a mask). -/
def maskByte (fx : Fx) (i : Nat) : Nat :=
  match fx.mask with
  | some mk => getB mk i
  | none => 255

/-- Combine pixel `i` of layer `cur` into `b` (the backdrop being rewritten). -/
def combinePx (cur : ByteArray) (fx : Fx) (i : Nat) (b : ByteArray) : ByteArray :=
  let f := mul255 fx.alpha (maskByte fx i)
  if f = 0 then b else
  let cb := px b i
  let cs := px cur i
  if fx.blend = .normal ∧ cs = cb then b else
  let res := if fx.blend = .normal then cs else blendRGB fx.blend cb cs
  let o := 4 * i
  let b := setB b o (Clip.blend res.1 cb.1 f)
  let b := setB b (o + 1) (Clip.blend res.2.1 cb.2.1 f)
  setB b (o + 2) (Clip.blend res.2.2 cb.2.2 f)

/-- `combinePx` preserves the size. -/
theorem combinePx_size (cur : ByteArray) (fx : Fx) (i : Nat) (b : ByteArray) :
    (combinePx cur fx i b).size = b.size := by
  unfold combinePx
  dsimp only
  repeat' split
  all_goals simp only [setB_size]

/-- `n` pixels from index `i`. -/
def span (cur : ByteArray) (fx : Fx) : (n i : Nat) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, i, b => span cur fx n (i + 1) (combinePx cur fx i b)

/-- `span` preserves the size. -/
theorem span_size (cur : ByteArray) (fx : Fx) (n i : Nat) (b : ByteArray) :
    (span cur fx n i b).size = b.size := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [span, ih, combinePx_size]

/-- Rows `y, y + 1, …` (`n` of them), columns `[x0, x0 + cw)`, of a width-`W` buffer. -/
def spans (W : Nat) (cur : ByteArray) (fx : Fx) (x0 cw : Nat) : (n y : Nat) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, y, b => spans W cur fx x0 cw n (y + 1) (span cur fx cw (y * W + x0) b)

/-- `spans` preserves the size. -/
theorem spans_size (W : Nat) (cur : ByteArray) (fx : Fx) (x0 cw n y : Nat) (b : ByteArray) :
    (spans W cur fx x0 cw n y b).size = b.size := by
  induction n generalizing y b with
  | zero => rfl
  | succ n ih => simp only [spans, ih, span_size]

/-- **Combine** layer `cur` onto backdrop `back` (both `W × H` RGBA) over the rectangle `r`
(clamped to the page): per pixel `out = lerp(cb, Blend(cb, cs), alpha · mask)`. Outside `r`,
and when the sizes differ, the backdrop is returned. -/
def combine (W H : Nat) (r : IRect) (back cur : ByteArray) (fx : Fx) : ByteArray :=
  if cur.size = back.size then
    let x0 := (max r.x0 0).toNat
    let x1 := (min r.x1 W).toNat
    let y0 := (max r.y0 0).toNat
    let y1 := (min r.y1 H).toNat
    spans W cur fx x0 (x1 - x0) (y1 - y0) y0 back
  else back

/-- Combining keeps the backdrop's size. -/
theorem combine_size (W H : Nat) (r : IRect) (back cur : ByteArray) (fx : Fx) :
    (combine W H r back cur fx).size = back.size := by
  unfold combine; split
  · exact spans_size _ _ _ _ _ _ _ _
  · rfl

/-! ## 4. Layer stack and masks -/

/-- Maximum number of open layers (each holds one saved page buffer). -/
def maxLayerDepth : Nat := 8

/-- Maximum number of soft masks kept (each `W · H` bytes). -/
def maxMasks : Nat := 8

/-- Maximum nesting of soft-mask definitions (the fuel of `renderTx`). -/
def maxMaskDepth : Nat := 4

/-- One frame of the layer stack. -/
inductive Layer where
  /-- An open layer: the saved backdrop and how to combine onto it. -/
  | opened (back : ByteArray) (fx : Fx)
  /-- A layer painted directly (trivial group, or beyond `maxLayerDepth`). -/
  | skipped

/-- Transparency state of a page render. -/
structure TxState where
  /-- Open layers, innermost first. -/
  stack : List Layer := []
  /-- Soft masks by identifier, most recent first. -/
  masks : List (Nat × ByteArray) := []

/-- Number of open (buffer-holding) layers. -/
def openCount : List Layer → Nat
  | [] => 0
  | .opened .. :: rest => openCount rest + 1
  | .skipped :: rest => openCount rest

/-- A layer's saved backdrop has the page size (or there is none). -/
def Layer.Ok (W H : Nat) : Layer → Prop
  | .opened back _ => back.size = 4 * W * H
  | .skipped => True

/-- Every saved backdrop has the page size. -/
def TxState.Sized (W H : Nat) (t : TxState) : Prop := ∀ l ∈ t.stack, l.Ok W H

/-- The soft mask `id`, if kept. -/
def TxState.mask? (t : TxState) (id : Nat) : Option ByteArray :=
  (t.masks.find? (·.1 = id)).map (·.2)

/-- Keep soft mask `id` (newest first, at most `maxMasks`). -/
def TxState.addMask (t : TxState) (id : Nat) (m : ByteArray) : TxState :=
  { t with masks := ((id, m) :: t.masks).take maxMasks }

/-- At most `maxMasks` masks are kept. -/
theorem addMask_length_le (t : TxState) (id : Nat) (m : ByteArray) :
    (t.addMask id m).masks.length ≤ maxMasks := by
  simp only [TxState.addMask, List.length_take]
  exact Nat.min_le_left _ _

/-- A buffer of `W · H` pixels, every byte `v`. -/
def fillBuf (W H v : Nat) : ByteArray := ByteArray.mk (Array.replicate (4 * W * H) (UInt8.ofNat v))

/-- `fillBuf` has the page size. -/
theorem fillBuf_size (W H v : Nat) : (fillBuf W H v).size = 4 * W * H := by
  simp [fillBuf, ByteArray.size]

/-- **Open a layer** over `buf`: save it; the scratch buffer is `buf` itself (`Normal`,
non-separable modes) or the neutral colour (separable modes). Beyond `maxLayerDepth` the
frame is `.skipped` and `buf` is painted directly. -/
def beginLayer (W H : Nat) (t : TxState) (buf : ByteArray) (fx : Fx) : TxState × ByteArray :=
  if openCount t.stack < maxLayerDepth then
    let cur := if fx.blend ≠ .normal ∧ fx.blend.separable then fillBuf W H (neutral fx.blend)
      else buf
    ({ t with stack := .opened buf fx :: t.stack }, cur)
  else ({ t with stack := .skipped :: t.stack }, buf)

/-- **Close the innermost layer**: combine it onto its saved backdrop over `r`. An empty
stack (unbalanced end) and a skipped frame leave the buffer as it is. -/
def endLayer (W H : Nat) (r : IRect) (t : TxState) (buf : ByteArray) : TxState × ByteArray :=
  match t.stack with
  | [] => (t, buf)
  | .skipped :: rest => ({ t with stack := rest }, buf)
  | .opened back fx :: rest => ({ t with stack := rest }, combine W H r back buf fx)

/-- Open layers stay within `maxLayerDepth`. -/
theorem beginLayer_open_le (W H : Nat) (t : TxState) (buf : ByteArray) (fx : Fx)
    (h : openCount t.stack ≤ maxLayerDepth) :
    openCount (beginLayer W H t buf fx).1.stack ≤ maxLayerDepth := by
  unfold beginLayer
  split
  · simp only [openCount]; omega
  · simp only [openCount]; exact h

/-- Opening a layer keeps the page size and the `Sized` invariant. -/
theorem beginLayer_size (W H : Nat) (t : TxState) (buf : ByteArray) (fx : Fx)
    (hb : buf.size = 4 * W * H) (ht : t.Sized W H) :
    (beginLayer W H t buf fx).2.size = 4 * W * H ∧ (beginLayer W H t buf fx).1.Sized W H := by
  unfold beginLayer
  split
  · refine ⟨?_, ?_⟩
    · simp only; split
      · exact fillBuf_size _ _ _
      · exact hb
    · intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hb
      · exact ht l hl
  · refine ⟨hb, ?_⟩
    intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · trivial
    · exact ht l hl

/-- Closing a layer keeps the page size and the `Sized` invariant. -/
theorem endLayer_size (W H : Nat) (r : IRect) (t : TxState) (buf : ByteArray)
    (hb : buf.size = 4 * W * H) (ht : t.Sized W H) :
    (endLayer W H r t buf).2.size = 4 * W * H ∧ (endLayer W H r t buf).1.Sized W H := by
  unfold endLayer
  split
  · exact ⟨hb, ht⟩
  · rename_i rest heq
    refine ⟨hb, fun l hl => ht l ?_⟩
    simp [heq, hl]
  · rename_i back fx rest heq
    have hback : back.size = 4 * W * H := ht (.opened back fx) (by simp [heq])
    refine ⟨by rw [combine_size]; exact hback, fun l hl => ht l ?_⟩
    simp [heq, hl]

/-- A transparency group's layer: alpha `ca`, blend mode and soft mask of the group. A group
with alpha 1, `Normal` and no (kept) mask is painted directly (`.skipped`; exact without
knockout). -/
def beginGroup (W H : Nat) (t : TxState) (buf : ByteArray) (g : GroupInfo) : TxState × ByteArray :=
  let fx : Fx := { alpha := compByte g.alpha, blend := g.blend, mask := g.smask.bind t.mask? }
  if fx.alpha = 255 ∧ fx.blend = .normal ∧ fx.mask.isNone then
    ({ t with stack := .skipped :: t.stack }, buf)
  else beginLayer W H t buf fx

/-- Opening a group keeps the page size and the `Sized` invariant. -/
theorem beginGroup_size (W H : Nat) (t : TxState) (buf : ByteArray) (g : GroupInfo)
    (hb : buf.size = 4 * W * H) (ht : t.Sized W H) :
    (beginGroup W H t buf g).2.size = 4 * W * H ∧ (beginGroup W H t buf g).1.Sized W H := by
  unfold beginGroup
  simp only
  split
  · refine ⟨hb, ?_⟩
    intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · trivial
    · exact ht l hl
  · exact beginLayer_size W H t buf _ hb ht

/-- The layer effect of a painting item: its blend mode and (kept) soft mask; `none` when it
paints plainly. -/
def styleFx (t : TxState) (blend : BlendMode) (smask : Option Nat) : Option Fx :=
  let mk := smask.bind t.mask?
  if blend = .normal ∧ mk.isNone then none else some { blend, mask := mk }

/-- The layer effect of a display item (fills, strokes, glyph runs, images). -/
def itemFx (t : TxState) : DisplayItem → Option Fx
  | .fillPath _ _ st _ => styleFx t st.blend st.smask
  | .strokePath _ st _ => styleFx t st.blend st.smask
  | .glyphRun r _ => styleFx t r.fill.blend r.fill.smask
  | .image _ _ f _ => styleFx t f.blend f.smask
  | _ => none

/-! ## 5. Soft masks -/

/-- A buffer of `W · H` opaque pixels of colour `rgb`. -/
def solidBuf (W H : Nat) (rgb : Nat × Nat × Nat) : ByteArray :=
  let go : Nat → ByteArray → ByteArray := fun n b =>
    n.fold (fun _ _ b => ((b.push (UInt8.ofNat rgb.1)).push (UInt8.ofNat rgb.2.1)).push
      (UInt8.ofNat rgb.2.2) |>.push 255) b
  go (W * H) (ByteArray.emptyWithCapacity (4 * W * H))

/-- Luminosity of an RGB byte triple: `round((30 R + 59 G + 11 B) / 100)`. -/
def lumByte (c : Nat × Nat × Nat) : Nat := min 255 ((30 * c.1 + 59 * c.2.1 + 11 * c.2.2 + 50) / 100)

/-- `n` mask bytes from pixel `i` on, each `f i`. -/
def tabulate (f : Nat → Nat) : (n i : Nat) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, i, b => tabulate f n (i + 1) (b.push (UInt8.ofNat (f i)))

/-- `tabulate` appends exactly `n` bytes. -/
theorem tabulate_size (f : Nat → Nat) (n i : Nat) (b : ByteArray) :
    (tabulate f n i b).size = b.size + n := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [tabulate, ih, ByteArray.size_push]; omega

/-- Luminosity mask of a rendered buffer (`W · H` bytes). -/
def lumMask (W H : Nat) (r : ByteArray) : ByteArray :=
  tabulate (fun i => lumByte (px r i)) (W * H) 0 ByteArray.empty

/-- Alpha mask from renders over black (`r0`) and white (`r1`): `255 − (ΣR₁ − ΣR₀)/3`. -/
def alphaMask (W H : Nat) (r0 r1 : ByteArray) : ByteArray :=
  tabulate (fun i =>
    let a := px r0 i
    let b := px r1 i
    255 - min 255 ((b.1 + b.2.1 + b.2.2 - (a.1 + a.2.1 + a.2.2) + 1) / 3)) (W * H) 0
    ByteArray.empty

/-- **The soft mask** of `info`, given `draw` (render the mask group's items onto a backdrop
buffer): luminosity over `/BC`, or alpha from two renders. `W · H` bytes. -/
def maskFrom (info : SoftMaskInfo) (W H : Nat) (draw : ByteArray → ByteArray) : ByteArray :=
  match info.kind with
  | .luminosity => lumMask W H (draw (solidBuf W H (deviceRGB info.backdrop)))
  | .alpha => alphaMask W H (draw (fillBuf W H 0)) (draw (fillBuf W H 255))

/-- A soft mask has one byte per pixel. -/
theorem maskFrom_size (info : SoftMaskInfo) (W H : Nat) (draw : ByteArray → ByteArray) :
    (maskFrom info W H draw).size = W * H := by
  unfold maskFrom lumMask alphaMask
  split <;> (rw [tabulate_size]; show 0 + W * H = W * H; omega)

/-! ## 6. The driver -/

/-- A renderer state `S` seen by the transparency driver: the page buffer, the `TxState`, and
the plain painter of one item (which ignores transparency items). -/
structure Painter (S : Type) where
  /-- Current page (or layer) buffer. -/
  buf : S → ByteArray
  /-- Replace the buffer. -/
  setBuf : S → ByteArray → S
  /-- Transparency state. -/
  tx : S → TxState
  /-- Replace the transparency state. -/
  setTx : S → TxState → S
  /-- Paint one item plainly (e.g. `Glyph.renderItemG`). -/
  paint : S → DisplayItem → S

/-- The laws `renderTx_inv` needs: lenses behave, painting keeps the buffer size and the
transparency state. -/
structure Painter.Lawful {S : Type} (P : Painter S) : Prop where
  /-- Get after set. -/
  buf_setBuf : ∀ s b, P.buf (P.setBuf s b) = b
  /-- Setting the buffer keeps the transparency state. -/
  tx_setBuf : ∀ s b, P.tx (P.setBuf s b) = P.tx s
  /-- Setting the transparency state keeps the buffer. -/
  buf_setTx : ∀ s t, P.buf (P.setTx s t) = P.buf s
  /-- Get after set. -/
  tx_setTx : ∀ s t, P.tx (P.setTx s t) = t
  /-- Painting keeps the buffer size. -/
  paint_size : ∀ s it, (P.buf (P.paint s it)).size = (P.buf s).size
  /-- Painting keeps the transparency state. -/
  paint_tx : ∀ s it, P.tx (P.paint s it) = P.tx s

/-- Paint one item, inside a layer when it has a blend mode or a soft mask (`itemFx`). -/
def paintFx {S : Type} (P : Painter S) (W H : Nat) (s : S) (it : DisplayItem) : S :=
    match itemFx (P.tx s) it with
    | none => P.paint s it
    | some fx =>
      let r := beginLayer W H (P.tx s) (P.buf s) fx
      let s1 := P.paint (P.setBuf (P.setTx s r.1) r.2) it
      let r2 := endLayer W H (Clip.pageRect W H) (P.tx s1) (P.buf s1)
      P.setBuf (P.setTx s1 r2.1) r2.2

/-- **The transparency driver** for one item (fuel: soft-mask nesting): groups open and close
layers, soft-mask items define masks (their items drawn by the driver at one less fuel into
a fresh buffer, with an empty layer stack), painting items with a blend mode or soft mask are
painted inside a layer, everything else goes to `P.paint`. -/
def renderTx {S : Type} (P : Painter S) (W H : Nat) : Nat → S → DisplayItem → S
  | _, s, .groupBegin g =>
    let r := beginGroup W H (P.tx s) (P.buf s) g
    P.setBuf (P.setTx s r.1) r.2
  | _, s, .groupEnd =>
    let r := endLayer W H (Clip.pageRect W H) (P.tx s) (P.buf s)
    P.setBuf (P.setTx s r.1) r.2
  | 0, s, .softMask .. => s
  | f + 1, s, .softMask id info items =>
    let draw : ByteArray → ByteArray := fun base =>
      P.buf (items.foldl (renderTx P W H f) (P.setBuf (P.setTx s { masks := (P.tx s).masks }) base))
    P.setTx s ((P.tx s).addMask id (maskFrom info W H draw))
  | _, s, it => paintFx P W H s it

/-- The driver's invariant: a page-size buffer and page-size saved backdrops. -/
def Inv {S : Type} (P : Painter S) (W H : Nat) (s : S) : Prop :=
  (P.buf s).size = 4 * W * H ∧ (P.tx s).Sized W H

/-- `addMask` keeps the layer stack. -/
theorem addMask_stack (t : TxState) (id : Nat) (m : ByteArray) : (t.addMask id m).stack = t.stack :=
  rfl

/-- The default arm of `renderTx` keeps the invariant. -/
theorem paintFx_inv {S : Type} (P : Painter S) (hP : P.Lawful) (W H : Nat) (s : S)
    (it : DisplayItem) (h : Inv P W H s) :
    Inv P W H (paintFx P W H s it) := by
  unfold paintFx
  split
  · exact ⟨by rw [hP.paint_size]; exact h.1, by rw [hP.paint_tx]; exact h.2⟩
  · rename_i fx _
    have hb := beginLayer_size W H (P.tx s) (P.buf s) fx h.1 h.2
    have h1 : (P.buf (P.paint (P.setBuf (P.setTx s (beginLayer W H (P.tx s) (P.buf s) fx).1)
        (beginLayer W H (P.tx s) (P.buf s) fx).2) it)).size = 4 * W * H := by
      rw [hP.paint_size, hP.buf_setBuf]; exact hb.1
    have h2 : (P.tx (P.paint (P.setBuf (P.setTx s (beginLayer W H (P.tx s) (P.buf s) fx).1)
        (beginLayer W H (P.tx s) (P.buf s) fx).2) it)).Sized W H := by
      rw [hP.paint_tx, hP.tx_setBuf, hP.tx_setTx]; exact hb.2
    have he := endLayer_size W H (Clip.pageRect W H) _ _ h1 h2
    exact ⟨by simp only [hP.buf_setBuf]; exact he.1,
      by simp only [hP.tx_setBuf, hP.tx_setTx]; exact he.2⟩

/-- **The driver keeps the page buffer size** (and every saved backdrop's), for a lawful
painter. -/
theorem renderTx_inv {S : Type} (P : Painter S) (hP : P.Lawful) (W H : Nat) :
    ∀ (f : Nat) (s : S) (it : DisplayItem), Inv P W H s → Inv P W H (renderTx P W H f s it) := by
  intro f s it h
  cases it with
  | groupBegin g =>
    simp only [renderTx]
    have := beginGroup_size W H (P.tx s) (P.buf s) g h.1 h.2
    exact ⟨by rw [hP.buf_setBuf]; exact this.1, by rw [hP.tx_setBuf, hP.tx_setTx]; exact this.2⟩
  | groupEnd =>
    simp only [renderTx]
    have := endLayer_size W H (Clip.pageRect W H) (P.tx s) (P.buf s) h.1 h.2
    exact ⟨by rw [hP.buf_setBuf]; exact this.1, by rw [hP.tx_setBuf, hP.tx_setTx]; exact this.2⟩
  | softMask id info items =>
    cases f with
    | zero => simp only [renderTx]; exact h
    | succ f =>
      simp only [renderTx]
      refine ⟨by rw [hP.buf_setTx]; exact h.1, ?_⟩
      rw [hP.tx_setTx]
      intro l hl
      exact h.2 l hl
  | _ => all_goals (cases f <;> (simp only [renderTx]; exact paintFx_inv P hP W H s _ h))

/-- Folding the driver keeps the invariant. -/
theorem foldl_renderTx_inv {S : Type} (P : Painter S) (hP : P.Lawful) (W H f : Nat)
    (l : List DisplayItem) : ∀ (s : S), Inv P W H s → Inv P W H (l.foldl (renderTx P W H f) s) := by
  induction l with
  | nil => intro s h; exact h
  | cons it rest ih => intro s h; exact ih _ (renderTx_inv P hP W H f s it h)

/-- **A page rendered through the driver keeps `4 · W · H` bytes.** -/
theorem renderTx_items_size {S : Type} (P : Painter S) (hP : P.Lawful) (W H f : Nat)
    (items : Array DisplayItem) (s : S) (hb : (P.buf s).size = 4 * W * H)
    (ht : (P.tx s).stack = []) :
    (P.buf (items.foldl (renderTx P W H f) s)).size = 4 * W * H := by
  rw [← Array.foldl_toList]
  exact (foldl_renderTx_inv P hP W H f items.toList s ⟨hb, by
    intro l hl; rw [ht] at hl; cases hl⟩).1

end SafePdf.Core.Raster.Transparency
