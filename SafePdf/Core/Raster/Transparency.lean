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

## Speed (task 7.2g)

The 7.3c driver combined every layer over the whole page (≈ 15 ms per layer at 612 × 792
compiled; ≈ 60 ms with a separable blend mode, whose scratch buffer was a fresh page). It is kept
as the specification `renderTxSpec` (section 7); `renderTx` gives the same bytes (random scenes,
`Tests/RasterTxFast.lean`) and differs in four ways:

* **Dirty rectangles.** Each open layer carries an upper bound of the pixels where it can
  differ from its initial content (`Layer.opened … dirty`): the union (`unionR`) of the bounds
  of the items painted into it (`Painter.bound`, e.g. `Clip.itemBound`; `none` = the whole
  page, the default) and of the rectangles its inner layers combined over. `endLayer` combines
  only over it. Outside it, the layer still holds its initial content, which `combine` leaves
  unchanged: the backdrop itself (`Normal`; non-separable modes: `B(cb, cb) = cb`) or the
  mode's neutral colour where that is exact (`exactNeutral`: every separable mode except
  `HardLight`, checked for every byte by `#guard`).
* **Item layers** (an item with a blend mode or soft mask, `beginItem`) know their bound before
  painting: the scratch buffer is the `spare` buffer of the last closed layer, initialised only
  over the bound (copied rows or the neutral colour), so they allocate nothing.
* **Fast loops**: `combineFast` (the pixels `combine` leaves unchanged are skipped after six
  byte reads), `lumLoop`/`alphaLoop`, row-copy `fillBuf`/`solidBuf`.
* The transparency state is taken out of the renderer state before a layer is opened or
  closed, so the buffers it holds are written in place (no copy-on-write of the page).

`scripts/bench-raster.sh` (612 × 792, compiled): 100 groups at alpha 0.5: 1586 → 9 ms
(167 ms without bounds); luminosity-masked full-page fill: 62 → 9 ms; 1000 `Multiply`
rectangles: 61.7 s → 12 ms (1.7 s without bounds). `Glyph.painterG` does not set `bound` yet:
it gets the "without bounds" figures until it does.

## Wiring

`renderTx P W H fuel` is the transparency driver over any renderer state `S` given a
`Painter S` (lenses to the page buffer and the `TxState`, and the plain item painter, e.g.
`Glyph.renderItemG`); see the task report for the exact `Glyph` change.
-/

namespace SafePdf.Core.Raster.Transparency

open SafePdf.Core
open SafePdf.Core.Raster.Fill (IRect)
open SafePdf.Core.Raster.Clip (mul255 getB setB setB_size compByte deviceRGB getU mul255U pxU emptyRect
  pageRect)
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

/-- A blend mode whose neutral source byte is exactly neutral: `B(cb, neutral m) = cb` for
every byte `cb` (`Normal` and the non-separable modes start from a copy of the backdrop:
`B(cb, cb) = cb`, tested). False only for `HardLight` (`B(cb, 128) = cb + 1` for `cb < 128`;
`Overlay` and `SoftLight` round back to `cb`, checked below for every byte): its layers always
combine over the whole page, as before. -/
def exactNeutral : BlendMode → Bool
  | .hardLight => false
  | _ => true

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

/-! ### Fast combine (task 7.2g)

`combineFast` computes the bytes of `combine` (tested on random layers,
`Tests/RasterTxFast.lean`; not proved): the same row/pixel order, with `UInt32` arithmetic
(`Clip.getU`, `Clip.mul255U`, `Clip.pxU`), no tuples or `Option` match per pixel, and pixels
that `combine` leaves as they are skipped after six byte reads: a pixel of a `Normal` or
non-separable layer equal to its backdrop (`B(cb, cb) = cb`), and a pixel of a separable layer
equal to the mode's exactly neutral colour (`exactNeutral`: `B(cb, n) = cb`, then
`blend cb cb f = cb`). -/

/-- `combinePx` on `UInt32`s: mask bytes from `mk` when `useMask`, alpha `al ≤ 255`, neutral
byte `nn` of the mode. -/
@[inline] def combinePxF (cur mk : ByteArray) (useMask : Bool) (al nn : UInt32) (m : BlendMode)
    (i : Nat) (b : ByteArray) : ByteArray :=
  let f := mul255U al (if useMask then getU mk i else 255)
  if f == 0 then b else
  let o := 4 * i
  let br := getU b o
  let bg := getU b (o + 1)
  let bb := getU b (o + 2)
  let sr := getU cur o
  let sg := getU cur (o + 1)
  let sb := getU cur (o + 2)
  if m == .normal then
    if sr == br && sg == bg && sb == bb then b else pxU b o sr sg sb f
  else if (if m.separable then exactNeutral m && sr == nn && sg == nn && sb == nn
      else sr == br && sg == bg && sb == bb) then b
  else
    let res := blendRGB m (br.toNat, bg.toNat, bb.toNat) (sr.toNat, sg.toNat, sb.toNat)
    pxU b o (UInt32.ofNat res.1) (UInt32.ofNat res.2.1) (UInt32.ofNat res.2.2) f

/-- `combinePxF` preserves the size. -/
theorem combinePxF_size (cur mk : ByteArray) (useMask : Bool) (al nn : UInt32) (m : BlendMode)
    (i : Nat) (b : ByteArray) : (combinePxF cur mk useMask al nn m i b).size = b.size := by
  unfold combinePxF
  dsimp only
  repeat' split
  all_goals simp only [Clip.pxU_size]

/-- `span` with `combinePxF`. -/
def spanF (cur mk : ByteArray) (useMask : Bool) (al nn : UInt32) (m : BlendMode) :
    (n i : Nat) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, i, b => spanF cur mk useMask al nn m n (i + 1) (combinePxF cur mk useMask al nn m i b)

/-- `spanF` preserves the size. -/
theorem spanF_size (cur mk : ByteArray) (useMask : Bool) (al nn : UInt32) (m : BlendMode)
    (n i : Nat) (b : ByteArray) : (spanF cur mk useMask al nn m n i b).size = b.size := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [spanF, ih, combinePxF_size]

/-- `spans` with `spanF`. -/
def spansF (W : Nat) (cur mk : ByteArray) (useMask : Bool) (al nn : UInt32) (m : BlendMode)
    (x0 cw : Nat) : (n y : Nat) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, y, b =>
    spansF W cur mk useMask al nn m x0 cw n (y + 1)
      (spanF cur mk useMask al nn m cw (y * W + x0) b)

/-- `spansF` preserves the size. -/
theorem spansF_size (W : Nat) (cur mk : ByteArray) (useMask : Bool) (al nn : UInt32)
    (m : BlendMode) (x0 cw n y : Nat) (b : ByteArray) :
    (spansF W cur mk useMask al nn m x0 cw n y b).size = b.size := by
  induction n generalizing y b with
  | zero => rfl
  | succ n ih => simp only [spansF, ih, spanF_size]

/-- **Fast combine**: the bytes of `combine W H r back cur fx` (an alpha above 255, never
produced by the driver, falls back to `combine`). -/
def combineFast (W H : Nat) (r : IRect) (back cur : ByteArray) (fx : Fx) : ByteArray :=
  if cur.size = back.size then
    if fx.alpha ≤ 255 then
      let x0 := (max r.x0 0).toNat
      let x1 := (min r.x1 W).toNat
      let y0 := (max r.y0 0).toNat
      let y1 := (min r.y1 H).toNat
      let mk := fx.mask.getD ByteArray.empty
      spansF W cur mk fx.mask.isSome (UInt32.ofNat fx.alpha)
        (UInt32.ofNat (neutral fx.blend)) fx.blend x0 (x1 - x0) (y1 - y0) y0
        back
    else combine W H r back cur fx
  else back

/-- Fast combining keeps the backdrop's size. -/
theorem combineFast_size (W H : Nat) (r : IRect) (back cur : ByteArray) (fx : Fx) :
    (combineFast W H r back cur fx).size = back.size := by
  unfold combineFast; split
  · split
    · exact spansF_size _ _ _ _ _ _ _ _ _ _ _ _
    · exact combine_size _ _ _ _ _ _
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
  /-- An open layer: the saved backdrop, how to combine onto it, and its **dirty rectangle**
  (task 7.2g): an upper bound of the pixels where the layer can differ from its initial
  content, `none` = unknown (the whole page). -/
  | opened (back : ByteArray) (fx : Fx) (dirty : Option IRect)
  /-- A layer painted directly (trivial group, or beyond `maxLayerDepth`). -/
  | skipped
  /-- A **knockout** frame (task 7.3i), pushed on top of a knockout group's own frame: `base`
  is the group's initial content (its backdrop, or the neutral colour). Items with constant
  alpha ≠ 1 painted while it is the innermost frame composite over `base`, not over the
  earlier items of the group (`knockItem`). Painting passes through it to the enclosing open
  layer (like `skipped`); it counts as an open layer (it holds a page buffer). -/
  | knock (base : ByteArray)

/-- Transparency state of a page render. -/
structure TxState where
  /-- Open layers, innermost first. -/
  stack : List Layer := []
  /-- Soft masks by identifier, most recent first. -/
  masks : List (Nat × ByteArray) := []
  /-- A page buffer to reuse as the scratch buffer of the next item layer (the scratch buffer
  of the last closed layer; its content is irrelevant), so that item layers allocate nothing. -/
  spare : ByteArray := ByteArray.empty

/-- Number of open (buffer-holding) layers. -/
def openCount : List Layer → Nat
  | [] => 0
  | .opened .. :: rest => openCount rest + 1
  | .skipped :: rest => openCount rest
  | .knock _ :: rest => openCount rest + 1

/-- A layer's saved backdrop has the page size (or there is none). -/
def Layer.Ok (W H : Nat) : Layer → Prop
  | .opened back _ _ => back.size = 4 * W * H
  | .skipped => True
  | .knock base => base.size = 4 * W * H

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

/-! ### Dirty rectangles (task 7.2g) -/

/-- An empty rectangle (no pixel). -/
def rectEmpty (r : IRect) : Bool := r.x1 ≤ r.x0 || r.y1 ≤ r.y0

/-- The smallest rectangle containing both (an empty operand is ignored). -/
def unionR (a b : IRect) : IRect :=
  if rectEmpty a then b else if rectEmpty b then a
  else ⟨min a.x0 b.x0, min a.y0 b.y0, max a.x1 b.x1, max a.y1 b.y1⟩

/-- Grow a dirty rectangle (`none` = the whole page absorbs). -/
def addDirty : Option IRect → Option IRect → Option IRect
  | some a, some b => some (unionR a b)
  | _, _ => none

/-- Grow the dirty rectangle of the innermost open layer by `r` (skipped frames paint into it). -/
def touchStack (r : Option IRect) : List Layer → List Layer
  | [] => []
  | .skipped :: rest => .skipped :: touchStack r rest
  | .knock b :: rest => .knock b :: touchStack r rest
  | .opened back fx d :: rest => .opened back fx (addDirty d r) :: rest

/-- Record that the pixels within `r` may have changed in the current buffer. -/
def TxState.touch (t : TxState) (r : Option IRect) : TxState :=
  { t with stack := touchStack r t.stack }

/-- Touching keeps the number of open layers. -/
theorem openCount_touchStack (r : Option IRect) (l : List Layer) :
    openCount (touchStack r l) = openCount l := by
  induction l with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [touchStack, openCount, ih]

/-- Touching keeps every saved backdrop. -/
theorem touchStack_ok (W H : Nat) (r : Option IRect) (l : List Layer)
    (h : ∀ x ∈ l, x.Ok W H) : ∀ x ∈ touchStack r l, x.Ok W H := by
  induction l with
  | nil => intro x hx; cases hx
  | cons y rest ih =>
    intro x hx
    cases y with
    | skipped =>
      simp only [touchStack, List.mem_cons] at hx
      rcases hx with rfl | hx
      · trivial
      · exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) x hx
    | opened back fx d =>
      simp only [touchStack, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h (.opened back fx d) (List.mem_cons_self ..)
      · exact h x (List.mem_cons_of_mem _ hx)
    | knock b =>
      simp only [touchStack, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h (.knock b) (List.mem_cons_self ..)
      · exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) x hx

/-- Touching keeps the `Sized` invariant. -/
theorem touch_sized (W H : Nat) (t : TxState) (r : Option IRect) (h : t.Sized W H) :
    (t.touch r).Sized W H :=
  touchStack_ok W H r t.stack h

/-! ### Buffers -/

/-- Append `n` copies of `v`. -/
def pushN (v : UInt8) : Nat → ByteArray → ByteArray
  | 0, b => b
  | n + 1, b => pushN v n (b.push v)

/-- `pushN` appends `n` bytes. -/
theorem pushN_size (v : UInt8) (n : Nat) (b : ByteArray) : (pushN v n b).size = b.size + n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [pushN, ih, ByteArray.size_push]; omega

/-- Append `n` copies of `row`. -/
def appendN (row : ByteArray) : Nat → ByteArray → ByteArray
  | 0, b => b
  | n + 1, b => appendN row n (b ++ row)

/-- `appendN` appends `n · row.size` bytes. -/
theorem appendN_size (row : ByteArray) (n : Nat) (b : ByteArray) :
    (appendN row n b).size = b.size + n * row.size := by
  induction n generalizing b with
  | zero => simp [appendN]
  | succ n ih => simp only [appendN, ih, ByteArray.size_append, Nat.succ_mul]; omega

/-- A buffer of `W · H` pixels, every byte `v` (one row, then `H` row copies). -/
def fillBuf (W H v : Nat) : ByteArray := appendN (pushN (UInt8.ofNat v) (4 * W) .empty) H .empty

/-- `fillBuf` has the page size. -/
theorem fillBuf_size (W H v : Nat) : (fillBuf W H v).size = 4 * W * H := by
  simp only [fillBuf, appendN_size, pushN_size, ByteArray.size_empty, Nat.zero_add]
  rw [Nat.mul_comm]

/-- The 7.3c definition of `fillBuf` (kept for the reference driver; same bytes). -/
def fillBufSpec (W H v : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate (4 * W * H) (UInt8.ofNat v))

/-- Copying `len` bytes inside both buffers keeps the destination's size. -/
theorem copySlice_size (src dst : ByteArray) (so d len : Nat) (h1 : d + len ≤ dst.size)
    (h2 : so + len ≤ src.size) : (src.copySlice so dst d len).size = dst.size := by
  simp only [ByteArray.copySlice, ByteArray.size, Array.size_append, Array.size_extract]
  simp only [ByteArray.size] at h1 h2
  omega

/-- Copy `len` bytes from offset `so` of `src` to offset `d` of `dst` when both ranges are
inside the buffers (else `dst`). -/
@[inline] def copyIn (src dst : ByteArray) (so d len : Nat) : ByteArray :=
  if d + len ≤ dst.size ∧ so + len ≤ src.size then src.copySlice so dst d len else dst

/-- `copyIn` keeps the destination's size. -/
theorem copyIn_size (src dst : ByteArray) (so d len : Nat) :
    (copyIn src dst so d len).size = dst.size := by
  unfold copyIn; split
  · rename_i h; exact copySlice_size _ _ _ _ _ h.1 h.2
  · rfl

/-- Rows `y, y + 1, …` (`n` of them), columns `[x0, x0 + cw)`, of `src` copied into `dst`
(both of width `W`). -/
def copyRows (W : Nat) (src : ByteArray) (x0 cw : Nat) : (n y : Nat) → ByteArray → ByteArray
  | 0, _, d => d
  | n + 1, y, d =>
    copyRows W src x0 cw n (y + 1) (copyIn src d (4 * (y * W + x0)) (4 * (y * W + x0)) (4 * cw))

/-- `copyRows` keeps the size. -/
theorem copyRows_size (W : Nat) (src : ByteArray) (x0 cw n y : Nat) (d : ByteArray) :
    (copyRows W src x0 cw n y d).size = d.size := by
  induction n generalizing y d with
  | zero => rfl
  | succ n ih => simp only [copyRows, ih, copyIn_size]

/-- Rows `y, y + 1, …` (`n` of them) from column `x0` of `dst` (width `W`) overwritten with
`row` (`cw` pixels). -/
def fillRows (W : Nat) (row : ByteArray) (x0 cw : Nat) : (n y : Nat) → ByteArray → ByteArray
  | 0, _, d => d
  | n + 1, y, d => fillRows W row x0 cw n (y + 1) (copyIn row d 0 (4 * (y * W + x0)) (4 * cw))

/-- `fillRows` keeps the size. -/
theorem fillRows_size (W : Nat) (row : ByteArray) (x0 cw n y : Nat) (d : ByteArray) :
    (fillRows W row x0 cw n y d).size = d.size := by
  induction n generalizing y d with
  | zero => rfl
  | succ n ih => simp only [fillRows, ih, copyIn_size]

/-! ### Opening and closing layers -/

/-- **Open a layer** over `buf`: save it; the scratch buffer is `buf` itself (`Normal`,
non-separable modes) or the neutral colour (separable modes). Beyond `maxLayerDepth` the
frame is `.skipped` and `buf` is painted directly. The dirty rectangle starts empty, except
for the modes without an exact neutral byte (`exactNeutral`): there it is the whole page. -/
def beginLayer (W H : Nat) (t : TxState) (buf : ByteArray) (fx : Fx) : TxState × ByteArray :=
  if openCount t.stack < maxLayerDepth then
    let cur := if fx.blend ≠ .normal ∧ fx.blend.separable then fillBuf W H (neutral fx.blend)
      else buf
    let d := if exactNeutral fx.blend then some emptyRect else none
    ({ t with stack := .opened buf fx d :: t.stack }, cur)
  else ({ t with stack := .skipped :: t.stack }, buf)

/-- **Close the innermost layer**: combine it onto its saved backdrop over `r` ∩ its dirty
rectangle (outside it the layer equals its initial content, which combines to the backdrop),
grow the enclosing layer's dirty rectangle by what was combined, keep the scratch buffer as
the `spare`. An empty stack (unbalanced end) and a skipped frame leave the buffer as it is. -/
def endLayer (W H : Nat) (r : IRect) (t : TxState) (buf : ByteArray) : TxState × ByteArray :=
  match t.stack with
  | [] => (t, buf)
  | .skipped :: rest => ({ t with stack := rest }, buf)
  | .knock _ :: rest => ({ t with stack := rest }, buf)
  | .opened back fx d :: rest =>
    let rr := (match d with | some d => r.inter d | none => r).inter (pageRect W H)
    let t' := { t with stack := touchStack (some rr) rest, spare := buf }
    (t', combineFast W H rr back buf fx)

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
  · rename_i rest heq
    refine ⟨hb, fun l hl => ht l ?_⟩
    simp [heq, hl]
  · rename_i back fx d rest heq
    have hback : back.size = 4 * W * H := ht (.opened back fx d) (by simp [heq])
    refine ⟨by rw [combineFast_size]; exact hback, ?_⟩
    exact touchStack_ok W H _ rest (fun l hl => ht l (by simp [heq, hl]))

/-- **Open an item layer** with a known bound `bd` of what the item paints (task 7.2g): the
scratch buffer is the `spare` buffer (or `buf`), initialised only over `bd` ∩ page (copied
from `buf`, or the neutral colour for separable modes), and the dirty rectangle is that
rectangle. Without a bound, or for a mode without an exact neutral byte, as `beginLayer`. -/
def beginItem (W H : Nat) (t : TxState) (buf : ByteArray) (fx : Fx) (bd : Option IRect) :
    TxState × ByteArray :=
  match bd with
  | some rb =>
    if openCount t.stack < maxLayerDepth ∧ exactNeutral fx.blend then
      let rb := rb.inter (Clip.pageRect W H)
      let x0 := rb.x0.toNat
      let y0 := rb.y0.toNat
      let cw := rb.width
      let ch := rb.height
      let sp := t.spare
      let t := { t with spare := ByteArray.empty }
      let cur0 := if sp.size = buf.size then sp else buf
      let cur := if fx.blend ≠ .normal ∧ fx.blend.separable then
          fillRows W (pushN (UInt8.ofNat (neutral fx.blend)) (4 * cw) .empty) x0 cw ch y0 cur0
        else copyRows W buf x0 cw ch y0 cur0
      ({ t with stack := .opened buf fx (some rb) :: t.stack }, cur)
    else beginLayer W H t buf fx
  | none => beginLayer W H t buf fx

/-- Opening an item layer keeps the page size and the `Sized` invariant. -/
theorem beginItem_size (W H : Nat) (t : TxState) (buf : ByteArray) (fx : Fx)
    (bd : Option IRect) (hb : buf.size = 4 * W * H) (ht : t.Sized W H) :
    (beginItem W H t buf fx bd).2.size = 4 * W * H ∧ (beginItem W H t buf fx bd).1.Sized W H := by
  unfold beginItem
  split
  · split
    · refine ⟨?_, ?_⟩
      · simp only
        have hc : (if t.spare.size = buf.size then t.spare else buf).size = buf.size := by
          split
          · assumption
          · rfl
        split
        · rw [fillRows_size, hc, hb]
        · rw [copyRows_size, hc, hb]
      · intro l hl
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact hb
        · exact ht l hl
    · exact beginLayer_size W H t buf fx hb ht
  · exact beginLayer_size W H t buf fx hb ht

/-- Item layers stay within `maxLayerDepth`. -/
theorem beginItem_open_le (W H : Nat) (t : TxState) (buf : ByteArray) (fx : Fx)
    (bd : Option IRect) (h : openCount t.stack ≤ maxLayerDepth) :
    openCount (beginItem W H t buf fx bd).1.stack ≤ maxLayerDepth := by
  unfold beginItem
  split
  · split
    · rename_i hc; simp only [openCount]; omega
    · exact beginLayer_open_le W H t buf fx h
  · exact beginLayer_open_le W H t buf fx h

/-- For a knockout group (task 7.3i): push a `knock` frame holding the group's initial content
`r.2` on top of the group's frame, if fewer than `maxLayerDepth` buffers are held (else the
knockout is ignored: documented degradation). -/
def pushKnock (k : Bool) (r : TxState × ByteArray) : TxState × ByteArray :=
  if k ∧ openCount r.1.stack < maxLayerDepth then
    ({ r.1 with stack := .knock r.2 :: r.1.stack }, r.2)
  else r

/-- Drop a `knock` frame on top of the stack (the end of a knockout group, before its own frame
is closed). -/
def popKnock (t : TxState) : TxState :=
  match t.stack with
  | .knock _ :: rest => { t with stack := rest }
  | _ => t

/-- The base buffer of the innermost frame when it is a `knock` frame. -/
def knockBase (t : TxState) : Option ByteArray :=
  match t.stack with
  | .knock b :: _ => some b
  | _ => none

/-- Pushing a knockout frame keeps the page size and the `Sized` invariant. -/
theorem pushKnock_size (W H : Nat) (k : Bool) (r : TxState × ByteArray)
    (hb : r.2.size = 4 * W * H) (ht : r.1.Sized W H) :
    (pushKnock k r).2.size = 4 * W * H ∧ (pushKnock k r).1.Sized W H := by
  unfold pushKnock
  split
  · refine ⟨hb, ?_⟩
    intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hb
    · exact ht l hl
  · exact ⟨hb, ht⟩

/-- Dropping a knockout frame keeps the `Sized` invariant. -/
theorem popKnock_sized (W H : Nat) (t : TxState) (ht : t.Sized W H) : (popKnock t).Sized W H := by
  unfold popKnock
  split
  · rename_i b rest heq
    intro l hl
    exact ht l (by simp [heq, hl])
  · exact ht

/-- A transparency group's layer: alpha `ca`, blend mode and soft mask of the group. A group
with alpha 1, `Normal` and no (kept) mask is painted directly (`.skipped`; exact without
knockout). A knockout group (`/K true`, task 7.3i) then gets a `knock` frame (`pushKnock`). -/
def beginGroup (W H : Nat) (t : TxState) (buf : ByteArray) (g : GroupInfo) : TxState × ByteArray :=
  let fx : Fx := { alpha := compByte g.alpha, blend := g.blend, mask := g.smask.bind t.mask? }
  pushKnock g.knockout <|
    if fx.alpha = 255 ∧ fx.blend = .normal ∧ fx.mask.isNone then
      ({ t with stack := .skipped :: t.stack }, buf)
    else beginLayer W H t buf fx

/-- Opening a group keeps the page size and the `Sized` invariant. -/
theorem beginGroup_size (W H : Nat) (t : TxState) (buf : ByteArray) (g : GroupInfo)
    (hb : buf.size = 4 * W * H) (ht : t.Sized W H) :
    (beginGroup W H t buf g).2.size = 4 * W * H ∧ (beginGroup W H t buf g).1.Sized W H := by
  unfold beginGroup
  simp only
  apply pushKnock_size
  · split
    · exact hb
    · exact (beginLayer_size W H t buf _ hb ht).1
  · split
    · intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · trivial
      · exact ht l hl
    · exact (beginLayer_size W H t buf _ hb ht).2

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

/-- A buffer of `W · H` opaque pixels of colour `rgb` (one row, then `H` row copies). -/
def solidBuf (W H : Nat) (rgb : Nat × Nat × Nat) : ByteArray :=
  let px : ByteArray := (((ByteArray.empty.push (UInt8.ofNat rgb.1)).push
    (UInt8.ofNat rgb.2.1)).push (UInt8.ofNat rgb.2.2)).push 255
  appendN (appendN px W .empty) H .empty

/-- The 7.3c definition of `solidBuf` (kept for the reference driver; same bytes). -/
def solidBufSpec (W H : Nat) (rgb : Nat × Nat × Nat) : ByteArray :=
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

/-- Luminosity mask of a rendered buffer (`W · H` bytes; the 7.3c reference). -/
def lumMask (W H : Nat) (r : ByteArray) : ByteArray :=
  tabulate (fun i => lumByte (px r i)) (W * H) 0 ByteArray.empty

/-- Alpha mask from renders over black (`r0`) and white (`r1`): `255 − (ΣR₁ − ΣR₀)/3` (the
7.3c reference). -/
def alphaMask (W H : Nat) (r0 r1 : ByteArray) : ByteArray :=
  tabulate (fun i =>
    let a := px r0 i
    let b := px r1 i
    255 - min 255 ((b.1 + b.2.1 + b.2.2 - (a.1 + a.2.1 + a.2.2) + 1) / 3)) (W * H) 0
    ByteArray.empty

/-- `lumMask` on `UInt32`s: `n` bytes from pixel `i` on. -/
def lumLoop (r : ByteArray) : (n i : Nat) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, i, b =>
    let o := 4 * i
    let v := (30 * getU r o + 59 * getU r (o + 1) + 11 * getU r (o + 2) + 50) / 100
    lumLoop r n (i + 1) (b.push (if v < 255 then v.toUInt8 else 255))

/-- `lumLoop` appends exactly `n` bytes. -/
theorem lumLoop_size (r : ByteArray) (n i : Nat) (b : ByteArray) :
    (lumLoop r n i b).size = b.size + n := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [lumLoop, ih, ByteArray.size_push]; omega

/-- `alphaMask` on `UInt32`s: `n` bytes from pixel `i` on. -/
def alphaLoop (r0 r1 : ByteArray) : (n i : Nat) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, i, b =>
    let o := 4 * i
    let sa := getU r0 o + getU r0 (o + 1) + getU r0 (o + 2)
    let sb := getU r1 o + getU r1 (o + 1) + getU r1 (o + 2)
    let q := if sa ≤ sb then (sb - sa + 1) / 3 else 0
    alphaLoop r0 r1 n (i + 1) (b.push (255 - (if q < 255 then q else 255)).toUInt8)

/-- `alphaLoop` appends exactly `n` bytes. -/
theorem alphaLoop_size (r0 r1 : ByteArray) (n i : Nat) (b : ByteArray) :
    (alphaLoop r0 r1 n i b).size = b.size + n := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [alphaLoop, ih, ByteArray.size_push]; omega

/-- **The soft mask** of `info`, given `draw` (render the mask group's items onto a backdrop
buffer): luminosity over `/BC`, or alpha from two renders. `W · H` bytes. The bytes of
`maskFromSpec` (tested), with the fast buffers and loops of task 7.2g. -/
def maskFrom (info : SoftMaskInfo) (W H : Nat) (draw : ByteArray → ByteArray) : ByteArray :=
  match info.kind with
  | .luminosity => lumLoop (draw (solidBuf W H (deviceRGB info.backdrop))) (W * H) 0 .empty
  | .alpha => alphaLoop (draw (fillBuf W H 0)) (draw (fillBuf W H 255)) (W * H) 0 .empty

/-- A soft mask has one byte per pixel. -/
theorem maskFrom_size (info : SoftMaskInfo) (W H : Nat) (draw : ByteArray → ByteArray) :
    (maskFrom info W H draw).size = W * H := by
  unfold maskFrom
  split
  · rw [lumLoop_size]; show 0 + W * H = W * H; omega
  · rw [alphaLoop_size]; show 0 + W * H = W * H; omega

/-- The 7.3c soft mask (reference of `maskFrom`). -/
def maskFromSpec (info : SoftMaskInfo) (W H : Nat) (draw : ByteArray → ByteArray) : ByteArray :=
  match info.kind with
  | .luminosity => lumMask W H (draw (solidBufSpec W H (deviceRGB info.backdrop)))
  | .alpha => alphaMask W H (draw (fillBufSpec W H 0)) (draw (fillBufSpec W H 255))

/-- The reference soft mask has one byte per pixel. -/
theorem maskFromSpec_size (info : SoftMaskInfo) (W H : Nat) (draw : ByteArray → ByteArray) :
    (maskFromSpec info W H draw).size = W * H := by
  unfold maskFromSpec lumMask alphaMask
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
  /-- An upper bound, known before painting, of the device pixels painting the item can
  change (task 7.2g; e.g. `Clip.itemBound`); `none` = unknown (the whole page, the default).
  Layers are combined only over the union of these bounds. The law (pixels outside the bound
  are unchanged) is not part of `Lawful`: a painter breaking it loses the paint outside the
  bound inside layers, nothing else. -/
  bound : DisplayItem → Option IRect := fun _ => none

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

/-- Paint one item, inside a layer when it has a blend mode or a soft mask (`itemFx`); grow
the enclosing layer's dirty rectangle by the item's bound. The transparency state is taken out
of `s` before a layer is opened or closed, so that the buffers it holds stay unshared (written
in place). -/
def paintFx {S : Type} (P : Painter S) (W H : Nat) (s : S) (it : DisplayItem) : S :=
    match itemFx (P.tx s) it with
    | none =>
      let s1 := P.paint s it
      if openCount (P.tx s1).stack = 0 then s1 else P.setTx s1 ((P.tx s1).touch (P.bound it))
    | some fx =>
      let t := P.tx s
      let s0 := P.setTx s {}
      let r := beginItem W H t (P.buf s0) fx (P.bound it)
      let s1 := P.paint (P.setBuf (P.setTx s0 r.1) r.2) it
      let t1 := (P.tx s1).touch (P.bound it)
      let s2 := P.setTx s1 {}
      let r2 := endLayer W H (Clip.pageRect W H) t1 (P.buf s2)
      P.setBuf (P.setTx s2 r2.1) r2.2

/-- The driver's invariant: a page-size buffer and page-size saved backdrops. -/
def Inv {S : Type} (P : Painter S) (W H : Nat) (s : S) : Prop :=
  (P.buf s).size = 4 * W * H ∧ (P.tx s).Sized W H

/-! ### Knockout (task 7.3i)

MuPDF (`draw-device.c`, `fz_knockout_begin`/`fz_knockout_end`, 1.25.1) paints an item of
constant alpha ≠ 1 inside a knockout group onto a copy of the group's initial backdrop `B`,
records its **shape** (coverage without alpha), and merges: `dest = lerp(dest, B ⊕ item,
shape)`; items with alpha 1 are painted directly. Here (`knockItem`): `B ⊕ item` is the item
painted (with its blend mode and soft mask, `paintC`) onto the `knock` frame's `base`, and the
shape comes from two plain renders of the item made opaque (`opaqueItem`: alpha 1, `Normal`,
no mask) over black (`R₀ = s·C`) and white (`R₁ = 1 − s + s·C`): `s = 255 − (ΣR₁ − ΣR₀)/3`
(exact for coverage 0 and 255, ±1 at anti-aliased edges). Outside the item's bound `s = 0`, so
the merge runs over the bound only (`renderTx`) or the whole page (`renderTxSpec`) with the same
bytes. A glyph run that fills and strokes is, as in MuPDF (`pdf-op-run.c`, `pdf_show_text`),
its own knockout group of a fill run and a stroke run (`splitRun?`), unless the stroke's alpha
is 0, or 1 with `Normal`. -/

/-- The constant alpha byte of a painting item (255 for the others; a run that both fills and
strokes: the smaller of its two alphas). -/
def itemAlpha : DisplayItem → Nat
  | .fillPath _ _ st _ => compByte st.alpha
  | .strokePath _ st _ => compByte st.alpha
  | .glyphRun r _ =>
    match r.renderMode with
    | .stroke | .strokeClip => compByte r.stroke.alpha
    | .fillStroke | .fillStrokeClip => min (compByte r.fill.alpha) (compByte r.stroke.alpha)
    | _ => compByte r.fill.alpha
  | .image _ _ f _ => compByte f.alpha
  | .shading _ _ _ f _ => compByte f.alpha
  | _ => 255

/-- A fill snapshot made opaque: alpha 1, `Normal`, no soft mask. -/
def opaqueFill (f : Content.FillStyle) : Content.FillStyle :=
  { f with alpha := Comp.one, blend := .normal, smask := none }

/-- A stroke snapshot made opaque: alpha 1, `Normal`, no soft mask. -/
def opaqueStroke (f : Content.StrokeStyle) : Content.StrokeStyle :=
  { f with alpha := Comp.one, blend := .normal, smask := none }

/-- The item painted with alpha 1, `Normal` and no soft mask (its shape, `knockItem`). -/
def opaqueItem : DisplayItem → DisplayItem
  | .fillPath p rule st c => .fillPath p rule (opaqueFill st) c
  | .strokePath p st c => .strokePath p (opaqueStroke st) c
  | .glyphRun r c => .glyphRun { r with fill := opaqueFill r.fill, stroke := opaqueStroke r.stroke } c
  | .image src m f c => .image src m (opaqueFill f) c
  | .shading n res m f c => .shading n res m (opaqueFill f) c
  | it => it

/-- A glyph run that fills and strokes, as MuPDF's knockout group (`pdf_show_text`): its fill
run and its stroke run, unless the stroke's alpha is 0, or 1 with `Normal`. -/
def splitRun? : DisplayItem → Option (DisplayItem × DisplayItem)
  | .glyphRun r c =>
    match r.renderMode with
    | .fillStroke | .fillStrokeClip =>
      let a := compByte r.stroke.alpha
      if a = 0 ∨ (a = 255 ∧ r.stroke.blend = .normal) then none
      else some (.glyphRun { r with renderMode := .fill } c, .glyphRun { r with renderMode := .stroke } c)
    | _ => none
  | _ => none

/-- Merge pixel `i`: shape `s` from the renders over black (`r0`) and white (`r1`), then
`dest = lerp(dest, c, s)`. -/
def knockPx (c r0 r1 : ByteArray) (i : Nat) (dest : ByteArray) : ByteArray :=
  let o := 4 * i
  let sa := getB r0 o + getB r0 (o + 1) + getB r0 (o + 2)
  let sb := getB r1 o + getB r1 (o + 1) + getB r1 (o + 2)
  let q := if sa ≤ sb then (sb - sa + 1) / 3 else 0
  let sh := 255 - min 255 q
  if sh = 0 then dest else
  let d := setB dest o (Clip.blend (getB c o) (getB dest o) sh)
  let d := setB d (o + 1) (Clip.blend (getB c (o + 1)) (getB dest (o + 1)) sh)
  setB d (o + 2) (Clip.blend (getB c (o + 2)) (getB dest (o + 2)) sh)

/-- `knockPx` preserves the size. -/
theorem knockPx_size (c r0 r1 : ByteArray) (i : Nat) (dest : ByteArray) :
    (knockPx c r0 r1 i dest).size = dest.size := by
  unfold knockPx
  dsimp only
  repeat' split
  all_goals simp only [setB_size]

/-- `n` pixels from index `i`. -/
def knockSpan (c r0 r1 : ByteArray) : (n i : Nat) → ByteArray → ByteArray
  | 0, _, d => d
  | n + 1, i, d => knockSpan c r0 r1 n (i + 1) (knockPx c r0 r1 i d)

/-- `knockSpan` preserves the size. -/
theorem knockSpan_size (c r0 r1 : ByteArray) (n i : Nat) (d : ByteArray) :
    (knockSpan c r0 r1 n i d).size = d.size := by
  induction n generalizing i d with
  | zero => rfl
  | succ n ih => simp only [knockSpan, ih, knockPx_size]

/-- Rows `y, y + 1, …` (`n` of them), columns `[x0, x0 + cw)`. -/
def knockRows (W : Nat) (c r0 r1 : ByteArray) (x0 cw : Nat) : (n y : Nat) → ByteArray → ByteArray
  | 0, _, d => d
  | n + 1, y, d => knockRows W c r0 r1 x0 cw n (y + 1) (knockSpan c r0 r1 cw (y * W + x0) d)

/-- `knockRows` preserves the size. -/
theorem knockRows_size (W : Nat) (c r0 r1 : ByteArray) (x0 cw n y : Nat) (d : ByteArray) :
    (knockRows W c r0 r1 x0 cw n y d).size = d.size := by
  induction n generalizing y d with
  | zero => rfl
  | succ n ih => simp only [knockRows, ih, knockSpan_size]

/-- **Knockout merge** over the rectangle `r` (clamped to the page): per pixel
`dest = lerp(dest, c, shape)`, the shape from `r0`/`r1`. -/
def knockMerge (W H : Nat) (r : IRect) (dest c r0 r1 : ByteArray) : ByteArray :=
  let x0 := (max r.x0 0).toNat
  let x1 := (min r.x1 W).toNat
  let y0 := (max r.y0 0).toNat
  let y1 := (min r.y1 H).toNat
  knockRows W c r0 r1 x0 (x1 - x0) (y1 - y0) y0 dest

/-- The knockout merge keeps the destination's size. -/
theorem knockMerge_size (W H : Nat) (r : IRect) (dest c r0 r1 : ByteArray) :
    (knockMerge W H r dest c r0 r1).size = dest.size :=
  knockRows_size _ _ _ _ _ _ _ _ _

/-- **Paint one knockout element** (an item of alpha ≠ 1 under a `knock base` frame): the item
over `base` with `paintC` (which applies its blend mode and soft mask; masks are kept, the
layer stack starts empty), its shape from two opaque renders, merged into the current buffer
over `r`; the enclosing layer's dirty rectangle grows by the item's bound. -/
def knockItem {S : Type} (P : Painter S) (W H : Nat) (paintC : S → DisplayItem → S) (r : IRect)
    (base : ByteArray) (s : S) (it : DisplayItem) : S :=
  let t := P.tx s
  let dest := P.buf s
  let s1 := paintC (P.setBuf (P.setTx s { masks := t.masks }) base) it
  let c := P.buf s1
  let op := opaqueItem it
  let s2 := P.paint (P.setBuf (P.setTx s1 {}) (fillBuf W H 0)) op
  let r0 := P.buf s2
  let s3 := P.paint (P.setBuf s2 (fillBuf W H 255)) op
  let r1 := P.buf s3
  P.setBuf (P.setTx s3 (t.touch (P.bound it))) (knockMerge W H r dest c r0 r1)

/-- Paint an item with `paintC`, as a knockout element when the innermost frame is a `knock`
frame and the item's alpha is not 1. The merge rectangle is the item's bound (`fast`) or the
page. -/
def paintK {S : Type} (P : Painter S) (W H : Nat) (paintC : S → DisplayItem → S) (fast : Bool)
    (s : S) (it : DisplayItem) : S :=
  match knockBase (P.tx s) with
  | some b =>
    if itemAlpha it = 255 then paintC s it
    else
      let pg := Clip.pageRect W H
      let r := if fast then ((P.bound it).getD pg).inter pg else pg
      knockItem P W H paintC r b s it
  | none => paintC s it

/-- `paintK`, with a glyph run that fills and strokes painted as its own knockout group
(`splitRun?`; a `knock` frame on the current buffer around its fill run and its stroke run, if
fewer than `maxLayerDepth` buffers are held). -/
def paintKT {S : Type} (P : Painter S) (W H : Nat) (paintC : S → DisplayItem → S) (fast : Bool)
    (s : S) (it : DisplayItem) : S :=
  match splitRun? it with
  | some (fi, si) =>
    let t := P.tx s
    if openCount t.stack < maxLayerDepth then
      let s1 := P.setTx s { t with stack := .knock (P.buf s) :: t.stack }
      let s2 := paintK P W H paintC fast (paintK P W H paintC fast s1 fi) si
      P.setTx s2 (popKnock (P.tx s2))
    else paintC s it
  | none => paintK P W H paintC fast s it

/-- A knockout element keeps the invariant. -/
theorem knockItem_inv {S : Type} (P : Painter S) (hP : P.Lawful) (W H : Nat)
    (paintC : S → DisplayItem → S) (r : IRect) (base : ByteArray) (s : S) (it : DisplayItem)
    (h : Inv P W H s) : Inv P W H (knockItem P W H paintC r base s it) := by
  unfold knockItem
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [hP.buf_setBuf, knockMerge_size]; exact h.1
  · rw [hP.tx_setBuf, hP.tx_setTx]; exact touch_sized W H _ _ h.2

/-- `paintK` keeps the invariant, given that `paintC` does. -/
theorem paintK_inv {S : Type} (P : Painter S) (hP : P.Lawful) (W H : Nat)
    (paintC : S → DisplayItem → S) (hC : ∀ s it, Inv P W H s → Inv P W H (paintC s it))
    (fast : Bool) (s : S) (it : DisplayItem) (h : Inv P W H s) :
    Inv P W H (paintK P W H paintC fast s it) := by
  unfold paintK
  split
  · split
    · exact hC s it h
    · exact knockItem_inv P hP W H paintC _ _ s it h
  · exact hC s it h

/-- `paintKT` keeps the invariant, given that `paintC` does. -/
theorem paintKT_inv {S : Type} (P : Painter S) (hP : P.Lawful) (W H : Nat)
    (paintC : S → DisplayItem → S) (hC : ∀ s it, Inv P W H s → Inv P W H (paintC s it))
    (fast : Bool) (s : S) (it : DisplayItem) (h : Inv P W H s) :
    Inv P W H (paintKT P W H paintC fast s it) := by
  unfold paintKT
  split
  · rename_i fi si _
    dsimp only
    split
    · have h1 : Inv P W H (P.setTx s { P.tx s with stack := .knock (P.buf s) :: (P.tx s).stack }) := by
        refine ⟨by rw [hP.buf_setTx]; exact h.1, ?_⟩
        rw [hP.tx_setTx]
        intro l hl
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact h.1
        · exact h.2 l hl
      have h2 := paintK_inv P hP W H paintC hC fast _ si
        (paintK_inv P hP W H paintC hC fast _ fi h1)
      exact ⟨by rw [hP.buf_setTx]; exact h2.1, by rw [hP.tx_setTx]; exact popKnock_sized W H _ h2.2⟩
    · exact hC s it h
  · exact paintK_inv P hP W H paintC hC fast s it h

/-- **The transparency driver** for one item (fuel: soft-mask nesting): groups open and close
layers, soft-mask items define masks (their items drawn by the driver at one less fuel into
a fresh buffer, with an empty layer stack), painting items with a blend mode or soft mask are
painted inside a layer, everything else goes to `P.paint`. -/
def renderTx {S : Type} (P : Painter S) (W H : Nat) : Nat → S → DisplayItem → S
  | _, s, .groupBegin g =>
    let r := beginGroup W H (P.tx s) (P.buf s) g
    P.setBuf (P.setTx s r.1) r.2
  | _, s, .groupEnd =>
    let t := popKnock (P.tx s)
    let s0 := P.setTx s {}
    let r := endLayer W H (Clip.pageRect W H) t (P.buf s0)
    P.setBuf (P.setTx s0 r.1) r.2
  | 0, s, .softMask .. => s
  | f + 1, s, .softMask id info items =>
    let draw : ByteArray → ByteArray := fun base =>
      P.buf (items.foldl (renderTx P W H f) (P.setBuf (P.setTx s { masks := (P.tx s).masks }) base))
    P.setTx s ((P.tx s).addMask id (maskFrom info W H draw))
  | _, s, it => paintKT P W H (paintFx P W H) true s it

/-- `addMask` keeps the layer stack. -/
theorem addMask_stack (t : TxState) (id : Nat) (m : ByteArray) : (t.addMask id m).stack = t.stack :=
  rfl

/-- The default arm of `renderTx` keeps the invariant. -/
theorem paintFx_inv {S : Type} (P : Painter S) (hP : P.Lawful) (W H : Nat) (s : S)
    (it : DisplayItem) (h : Inv P W H s) :
    Inv P W H (paintFx P W H s it) := by
  unfold paintFx
  split
  · simp only
    split
    · exact ⟨by rw [hP.paint_size]; exact h.1, by rw [hP.paint_tx]; exact h.2⟩
    · refine ⟨by rw [hP.buf_setTx, hP.paint_size]; exact h.1, ?_⟩
      rw [hP.tx_setTx]
      exact touch_sized W H _ _ (by rw [hP.paint_tx]; exact h.2)
  · rename_i fx _
    simp only
    have hb0 : (P.buf (P.setTx s {})).size = 4 * W * H := by rw [hP.buf_setTx]; exact h.1
    have hb := beginItem_size W H (P.tx s) (P.buf (P.setTx s {})) fx (P.bound it) hb0 h.2
    generalize beginItem W H (P.tx s) (P.buf (P.setTx s {})) fx (P.bound it) = r at hb ⊢
    have h1 : (P.buf (P.setTx (P.paint (P.setBuf (P.setTx (P.setTx s {}) r.1) r.2) it) {})).size =
        4 * W * H := by
      rw [hP.buf_setTx, hP.paint_size, hP.buf_setBuf]; exact hb.1
    have h2 : ((P.tx (P.paint (P.setBuf (P.setTx (P.setTx s {}) r.1) r.2) it)).touch
        (P.bound it)).Sized W H := by
      apply touch_sized
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
    have hb0 : (P.buf (P.setTx s {})).size = 4 * W * H := by rw [hP.buf_setTx]; exact h.1
    have := endLayer_size W H (Clip.pageRect W H) (popKnock (P.tx s)) (P.buf (P.setTx s {})) hb0
      (popKnock_sized W H _ h.2)
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
  | _ =>
    all_goals
      have hk := paintKT_inv P hP W H _ (paintFx_inv P hP W H) true s
      cases f <;> (simp only [renderTx]; exact hk _ h)

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

/-! ## 7. The reference driver (the 7.3c driver, kept as the specification)

Every layer combines over the whole page with `combine`, scratch buffers are fresh page-size
buffers, soft masks use the 7.3c loops. `renderTx` must produce exactly its bytes (tested on
random scenes, `Tests/RasterTxFast.lean`): outside a layer's dirty rectangle the layer still
holds its initial content (the backdrop, or the exactly neutral colour), and `combine` leaves
such a pixel as it is (`Normal`: skipped; other modes: `B(cb, n) = cb`, then
`blend cb cb f = cb`). -/

/-- `beginLayer` of 7.3c. -/
def beginLayerSpec (W H : Nat) (t : TxState) (buf : ByteArray) (fx : Fx) : TxState × ByteArray :=
  if openCount t.stack < maxLayerDepth then
    let cur := if fx.blend ≠ .normal ∧ fx.blend.separable then fillBufSpec W H (neutral fx.blend)
      else buf
    ({ t with stack := .opened buf fx none :: t.stack }, cur)
  else ({ t with stack := .skipped :: t.stack }, buf)

/-- `endLayer` of 7.3c: `combine` over `r`. -/
def endLayerSpec (W H : Nat) (r : IRect) (t : TxState) (buf : ByteArray) : TxState × ByteArray :=
  match t.stack with
  | [] => (t, buf)
  | .skipped :: rest => ({ t with stack := rest }, buf)
  | .knock _ :: rest => ({ t with stack := rest }, buf)
  | .opened back fx _ :: rest => ({ t with stack := rest }, combine W H r back buf fx)

/-- `beginGroup` of 7.3c, with the knockout frame of task 7.3i. -/
def beginGroupSpec (W H : Nat) (t : TxState) (buf : ByteArray) (g : GroupInfo) :
    TxState × ByteArray :=
  let fx : Fx := { alpha := compByte g.alpha, blend := g.blend, mask := g.smask.bind t.mask? }
  pushKnock g.knockout <|
    if fx.alpha = 255 ∧ fx.blend = .normal ∧ fx.mask.isNone then
      ({ t with stack := .skipped :: t.stack }, buf)
    else beginLayerSpec W H t buf fx

/-- `paintFx` of 7.3c. -/
def paintFxSpec {S : Type} (P : Painter S) (W H : Nat) (s : S) (it : DisplayItem) : S :=
  match itemFx (P.tx s) it with
  | none => P.paint s it
  | some fx =>
    let r := beginLayerSpec W H (P.tx s) (P.buf s) fx
    let s1 := P.paint (P.setBuf (P.setTx s r.1) r.2) it
    let r2 := endLayerSpec W H (Clip.pageRect W H) (P.tx s1) (P.buf s1)
    P.setBuf (P.setTx s1 r2.1) r2.2

/-- **The reference driver** (`renderTx` of 7.3c). -/
def renderTxSpec {S : Type} (P : Painter S) (W H : Nat) : Nat → S → DisplayItem → S
  | _, s, .groupBegin g =>
    let r := beginGroupSpec W H (P.tx s) (P.buf s) g
    P.setBuf (P.setTx s r.1) r.2
  | _, s, .groupEnd =>
    let r := endLayerSpec W H (Clip.pageRect W H) (popKnock (P.tx s)) (P.buf s)
    P.setBuf (P.setTx s r.1) r.2
  | 0, s, .softMask .. => s
  | f + 1, s, .softMask id info items =>
    let draw : ByteArray → ByteArray := fun base =>
      P.buf (items.foldl (renderTxSpec P W H f)
        (P.setBuf (P.setTx s { masks := (P.tx s).masks }) base))
    P.setTx s ((P.tx s).addMask id (maskFromSpec info W H draw))
  | _, s, it => paintKT P W H (paintFxSpec P W H) false s it

/-! ## 8. Checks -/

-- The fast buffers have the 7.3c bytes.
#guard fillBuf 3 2 7 == fillBufSpec 3 2 7 && fillBuf 0 4 1 == fillBufSpec 0 4 1 &&
  solidBuf 3 2 (1, 2, 3) == solidBufSpec 3 2 (1, 2, 3)
-- Exactly neutral modes: `B(cb, neutral m) = cb` for every byte.
#guard [BlendMode.multiply, .screen, .darken, .lighten, .colorDodge, .colorBurn, .difference,
  .exclusion].all fun m => exactNeutral m && (List.range 256).all fun cb => blendSep m cb (neutral m) == cb
-- `exactNeutral` is exactly the set of separable modes whose neutral byte is neutral for every byte.
#guard [BlendMode.multiply, .screen, .overlay, .darken, .lighten, .colorDodge, .colorBurn,
  .hardLight, .softLight, .difference, .exclusion].all fun m =>
  exactNeutral m == (List.range 256).all fun cb => blendSep m cb (neutral m) == cb
-- Non-separable modes: `B(cb, cb) = cb` on a few pixels.
#guard [BlendMode.hue, .saturation, .color, .luminosity].all fun m =>
  [(0, 0, 0), (255, 255, 255), (12, 200, 99), (128, 128, 128), (255, 0, 7), (3, 254, 1)].all
    fun c => blendRGB m c c == c
-- `unionR` ignores empty rectangles.
#guard unionR emptyRect ⟨1, 2, 3, 4⟩ == ⟨1, 2, 3, 4⟩ &&
  unionR ⟨1, 2, 3, 4⟩ ⟨5, 0, 6, 1⟩ == ⟨1, 0, 6, 4⟩

end SafePdf.Core.Raster.Transparency
