import SafePdf.Core.Raster.Fill
import SafePdf.Core.Raster.Stroke
import SafePdf.Core.Content.DisplayList

/-!
# Clipping and page-level path rendering (task 7.2c)

Plan.md §6 Phase 7 ("scanline fill …, stroking, clipping, anti-aliasing"; "Proven: totality,
resource bounds (S3: work ≤ f(area, display-list size))"), §4 **S3**. ISO 32000-2 §8.5.4
(clipping path operators: the clip region is the intersection of the current clip with the
inside of the new path under its rule), §8.6.4 / §10.4.2 (device colour spaces; the naive
CMYK → RGB conversion), §11.3.7.2 (constant alpha `CA`/`ca`).

## Design

* **Clip masks.** A `Content.Clip` is a list of `ClipPath`s, newest first; the region is the
  intersection of all of them (`[]` = unclipped, represented by `none`). Each clip path is
  filled with its own rule by the 7.2a rasterizer (`Fill.fillEdgesCounted`) into a coverage
  `Fill.Mask`. The newest path is filled only over the rectangle of the intersection of the
  older ones (outside it the result is 0 anyway), so nested clips get cheaper as they nest.
* **Intersection = coverage product** (`mul255 a b = round(a·b / 255)`), as MuPDF composes
  clip masks (each clip is a mask multiplied into the next). It treats the two coverages as
  independent area fractions, which is right for unrelated edges; on interior pixels
  (`255`) and exterior pixels (`0`) it agrees with `min` exactly (`mul255_255_left`,
  `mul255_zero_left`), so the only difference is along anti-aliased edges that coincide,
  where the product is slightly lighter-weighted. Choosing MuPDF's rule keeps the pixel
  differential (M7) tight. Both bounds that matter hold: the product is `≤` each factor
  (`mul255_le_left`, `mul255_le_right`).
* **Clip cache.** Display items of one page usually share a few clip lists (the persistent
  list of the interpreter). `ClipCache` keeps at most `Config.clipCacheSize`
  (`Limits.clipCacheSize`, 16) `(Clip, Mask)` pairs, most recently inserted first (oldest evicted). A miss on `cp :: rest` looks up
  `rest` first (recursively), so a nested clip reuses the mask of its parent. Keys are
  compared with the derived `DecidableEq` on paths (no pointer equality in pure code).
* **Applying a clip** to a fill or stroke mask is the same product, evaluated per pixel at
  compositing time (`covAt`): `covAt_le_mask`, `covAt_le_clip`. Fill masks are computed over
  the clip's rectangle only (`itemWindow`).
* **Compositing.** The page buffer is RGBA8, row-major, **opaque white** to start; every pixel
  stays opaque (alpha byte 255), so straight and premultiplied source-over coincide:
  `out = round((src·a + dst·(255 − a)) / 255)` per channel with `a = cov · alpha / 255`
  (`blend`). `alpha` is the item's constant alpha (`ca` for fills, `CA` for strokes, carried
  by `FillStyle.alpha` / `StrokeStyle.alpha`). Colours (`deviceRGB`): Gray `g ↦ (g, g, g)`;
  RGB as is; CMYK naive `r = 1 − min(1, c + k)` (and likewise `g`, `b`), as ISO 32000-2
  §10.4.2.4 describes and MuPDF does without ICC; a **pattern** colour → mid grey `(128, 128,
  128)` (the same placeholder as the SVG view, until patterns are rendered). Colours of
  `Indexed`/`Separation`/`DeviceN`/`Lab` spaces already arrive as their alternate's device
  colour (`Content.GState` module doc). Components are rounded to bytes with
  `round(raw · 255 / 10⁶)` (`compByte`: gray 0.5 → 128).
* **Compositing speed (task 7.2e).** `composite` is a row-by-row loop over the paintable
  rectangle (`paintRect`: item rectangle ∩ mask ∩ clip ∩ page) with incremental byte offsets,
  `UInt32` arithmetic, zero-coverage pixels skipped and opaque pixels written directly; the
  7.2c per-pixel loop (`compositeSpec`, coverage closure `covAt`, `Int` coordinates and a
  division per pixel, ≈ 150 ns/px compiled) is kept as its specification. They agree byte
  for byte (tested on 5000 pseudo-random cases, `Tests/RasterComposite.lean`; not proved).
  `scripts/bench-raster.sh`: full-page fill 69 → 6 ms.
* **The page.** `renderPaths page zoom rot items` uses the CropBox and the rotation
  `Geom.rotAdd page.rotate rot` (page `/Rotate` + user rotation), the view matrix
  `Geom.viewMatrix` (C2, task 7.1; y flipped, origin top-left) and a pixel size of
  `⌈screenSize⌉`, each side capped at `Config.maxPageSide` (`Limits.maxPageSide`, 16384: the
  pixel count stays `≤ 2²⁸`, as `Limits.maxImagePixels`; a larger page is cropped, never an
  error).
  Only `fillPath` and `strokePath` items paint here; `clip` items are informational (every
  item carries its clip); glyph runs, images and shadings are 7.3's.
* **Strokes are a parameter** (`StrokeFn`, given the render `Config`): the default
  `defaultStroke` is 7.2b's stroker; `hairlineStroke` is a simpler placeholder that draws
  every segment (curves as their chord) as a 1-pixel-wide band. Whatever the stroker
  returns, compositing only visits the part of its mask inside the item's window, so the
  compositing work stays bounded.

## What is proven

* `mul255_le_left`/`_right`/`_le_255`, `mul255_255_left`, `mul255_zero_left`: the coverage
  product never exceeds either factor nor 255, and is exact on 0 and 255.
* `Mask.tabulate_size`, `Mask.tabulate_get`, `Mask.inter_get_le_left`/`_right`: an intersected
  clip mask has `w · h` bytes and its coverage is pointwise `≤` both operands.
* `covAt_le_mask`, `covAt_le_clip`, `covAt_le_255`: clipped coverage `≤` unclipped coverage,
  `≤` clip coverage, `≤ 255`.
* `renderItems_size`, `renderPaths_size`: the output buffer has exactly `4 · w · h` bytes
  (`composite_size`, `compositeSpec_size`: compositing preserves the buffer size).
* **S3**: `clipMaskC_steps_le` (a clip list costs at most `Σ pathCost` over its paths, cache
  hits cost 0), `renderItemsCounted_steps_le` (the counted work of a page is at most
  `Σ itemCost` over the items, where
  `pathCost = H · (S · (segCap · #segments + 1) + W + 1) + W·H` (`segCap` from
  `Limits.curveSegCap`)
  bounds flattening + scanline + compositing of one path on a `W × H` page). The stroker's own
  work is 7.2b's theorem; here a stroke counts only its compositing (`≤ W · H`). The derived
  `DecidableEq` key comparison of the cache and the crossing sort of 7.2a are not counted.
-/

namespace SafePdf.Core.Raster.Clip

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill
open SafePdf.Core.Content (FillRule Clip ClipPath Color Comp FillStyle StrokeStyle DisplayItem
  DisplayList Path)

/-! ## 1. Coverage arithmetic -/

/-- Product of two coverages in `0 … 255`, rounded: `round(a · b / 255)`. -/
def mul255 (a b : Nat) : Nat := (a * b + 127) / 255

/-- The product does not exceed the left factor. -/
theorem mul255_le_left (a b : Nat) (hb : b ≤ 255) : mul255 a b ≤ a := by
  unfold mul255
  have : a * b ≤ a * 255 := Nat.mul_le_mul_left a hb
  generalize a * b = p at this
  omega

/-- The product does not exceed the right factor. -/
theorem mul255_le_right (a b : Nat) (ha : a ≤ 255) : mul255 a b ≤ b := by
  unfold mul255
  have : a * b ≤ 255 * b := Nat.mul_le_mul_right b ha
  generalize a * b = p at this
  omega

/-- The product of coverages is a coverage. -/
theorem mul255_le_255 (a b : Nat) (ha : a ≤ 255) (hb : b ≤ 255) : mul255 a b ≤ 255 :=
  Nat.le_trans (mul255_le_left a b hb) ha

/-- Full coverage is the unit of the product. -/
theorem mul255_255_left (b : Nat) : mul255 255 b = b := by
  unfold mul255; omega

/-- Zero coverage absorbs. -/
theorem mul255_zero_left (b : Nat) : mul255 0 b = 0 := by
  unfold mul255; simp

/-- A `UInt8` read as a coverage is at most 255. -/
theorem toNat_le_255 (u : UInt8) : u.toNat ≤ 255 := by
  have := u.toNat_lt; simp at this; omega

/-! ## 2. Rectangles and masks -/

/-- Intersection of two pixel rectangles (possibly empty). -/
def _root_.SafePdf.Core.Raster.Fill.IRect.inter (a b : IRect) : IRect :=
  ⟨max a.x0 b.x0, max a.y0 b.y0, min a.x1 b.x1, min a.y1 b.y1⟩

/-- Width in pixels (0 for an empty rectangle). -/
def _root_.SafePdf.Core.Raster.Fill.IRect.width (r : IRect) : Nat := (r.x1 - r.x0).toNat

/-- Height in pixels (0 for an empty rectangle). -/
def _root_.SafePdf.Core.Raster.Fill.IRect.height (r : IRect) : Nat := (r.y1 - r.y0).toNat

/-- The intersection is no wider than the left operand. -/
theorem _root_.SafePdf.Core.Raster.Fill.IRect.inter_width_le_left (a b : IRect) : (a.inter b).width ≤ a.width := by
  simp only [IRect.inter, IRect.width]; omega

/-- The intersection is no taller than the left operand. -/
theorem _root_.SafePdf.Core.Raster.Fill.IRect.inter_height_le_left (a b : IRect) : (a.inter b).height ≤ a.height := by
  simp only [IRect.inter, IRect.height]; omega

/-- The intersection is no wider than the right operand. -/
theorem _root_.SafePdf.Core.Raster.Fill.IRect.inter_width_le_right (a b : IRect) : (a.inter b).width ≤ b.width := by
  simp only [IRect.inter, IRect.width]; omega

/-- The intersection is no taller than the right operand. -/
theorem _root_.SafePdf.Core.Raster.Fill.IRect.inter_height_le_right (a b : IRect) : (a.inter b).height ≤ b.height := by
  simp only [IRect.inter, IRect.height]; omega

/-- The pixel rectangle a mask covers. -/
def _root_.SafePdf.Core.Raster.Fill.Mask.rect (m : Mask) : IRect := ⟨m.x0, m.y0, m.x0 + m.w, m.y0 + m.h⟩

/-- A mask over the rectangle `r` whose pixel `(x, y)` is `f x y`. -/
def _root_.SafePdf.Core.Raster.Fill.Mask.tabulate (r : IRect) (f : Int → Int → UInt8) : Mask :=
  let w := r.width
  let h := r.height
  { x0 := r.x0, y0 := r.y0, w := w, h := h,
    data := ByteArray.mk (Array.ofFn (n := w * h) fun i =>
      f (r.x0 + ((i.val % w : Nat) : Int)) (r.y0 + ((i.val / w : Nat) : Int))) }

/-- Indexing a `ByteArray` built from an array. -/
theorem byteArray_mk_getElem? (a : Array UInt8) (i : Nat) : (ByteArray.mk a)[i]? = a[i]? := by
  show decidableGetElem? (ByteArray.mk a) i = _
  unfold decidableGetElem?
  by_cases h : i < a.size
  · have h' : i < (ByteArray.mk a).size := h
    simp only [h', Array.getElem?_eq_getElem h]; rfl
  · have h' : ¬ i < (ByteArray.mk a).size := h
    simp only [h', Array.getElem?_eq_none (Nat.le_of_not_lt h)]; rfl

/-- **Buffer shape.** A tabulated mask has exactly `w · h` bytes. -/
theorem _root_.SafePdf.Core.Raster.Fill.Mask.tabulate_size (r : IRect) (f : Int → Int → UInt8) :
    (Mask.tabulate r f).data.size = (Mask.tabulate r f).w * (Mask.tabulate r f).h := by
  simp [Mask.tabulate, ByteArray.size]

/-- A tabulated mask reads back `f` inside its rectangle and `0` outside. -/
theorem _root_.SafePdf.Core.Raster.Fill.Mask.tabulate_get (r : IRect) (f : Int → Int → UInt8) (x y : Int) :
    (Mask.tabulate r f).get x y =
      if r.x0 ≤ x ∧ x < r.x0 + r.width ∧ r.y0 ≤ y ∧ y < r.y0 + r.height then f x y else 0 := by
  simp only [Mask.get, Mask.tabulate]
  split
  · rename_i hin
    simp only [hin, and_self, ite_true]
    obtain ⟨h1, h2, h3, h4⟩ := hin
    generalize hw : r.width = w at *
    generalize hh : r.height = h at *
    obtain ⟨i, hi⟩ : ∃ i : Nat, (i : Int) = x - r.x0 := ⟨(x - r.x0).toNat, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j : Nat, (j : Int) = y - r.y0 := ⟨(y - r.y0).toNat, by omega⟩
    have hiw : i < w := by omega
    have hjh : j < h := by omega
    have hk : ((y - r.y0) * (w : Int) + (x - r.x0)).toNat = j * w + i := by
      rw [← hi, ← hj]; omega
    have hlt : j * w + i < w * h := by
      have : (j + 1) * w ≤ h * w := Nat.mul_le_mul_right w hjh
      rw [Nat.succ_mul] at this; rw [Nat.mul_comm w h]; omega
    rw [hk, byteArray_mk_getElem?, Array.getElem?_ofFn]
    simp only [hlt, dite_true, Option.getD_some]
    have hw0 : 0 < w := by omega
    have hm : (j * w + i) % w = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hiw
    have hd : (j * w + i) / w = j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hiw]; omega
    rw [hm, hd, hi, hj]
    congr 1 <;> omega
  · rename_i hout
    have : ¬ (r.x0 ≤ x ∧ x < r.x0 + r.width ∧ r.y0 ≤ y ∧ y < r.y0 + r.height) := hout
    simp only [this, ite_false]

/-- Pointwise product of two masks over the intersection of their rectangles. -/
def _root_.SafePdf.Core.Raster.Fill.Mask.inter (a b : Mask) : Mask :=
  Mask.tabulate (a.rect.inter b.rect)
    (fun x y => UInt8.ofNatClamp (mul255 (a.get x y).toNat (b.get x y).toNat))

/-- Reading a clamped byte of a value `≤ 255` gives the value back. -/
theorem toNat_ofNatClamp_le (n : Nat) (h : n ≤ 255) : (UInt8.ofNatClamp n).toNat = n :=
  UInt8.toNat_ofNatClamp_of_lt (by simp [UInt8.size]; omega)

/-- The intersection's coverage is the product, or 0. -/
theorem _root_.SafePdf.Core.Raster.Fill.Mask.inter_get (a b : Mask) (x y : Int) :
    ((a.inter b).get x y).toNat = 0 ∨
      ((a.inter b).get x y).toNat = mul255 (a.get x y).toNat (b.get x y).toNat := by
  simp only [Mask.inter, Mask.tabulate_get]
  split
  · right
    exact toNat_ofNatClamp_le _
      (mul255_le_255 _ _ (toNat_le_255 _) (toNat_le_255 _))
  · left; rfl

/-- **Intersection ≤ left operand**, pointwise. -/
theorem _root_.SafePdf.Core.Raster.Fill.Mask.inter_get_le_left (a b : Mask) (x y : Int) :
    ((a.inter b).get x y).toNat ≤ (a.get x y).toNat := by
  rcases Mask.inter_get a b x y with h | h <;> rw [h]
  · exact Nat.zero_le _
  · exact mul255_le_left _ _ (toNat_le_255 _)

/-- **Intersection ≤ right operand**, pointwise. -/
theorem _root_.SafePdf.Core.Raster.Fill.Mask.inter_get_le_right (a b : Mask) (x y : Int) :
    ((a.inter b).get x y).toNat ≤ (b.get x y).toNat := by
  rcases Mask.inter_get a b x y with h | h <;> rw [h]
  · exact Nat.zero_le _
  · exact mul255_le_right _ _ (toNat_le_255 _)

/-- The area (pixel count) of a mask's rectangle. -/
def _root_.SafePdf.Core.Raster.Fill.Mask.area (m : Mask) : Nat := m.w * m.h

/-! ## 3. Counted fill bounds (from 7.2a) -/

/-- The mask of `fillEdgesCounted` is no wider than its window. -/
theorem fillEdgesCounted_w_le (es : Array Edge) (rule : FillRule) (win : IRect) (cfg : Config) :
    (fillEdgesCounted es rule win cfg).1.w ≤ win.width := by
  have := (maskRect_le (es.mergeSort (fun a b => a.y0 ≤ b.y0)) win).1
  simp only [fillEdgesCounted, IRect.width]; omega

/-- The mask of `fillEdgesCounted` is no taller than its window. -/
theorem fillEdgesCounted_h_le (es : Array Edge) (rule : FillRule) (win : IRect) (cfg : Config) :
    (fillEdgesCounted es rule win cfg).1.h ≤ win.height := by
  have := (maskRect_le (es.mergeSort (fun a b => a.y0 ≤ b.y0)) win).2
  simp only [fillEdgesCounted, IRect.height]; omega

/-- Fill a page-space path through `m` over `win`, with the counted rasterizer work. -/
def fillCounted (cfg : Config) (m : Aff) (p : Path) (rule : FillRule) (win : IRect) :
    Mask × Nat :=
  fillEdgesCounted (flatten cfg win (ofContentPath m p cfg)) rule win cfg

/-- Work bound of one path fill in terms of the window and the segment count. -/
theorem fillCounted_steps_le (cfg : Config) (m : Aff) (p : Path) (rule : FillRule)
    (win : IRect) :
    (fillCounted cfg m p rule win).2 ≤
      win.height * (cfg.samples * (cfg.segCap * p.segs.size + 1) + win.width + 1) := by
  simp only [fillCounted]
  have h1 := fillEdgesCounted_steps_le (flatten cfg win (ofContentPath m p cfg)) rule win cfg
  have h2 := fillEdgesCounted_w_le (flatten cfg win (ofContentPath m p cfg)) rule win cfg
  have h3 := fillEdgesCounted_h_le (flatten cfg win (ofContentPath m p cfg)) rule win cfg
  have h4 := flatten_size_le cfg win (ofContentPath m p cfg)
  have h5 : (ofContentPath m p cfg).size = p.segs.size := by simp [ofContentPath]
  rw [h5] at h4
  refine Nat.le_trans h1 (Nat.mul_le_mul h3 ?_)
  have := Nat.mul_le_mul_left cfg.samples h4
  omega

/-- The fill mask lies in a rectangle no wider than the window. -/
theorem fillCounted_w_le (cfg : Config) (m : Aff) (p : Path) (rule : FillRule) (win : IRect) :
    (fillCounted cfg m p rule win).1.w ≤ win.width :=
  fillEdgesCounted_w_le _ _ _ _

/-- The fill mask lies in a rectangle no taller than the window. -/
theorem fillCounted_h_le (cfg : Config) (m : Aff) (p : Path) (rule : FillRule) (win : IRect) :
    (fillCounted cfg m p rule win).1.h ≤ win.height :=
  fillEdgesCounted_h_le _ _ _ _

/-! ## 4. Clip masks with a bounded cache -/

/-- Cached clip masks, most recently inserted first, at most `Config.clipCacheSize` entries
(`Limits.clipCacheSize`). -/
structure ClipCache where
  /-- `(clip list, its mask)` pairs. -/
  entries : List (Clip × Mask) := []
  /-- Number of hits (for tests and statistics). -/
  hits : Nat := 0
  deriving Inhabited

/-- Look `c` up in the cache. -/
def ClipCache.find? (cc : ClipCache) (c : Clip) : Option Mask :=
  (cc.entries.find? (fun e => decide (e.1 = c))).map (·.2)

/-- Insert an entry, evicting the oldest beyond `cap` entries (`Config.clipCacheSize`). -/
def ClipCache.insert (cc : ClipCache) (cap : Nat) (c : Clip) (m : Mask) : ClipCache :=
  { cc with entries := ((c, m) :: cc.entries).take cap }

/-- The cache never holds more than `cap` entries after an insertion. -/
theorem ClipCache.insert_length_le (cc : ClipCache) (cap : Nat) (c : Clip) (m : Mask) :
    (cc.insert cap c m).entries.length ≤ cap := by
  simp only [ClipCache.insert, List.length_take]; exact Nat.min_le_left _ _

/-- Cost bound for one path on a page of `W × H` pixels: flattening + scanline (7.2a's bound
with the window at most the page) + one pass over at most `W · H` pixels. -/
def pathCost (cfg : Config) (W H : Nat) (p : Path) : Nat :=
  H * (cfg.samples * (cfg.segCap * p.segs.size + 1) + W + 1) + W * H

/-- Cost bound for a clip list: the sum over its paths. -/
def clipCost (cfg : Config) (W H : Nat) : Clip → Nat
  | [] => 0
  | cp :: rest => pathCost cfg W H cp.path + clipCost cfg W H rest

/-- The page rectangle `[0, W) × [0, H)`. -/
def pageRect (W H : Nat) : IRect := ⟨0, 0, W, H⟩

/-- Window of the newest clip path: the older clips' rectangle (or the page). -/
def clipWindow (W H : Nat) : Option Mask → IRect
  | none => pageRect W H
  | some t => t.rect.inter (pageRect W H)

/-- The clip window is inside the page: width. -/
theorem clipWindow_width_le (W H : Nat) (t : Option Mask) : (clipWindow W H t).width ≤ W := by
  cases t with
  | none => simp [clipWindow, pageRect, IRect.width]
  | some t =>
    have := IRect.inter_width_le_right t.rect (pageRect W H)
    simp only [clipWindow]; simp [pageRect, IRect.width] at this ⊢; omega

/-- The clip window is inside the page: height. -/
theorem clipWindow_height_le (W H : Nat) (t : Option Mask) :
    (clipWindow W H t).height ≤ H := by
  cases t with
  | none => simp [clipWindow, pageRect, IRect.height]
  | some t =>
    have := IRect.inter_height_le_right t.rect (pageRect W H)
    simp only [clipWindow]; simp [pageRect, IRect.height] at this ⊢; omega

/-- Combine the newest clip path's mask with the older clips' mask. -/
def combine (hm : Mask) : Option Mask → Mask
  | none => hm
  | some t => hm.inter t

/-- The combined mask is no larger than the head mask's rectangle. -/
theorem combine_area_le (hm : Mask) (t : Option Mask) : (combine hm t).area ≤ hm.w * hm.h := by
  cases t with
  | none => simp [combine, Mask.area]
  | some t =>
    simp only [combine, Mask.inter, Mask.area, Mask.tabulate]
    have h1 := IRect.inter_width_le_left hm.rect t.rect
    have h2 := IRect.inter_height_le_left hm.rect t.rect
    have : hm.rect.width = hm.w := by simp only [Mask.rect, IRect.width]; omega
    have : hm.rect.height = hm.h := by simp only [Mask.rect, IRect.height]; omega
    exact Nat.mul_le_mul (by omega) (by omega)

/-- **Clip mask** of a clip list on a `W × H` page through the page → device matrix `m`
(`none` = unclipped), with the updated cache and the counted work. -/
def clipMaskC (cfg : Config) (m : Aff) (W H : Nat) (cc : ClipCache) :
    Clip → Option Mask × ClipCache × Nat
  | [] => (none, cc, 0)
  | cp :: rest =>
    match cc.find? (cp :: rest) with
    | some mk => (some mk, { cc with hits := cc.hits + 1 }, 0)
    | none =>
      let r1 := clipMaskC cfg m W H cc rest
      let win := clipWindow W H r1.1
      let f := fillCounted cfg m cp.path cp.rule win
      let res := combine f.1 r1.1
      (some res, r1.2.1.insert cfg.clipCacheSize (cp :: rest) res, r1.2.2 + f.2 + res.area)

/-- **S3 for clips.** Computing a clip list's mask costs at most `clipCost` (cache hits cost
nothing). -/
theorem clipMaskC_steps_le (cfg : Config) (m : Aff) (W H : Nat) (cc : ClipCache) (c : Clip) :
    (clipMaskC cfg m W H cc c).2.2 ≤ clipCost cfg W H c := by
  induction c generalizing cc with
  | nil => simp [clipMaskC]
  | cons cp rest ih =>
    simp only [clipMaskC]
    split
    · exact Nat.zero_le _
    · simp only [clipCost, pathCost]
      have h0 := ih cc
      have h1 := fillCounted_steps_le cfg m cp.path cp.rule
        (clipWindow W H (clipMaskC cfg m W H cc rest).1)
      have hw := clipWindow_width_le W H (clipMaskC cfg m W H cc rest).1
      have hh := clipWindow_height_le W H (clipMaskC cfg m W H cc rest).1
      have h2 := combine_area_le
        (fillCounted cfg m cp.path cp.rule (clipWindow W H (clipMaskC cfg m W H cc rest).1)).1
        (clipMaskC cfg m W H cc rest).1
      have h3 := fillCounted_w_le cfg m cp.path cp.rule
        (clipWindow W H (clipMaskC cfg m W H cc rest).1)
      have h4 := fillCounted_h_le cfg m cp.path cp.rule
        (clipWindow W H (clipMaskC cfg m W H cc rest).1)
      generalize (clipMaskC cfg m W H cc rest) = r1 at *
      generalize (fillCounted cfg m cp.path cp.rule (clipWindow W H r1.1)) = f at *
      generalize hcw : (clipWindow W H r1.1).width = cw at *
      generalize hch : (clipWindow W H r1.1).height = ch at *
      have e1 : ch * (cfg.samples * (cfg.segCap * cp.path.segs.size + 1) + cw + 1) ≤
          H * (cfg.samples * (cfg.segCap * cp.path.segs.size + 1) + W + 1) :=
        Nat.mul_le_mul hh (by omega)
      have e2 : f.1.w * f.1.h ≤ W * H := Nat.mul_le_mul (by omega) (by omega)
      omega

/-! ## 5. Colours and compositing -/

/-- A colour component as a byte: `round(raw · 255 / 10⁶)`. -/
def compByte (c : Comp) : Nat := (c.raw.toNat * 255 + 500000) / 1000000

/-- A component byte is at most 255. -/
theorem compByte_le (c : Comp) : compByte c ≤ 255 := by
  have := c.hi
  unfold compByte; unfold Content.fixedScale at this; omega

/-- Device colour → RGB bytes (naive CMYK conversion; patterns → mid grey). -/
def deviceRGB : Color → Nat × Nat × Nat
  | .gray g => (compByte g, compByte g, compByte g)
  | .rgb r g b => (compByte r, compByte g, compByte b)
  | .cmyk c m y k =>
    (255 - min 255 (compByte c + compByte k), 255 - min 255 (compByte m + compByte k),
      255 - min 255 (compByte y + compByte k))
  | .pattern _ => (128, 128, 128)

/-- Source-over of `s` onto `d` with opacity `a` (all bytes): `round((s·a + d·(255 − a))/255)`. -/
def blend (s d a : Nat) : UInt8 := UInt8.ofNatClamp ((s * a + d * (255 - a) + 127) / 255)

/-- Read a byte (`0` out of range). -/
def getB (b : ByteArray) (i : Nat) : Nat := (b[i]?.getD 0).toNat

/-- Write a byte (ignored out of range). -/
def setB (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if h : i < b.size then b.set i v h else b

/-- Writing a byte preserves the size. -/
theorem setB_size (b : ByteArray) (i : Nat) (v : UInt8) : (setB b i v).size = b.size := by
  unfold setB; split
  · cases b; show (Array.set _ _ _ _).size = _; simp; rfl
  · rfl

/-- Composite colour `rgb` with opacity `a` (`0 … 255`) at pixel `(x, y)` of a page buffer
of width `W` (RGBA, row-major). -/
def blendPx (b : ByteArray) (W : Nat) (x y : Int) (rgb : Nat × Nat × Nat) (a : Nat) :
    ByteArray :=
  if a = 0 ∨ x < 0 ∨ (W : Int) ≤ x ∨ y < 0 then b
  else
    let i := 4 * (y.toNat * W + x.toNat)
    let b := setB b i (blend rgb.1 (getB b i) a)
    let b := setB b (i + 1) (blend rgb.2.1 (getB b (i + 1)) a)
    setB b (i + 2) (blend rgb.2.2 (getB b (i + 2)) a)

/-- Compositing a pixel preserves the buffer size. -/
theorem blendPx_size (b : ByteArray) (W : Nat) (x y : Int) (rgb : Nat × Nat × Nat) (a : Nat) :
    (blendPx b W x y rgb a).size = b.size := by
  unfold blendPx; split
  · rfl
  · simp only [setB_size]

/-- Clipped coverage of pixel `(x, y)`: the mask coverage times the clip coverage. -/
def covAt (m : Mask) (c : Option Mask) (x y : Int) : Nat :=
  match c with
  | none => (m.get x y).toNat
  | some c => mul255 (m.get x y).toNat (c.get x y).toNat

/-- **Clipped coverage ≤ unclipped coverage.** -/
theorem covAt_le_mask (m : Mask) (c : Option Mask) (x y : Int) :
    covAt m c x y ≤ (m.get x y).toNat := by
  cases c with
  | none => exact Nat.le_refl _
  | some c => exact mul255_le_left _ _ (toNat_le_255 _)

/-- **Clipped coverage ≤ clip coverage.** -/
theorem covAt_le_clip (m c : Mask) (x y : Int) : covAt m (some c) x y ≤ (c.get x y).toNat :=
  mul255_le_right _ _ (toNat_le_255 _)

/-- Clipped coverage is a coverage. -/
theorem covAt_le_255 (m : Mask) (c : Option Mask) (x y : Int) : covAt m c x y ≤ 255 :=
  Nat.le_trans (covAt_le_mask m c x y) (toNat_le_255 _)

/-- **Reference compositor** (the 7.2c definition, kept as the specification of `composite`):
composite over the pixels `i, i+1, …` (`fuel` of them) of rectangle `r` (row-major, width
`w`), with coverage `cov`, colour `rgb` and constant alpha `alpha`. -/
def compLoopSpec (W : Nat) (cov : Int → Int → Nat) (r : IRect) (w : Nat) (rgb : Nat × Nat × Nat)
    (alpha : Nat) : (fuel i : Nat) → ByteArray → ByteArray
  | 0, _, b => b
  | fuel + 1, i, b =>
    let x := r.x0 + ((i % w : Nat) : Int)
    let y := r.y0 + ((i / w : Nat) : Int)
    compLoopSpec W cov r w rgb alpha fuel (i + 1) (blendPx b W x y rgb (mul255 (cov x y) alpha))

/-- The reference compositor preserves the buffer size. -/
theorem compLoopSpec_size (W : Nat) (cov : Int → Int → Nat) (r : IRect) (w : Nat)
    (rgb : Nat × Nat × Nat) (alpha : Nat) (fuel i : Nat) (b : ByteArray) :
    (compLoopSpec W cov r w rgb alpha fuel i b).size = b.size := by
  induction fuel generalizing i b with
  | zero => rfl
  | succ n ih => simp only [compLoopSpec, ih, blendPx_size]

/-- **Reference compositor**: the coverage `cov` over the rectangle `r`, one pixel at a time
(the specification `composite` is tested against, `Tests/RasterComposite.lean`). -/
def compositeSpec (b : ByteArray) (W : Nat) (cov : Int → Int → Nat) (r : IRect)
    (rgb : Nat × Nat × Nat) (alpha : Nat) : ByteArray :=
  compLoopSpec W cov r r.width rgb alpha (r.width * r.height) 0 b

/-- The reference compositor preserves the buffer size. -/
theorem compositeSpec_size (b : ByteArray) (W : Nat) (cov : Int → Int → Nat) (r : IRect)
    (rgb : Nat × Nat × Nat) (alpha : Nat) : (compositeSpec b W cov r rgb alpha).size = b.size :=
  compLoopSpec_size _ _ _ _ _ _ _ _ _

/-! ### Fast compositor (task 7.2e)

Same result as `compositeSpec … (covAt fm cm) …`, computed row by row over the rectangle
`r ∩ fm.rect ∩ cm.rect ∩ ([0, W) × [0, ∞))` (outside it the reference compositor's coverage
is 0, or `blendPx` skips the pixel), with the mask/clip/page byte offsets advanced
incrementally (no division, no `Int` per pixel, no coverage closure), `UInt32` arithmetic
(every intermediate `≤ 255 · 255 + 127`), zero-coverage pixels skipped after one byte read,
and opaque pixels (`a = 255`, where `blend s d 255 = s`) written without reading the page.
Each channel is read and written through `getB`/`setB` exactly as `blendPx` does, so even an
odd-sized buffer gives the same bytes. Inputs outside the byte range (`alpha` or a colour
component `> 255`, never produced by `paintMask`) fall back to `compositeSpec`. -/

/-- A byte of `b` as `UInt32` (`0` out of range). -/
@[inline] def getU (b : ByteArray) (i : Nat) : UInt32 :=
  if h : i < b.size then (b.get i h).toUInt32 else 0

/-- `mul255` on `UInt32` (arguments `≤ 255`). -/
@[inline] def mul255U (a b : UInt32) : UInt32 := (a * b + 127) / 255

/-- Composite one pixel at byte offset `i` with colour `(sr, sg, sb)` and opacity `a`
(`UInt32`s `≤ 255`), as `blendPx` does inside the page. -/
@[inline] def pxU (b : ByteArray) (i : Nat) (sr sg sb a : UInt32) : ByteArray :=
  if a == 0 then b
  else if a == 255 then
    let b := setB b i sr.toUInt8
    let b := setB b (i + 1) sg.toUInt8
    setB b (i + 2) sb.toUInt8
  else
    let ia := 255 - a
    let b := setB b i ((sr * a + getU b i * ia + 127) / 255).toUInt8
    let b := setB b (i + 1) ((sg * a + getU b (i + 1) * ia + 127) / 255).toUInt8
    setB b (i + 2) ((sb * a + getU b (i + 2) * ia + 127) / 255).toUInt8

/-- `pxU` preserves the buffer size. -/
theorem pxU_size (b : ByteArray) (i : Nat) (sr sg sb a : UInt32) :
    (pxU b i sr sg sb a).size = b.size := by
  unfold pxU; split
  · rfl
  · split <;> simp only [setB_size]

/-- One row, unclipped: `n` pixels, mask bytes from `mi`, page bytes from `bi`. -/
def rowM (md : ByteArray) (sr sg sb al : UInt32) : (n mi bi : Nat) → ByteArray → ByteArray
  | 0, _, _, b => b
  | n + 1, mi, bi, b =>
    let c := getU md mi
    let b := if c == 0 then b else pxU b bi sr sg sb (mul255U c al)
    rowM md sr sg sb al n (mi + 1) (bi + 4) b

/-- One row, clipped: as `rowM` with the clip bytes from `ci` multiplied in. -/
def rowC (md cd : ByteArray) (sr sg sb al : UInt32) :
    (n mi ci bi : Nat) → ByteArray → ByteArray
  | 0, _, _, _, b => b
  | n + 1, mi, ci, bi, b =>
    let c := getU md mi
    let b := if c == 0 then b else pxU b bi sr sg sb (mul255U (mul255U c (getU cd ci)) al)
    rowC md cd sr sg sb al n (mi + 1) (ci + 1) (bi + 4) b

/-- `rowM` preserves the buffer size. -/
theorem rowM_size (md : ByteArray) (sr sg sb al : UInt32) (n mi bi : Nat) (b : ByteArray) :
    (rowM md sr sg sb al n mi bi b).size = b.size := by
  induction n generalizing mi bi b with
  | zero => rfl
  | succ n ih => simp only [rowM, ih]; split <;> simp only [pxU_size]

/-- `rowC` preserves the buffer size. -/
theorem rowC_size (md cd : ByteArray) (sr sg sb al : UInt32) (n mi ci bi : Nat)
    (b : ByteArray) : (rowC md cd sr sg sb al n mi ci bi b).size = b.size := by
  induction n generalizing mi ci bi b with
  | zero => rfl
  | succ n ih => simp only [rowC, ih]; split <;> simp only [pxU_size]

/-- Byte offset of pixel `(x, y)` in a row-major byte grid of width `w` with origin
`(x0, y0)` (arguments inside the grid). -/
@[inline] def offs (x0 y0 : Int) (w : Nat) (x y : Int) : Nat := ((y - y0) * w + (x - x0)).toNat

/-- Rows `y, y+1, …` (`n` of them) of columns `[x, x + cw)`; `clip` is the clip mask, if any. -/
def rows (W : Nat) (fm : Mask) (cm : Option Mask) (sr sg sb al : UInt32) (x : Int) (cw : Nat) :
    (n : Nat) → (y : Int) → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, y, b =>
    let mi := offs fm.x0 fm.y0 fm.w x y
    let bi := 4 * (y.toNat * W + x.toNat)
    let b := match cm with
      | none => rowM fm.data sr sg sb al cw mi bi b
      | some c => rowC fm.data c.data sr sg sb al cw mi (offs c.x0 c.y0 c.w x y) bi b
    rows W fm cm sr sg sb al x cw n (y + 1) b

/-- `rows` preserves the buffer size. -/
theorem rows_size (W : Nat) (fm : Mask) (cm : Option Mask) (sr sg sb al : UInt32) (x : Int)
    (cw : Nat) (n : Nat) (y : Int) (b : ByteArray) :
    (rows W fm cm sr sg sb al x cw n y b).size = b.size := by
  induction n generalizing y b with
  | zero => rfl
  | succ n ih =>
    simp only [rows, ih]; split <;> simp only [rowM_size, rowC_size]

/-- The rectangle a mask can paint on a page of width `W` within `r`: `r ∩ fm.rect ∩ clip
rect ∩ ([0, W) × [0, ∞))`. -/
def paintRect (W : Nat) (fm : Mask) (cm : Option Mask) (r : IRect) : IRect :=
  let r := (r.inter fm.rect).inter ⟨0, 0, W, max r.y1 0⟩
  match cm with
  | none => r
  | some c => r.inter c.rect

/-- **Composite** the mask `fm`, clipped by `cm`, over the rectangle `r` of a page of width
`W`, with colour `rgb` and constant alpha `alpha` (bytes). Equal to
`compositeSpec b W (covAt fm cm) r rgb alpha` (tested in `Tests/RasterComposite.lean`). -/
def composite (b : ByteArray) (W : Nat) (fm : Mask) (cm : Option Mask) (r : IRect)
    (rgb : Nat × Nat × Nat) (alpha : Nat) : ByteArray :=
  if alpha ≤ 255 ∧ rgb.1 ≤ 255 ∧ rgb.2.1 ≤ 255 ∧ rgb.2.2 ≤ 255 then
    let p := paintRect W fm cm r
    rows W fm cm (UInt32.ofNat rgb.1) (UInt32.ofNat rgb.2.1) (UInt32.ofNat rgb.2.2)
      (UInt32.ofNat alpha) p.x0 p.width p.height p.y0 b
  else compositeSpec b W (covAt fm cm) r rgb alpha

/-- Compositing preserves the buffer size. -/
theorem composite_size (b : ByteArray) (W : Nat) (fm : Mask) (cm : Option Mask) (r : IRect)
    (rgb : Nat × Nat × Nat) (alpha : Nat) : (composite b W fm cm r rgb alpha).size = b.size := by
  unfold composite; split
  · exact rows_size _ _ _ _ _ _ _ _ _ _ _ _
  · exact compositeSpec_size _ _ _ _ _ _

/-! ## 6. Strokes (parameter) -/

/-- A stroker: raster configuration (caps), page → device matrix, device window, page-space
path, stroke style ↦ coverage mask (expected inside the window; compositing ignores anything
outside it). Task 7.2b. -/
abbrev StrokeFn := Config → Aff → IRect → Path → StrokeStyle → Mask

/-- A stroker that paints nothing. -/
def noStroke : StrokeFn := fun _ _ _ _ _ => {}

/-- A 1-pixel band around the device segment `a → b` (sorted so all bands have the same
orientation, hence never cancel under nonzero). -/
def bandEdges (es : Array Edge) (a b : FPt) : Array Edge :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  if dx.natAbs ≥ dy.natAbs then
    let (a, b) := if a.x ≤ b.x then (a, b) else (b, a)
    es ++ polygonEdges #[⟨a.x, a.y - 128⟩, ⟨b.x, b.y - 128⟩, ⟨b.x, b.y + 128⟩, ⟨a.x, a.y + 128⟩]
  else
    let (a, b) := if a.y ≤ b.y then (a, b) else (b, a)
    es ++ polygonEdges #[⟨a.x - 128, a.y⟩, ⟨b.x - 128, b.y⟩, ⟨b.x + 128, b.y⟩, ⟨a.x + 128, a.y⟩]

/-- Edges of 1-pixel bands along every segment of a device path (curves as their chords). -/
def hairlineEdges (p : DPath) : Array Edge :=
  let st := p.foldl (fun (st : Array Edge × FPt × FPt) s =>
    match s with
    | .moveTo q => (st.1, q, q)
    | .lineTo q => (bandEdges st.1 st.2.1 q, q, st.2.2)
    | .curveTo _ _ q => (bandEdges st.1 st.2.1 q, q, st.2.2)
    | .closePath => (bandEdges st.1 st.2.1 st.2.2, st.2.2, st.2.2)) (#[], ⟨0, 0⟩, ⟨0, 0⟩)
  st.1

/-- **Placeholder stroker** until 7.2b: every segment as a 1-pixel-wide band (width, caps,
joins and dashes ignored). -/
def hairlineStroke : StrokeFn := fun cfg m win p _ =>
  fillEdges (hairlineEdges (ofContentPath m p cfg)) .nonzero win cfg

/-- The stroker `renderPaths` uses by default: 7.2b's `Stroke.strokePath`, with the render
configuration (so its caps come from the same `Limits`). -/
def defaultStroke : StrokeFn := fun cfg m win p s => Stroke.strokePath m p s win cfg

/-! ## 7. Rendering path items -/

/-- An RGBA8 image, row-major, `4 · w · h` bytes. -/
structure Image where
  /-- Width in pixels. -/
  w : Nat
  /-- Height in pixels. -/
  h : Nat
  /-- RGBA bytes. -/
  data : ByteArray
  deriving Inhabited

/-- Rendering state: page buffer, clip cache, counted work. -/
structure RState where
  /-- RGBA page buffer. -/
  buf : ByteArray
  /-- Clip masks of this page. -/
  cache : ClipCache := {}
  /-- Counted work. -/
  steps : Nat := 0

/-- Device window of an item: its clip's rectangle (or the page). -/
def itemWindow (W H : Nat) (c : Option Mask) : IRect := clipWindow W H c

/-- Paint one coverage mask: composite it, clipped, over its rectangle ∩ the window. -/
def paintMask (W H : Nat) (st : RState) (cm : Option Mask) (fm : Mask) (color : Color)
    (alpha : Comp) (cc : ClipCache) (s : Nat) : RState :=
  let r := fm.rect.inter (itemWindow W H cm)
  { buf := composite st.buf W fm cm r (deviceRGB color) (compByte alpha),
    cache := cc, steps := st.steps + s + r.width * r.height }

/-- Render one display item (fills and strokes; everything else is skipped). -/
def renderItem (cfg : Config) (m : Aff) (W H : Nat) (stroke : StrokeFn) (st : RState) :
    DisplayItem → RState
  | .fillPath p rule style clip =>
    let c := clipMaskC cfg m W H st.cache clip
    let f := fillCounted cfg m p rule (itemWindow W H c.1)
    paintMask W H st c.1 f.1 style.color style.alpha c.2.1 (c.2.2 + f.2)
  | .strokePath p style clip =>
    let c := clipMaskC cfg m W H st.cache clip
    let fm := stroke cfg m (itemWindow W H c.1) p style
    paintMask W H st c.1 fm style.color style.alpha c.2.1 c.2.2
  | _ => st

/-- An opaque white RGBA buffer of `W · H` pixels. -/
def whiteBuf (W H : Nat) : ByteArray := ByteArray.mk (Array.replicate (4 * W * H) 255)

/-- Render path items onto a white `W × H` page through `m`, with the final state. -/
def renderItemsCounted (cfg : Config) (m : Aff) (W H : Nat) (items : DisplayList)
    (stroke : StrokeFn := defaultStroke) : RState :=
  items.foldl (renderItem cfg m W H stroke) { buf := whiteBuf W H }

/-- Render path items onto a white `W × H` page through `m`. -/
def renderItems (cfg : Config) (m : Aff) (W H : Nat) (items : DisplayList)
    (stroke : StrokeFn := defaultStroke) : Image :=
  ⟨W, H, (renderItemsCounted cfg m W H items stroke).buf⟩

/-- One item preserves the buffer size. -/
theorem renderItem_size (cfg : Config) (m : Aff) (W H : Nat) (stroke : StrokeFn) (st : RState)
    (it : DisplayItem) : (renderItem cfg m W H stroke st it).buf.size = st.buf.size := by
  cases it <;> simp only [renderItem, paintMask, composite_size]

/-- Folding items preserves the buffer size. -/
theorem foldl_renderItem_size (cfg : Config) (m : Aff) (W H : Nat) (stroke : StrokeFn)
    (l : List DisplayItem) (st : RState) :
    (l.foldl (renderItem cfg m W H stroke) st).buf.size = st.buf.size := by
  induction l generalizing st with
  | nil => rfl
  | cons it rest ih => simp only [List.foldl, ih, renderItem_size]

/-- **Buffer shape.** The rendered image has exactly `4 · w · h` bytes. -/
theorem renderItems_size (cfg : Config) (m : Aff) (W H : Nat) (items : DisplayList)
    (stroke : StrokeFn) :
    (renderItems cfg m W H items stroke).data.size =
      4 * (renderItems cfg m W H items stroke).w * (renderItems cfg m W H items stroke).h := by
  simp only [renderItems, renderItemsCounted]
  rw [← Array.foldl_toList, foldl_renderItem_size]
  simp [whiteBuf, ByteArray.size]

/-- Cost bound of one item on a `W × H` page: its clip, its path (fills), and the compositing
(`≤ W · H`) of a stroke (the stroker's own work is 7.2b's bound). -/
def itemCost (cfg : Config) (W H : Nat) : DisplayItem → Nat
  | .fillPath p _ _ clip => clipCost cfg W H clip + pathCost cfg W H p
  | .strokePath _ _ clip => clipCost cfg W H clip + W * H
  | _ => 0

/-- The compositing rectangle of an item is inside the page. -/
theorem paint_area_le (W H : Nat) (fm : Mask) (cm : Option Mask) :
    (fm.rect.inter (itemWindow W H cm)).width * (fm.rect.inter (itemWindow W H cm)).height ≤
      W * H := by
  have h1 := IRect.inter_width_le_right fm.rect (itemWindow W H cm)
  have h2 := IRect.inter_height_le_right fm.rect (itemWindow W H cm)
  have h3 := clipWindow_width_le W H cm
  have h4 := clipWindow_height_le W H cm
  simp only [itemWindow] at h1 h2 ⊢
  exact Nat.mul_le_mul (by omega) (by omega)

/-- One item adds at most `itemCost` to the counted work. -/
theorem renderItem_steps_le (cfg : Config) (m : Aff) (W H : Nat) (stroke : StrokeFn)
    (st : RState) (it : DisplayItem) :
    (renderItem cfg m W H stroke st it).steps ≤ st.steps + itemCost cfg W H it := by
  cases it with
  | fillPath p rule style clip =>
    simp only [renderItem, paintMask, itemCost, pathCost]
    have h0 := clipMaskC_steps_le cfg m W H st.cache clip
    have h1 := fillCounted_steps_le cfg m p rule
      (itemWindow W H (clipMaskC cfg m W H st.cache clip).1)
    have hw := clipWindow_width_le W H (clipMaskC cfg m W H st.cache clip).1
    have hh := clipWindow_height_le W H (clipMaskC cfg m W H st.cache clip).1
    have ha := paint_area_le W H
      (fillCounted cfg m p rule (itemWindow W H (clipMaskC cfg m W H st.cache clip).1)).1
      (clipMaskC cfg m W H st.cache clip).1
    simp only [itemWindow] at h1 ha ⊢
    generalize (clipMaskC cfg m W H st.cache clip) = c at *
    generalize (fillCounted cfg m p rule (clipWindow W H c.1)) = f at *
    generalize (clipWindow W H c.1).width = cw at *
    generalize (clipWindow W H c.1).height = ch at *
    have e1 : ch * (cfg.samples * (cfg.segCap * p.segs.size + 1) + cw + 1) ≤
        H * (cfg.samples * (cfg.segCap * p.segs.size + 1) + W + 1) :=
      Nat.mul_le_mul hh (by omega)
    omega
  | strokePath p style clip =>
    simp only [renderItem, paintMask, itemCost]
    have h0 := clipMaskC_steps_le cfg m W H st.cache clip
    have ha := paint_area_le W H
      (stroke cfg m (itemWindow W H (clipMaskC cfg m W H st.cache clip).1) p style)
      (clipMaskC cfg m W H st.cache clip).1
    omega
  | _ => simp [renderItem, itemCost]

/-- Folding items: the work is at most the sum of the item costs. -/
theorem foldl_renderItem_steps_le (cfg : Config) (m : Aff) (W H : Nat) (stroke : StrokeFn)
    (l : List DisplayItem) (st : RState) :
    (l.foldl (renderItem cfg m W H stroke) st).steps ≤
      st.steps + (l.map (itemCost cfg W H)).sum := by
  induction l generalizing st with
  | nil => simp
  | cons it rest ih =>
    simp only [List.foldl, List.map, List.sum_cons]
    have := ih (renderItem cfg m W H stroke st it)
    have := renderItem_steps_le cfg m W H stroke st it
    omega

/-- **S3 for a page of path items.** The counted work (clip masks, fills, compositing) is at
most the sum over the items of `itemCost`, i.e. `O(#items × (#clip paths + 1) × (W·H +
H · (S · segCap · #segments)))`, with `segCap = max 1 cfg.curveSegCap` (`Limits.curveSegCap`)
and `W, H ≤ cfg.maxPageSide` for a page (`pageSize_le`). -/
theorem renderItemsCounted_steps_le (cfg : Config) (m : Aff) (W H : Nat) (items : DisplayList)
    (stroke : StrokeFn) :
    (renderItemsCounted cfg m W H items stroke).steps ≤
      (items.toList.map (itemCost cfg W H)).sum := by
  simp only [renderItemsCounted]
  rw [← Array.foldl_toList]
  have := foldl_renderItem_steps_le cfg m W H stroke items.toList { buf := whiteBuf W H }
  simpa using this

/-! ## 8. Pages -/

/-- Pixel size of a page box at zoom `z` and rotation `r`: `⌈screenSize⌉`, each side capped at
`side` (`Config.maxPageSide`, `Limits.maxPageSide`; default `16384`, `16384² = 2²⁸ =
Limits.maxImagePixels`). A larger page is cropped (documented degradation). -/
def pageSize (side : Nat) (z : Rat) (r : Doc.Rotation) (bx : Box) : Nat × Nat :=
  let s := screenSize z r bx
  (min side s.1.ceil.toNat, min side s.2.ceil.toNat)

/-- **Render the path items of a page** at zoom `zoom` (pixels per page unit) and user rotation
`rot` (added to the page's `/Rotate`), onto its CropBox, white background. Strokes go through
`strokeMask` (default: 7.2b's stroker). The raster caps come from `cfg` (`Config.ofLimits`). -/
def renderPaths (page : Doc.Page) (zoom : Rat) (rot : Doc.Rotation) (items : DisplayList)
    (strokeMask : StrokeFn := defaultStroke) (cfg : Config := {}) : Image :=
  let r := rotAdd page.rotate rot
  let bx := Box.ofRect page.cropBox
  let sz := pageSize cfg.maxPageSide zoom r bx
  renderItems cfg (viewMatrix zoom r bx) sz.1 sz.2 items strokeMask

/-- **Buffer shape** of a rendered page: `4 · w · h` bytes. -/
theorem renderPaths_size (page : Doc.Page) (zoom : Rat) (rot : Doc.Rotation)
    (items : DisplayList) (strokeMask : StrokeFn) (cfg : Config) :
    (renderPaths page zoom rot items strokeMask cfg).data.size =
      4 * (renderPaths page zoom rot items strokeMask cfg).w *
        (renderPaths page zoom rot items strokeMask cfg).h :=
  renderItems_size _ _ _ _ _ _

/-- The page is at most `side` (`Limits.maxPageSide`) pixels wide and tall. -/
theorem pageSize_le (side : Nat) (z : Rat) (r : Doc.Rotation) (bx : Box) :
    (pageSize side z r bx).1 ≤ side ∧ (pageSize side z r bx).2 ≤ side := by
  simp only [pageSize]; constructor <;> exact Nat.min_le_left _ _

/-! ## 9. Checks -/

/-- A closed page-space polygon through integer points. -/
private def polyP (pts : List (Int × Int)) : Path :=
  let pt := fun (x y : Int) => (⟨Content.Fixed.ofInt x, Content.Fixed.ofInt y⟩ : Content.Point)
  match pts with
  | [] => {}
  | (x, y) :: rest =>
    ⟨(#[Content.Segment.moveTo (pt x y)] ++
      (rest.map fun (a, b) => Content.Segment.lineTo (pt a b)).toArray).push .closePath⟩

/-- Axis-aligned rectangle `[x0, x1] × [y0, y1]`. -/
private def rectP (x0 y0 x1 y1 : Int) : Path := polyP [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]

private def gray (n : Nat) : Color :=
  .gray (Comp.ofFixed (Content.Fixed.div (Content.Fixed.ofInt n) (Content.Fixed.ofInt 100)))

-- Identity device transform (device = page coordinates, y down): the tests use it directly.
private def idm : Aff := Aff.id

private def px (img : Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (getB img.data i, getB img.data (i + 1), getB img.data (i + 2))

#guard mul255 255 255 == 255 && mul255 128 255 == 128 && mul255 0 200 == 0 && mul255 128 128 == 64
#guard compByte (Comp.ofFixed (Content.Fixed.div Content.Fixed.one (Content.Fixed.ofInt 2))) == 128
-- Rectangle [2,18]² clipped by [5,10]²: exactly the 5×5 clip square is painted black.
#guard
  let img := renderItems {} idm 20 20
    #[.fillPath (rectP 2 2 18 18) .nonzero ⟨gray 0, Comp.one⟩ [⟨rectP 5 5 10 10, .nonzero⟩]]
  px img 5 5 == (0, 0, 0) && px img 9 9 == (0, 0, 0) && px img 4 5 == (255, 255, 255) &&
    px img 10 9 == (255, 255, 255) && px img 3 3 == (255, 255, 255) &&
    img.data.size == 4 * 20 * 20
-- Gray 0.5 fill → 128.
#guard px (renderItems {} idm 4 4 #[.fillPath (rectP 0 0 4 4) .nonzero ⟨gray 50, Comp.one⟩ []])
    1 1 == (128, 128, 128)
-- Mask intersection coverage ≤ operands, cache reuse on a shared clip; a zero-size cache
-- (`Limits.clipCacheSize := 0`) never hits but renders the same image.
#guard
  let c : Clip := [⟨rectP 1 1 6 6, .nonzero⟩]
  let it := DisplayItem.fillPath (rectP 0 0 8 8) .nonzero ⟨gray 0, Comp.one⟩ c
  (renderItemsCounted {} idm 8 8 #[it, it, it]).cache.hits == 2 &&
    (renderItemsCounted (Config.ofLimits { clipCacheSize := 0 }) idm 8 8 #[it, it, it]).cache.hits
      == 0 &&
    (renderItems (Config.ofLimits { clipCacheSize := 0 }) idm 8 8 #[it, it, it]).data ==
      (renderItems {} idm 8 8 #[it, it, it]).data
-- The page side cap crops: a 30 × 10 box at zoom 1 with `maxPageSide := 8` is 8 × 8.
#guard pageSize 8 1 .r0 ⟨0, 0, 30, 10⟩ == (8, 8) && pageSize 16384 1 .r0 ⟨0, 0, 30, 10⟩ == (30, 10)

end SafePdf.Core.Raster.Clip
