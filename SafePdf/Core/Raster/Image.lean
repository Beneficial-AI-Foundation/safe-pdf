import SafePdf.Core.Raster.Clip
import SafePdf.Core.Content.Run

/-!
# Images: decoding sample data and placing it on the page (tasks 7.3b, 7.3e)

Plan.md §6 Phase 7 ("images composited from quarantine-zone decodes"; "Proven: totality,
resource bounds"), §4 **S3**. ISO 32000-2 §8.9 (images): §8.9.3 (sample representation),
§8.9.5 (image dictionaries: `/Width`, `/Height`, `/BitsPerComponent`, `/ColorSpace`,
`/Decode`, `/ImageMask`, `/Interpolate`, `/Mask`, `/SMask`), §8.9.6 (masked images: stencil
masks, explicit masks, colour-key masking), §8.9.7 (inline images), §11.6.5.3 (soft-mask
images, `/Matte`), §8.3.3 / §8.9.4 (image space: the unit square, sample `(0, 0)` at its
top-left corner). Rendering choices follow MuPDF 1.25.1 (`source/fitz/draw-device.c`
`fz_draw_fill_image`, `draw-affine.c` `fz_paint_image_imp`, `fz_gridfit_matrix`).

## Pipeline

1. **Data.** An image XObject is fetched through `Source σ` (5.2b) and decoded with the
   source's `decode` (the document budget is charged, `Doc.decodeBodyB`); an inline image's
   still-encoded bytes are decoded here with `Filter.decodeStream` (bounded by
   `Limits.maxDecodedStreamBytes`). Flate, LZW, RunLength, ASCIIHex, ASCII85 (with
   predictors) are the core's byte filters. A chain that reaches an **image codec**
   (`/DCTDecode`, `/JPXDecode`, `/JBIG2Decode`, `/CCITTFaxDecode`, detected with
   `Filter.parseChain` before decoding) yields the **placeholder**: a 1 × 1 mid-grey
   (`128`) opaque pixmap, i.e. a grey box over the image's unit square (its soft mask, if
   decodable, still applies). The codecs belong to the quarantine zone (Plan.md §6 Phase 3,
   S7) and replace the placeholder later.
2. **Parameters** (`ImgDict`, entries resolved one level through the source): `/Width`,
   `/Height` (both `≥ 1`; `w · h ≤ Limits.maxImagePixels`, else
   `Error.limitExceeded .imagePixels`), `/BitsPerComponent` ∈ {1, 2, 4, 8, 16} (else
   `malformed`; `1` for stencil masks), `/Decode` (used when it has `2 · ncomp` numbers),
   `/ImageMask`, `/Interpolate`, a `/Mask` array (colour key).
3. **Colour space** (`Run.csInfo`, the interpreter's own resolution, so fills and images
   agree): `DeviceGray`/`RGB`/`CMYK`, `CalGray`/`CalRGB` and `ICCBased` (by `/N` or a matching
   `/Alternate`) as device spaces; `Indexed` (lookup string or stream; indices clamp to
   `hival`, and to 255); `Separation` (type 2 tint transform, else the interpreter's darkness
   placeholder); `DeviceN` (the interpreter's average-darkness placeholder); `Lab` (`L*` as
   grey). An inline image's resource-name colour space has been replaced by the runner with
   the definition from the resources of the content that shows it (page or form; task 7.3f,
   `Run.annotInline`), as a direct object; a name left unresolved is looked up in the page's
   `/ColorSpace` resources (`ImageTable.named`). A missing or unknown space (and
   `Pattern`) yields the placeholder. Colour conversion to RGB is the same as
   `Clip.deviceRGB` (naive CMYK).
4. **Samples** (`samples`, row by row): rows padded to whole bytes (`rowBytes`), samples
   big-endian within bytes; 16-bit samples use their high byte. Each sample goes through a
   per-component lookup table (`lutComp`, ≤ 256 entries, computed exactly over `ℚ` once per
   image) that applies `/Decode` (`d = Dmin + s · (Dmax − Dmin) / (2^bpc − 1)`) and
   normalises to a byte: `round(255 · d)` for colour components, `round(d)` for `Indexed`
   indices, `round(255 · d / 100)` for `Lab` `L*`. The result has exactly `w · h · ncomp`
   bytes (`samples_size`). **Short data is padded with zeros** (as MuPDF does), so every read
   is the total `Clip.getB`; in-range reads hit the expected byte range (`sampleOffset_lt`).
   The sample buffer is also capped: `w · h · ncomp ≤ Limits.maxDecodedStreamBytes`, else
   `Error.limitExceeded .decodedStreamBytes`.
5. **RGBA** (`toRGBA`): `4 · w · h` bytes (`Pixmap.size_eq`, by construction). Stencil masks
   (`/ImageMask true`) keep the coverage `255 − byte(d)` in the alpha byte (default `/Decode
   [0 1]`: sample 0 paints) and take the fill colour at painting time.
6. **Masks** (§6b). *Colour key* (`applyKey`): a `/Mask` array of `2 · ncomp` integers makes
   pixels whose raw samples all lie in the ranges transparent. *Explicit mask* (a `/Mask`
   stream) and *soft mask* (`/SMask`, which wins and disables the colour key): decoded through
   the source like an image (`loadMask`: a stencil with its own `/Decode`, resp. `DeviceGray`
   with its own `/Decode`), then both images are resampled (nearest) to the finer of the two
   grids (when ≤ `maxImagePixels` pixels, else the image's grid) and the mask value multiplies
   the alpha (`withMask`). `/Matte` un-premultiplies the colours: `c = m + (c' − m) / α`
   (`Pixmap.unmatte`). An undecodable mask (image codec, error) is ignored.
7. **Placement** (`place`, MuPDF's choices; `smooth := false` keeps plain nearest sampling
   at pixel centres, the 7.3b behaviour, used as the exact-reference test):
   * **grid fitting** (`gridfit`): an axis-aligned matrix is expanded outward to whole pixels
     (tolerance `1/1000`), so sub-pixel-thin axis-aligned images cover one full pixel;
   * **area-averaging downscale** (`boxDown`): along an axis where the image has more
     samples than device pixels, the image is first box-filtered to `⌈device length⌉`
     samples (alpha-weighted mean of each source block; every source pixel read once), when
     it has at most `maxImagePixels` pixels. MuPDF filters only when both axes shrink, with
     a tent filter; the box filter is the documented approximation;
   * **sampling**: bilinear (`lerp`, 12-bit weights, MuPDF's half-pixel offset and clamped
     borders; premultiplied when the pixmap has alpha) for non-rectilinear matrices and for
     upscaling, except beyond 2× magnification without `/Interpolate`; else nearest;
   * **edge anti-aliasing** (`cov1`, non-axis-aligned images only — axis-aligned ones are
     grid-fitted): per image axis, the overlap of the device pixel's one-pixel-wide band
     across that axis's edges with the image, as a fraction of the pixel; the coverage is
     the product of both axes (exact for pixels crossed by one edge; a sub-pixel-thin image
     gets partial coverage). MuPDF does not anti-alias image edges (documented deviation).
   The device matrix is `CTM × view` (exact over `ℚ`); its inverse composed with
   `(x, y) ↦ (w·x, h·(1 − y))` maps a device point to continuous image coordinates. Per row,
   the start (pixel centre) is evaluated exactly and converted to `Int64` fixed point with
   32 fractional bits; per pixel the coordinates advance by rounded steps — no `ℚ`, no `Nat`
   bignums and no allocation per pixel (`Plan`, `pixel`, `colLoop`). The pixels visited are
   the device bounding box ∩ the item's clip window (`Clip.itemWindow`), hence at most
   `W · H`, plus at most `cap` source pixels averaged (`place_steps_le`). A singular matrix
   paints nothing.
8. **Compositing** per pixel: `a = mul255(sampleAlpha, mul255(edge · clip coverage, ca))`
   through `Clip.pxU` (the compositor's `UInt32` source-over, written directly when
   `a = 255`). Compiled (`leanc -O3`), a full-page 600 × 800 RGB image at 612 × 792 takes
   ≈ 6 ms to decode (was 52 ms) and ≈ 18 ms to place (was 97 ms; it is downscaled
   vertically and upscaled bilinearly horizontally); rotated 30° ≈ 15 ms. Most of the old
   cost was `UInt8.ofNatClamp`, which compiles to a `BitVec` computation (≈ 30 ns per call):
   `u8` replaces it.

## Wiring into `Glyph.renderPage`

`loadImages limits src s res items` decodes every distinct image XObject of a display list
once (by object number, also inside soft-mask groups), with its masks, under the session state `σ` (the document budget),
and resolves the page's named colour spaces; it returns an `ImageTable`. Decoded pixmaps on
one page are capped at `maxPageImagePixels` pixels in total (further XObjects get the
placeholder). `renderImage cfg m W H tbl st src ctm fill clip : Clip.RState` paints one image
item (clip mask through `Clip.clipMaskC` and its cache; inline images are decoded here,
purely). It preserves the buffer size (`renderImage_size`) and adds at most
`Clip.clipCost cfg W H clip + W · H + Limits.maxImagePixels` work (`renderImage_steps_le`).
-/

namespace SafePdf.Core.Raster.Image

open SafePdf SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill (IRect Mask Config)
open SafePdf.Core.Content (Fixed Comp Color DeviceSpace Source FillStyle Matrix ImageSource
  Clip DisplayItem DisplayList)
open SafePdf.Core.Content.Run (CSInfo)

/-! ## 1. Pixmaps -/

/-- A decoded image: RGBA, row-major, exactly `4 · w · h` bytes. For a stencil mask the
alpha byte is the coverage and the colour bytes are unused (the fill colour is applied when
painting). -/
structure Pixmap where
  /-- Width in samples. -/
  w : Nat
  /-- Height in samples. -/
  h : Nat
  /-- RGBA bytes. -/
  data : ByteArray
  /-- The buffer has one RGBA quadruple per sample. -/
  size_eq : data.size = 4 * w * h
  /-- `/ImageMask true`: paint the fill colour with the alpha byte as coverage. -/
  stencil : Bool := false
  /-- The `/Interpolate` hint: keeps bilinear sampling on at large magnifications (MuPDF). -/
  interpolate : Bool := false
  /-- Every alpha byte is `255` (a hint: `false` is always safe; it selects the cheaper
  straight-colour bilinear path). -/
  solid : Bool := false

/-- The **placeholder** for images the core does not decode (image codecs, unknown colour
spaces): one mid-grey (`128`) opaque sample, i.e. a grey box over the unit square. -/
def placeholder : Pixmap := ⟨1, 1, ByteArray.mk #[128, 128, 128, 255], rfl, false, false, true⟩

instance : Inhabited Pixmap := ⟨placeholder⟩

/-! ## 2. Sample unpacking -/

/-- A natural number as a byte, clamped to 255. Equal to `UInt8.ofNatClamp` (`u8_eq`), which
compiles to a `BitVec` computation with `2 ^ 8` evaluated per call (≈ 30 ns; this is ≈ 1 ns). -/
@[inline] def u8 (n : Nat) : UInt8 := if n < 256 then UInt8.ofNat n else 255

/-- `u8` is `UInt8.ofNatClamp`. -/
theorem u8_eq (n : Nat) : u8 n = UInt8.ofNatClamp n := by
  unfold u8 UInt8.ofNatClamp BitVec.ofNatClamp
  by_cases h : n < 256
  · simp only [h, ite_true, dite_true]
    apply UInt8.toNat_inj.mp
    simp [Nat.mod_eq_of_lt h]
  · simp only [h, ite_false, dite_false]; rfl

/-- Read a byte (`0` out of range), without an intermediate `Option` (equal to `Clip.getB`,
`rd_eq_getB`). -/
@[inline] def rd (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then (b.get i h).toNat else 0

/-- `rd` is `Clip.getB`. -/
theorem rd_eq_getB (b : ByteArray) (i : Nat) : rd b i = Clip.getB b i := by
  unfold rd Clip.getB
  split
  · rename_i h; simp [h, ByteArray.get]; rfl
  · rename_i h; simp [h]

/-- Bytes per row of `w` pixels with `nc` components of `bpc` bits (rows are padded to whole
bytes, §8.9.3). -/
def rowBytes (w nc bpc : Nat) : Nat := (w * nc * bpc + 7) / 8

/-- Byte offset (within its row) of sample `k` of `bpc` bits; for 16-bit samples, of the high
byte. -/
def byteOff (k bpc : Nat) : Nat := k * bpc / 8

/-- Sample `k` of the row starting at byte `row`, at most 8 significant bits (16-bit samples:
the high byte). Short data reads as 0. -/
def sampleAt (data : ByteArray) (row k bpc : Nat) : Nat :=
  let byte := rd data (row + byteOff k bpc)
  if 8 ≤ bpc then byte
  else (byte >>> (8 - bpc - (k * bpc) % 8)) % (2 ^ bpc)

/-- **Reads stay in the image's data range.** For row `r < h` and sample `k < w · nc` of a row,
the byte read lies before `h · rowBytes w nc bpc`, the size the data must have (shorter data
reads as 0). -/
theorem sampleOffset_lt (w h nc bpc r k : Nat) (hb : 1 ≤ bpc) (hr : r < h) (hk : k < w * nc) :
    r * rowBytes w nc bpc + byteOff k bpc < h * rowBytes w nc bpc := by
  have h1 : (k + 1) * bpc ≤ w * nc * bpc := Nat.mul_le_mul_right _ hk
  have h2 : (k + 1) * bpc = k * bpc + bpc := Nat.succ_mul _ _
  have h3 : (r + 1) * rowBytes w nc bpc ≤ h * rowBytes w nc bpc := Nat.mul_le_mul_right _ hr
  have h4 : (r + 1) * rowBytes w nc bpc = r * rowBytes w nc bpc + rowBytes w nc bpc :=
    Nat.succ_mul _ _
  unfold byteOff
  unfold rowBytes at h3 h4 ⊢
  generalize k * bpc = a at *
  generalize w * nc * bpc = n at *
  generalize r * ((n + 7) / 8) = x at *
  generalize h * ((n + 7) / 8) = y at *
  omega

/-! ## 3. Decode arrays and lookup tables -/

/-- Round to the nearest integer (halves up). -/
def roundRat (q : Rat) : Int := (q + 1 / 2).floor

/-- Clamp an integer to a byte. -/
def clampByte (x : Int) : UInt8 := if x < 0 then 0 else u8 x.toNat

/-- Lookup table of one component for `bits`-bit samples (`2^bits` entries): `/Decode` range
`[dmin, dmax]`, then the byte `round((d − lo) · scale)` clamped to `0 … 255`. -/
def lutComp (bits : Nat) (dmin dmax lo scale : Rat) : ByteArray :=
  let maxv : Rat := ((2 ^ bits - 1 : Nat) : Rat)
  ByteArray.mk ((Array.range (2 ^ bits)).map fun (s : Nat) =>
    clampByte (roundRat ((dmin + (s : Rat) * (dmax - dmin) / maxv - lo) * scale)))

/-- How decoded components become bytes: colour components (`[0, 1]` → `0 … 255`), palette
indices, or `Lab` (`L*` in `[0, 100]`). -/
inductive Norm where
  /-- `[0, 1]` components (device, `Separation`, `DeviceN`, stencil masks). -/
  | unit
  /-- `Indexed`: the index itself. -/
  | index
  /-- `Lab`: `L*/100` (other components unused). -/
  | lab
  deriving DecidableEq, Repr, Inhabited

/-- Default `/Decode` range of component `j` for `bpc`-bit samples (§8.9.5.2, Table 90). -/
def Norm.defaultRange (n : Norm) (bpc j : Nat) : Rat × Rat :=
  match n with
  | .unit => (0, 1)
  | .index => (0, ((2 ^ bpc - 1 : Nat) : Rat))
  | .lab => if j = 0 then (0, 100) else (-100, 100)

/-- Normalisation `(lo, scale)` of component `j`. -/
def Norm.scaling (n : Norm) (j : Nat) : Rat × Rat :=
  match n with
  | .unit => (0, 255)
  | .index => (0, 1)
  | .lab => if j = 0 then (0, 255 / 100) else (0, 1)

/-- The lookup tables of all `nc` components, concatenated (`2^bits` entries each): component
`j`'s range is the `j`-th pair of `decode` when it has `2 · nc` numbers, else the default. -/
def luts (n : Norm) (nc bpc bits : Nat) (decode : Option (List Rat)) : ByteArray :=
  (List.range nc).foldl (fun acc j =>
    let dflt := n.defaultRange bpc j
    let rng : Rat × Rat :=
      match decode with
      | some ds => if ds.length = 2 * nc then (ds.getD (2 * j) dflt.1, ds.getD (2 * j + 1) dflt.2)
                   else dflt
      | none => dflt
    let sc := n.scaling j
    acc ++ lutComp bits rng.1 rng.2 sc.1 sc.2) ByteArray.empty

/-! ## 4. The sample buffer -/

/-- Byte `i` of a lookup table (`0` out of range), without an intermediate `Option`. -/
@[inline] def lutAt (lut : ByteArray) (i : Nat) : UInt8 :=
  if h : i < lut.size then lut.get i h else 0

/-- One row of the sample buffer: `fuel` samples from sample `k` of the row starting at byte
`row`; `jo` is the offset of the current component's table (`nv` entries per component, `tot =
nc · nv` in all; it cycles without a division per sample). 8-bit samples are read directly. -/
def samplesLoop (data lut : ByteArray) (bpc nv tot row : Nat) :
    (fuel k jo : Nat) → ByteArray → ByteArray
  | 0, _, _, acc => acc
  | fuel + 1, k, jo, acc =>
    let s := if bpc = 8 then rd data (row + k) else sampleAt data row k bpc
    let jo' := if jo + nv < tot then jo + nv else 0
    samplesLoop data lut bpc nv tot row fuel (k + 1) jo' (acc.push (lutAt lut (jo + s)))

/-- `samplesLoop` pushes exactly one byte per step. -/
theorem samplesLoop_size (data lut : ByteArray) (bpc nv tot row : Nat) :
    ∀ (fuel k jo : Nat) (acc : ByteArray),
      (samplesLoop data lut bpc nv tot row fuel k jo acc).size = acc.size + fuel
  | 0, _, _, _ => rfl
  | fuel + 1, k, jo, acc => by
    simp only [samplesLoop]
    rw [samplesLoop_size data lut bpc nv tot row fuel, ByteArray.size_push]; omega

/-- Rows `r, r + 1, …` (`fuel` of them) of `wn` samples each (row stride `stride` bytes). -/
def samplesRows (data lut : ByteArray) (wn bpc nv tot stride : Nat) :
    (fuel r : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, r, acc =>
    samplesRows data lut wn bpc nv tot stride fuel (r + 1)
      (samplesLoop data lut bpc nv tot (r * stride) wn 0 0 acc)

/-- `samplesRows` pushes `wn` bytes per row. -/
theorem samplesRows_size (data lut : ByteArray) (wn bpc nv tot stride : Nat) :
    ∀ (fuel r : Nat) (acc : ByteArray),
      (samplesRows data lut wn bpc nv tot stride fuel r acc).size = acc.size + fuel * wn
  | 0, _, _ => by simp [samplesRows]
  | fuel + 1, r, acc => by
    simp only [samplesRows]
    rw [samplesRows_size data lut wn bpc nv tot stride fuel, samplesLoop_size, Nat.succ_mul]
    omega

/-- **Decoded samples** of a `w × h` image with `nc` components of `bpc` bits, through the
lookup tables `lut` (`2^bits` entries per component): one normalised byte per sample, row
by row (sample `k` of a row is component `k % nc`). -/
def samples (data lut : ByteArray) (w h nc bpc bits : Nat) : ByteArray :=
  samplesRows data lut (w * nc) bpc (2 ^ bits) (nc * 2 ^ bits) (rowBytes w nc bpc) h 0
    (ByteArray.emptyWithCapacity (w * h * nc))

/-- **The sample buffer has exactly `w · h · ncomp` bytes.** -/
theorem samples_size (data lut : ByteArray) (w h nc bpc bits : Nat) :
    (samples data lut w h nc bpc bits).size = w * h * nc := by
  simp only [samples, samplesRows_size]
  show 0 + h * (w * nc) = w * h * nc
  rw [Nat.zero_add, ← Nat.mul_assoc, Nat.mul_comm h w]

/-! ## 5. Colour conversion -/

/-- How normalised component bytes become RGB(A). -/
inductive Conv where
  /-- `DeviceGray` (and fallbacks). -/
  | gray
  /-- `DeviceRGB`. -/
  | rgb
  /-- `DeviceCMYK`, naive (`Clip.deviceRGB`). -/
  | cmyk
  /-- A 256-entry RGB palette (768 bytes), indexed by the first component, or by the average
  of all components when `avg` (`DeviceN`). -/
  | pal (avg : Bool) (tbl : ByteArray)
  /-- Stencil mask: coverage `255 − component`. -/
  | stencil

/-- A 256-entry RGB palette from a colour function. -/
def palette (f : Nat → Color) : ByteArray :=
  (List.range 256).foldl (fun acc i =>
    let c := Clip.deviceRGB (f i)
    ((acc.push (u8 c.1)).push (u8 c.2.1)).push
      (u8 c.2.2)) ByteArray.empty

/-- A byte as a `Fixed` in `[0, 1]`. -/
def byteFrac (i : Nat) : Fixed := Fixed.div (Fixed.ofInt i) (Fixed.ofInt 255)

/-- Components, conversion and normalisation of a resolved colour space; `none` for spaces
drawn as the placeholder (`Pattern`). -/
def planOf (info : CSInfo) : Option (Nat × Conv × Norm) :=
  match info with
  | .dev .gray _ => some (1, .gray, .unit)
  | .dev .rgb _ => some (3, .rgb, .unit)
  | .dev .cmyk _ => some (4, .cmyk, .unit)
  | .pattern => none
  | .indexed .. => some (1, .pal false (palette fun i => info.color [Fixed.ofInt i]), .index)
  | .separation .. => some (1, .pal false (palette fun i => info.color [byteFrac i]), .unit)
  | .deviceN n _ =>
    some (n, .pal true (palette fun i => info.color (List.replicate n (byteFrac i))), .unit)
  | .lab =>
    some (3, .pal false (palette fun i =>
      info.color [Fixed.div (Fixed.ofInt (i * 100)) (Fixed.ofInt 255), Fixed.zero, Fixed.zero]),
      .lab)

/-- Sum of `n` bytes from offset `b`. -/
def sumBytes (smp : ByteArray) : (n b : Nat) → Nat
  | 0, _ => 0
  | n + 1, b => rd smp b + sumBytes smp n (b + 1)

/-- Push the RGBA of the pixel whose components start at byte `b` of the sample buffer. -/
def pushPixel (smp : ByteArray) (nc : Nat) (cv : Conv) (b : Nat) (acc : ByteArray) : ByteArray :=
  let c0 := rd smp b
  match cv with
  | .gray =>
    let v := u8 c0
    (((acc.push v).push v).push v).push 255
  | .rgb =>
    (((acc.push (u8 c0)).push (u8 (rd smp (b + 1)))).push
      (u8 (rd smp (b + 2)))).push 255
  | .cmyk =>
    let k := rd smp (b + 3)
    (((acc.push (u8 (255 - min 255 (c0 + k)))).push
      (u8 (255 - min 255 (rd smp (b + 1) + k)))).push
      (u8 (255 - min 255 (rd smp (b + 2) + k)))).push 255
  | .pal avg tbl =>
    let i := if avg then sumBytes smp nc b / max nc 1 else c0
    (((acc.push (u8 (rd tbl (3 * i)))).push
      (u8 (rd tbl (3 * i + 1)))).push
      (u8 (rd tbl (3 * i + 2)))).push 255
  | .stencil => (((acc.push 0).push 0).push 0).push (u8 (255 - c0))

/-- `pushPixel` pushes four bytes. -/
theorem pushPixel_size (smp : ByteArray) (nc : Nat) (cv : Conv) (b : Nat) (acc : ByteArray) :
    (pushPixel smp nc cv b acc).size = acc.size + 4 := by
  cases cv <;> simp [pushPixel, ByteArray.size_push]

/-- Convert `fuel` pixels from pixel `p` on. -/
def rgbaLoop (smp : ByteArray) (nc : Nat) (cv : Conv) : (fuel p : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, p, acc => rgbaLoop smp nc cv fuel (p + 1) (pushPixel smp nc cv (p * nc) acc)

/-- `rgbaLoop` pushes four bytes per pixel. -/
theorem rgbaLoop_size (smp : ByteArray) (nc : Nat) (cv : Conv) :
    ∀ (fuel p : Nat) (acc : ByteArray), (rgbaLoop smp nc cv fuel p acc).size = acc.size + 4 * fuel
  | 0, _, _ => rfl
  | fuel + 1, p, acc => by
    simp only [rgbaLoop]; rw [rgbaLoop_size smp nc cv fuel, pushPixel_size]; omega

/-- **RGBA pixmap** of a `w × h` sample buffer (`4 · w · h` bytes by construction). -/
def toRGBA (smp : ByteArray) (w h nc : Nat) (cv : Conv) (stencil interp : Bool) : Pixmap :=
  { w, h, data := rgbaLoop smp nc cv (w * h) 0 (ByteArray.emptyWithCapacity (4 * w * h)),
    size_eq := by
      rw [rgbaLoop_size]; show 0 + 4 * (w * h) = 4 * w * h; rw [Nat.zero_add, Nat.mul_assoc],
    stencil, interpolate := interp, solid := !stencil }

/-! ## 6. Image parameters and decoding -/

/-- The parameters of an image dictionary that decoding needs (values resolved one level). -/
structure ImgDict where
  /-- `/Width` (0 when missing or malformed). -/
  w : Nat
  /-- `/Height`. -/
  h : Nat
  /-- `/BitsPerComponent` (`none` when absent). -/
  bpc : Option Nat
  /-- `/ImageMask`. -/
  mask : Bool
  /-- `/Decode` numbers. -/
  decode : Option (List Rat)
  /-- `/Interpolate`. -/
  interp : Bool
  /-- `/ColorSpace` (resolved one level). -/
  cs : Option PdfObject
  /-- Colour-key masking: a `/Mask` **array** `[min₁ max₁ … minₙ maxₙ]` of raw sample values
  (§8.9.6.4); `none` when absent or not an array of nonnegative integers. -/
  key : Option (List Nat) := none

/-- Entry `k` of `d`, resolved one level. -/
def entry {σ : Type} (src : Source σ) (s : σ) (d : Dict) (k : String) : Option PdfObject × σ :=
  match Dict.get? d (Content.Run.nm k) with
  | none => (none, s)
  | some o => let r := Content.Run.resolve src s o; (some r.1, r.2)

/-- A nonnegative integer entry. -/
def natOf : Option PdfObject → Option Nat
  | some o => Content.Interp.nat? o
  | none => none

/-- A boolean entry (default false). -/
def boolOf : Option PdfObject → Bool
  | some (.bool b) => b
  | _ => false

/-- Read the image parameters of `d`. -/
def imgDictOf {σ : Type} (src : Source σ) (s : σ) (d : Dict) : ImgDict × σ :=
  let (w, s) := entry src s d "Width"
  let (h, s) := entry src s d "Height"
  let (b, s) := entry src s d "BitsPerComponent"
  let (m, s) := entry src s d "ImageMask"
  let (dc, s) := entry src s d "Decode"
  let (ip, s) := entry src s d "Interpolate"
  let (cs, s) := entry src s d "ColorSpace"
  let (mk, s) := entry src s d "Mask"
  let dec : Option (List Rat) := match dc with
    | some (.array xs) => (xs.mapM Content.Interp.num?).map (·.map Fixed.toRat)
    | _ => none
  let key : Option (List Nat) := match mk with
    | some (.array xs) => xs.mapM Content.Interp.nat?
    | _ => none
  ({ w := (natOf w).getD 0, h := (natOf h).getD 0, bpc := natOf b, mask := boolOf m,
     decode := dec, interp := boolOf ip, cs, key }, s)

/-- Valid `/BitsPerComponent` values. -/
def validBpc (b : Nat) : Bool := b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8 ∨ b = 16

/-- Maximum number of colour components of an image (`DeviceN` allows 32 colorants); more is
drawn as the placeholder. -/
def maxComps : Nat := 32

/-! ### Colour-key masking (§8.9.6.4) -/

/-- Pairs `(min, max)` of a colour-key array, in the units `sampleAt` returns (16-bit samples:
their high byte, so the bounds are divided by 256). -/
def keyPairs (bpc : Nat) : List Nat → List (Nat × Nat)
  | lo :: hi :: rest =>
    (if bpc = 16 then (lo / 256, hi / 256) else (lo, hi)) :: keyPairs bpc rest
  | _ => []

/-- Do the raw samples `k, k + 1, …` of the row at byte `row` all lie in their key ranges? -/
def keyIn (data : ByteArray) (row k bpc : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (lo, hi) :: rest =>
    let s := sampleAt data row k bpc
    lo ≤ s && s ≤ hi && keyIn data row (k + 1) bpc rest

/-- Clear the alpha byte of every pixel (from pixel `p` at column `x` of row `y`, `fuel`
pixels, `w` per row) whose raw samples all lie in the key ranges `ks`. -/
def keyLoop (data : ByteArray) (w nc bpc stride : Nat) (ks : List (Nat × Nat)) :
    (fuel x y p : Nat) → ByteArray → ByteArray
  | 0, _, _, _, d => d
  | fuel + 1, x, y, p, d =>
    let d := if keyIn data (y * stride) (x * nc) bpc ks then Clip.setB d (4 * p + 3) 0 else d
    let last := x + 1 = w
    keyLoop data w nc bpc stride ks fuel (if last then 0 else x + 1) (if last then y + 1 else y)
      (p + 1) d

/-- `keyLoop` preserves the buffer size. -/
theorem keyLoop_size (data : ByteArray) (w nc bpc stride : Nat) (ks : List (Nat × Nat)) :
    ∀ (fuel x y p : Nat) (d : ByteArray),
      (keyLoop data w nc bpc stride ks fuel x y p d).size = d.size
  | 0, _, _, _, _ => rfl
  | fuel + 1, x, y, p, d => by
    simp only [keyLoop]; rw [keyLoop_size]; split <;> simp only [Clip.setB_size]

/-- **Colour-key masking**: pixels whose raw samples all lie in the `/Mask` ranges become
transparent (§8.9.6.4); a key without exactly `2 · nc` entries is ignored. The dimensions are
unchanged. -/
def applyKey (p : ImgDict) (bpc nc : Nat) (data : ByteArray) (pm : Pixmap) : Pixmap :=
  let ks := match p.key with
    | some k => if k.length = 2 * nc ∧ !p.mask then keyPairs bpc k else []
    | none => []
  { pm with
    data := if ks.isEmpty then pm.data
      else keyLoop data pm.w nc bpc (rowBytes pm.w nc bpc) ks (pm.w * pm.h) 0 0 0 pm.data
    size_eq := by split <;> simp only [keyLoop_size, pm.size_eq]
    solid := pm.solid && ks.isEmpty }

/-- Decode with a known plan (`bpc` bits, `nc` components, conversion, normalisation): checks
`/BitsPerComponent` and the sample-buffer cap, then samples, RGBA and colour-key masking. Too
many components yield the placeholder. -/
def finish (limits : Limits) (p : ImgDict) (bpc nc : Nat) (cv : Conv) (n : Norm)
    (data : ByteArray) : Except Error Pixmap :=
  if !validBpc bpc then .error (.malformed 0 "image: invalid /BitsPerComponent")
  else if nc = 0 ∨ maxComps < nc then .ok placeholder
  else if limits.maxDecodedStreamBytes < p.w * p.h * nc then
    .error (.limitExceeded .decodedStreamBytes)
  else
    .ok (applyKey p bpc nc data
      (toRGBA (samples data (luts n nc bpc (min bpc 8) p.decode) p.w p.h nc bpc (min bpc 8))
        p.w p.h nc cv p.mask p.interp))

/-- A pixmap from `finish` is the placeholder or has the image's dimensions. -/
theorem finish_dims {limits : Limits} {p : ImgDict} {bpc nc : Nat} {cv : Conv} {n : Norm}
    {data : ByteArray} {pm : Pixmap} (h : finish limits p bpc nc cv n data = .ok pm) :
    pm.w * pm.h = 1 ∨ (pm.w = p.w ∧ pm.h = p.h) := by
  unfold finish at h
  by_cases h1 : (!validBpc bpc) = true
  · simp [h1] at h
  · by_cases h2 : nc = 0 ∨ maxComps < nc
    · simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] at h
      cases h; exact .inl rfl
    · by_cases h3 : limits.maxDecodedStreamBytes < p.w * p.h * nc
      · simp [h1, h2, h3] at h
      · simp only [h1, h2, h3, ite_false, Bool.false_eq_true] at h
        cases h; exact .inr ⟨rfl, rfl⟩

/-- **Decode an image** from its parameters, resolved colour space (`none`: missing or not
understood) and decoded data. Errors: empty or oversized dimensions
(`limitExceeded .imagePixels`), a sample buffer above `maxDecodedStreamBytes`, an invalid
`/BitsPerComponent`. An undrawable colour space yields the placeholder. -/
def decodePixmap (limits : Limits) (p : ImgDict) (info : Option CSInfo) (data : ByteArray) :
    Except Error Pixmap :=
  if p.w = 0 ∨ p.h = 0 then .error (.malformed 0 "image: empty /Width or /Height")
  else if limits.maxImagePixels < p.w * p.h then .error (.limitExceeded .imagePixels)
  else if p.mask then finish limits p 1 1 .stencil .unit data
  else
    match p.bpc, info.bind planOf with
    | some b, some (nc, cv, n) => finish limits p b nc cv n data
    | _, _ => .ok placeholder

/-- A successfully decoded image is within `Limits.maxImagePixels` (or is the 1-pixel
placeholder). -/
theorem decodePixmap_pixels {limits : Limits} {p : ImgDict} {info : Option CSInfo}
    {data : ByteArray} {pm : Pixmap} (h : decodePixmap limits p info data = .ok pm) :
    pm.w * pm.h ≤ limits.maxImagePixels ∨ pm.w * pm.h = 1 := by
  unfold decodePixmap at h
  by_cases h1 : p.w = 0 ∨ p.h = 0
  · simp [h1] at h
  · by_cases h2 : limits.maxImagePixels < p.w * p.h
    · simp [h1, h2] at h
    · have hle : p.w * p.h ≤ limits.maxImagePixels := by omega
      have fin : ∀ b nc cv n, finish limits p b nc cv n data = .ok pm →
          pm.w * pm.h ≤ limits.maxImagePixels ∨ pm.w * pm.h = 1 := by
        intro b nc cv n hf
        rcases finish_dims hf with e | ⟨e1, e2⟩
        · exact .inr e
        · rw [e1, e2]; exact .inl hle
      simp only [h1, h2, ite_false] at h
      split at h
      · exact fin _ _ _ _ h
      · split at h
        · exact fin _ _ _ _ h
        · cases h; exact .inr rfl

/-- Does the filter chain of `d` reach an image codec (DCT, JPX, JBIG2, CCITT)? -/
def hasCodec (limits : Limits) (d : Dict) : Bool :=
  match Filter.parseChain limits d with
  | .ok stages => stages.any fun st => match st.kind with
    | .image _ => true
    | .byte _ => false
  | .error _ => false

/-- The colour space of an image: `Run.csInfo` (device names, arrays, references), else a
resource name looked up in `named`. -/
def csOf {σ : Type} (src : Source σ) (s : σ) (named : List (Name × CSInfo)) :
    Option PdfObject → Option CSInfo × σ
  | none => (none, s)
  | some o =>
    match Content.Run.csInfo src s o with
    | (some i, s) => (some i, s)
    | (none, s) =>
      match o with
      | .name n => ((named.find? (·.1 == n)).map (·.2), s)
      | _ => (none, s)

/-! ## 6b. Resampling, soft masks and explicit masks (§8.9.5.4, §8.9.6.3, §11.6.5.3) -/

/-- Push the four bytes at offset `i` of `d` (`0` out of range). -/
@[inline] def push4 (acc d : ByteArray) (i : Nat) : ByteArray :=
  (((acc.push (lutAt d i)).push (lutAt d (i + 1))).push (lutAt d (i + 2))).push (lutAt d (i + 3))

/-- `push4` pushes four bytes. -/
theorem push4_size (acc d : ByteArray) (i : Nat) : (push4 acc d i).size = acc.size + 4 := by
  simp [push4, ByteArray.size_push]

/-- One target row of a nearest-neighbour resampling: `fuel` pixels from target column `x`
(`sw` source and `tw` target columns), the source row starting at byte `ro`. -/
def resCols (d : ByteArray) (sw tw ro : Nat) : (fuel x : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, x, acc => resCols d sw tw ro fuel (x + 1) (push4 acc d (ro + 4 * (x * sw / tw)))

/-- `resCols` pushes four bytes per pixel. -/
theorem resCols_size (d : ByteArray) (sw tw ro : Nat) :
    ∀ (fuel x : Nat) (acc : ByteArray), (resCols d sw tw ro fuel x acc).size = acc.size + 4 * fuel
  | 0, _, _ => rfl
  | fuel + 1, x, acc => by
    simp only [resCols]; rw [resCols_size d sw tw ro fuel, push4_size]; omega

/-- Target rows `y, y + 1, …` (`fuel` of them) of a nearest-neighbour resampling from
`sw × sh` to `tw × th`. -/
def resRows (d : ByteArray) (sw sh tw th : Nat) : (fuel y : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, y, acc =>
    resRows d sw sh tw th fuel (y + 1) (resCols d sw tw (4 * sw * (y * sh / th)) tw 0 acc)

/-- `resRows` pushes `4 · tw` bytes per row. -/
theorem resRows_size (d : ByteArray) (sw sh tw th : Nat) :
    ∀ (fuel y : Nat) (acc : ByteArray),
      (resRows d sw sh tw th fuel y acc).size = acc.size + 4 * tw * fuel
  | 0, _, _ => rfl
  | fuel + 1, y, acc => by
    simp only [resRows]; rw [resRows_size d sw sh tw th fuel, resCols_size, Nat.mul_succ]; omega

/-- **Nearest-neighbour resampling** of a pixmap to `tw × th`: target pixel `(x, y)` takes
source pixel `(⌊x · w / tw⌋, ⌊y · h / th⌋)`. -/
def resample (pm : Pixmap) (tw th : Nat) : Pixmap :=
  { pm with
    w := tw
    h := th
    data := resRows pm.data pm.w pm.h tw th th 0 (ByteArray.emptyWithCapacity (4 * tw * th))
    size_eq := by rw [resRows_size]; exact Nat.zero_add _ }

/-- Multiply the alpha byte of pixels `p, p + 1, …` (`fuel` of them) of `d` by byte `ch` of
the same pixel of `m`. -/
def alphaLoop (m : ByteArray) (ch : Nat) : (fuel p : Nat) → ByteArray → ByteArray
  | 0, _, d => d
  | fuel + 1, p, d =>
    let i := 4 * p + 3
    alphaLoop m ch fuel (p + 1)
      (Clip.setB d i (u8 (Clip.mul255 (rd d i) (rd m (4 * p + ch)))))

/-- `alphaLoop` preserves the buffer size. -/
theorem alphaLoop_size (m : ByteArray) (ch : Nat) :
    ∀ (fuel p : Nat) (d : ByteArray), (alphaLoop m ch fuel p d).size = d.size
  | 0, _, _ => rfl
  | fuel + 1, p, d => by simp only [alphaLoop]; rw [alphaLoop_size m ch fuel, Clip.setB_size]

/-- Multiply the alpha of `pm` by channel `ch` of the mask pixmap `mk` (same pixel grid). -/
def Pixmap.mulAlpha (pm mk : Pixmap) (ch : Nat) : Pixmap :=
  { pm with
    data := alphaLoop mk.data ch (pm.w * pm.h) 0 pm.data
    size_eq := by rw [alphaLoop_size]; exact pm.size_eq
    solid := false }

/-- **Masking**: the alpha of `pm` times channel `ch` of the mask `mk`, both resampled
(nearest) to the finer grid `max w w' × max h h'` when that has at most `cap` pixels, else to
the base image's grid (ISO 32000-2 allows mask and image resolutions to differ). -/
def withMask (cap : Nat) (pm mk : Pixmap) (ch : Nat) : Pixmap :=
  let tw0 := max pm.w mk.w
  let th0 := max pm.h mk.h
  let fine := tw0 * th0 ≤ cap
  let tw := if fine then tw0 else pm.w
  let th := if fine then th0 else pm.h
  let base := if tw = pm.w ∧ th = pm.h then pm else resample pm tw th
  let m := if tw = mk.w ∧ th = mk.h then mk else resample mk tw th
  base.mulAlpha m ch

/-- Un-premultiply one component against the matte colour component `m` (§11.6.5.3):
`c = m + (c' − m) / α`, clamped to a byte. -/
def unmatteC (c m a : Nat) : UInt8 :=
  clampByte ((m : Int) + ((c : Int) - m) * 255 / (a : Int))

/-- Un-premultiply pixels `p, p + 1, …` (`fuel` of them) against the matte colour
`(mr, mg, mb)`; fully transparent and opaque pixels are unchanged. -/
def matteLoop (mr mg mb : Nat) : (fuel p : Nat) → ByteArray → ByteArray
  | 0, _, d => d
  | fuel + 1, p, d =>
    let i := 4 * p
    let a := rd d (i + 3)
    let d := if a = 0 ∨ a = 255 then d else
      let d := Clip.setB d i (unmatteC (rd d i) mr a)
      let d := Clip.setB d (i + 1) (unmatteC (rd d (i + 1)) mg a)
      Clip.setB d (i + 2) (unmatteC (rd d (i + 2)) mb a)
    matteLoop mr mg mb fuel (p + 1) d

/-- `matteLoop` preserves the buffer size. -/
theorem matteLoop_size (mr mg mb : Nat) :
    ∀ (fuel p : Nat) (d : ByteArray), (matteLoop mr mg mb fuel p d).size = d.size
  | 0, _, _ => rfl
  | fuel + 1, p, d => by
    simp only [matteLoop]; rw [matteLoop_size mr mg mb fuel]; split
    · rfl
    · simp only [Clip.setB_size]

/-- Un-premultiply a pixmap against the matte colour `rgb` (`/Matte` of its soft mask). -/
def Pixmap.unmatte (pm : Pixmap) (rgb : Nat × Nat × Nat) : Pixmap :=
  { pm with
    data := matteLoop rgb.1 rgb.2.1 rgb.2.2 (pm.w * pm.h) 0 pm.data
    size_eq := by rw [matteLoop_size]; exact pm.size_eq }

/-- `DeviceGray`, the colour space of soft-mask images. -/
def grayInfo : CSInfo := .dev .gray (.gray Comp.zero)

/-- A decoded mask and, for a soft mask, its `/Matte` components. -/
abbrev MaskImg := Pixmap × Option (List Fixed)

/-- **Load a mask image** (`/SMask` when `soft`, else a `/Mask` stream) from its reference:
decoded through the source like an image XObject — a soft mask as `DeviceGray` with its own
`/Decode` (the mask value is channel 0; `/BitsPerComponent` required), an explicit mask as an
`/ImageMask` stencil (`/Decode` honoured, coverage in channel 3: sample 0 paints) — plus a soft
mask's `/Matte` components. `none` for anything else (not a stream, an image codec, a decode
error): the image is then drawn unmasked. -/
def loadMask {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (soft : Bool) :
    Option PdfObject → Option MaskImg × σ
  | some (.ref n g) =>
    match src.fetch s n g with
    | (.ok (.stream st), s) =>
      if hasCodec limits st.dict then (none, s) else
      let (p, s) := imgDictOf src s st.dict
      let (mt, s) := entry src s st.dict "Matte"
      let matte : Option (List Fixed) := match mt with
        | some (.array xs) => if soft then xs.mapM Content.Interp.num? else none
        | _ => none
      if soft ∧ p.bpc.isNone then (none, s) else
      let p := { p with mask := !soft, key := none }
      match src.decode s n st with
      | (.ok bytes, s) =>
        match decodePixmap limits p (some grayInfo) bytes with
        | .ok pm => (some (pm, matte), s)
        | .error _ => (none, s)
      | (.error _, s) => (none, s)
    | (_, s) => (none, s)
  | _ => (none, s)

/-- **Apply an image's masks**: a soft mask (`/SMask`, which takes precedence; `/Matte`
un-premultiplies the colours, converted through the image's colour space) or an explicit
`/Mask` stencil. Stencil images (`/ImageMask`) are unmasked. Mask grids at most `cap` pixels
(`withMask`). -/
def applyMasks (cap : Nat) (info : Option CSInfo) (sm mk : Option MaskImg) (pm : Pixmap) :
    Pixmap :=
  if pm.stencil then pm else
  match sm, mk with
  | some (m, matte), _ =>
    let r := withMask cap pm m 0
    match matte, info with
    | some ms, some i => r.unmatte (Clip.deviceRGB (i.color ms))
    | _, _ => r
  | none, some (m, _) => withMask cap pm m 3
  | none, none => pm

/-- **Decode an image XObject** `num gen` through the source (its filters, the session
budget); an image codec yields the placeholder. Its `/SMask` (else its `/Mask` stream) is
loaded and applied (`applyMasks`); a soft mask disables colour-key masking (§8.9.6.4). -/
def loadXObject {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (named : List (Name × CSInfo))
    (num gen : Nat) : Except Error Pixmap × σ :=
  match src.fetch s num gen with
  | (.ok (.stream st), s) =>
    let (p, s) := imgDictOf src s st.dict
    let (info, s) := csOf src s named p.cs
    let (sm, s) := if p.mask then (none, s)
      else loadMask limits src s true (Dict.get? st.dict (Content.Run.nm "SMask"))
    let (mk, s) := if p.mask ∨ sm.isSome then (none, s)
      else loadMask limits src s false (Dict.get? st.dict (Content.Run.nm "Mask"))
    let p := if sm.isSome then { p with key := none } else p
    let fin := applyMasks limits.maxImagePixels info sm mk
    if hasCodec limits st.dict then (.ok (fin placeholder), s) else
    match src.decode s num st with
    | (.ok bytes, s) => ((decodePixmap limits p info bytes).map fin, s)
    | (.error e, s) => (.error e, s)
  | (.ok (.obj _), s) => (.error (.malformed 0 "image XObject is not a stream"), s)
  | (.error e, s) => (.error e, s)

/-- **Decode an inline image** (`BI … ID … EI`): parameters already abbreviation-expanded
(5.2b), raw data decoded with `Filter.decodeStream` (bounded by
`Limits.maxDecodedStreamBytes`); named colour spaces from `named`. Pure: inline images hold
no references. -/
def decodeInline (limits : Limits) (named : List (Name × CSInfo)) (params : Dict)
    (raw : ByteArray) : Except Error Pixmap :=
  if hasCodec limits params then .ok placeholder else
  let p := (imgDictOf Source.empty () params).1
  let info := (csOf Source.empty () named p.cs).1
  match Filter.decodeStream limits params raw with
  | .ok (.data b) => decodePixmap limits p info b
  | .ok (.image ..) => .ok placeholder
  | .error e => .error e

/-! ## 7. Per-page image table -/

/-- Maximum number of decoded image pixels held for one page (all XObjects together; each
pixel is 4 bytes, so 1 GiB). Further XObjects are drawn as the placeholder. A local cap
(no `Limits` field yet). -/
def maxPageImagePixels : Nat := 1 <<< 28

/-- The images of a page, decoded before rendering. -/
structure ImageTable where
  /-- Limits for decoding inline images. -/
  limits : Limits := {}
  /-- The page's named colour spaces (`/ColorSpace` resources), for inline images. -/
  named : List (Name × CSInfo) := []
  /-- Decoded image XObjects by `(num, gen)` (`none`: failed, drawn as nothing). -/
  xobjs : List ((Nat × Nat) × Option Pixmap) := []
  /-- Pixels held so far. -/
  pixels : Nat := 0

instance : Inhabited ImageTable := ⟨{}⟩

/-- Resolve the named colour spaces of a resource dictionary. -/
def namedSpaces {σ : Type} (src : Source σ) (s : σ) (res : Dict) : List (Name × CSInfo) × σ :=
  match Dict.get? res (Content.Run.nm "ColorSpace") with
  | none => ([], s)
  | some o =>
    let (d, s) := Content.Run.dictOf src s o
    d.foldl (fun (acc : List (Name × CSInfo) × σ) kv =>
      match Content.Run.csInfo src acc.2 kv.2 with
      | (some i, s) => ((kv.1, i) :: acc.1, s)
      | (none, s) => (acc.1, s)) ([], s)

/-- Add image XObject `num gen` to the table (once). -/
def ImageTable.add {σ : Type} (src : Source σ) (acc : ImageTable × σ) (num gen : Nat) :
    ImageTable × σ :=
  let t := acc.1
  if t.xobjs.any (·.1 == (num, gen)) then acc else
  let (r, s) := loadXObject t.limits src acc.2 t.named num gen
  match r with
  | .ok pm =>
    let n := pm.w * pm.h
    if maxPageImagePixels < t.pixels + n then
      ({ t with xobjs := ((num, gen), some placeholder) :: t.xobjs }, s)
    else ({ t with xobjs := ((num, gen), some pm) :: t.xobjs, pixels := t.pixels + n }, s)
  | .error _ => ({ t with xobjs := ((num, gen), none) :: t.xobjs }, s)

/-- **Load the images of a display list**: every distinct image XObject decoded once (in
first-use order), including images inside soft-mask groups (`DisplayList.foldDeep`, task
7.3f), the page's named colour spaces resolved (`res`: the page resources). -/
def loadImages {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (res : Dict)
    (items : DisplayList) : ImageTable × σ :=
  let (named, s) := namedSpaces src s res
  Content.DisplayList.foldDeep (fun acc it =>
    match it with
    | .image (.xobject _ n g) _ _ _ => ImageTable.add src acc n g
    | _ => acc) limits.maxXObjectDepth ({ limits, named }, s) items

/-- The pixmap of an image source (`none`: nothing to draw). Inline images are decoded here. -/
def ImageTable.pixmap (t : ImageTable) : ImageSource → Option Pixmap
  | .xobject _ n g => ((t.xobjs.find? (·.1 == (n, g))).map (·.2)).join
  | .inline params data =>
    match decodeInline t.limits t.named params data with
    | .ok pm => some pm
    | .error _ => none

/-! ## 8. Placement -/

/-- One in fixed point (32 fractional bits). -/
def fone : Int := 4294967296

/-- Composite colour `(r, g, b)` with opacity `a` (bytes) at byte offset `j` of the page
buffer (as `Clip.blendPx`; an opaque pixel is written directly). -/
def putPx (buf : ByteArray) (j r g b a : Nat) : ByteArray :=
  if a = 0 then buf
  else if a = 255 then
    Clip.setB (Clip.setB (Clip.setB buf j (u8 r)) (j + 1) (u8 g))
      (j + 2) (u8 b)
  else
    let buf := Clip.setB buf j (Clip.blend r (rd buf j) a)
    let buf := Clip.setB buf (j + 1) (Clip.blend g (rd buf (j + 1)) a)
    Clip.setB buf (j + 2) (Clip.blend b (rd buf (j + 2)) a)

/-- `putPx` preserves the buffer size. -/
theorem putPx_size (buf : ByteArray) (j r g b a : Nat) : (putPx buf j r g b a).size = buf.size := by
  unfold putPx; split
  · rfl
  · split <;> simp only [Clip.setB_size]

/-! ### Area-averaging downscale -/

/-- Running sums over a block of pixels: alpha-weighted colour and alpha. -/
structure Acc where
  /-- `Σ r · a`. -/
  r : Nat
  /-- `Σ g · a`. -/
  g : Nat
  /-- `Σ b · a`. -/
  b : Nat
  /-- `Σ a`. -/
  a : Nat

/-- Add `n` pixels from byte offset `i` to the sums. -/
def blockRow (d : ByteArray) : (n i r g b a : Nat) → Acc
  | 0, _, r, g, b, a => ⟨r, g, b, a⟩
  | n + 1, i, r, g, b, a =>
    let al := rd d (i + 3)
    blockRow d n (i + 4) (r + rd d i * al) (g + rd d (i + 1) * al) (b + rd d (i + 2) * al)
      (a + al)

/-- Add `k` rows of `n` pixels (row stride `rs` bytes) from byte offset `i` to the sums. -/
def blockSum (d : ByteArray) (n rs : Nat) : (k i : Nat) → Acc → Acc
  | 0, _, s => s
  | k + 1, i, s => blockSum d n rs k (i + rs) (blockRow d n i s.r s.g s.b s.a)

/-- Push the average of a block of `cnt` pixels: colour weighted by alpha (straight colour of
the premultiplied average), alpha averaged. -/
def pushAvg (acc : ByteArray) (s : Acc) (cnt : Nat) : ByteArray :=
  if s.a = 0 then (((acc.push 0).push 0).push 0).push 0
  else
    (((acc.push (u8 ((s.r + s.a / 2) / s.a))).push
      (u8 ((s.g + s.a / 2) / s.a))).push
      (u8 ((s.b + s.a / 2) / s.a))).push
      (u8 ((s.a + cnt / 2) / max cnt 1))

/-- `pushAvg` pushes four bytes. -/
theorem pushAvg_size (acc : ByteArray) (s : Acc) (cnt : Nat) :
    (pushAvg acc s cnt).size = acc.size + 4 := by
  unfold pushAvg; split <;> simp [ByteArray.size_push]

/-- One output row of the box filter: output columns `ox, ox + 1, …` (`fuel` of them), each
the average of source columns `[ox · sw / tw, (ox + 1) · sw / tw)` of source rows
`[y0, y0 + ny)`. -/
def boxCols (d : ByteArray) (sw tw y0 ny : Nat) : (fuel ox : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, ox, acc =>
    let x0 := ox * sw / tw
    let x1 := (ox + 1) * sw / tw
    boxCols d sw tw y0 ny fuel (ox + 1)
      (pushAvg acc (blockSum d (x1 - x0) (4 * sw) ny (4 * (y0 * sw + x0)) ⟨0, 0, 0, 0⟩)
        ((x1 - x0) * ny))

/-- `boxCols` pushes four bytes per output pixel. -/
theorem boxCols_size (d : ByteArray) (sw tw y0 ny : Nat) :
    ∀ (fuel ox : Nat) (acc : ByteArray),
      (boxCols d sw tw y0 ny fuel ox acc).size = acc.size + 4 * fuel
  | 0, _, _ => rfl
  | fuel + 1, ox, acc => by
    simp only [boxCols]; rw [boxCols_size d sw tw y0 ny fuel, pushAvg_size]; omega

/-- Output rows `oy, oy + 1, …` (`fuel` of them) of the box filter from `sw × sh` to
`tw × th`. -/
def boxRows (d : ByteArray) (sw sh tw th : Nat) : (fuel oy : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, oy, acc =>
    let y0 := oy * sh / th
    let y1 := (oy + 1) * sh / th
    boxRows d sw sh tw th fuel (oy + 1) (boxCols d sw tw y0 (y1 - y0) tw 0 acc)

/-- `boxRows` pushes `4 · tw` bytes per output row. -/
theorem boxRows_size (d : ByteArray) (sw sh tw th : Nat) :
    ∀ (fuel oy : Nat) (acc : ByteArray),
      (boxRows d sw sh tw th fuel oy acc).size = acc.size + 4 * tw * fuel
  | 0, _, _ => rfl
  | fuel + 1, oy, acc => by
    simp only [boxRows]; rw [boxRows_size d sw sh tw th fuel, boxCols_size, Nat.mul_succ]; omega

/-- **Area-averaging downscale** to `tw × th` (`1 ≤ tw ≤ w`, `1 ≤ th ≤ h` for a true box
filter): output pixel `(ox, oy)` is the alpha-weighted mean of the source block
`[ox·w/tw, (ox+1)·w/tw) × [oy·h/th, (oy+1)·h/th)`. Every source pixel is read once. -/
def boxDown (pm : Pixmap) (tw th : Nat) : Pixmap :=
  { pm with
    w := tw
    h := th
    data := boxRows pm.data pm.w pm.h tw th th 0 (ByteArray.emptyWithCapacity (4 * tw * th))
    size_eq := by rw [boxRows_size]; exact Nat.zero_add _ }

/-! ### Device geometry: grid fitting, sizes, fixed point -/

/-- MuPDF's grid-fitting tolerance (`MY_EPSILON`, device pixels). -/
def gridEps : Rat := 1 / 1000

/-- Snap down to a pixel boundary, unless within `gridEps` below the next one. -/
def snapLo (x : Rat) : Rat := if (x.ceil : Rat) - x ≤ gridEps then x.ceil else x.floor

/-- Snap up to a pixel boundary, unless within `gridEps` above the previous one. -/
def snapHi (x : Rat) : Rat := if x - (x.floor : Rat) ≤ gridEps then x.floor else x.ceil

/-- Origin `e` and extent `a` of one axis, expanded outward to whole pixels. -/
def snapSpan (e a : Rat) : Rat × Rat :=
  if 0 < a then let l := snapLo e; (l, snapHi (e + a) - l)
  else if a < 0 then let r := snapHi e; (r, snapLo (e + a) - r)
  else (e, a)

/-- **Grid fitting** (MuPDF `fz_gridfit_matrix`, non-tiled): an axis-aligned image
(`b = c = 0`) is expanded to cover every device pixel it touches, edges on pixel boundaries
(within `gridEps`). Other matrices are unchanged. -/
def gridfit (m : Aff) : Aff :=
  if m.b = 0 ∧ m.c = 0 then
    let x := snapSpan m.e m.a
    let y := snapSpan m.f m.d
    { m with a := x.2, e := x.1, d := y.2, f := y.1 }
  else m

/-- `⌈√q⌉` for `q ≥ 0`. -/
def ceilSqrt (q : Rat) : Nat :=
  let n := q.ceil.toNat
  let s := Nat.sqrt n
  if s * s < n then s + 1 else s

/-- Number of samples to keep along an axis of `n` samples whose device length is `√len2`:
`⌈√len2⌉` (at least 1) when that is fewer, else `n`. -/
def targetSide (len2 : Rat) (n : Nat) : Nat :=
  if len2 < (n : Rat) * n then max 1 (min n (ceilSqrt len2)) else n

/-- `q` in fixed point (32 fractional bits), clamped to `±lim`. -/
def toFix (q : Rat) (lim : Int) : Int64 :=
  Int64.ofInt (max (-lim) (min lim (q * (fone : Rat)).floor))

/-- `q` in fixed point rounded to nearest (per-pixel steps: the drift over a row stays below
one unit per 2³² steps of error each way), clamped to `±lim`. -/
def toFixR (q : Rat) (lim : Int) : Int64 :=
  Int64.ofInt (max (-lim) (min lim (roundRat (q * (fone : Rat)))))

/-- `√len2` in fixed point, clamped to `[2, 2⁴⁴]` (one device pixel in image units). -/
def fixLen (len2 : Rat) : Int64 :=
  let s := Nat.sqrt (len2 * (fone : Rat) * (fone : Rat)).floor.toNat
  Int64.ofNat (max 2 (min s (1 <<< 44)))

/-! ### Per-pixel sampling -/

/-- Everything the per-pixel loop needs, computed once per image. Coordinates are image
pixels in fixed point (`Int64`, 32 fractional bits). -/
structure Plan where
  /-- RGBA samples of the (possibly downscaled) pixmap. -/
  data : ByteArray
  /-- Pixmap width. -/
  pw : Nat
  /-- Pixmap height. -/
  ph : Nat
  /-- Width in fixed point. -/
  wF : Int64
  /-- Height in fixed point. -/
  hF : Int64
  /-- Image-`u` step per device pixel along a row. -/
  du : Int64
  /-- Image-`v` step per device pixel along a row. -/
  dv : Int64
  /-- One device pixel across the `u` edges, in image units (edge anti-aliasing). -/
  mU : Int64
  /-- One device pixel across the `v` edges, in image units. -/
  mV : Int64
  /-- Bilinear sampling (else nearest). -/
  lerp : Bool
  /-- Anti-aliased edges (else: painted iff the pixel centre maps inside the image). -/
  aa : Bool
  /-- Stencil mask: paint `(sr, sg, sb)` with the sample alpha as coverage. -/
  stencil : Bool
  /-- All sample alphas are 255. -/
  solid : Bool
  /-- Stencil colour, red. -/
  sr : UInt32
  /-- Stencil colour, green. -/
  sg : UInt32
  /-- Stencil colour, blue. -/
  sb : UInt32
  /-- Constant alpha (byte). -/
  alpha : UInt32
  /-- A clip mask is present (its bytes are the loop's `cd`). -/
  clip : Bool

/-- Integer part `i` of a coordinate as a sample index clamped to `[0, n)`. -/
@[inline] def idx (i : Int64) (n : Nat) : Nat :=
  if i < 0 then 0 else
  let k := i.toUInt64.toNat
  if k < n then k else n - 1

/-- Coverage (0–255) along one image axis of the device pixel whose centre maps to `u`, for
an image extent `[0, wF]` and one device pixel `m` across that axis's edges: with `aa`, the
overlap of `[u − m/2, u + m/2]` with `[0, wF]` over `m` (so a sub-pixel-thin image covers a
fraction of the pixel); without, `255` iff `0 ≤ u < wF`. -/
@[inline] def cov1 (aa : Bool) (u wF m : Int64) : UInt32 :=
  if aa then
    let h := m >>> 1
    if h ≤ u ∧ u + h ≤ wF then 255 else
    let lo := if u - h < 0 then 0 else u - h
    let hi := if u + h < wF then u + h else wF
    if hi ≤ lo then 0 else
    let c := ((hi - lo) * 255 + h) / m
    if 255 < c then 255 else c.toUInt64.toUInt32
  else if 0 ≤ u ∧ u < wF then 255 else 0

/-- Linear interpolation with a 12-bit weight. -/
@[inline] def lerpU (a b f : UInt32) : UInt32 := (a * (4096 - f) + b * f) >>> 12

/-- Bilinear interpolation of the bytes at four offsets. -/
@[inline] def bil (d : ByteArray) (i00 i10 i01 i11 : Nat) (fu fv : UInt32) : UInt32 :=
  lerpU (lerpU (Clip.getU d i00) (Clip.getU d i10) fu)
    (lerpU (Clip.getU d i01) (Clip.getU d i11) fu) fv

/-- Channel `k` premultiplied by alpha (`c · a`, up to 255²) at pixel offset `i`. -/
@[inline] def preU (d : ByteArray) (i k : Nat) : UInt32 :=
  Clip.getU d (i + k) * Clip.getU d (i + 3)

/-- Bilinear interpolation of channel `k` premultiplied by alpha, divided back by the
interpolated alpha `a > 0` (straight colour of the premultiplied interpolation). -/
@[inline] def bilPre (d : ByteArray) (i00 i10 i01 i11 k : Nat) (fu fv a : UInt32) : UInt32 :=
  let p := lerpU (lerpU (preU d i00 k) (preU d i10 k) fu)
    (lerpU (preU d i01 k) (preU d i11 k) fu) fv
  let c := (p + a / 2) / a
  if 255 < c then 255 else c

/-- **Paint one device pixel** at page byte offset `bi` (clip byte `ci` of `cd`), whose
centre maps to image coordinates `(u, v)`: coverage from the edges (`cov1`), the clip and the
constant alpha; the sample by nearest or bilinear interpolation (MuPDF's `lerp`: the sample
grid is offset by half a pixel, neighbours clamped at the image border); composited with
`Clip.pxU`. -/
def pixel (P : Plan) (cd : ByteArray) (u v : Int64) (bi ci : Nat) (buf : ByteArray) :
    ByteArray :=
  let cu := cov1 P.aa u P.wF P.mU
  let cv := cov1 P.aa v P.hF P.mV
  if cu == 0 || cv == 0 then buf else
  let c0 := if cu == 255 then cv else if cv == 255 then cu else Clip.mul255U cu cv
  let c1 := if P.clip then Clip.mul255U c0 (Clip.getU cd ci) else c0
  let cov := if P.alpha == 255 then c1 else Clip.mul255U c1 P.alpha
  if cov == 0 then buf else
  if P.lerp then
    let ul := u - 2147483648
    let vl := v - 2147483648
    let xi := ul >>> 32
    let yi := vl >>> 32
    let fu := ((ul >>> 20) &&& 4095).toUInt64.toUInt32
    let fv := ((vl >>> 20) &&& 4095).toUInt64.toUInt32
    let x0 := 4 * idx xi P.pw
    let x1 := 4 * idx (xi + 1) P.pw
    let r0 := 4 * P.pw * idx yi P.ph
    let r1 := 4 * P.pw * idx (yi + 1) P.ph
    let i00 := r0 + x0
    let i10 := r0 + x1
    let i01 := r1 + x0
    let i11 := r1 + x1
    let d := P.data
    if P.solid then
      Clip.pxU buf bi (bil d i00 i10 i01 i11 fu fv)
        (bil d (i00 + 1) (i10 + 1) (i01 + 1) (i11 + 1) fu fv)
        (bil d (i00 + 2) (i10 + 2) (i01 + 2) (i11 + 2) fu fv) cov
    else
      let a := bil d (i00 + 3) (i10 + 3) (i01 + 3) (i11 + 3) fu fv
      let fa := Clip.mul255U a cov
      if fa == 0 then buf
      else if P.stencil then Clip.pxU buf bi P.sr P.sg P.sb fa
      else
        Clip.pxU buf bi (bilPre d i00 i10 i01 i11 0 fu fv a) (bilPre d i00 i10 i01 i11 1 fu fv a)
          (bilPre d i00 i10 i01 i11 2 fu fv a) fa
  else
    let i := 4 * (P.pw * idx (v >>> 32) P.ph + idx (u >>> 32) P.pw)
    let d := P.data
    let fa := if P.solid then cov else Clip.mul255U (Clip.getU d (i + 3)) cov
    if P.stencil then Clip.pxU buf bi P.sr P.sg P.sb fa
    else Clip.pxU buf bi (Clip.getU d i) (Clip.getU d (i + 1)) (Clip.getU d (i + 2)) fa

/-- A conditional between two buffers of size `n` has size `n`. -/
theorem size_ite {c : Prop} [Decidable c] {x y : ByteArray} {n : Nat} (hx : x.size = n)
    (hy : y.size = n) : (if c then x else y).size = n := by
  split <;> assumption

/-- Painting a pixel preserves the buffer size. -/
theorem pixel_size (P : Plan) (cd : ByteArray) (u v : Int64) (bi ci : Nat) (buf : ByteArray) :
    (pixel P cd u v bi ci buf).size = buf.size := by
  unfold pixel
  dsimp only
  repeat' (first | exact Clip.pxU_size _ _ _ _ _ _ | rfl | apply size_ite)

/-- Paint one row: `fuel` device pixels, image coordinates `(u, v)` advancing by
`(P.du, P.dv)`, page byte offset `bi` (+4) and clip offset `ci` (+1) per pixel. -/
def colLoop (P : Plan) (cd : ByteArray) :
    (fuel : Nat) → (u v : Int64) → (bi ci : Nat) → ByteArray → ByteArray
  | 0, _, _, _, _, buf => buf
  | fuel + 1, u, v, bi, ci, buf =>
    colLoop P cd fuel (u + P.du) (v + P.dv) (bi + 4) (ci + 1) (pixel P cd u v bi ci buf)

/-- A row preserves the buffer size. -/
theorem colLoop_size (P : Plan) (cd : ByteArray) :
    ∀ (fuel : Nat) (u v : Int64) (bi ci : Nat) (buf : ByteArray),
      (colLoop P cd fuel u v bi ci buf).size = buf.size
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, u, v, bi, ci, buf => by
    simp only [colLoop]; rw [colLoop_size P cd fuel, pixel_size]

/-- Paint `fuel` rows of rectangle `r` from row `y` on, through the device → image map `A`
(page width `W`; clip mask grid origin `(cx, cy)`, width `cw`): each row's start (pixel
centre) is evaluated exactly over `ℚ`, then stepped in fixed point. -/
def rowLoop (P : Plan) (cd : ByteArray) (W : Nat) (A : Aff) (r : IRect) (cx cy : Int)
    (cw : Nat) : (fuel : Nat) → (y : Int) → ByteArray → ByteArray
  | 0, _, buf => buf
  | fuel + 1, y, buf =>
    let xc : Rat := (r.x0 : Rat) + 1 / 2
    let yc : Rat := (y : Rat) + 1 / 2
    let u0 := toFix (A.a * xc + A.c * yc + A.e) (1 <<< 60)
    let v0 := toFix (A.b * xc + A.d * yc + A.f) (1 <<< 60)
    let bi := 4 * (y.toNat * W + r.x0.toNat)
    let ci := Clip.offs cx cy cw r.x0 y
    rowLoop P cd W A r cx cy cw fuel (y + 1) (colLoop P cd r.width u0 v0 bi ci buf)

/-- Rows preserve the buffer size. -/
theorem rowLoop_size (P : Plan) (cd : ByteArray) (W : Nat) (A : Aff) (r : IRect) (cx cy : Int)
    (cw : Nat) :
    ∀ (fuel : Nat) (y : Int) (buf : ByteArray),
      (rowLoop P cd W A r cx cy cw fuel y buf).size = buf.size
  | 0, _, _ => rfl
  | fuel + 1, y, buf => by
    simp only [rowLoop]; rw [rowLoop_size P cd W A r cx cy cw fuel, colLoop_size]

/-- Device bounding box (whole pixels) of the unit square mapped by `dev`. -/
def deviceBox (dev : Aff) : IRect :=
  let ps := [dev.apply ⟨0, 0⟩, dev.apply ⟨1, 0⟩, dev.apply ⟨0, 1⟩, dev.apply ⟨1, 1⟩]
  let p0 := dev.apply ⟨0, 0⟩
  let mnx := ps.foldl (fun m p => min m p.x) p0.x
  let mxx := ps.foldl (fun m p => max m p.x) p0.x
  let mny := ps.foldl (fun m p => min m p.y) p0.y
  let mxy := ps.foldl (fun m p => max m p.y) p0.y
  ⟨mnx.floor, mny.floor, mxx.ceil, mxy.ceil⟩

/-- The device rectangle visited for an image: its bounding box ∩ the item's clip window. -/
def placeRect (W H : Nat) (dev : Aff) (cm : Option Mask) : IRect :=
  (deviceBox dev).inter (Clip.itemWindow W H cm)

/-- The sampling plan of a pixmap placed by `dev` (see `place`). -/
def mkPlan (pm : Pixmap) (dev A : Aff) (cm : Option Mask) (rgb : Nat × Nat × Nat) (alpha : Nat)
    (smooth : Bool) : Plan :=
  let wq : Rat := pm.w
  let hq : Rat := pm.h
  let lu2 := dev.a * dev.a + dev.b * dev.b
  let lv2 := dev.c * dev.c + dev.d * dev.d
  let rect := (dev.b = 0 ∧ dev.c = 0) ∨ (dev.a = 0 ∧ dev.d = 0)
  let up := wq * wq < lu2 ∨ hq * hq < lv2
  let big := 4 * wq * wq < lu2 ∨ 4 * hq * hq < lv2
  { data := pm.data, pw := pm.w, ph := pm.h,
    wF := toFix wq (1 <<< 60), hF := toFix hq (1 <<< 60),
    du := toFixR A.a (1 <<< 44), dv := toFixR A.b (1 <<< 44),
    mU := fixLen (A.a * A.a + A.c * A.c), mV := fixLen (A.b * A.b + A.d * A.d),
    lerp := smooth && (!decide rect || decide up) && (pm.interpolate || !decide big),
    aa := smooth && !decide (dev.b = 0 ∧ dev.c = 0),
    stencil := pm.stencil, solid := pm.solid,
    sr := UInt32.ofNat (min rgb.1 255), sg := UInt32.ofNat (min rgb.2.1 255),
    sb := UInt32.ofNat (min rgb.2.2 255), alpha := UInt32.ofNat (min alpha 255),
    clip := cm.isSome }

/-- Does placing `pm` by `dev` downscale it first (see `place`)? -/
def downscales (cap : Nat) (pm : Pixmap) (dev : Aff) (smooth : Bool) : Bool :=
  smooth && (targetSide (dev.a * dev.a + dev.b * dev.b) pm.w < pm.w ||
    targetSide (dev.c * dev.c + dev.d * dev.d) pm.h < pm.h) && decide (pm.w * pm.h ≤ cap)

/-- **Place a pixmap** on a `W × H` RGBA page buffer: the unit square mapped by `dev0` (image
space → device), clip mask `cm`, fill colour `rgb` (stencil masks), constant alpha `alpha`
(byte). With `smooth` (the renderer's choice; `false` gives plain nearest-neighbour sampling
at pixel centres, the 7.3b behaviour), MuPDF's choices (`fz_draw_fill_image`,
`fz_paint_image_imp`, 1.25.1): an axis-aligned matrix is **grid-fitted**; an image larger
than its device size along an axis is first **area-averaged** (`boxDown`) to `⌈device size⌉`
samples along it (when it has at most `cap` pixels); sampling is **bilinear** for
non-rectilinear matrices and for upscaling, except beyond 2× magnification without
`/Interpolate`; edges of non-axis-aligned images are **anti-aliased** (`cov1`). Returns the
buffer and the work done: device pixels visited plus source pixels averaged. -/
def place (cap W H : Nat) (pm0 : Pixmap) (dev0 : Aff) (cm : Option Mask)
    (rgb : Nat × Nat × Nat) (alpha : Nat) (buf : ByteArray) (smooth : Bool := true) :
    ByteArray × Nat :=
  let dev := if smooth then gridfit dev0 else dev0
  if dev.det = 0 then (buf, 0) else
  let down := downscales cap pm0 dev smooth
  let pm := if down then
      boxDown pm0 (targetSide (dev.a * dev.a + dev.b * dev.b) pm0.w)
        (targetSide (dev.c * dev.c + dev.d * dev.d) pm0.h)
    else pm0
  let A := Aff.inv dev * ⟨(pm.w : Rat), 0, 0, -(pm.h : Rat), 0, (pm.h : Rat)⟩
  let r := placeRect W H dev cm
  let P := mkPlan pm dev A cm rgb alpha smooth
  let cd := match cm with | some c => c.data | none => ByteArray.empty
  let cx := match cm with | some c => c.x0 | none => 0
  let cy := match cm with | some c => c.y0 | none => 0
  let cw := match cm with | some c => c.w | none => 0
  (rowLoop P cd W A r cx cy cw r.height r.y0 buf,
    r.width * r.height + if down then pm0.w * pm0.h else 0)

/-- Placing preserves the buffer size. -/
theorem place_size (cap W H : Nat) (pm : Pixmap) (dev : Aff) (cm : Option Mask)
    (rgb : Nat × Nat × Nat) (alpha : Nat) (buf : ByteArray) (smooth : Bool) :
    (place cap W H pm dev cm rgb alpha buf smooth).1.size = buf.size := by
  unfold place
  generalize (if smooth = true then gridfit dev else dev) = d
  dsimp only
  split
  · rfl
  · exact rowLoop_size _ _ _ _ _ _ _ _ _ _ _

/-- The visited rectangle lies inside the page. -/
theorem placeRect_area_le (W H : Nat) (dev : Aff) (cm : Option Mask) :
    (placeRect W H dev cm).width * (placeRect W H dev cm).height ≤ W * H := by
  have h1 := IRect.inter_width_le_right (deviceBox dev) (Clip.itemWindow W H cm)
  have h2 := IRect.inter_height_le_right (deviceBox dev) (Clip.itemWindow W H cm)
  have h3 := Clip.clipWindow_width_le W H cm
  have h4 := Clip.clipWindow_height_le W H cm
  simp only [placeRect, Clip.itemWindow] at h1 h2 ⊢
  exact Nat.mul_le_mul (by omega) (by omega)

/-- A downscale reads at most `cap` source pixels. -/
theorem downscales_le (cap : Nat) (pm : Pixmap) (dev : Aff) (smooth : Bool)
    (h : downscales cap pm dev smooth = true) : pm.w * pm.h ≤ cap := by
  simp only [downscales, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- **S3 for placement.** Placing an image visits at most `W · H` device pixels (one constant
step each), whatever the image size or matrix, plus at most `cap` source pixels averaged by
the downscale. -/
theorem place_steps_le (cap W H : Nat) (pm : Pixmap) (dev : Aff) (cm : Option Mask)
    (rgb : Nat × Nat × Nat) (alpha : Nat) (buf : ByteArray) (smooth : Bool) :
    (place cap W H pm dev cm rgb alpha buf smooth).2 ≤ W * H + cap := by
  unfold place
  generalize (if smooth = true then gridfit dev else dev) = d
  dsimp only
  split
  · exact Nat.zero_le _
  · have h1 := placeRect_area_le W H d cm
    have h2 := downscales_le cap pm d smooth
    revert h2
    generalize downscales cap pm d smooth = dn
    intro h2
    cases dn
    · simp only [Bool.false_eq_true, ite_false]; omega
    · simp only [ite_true]; have := h2 rfl; omega

/-! ## 9. Display items -/

/-- **Paint one image item** (`DisplayItem.image src ctm fill clip`) on a `W × H` page through
the page → device matrix `m`: the clip mask from `Clip.clipMaskC` (cached), the pixmap from
`tbl` (inline images decoded here), placed with `CTM × m` (`place`, smooth; downscale cap
`Limits.maxImagePixels`); `fill` gives the stencil colour and the constant alpha `ca`.
Nothing is drawn for an image that failed to decode. -/
def renderImage (cfg : Config) (m : Aff) (W H : Nat) (tbl : ImageTable) (st : Clip.RState)
    (src : ImageSource) (ctm : Matrix) (fill : FillStyle) (clip : Clip) : Clip.RState :=
  match tbl.pixmap src with
  | none => st
  | some pm =>
    let c := Clip.clipMaskC cfg m W H st.cache clip
    let p := place tbl.limits.maxImagePixels W H pm (Aff.ofMatrix ctm * m) c.1
      (Clip.deviceRGB fill.color) (Clip.compByte fill.alpha) st.buf
    { buf := p.1, cache := c.2.1, steps := st.steps + c.2.2 + p.2 }

/-- Painting an image preserves the buffer size. -/
theorem renderImage_size (cfg : Config) (m : Aff) (W H : Nat) (tbl : ImageTable)
    (st : Clip.RState) (src : ImageSource) (ctm : Matrix) (fill : FillStyle) (clip : Clip) :
    (renderImage cfg m W H tbl st src ctm fill clip).buf.size = st.buf.size := by
  unfold renderImage; split
  · rfl
  · exact place_size _ _ _ _ _ _ _ _ _ _

/-- **S3 for an image item.** The counted work is at most the clip's cost plus `W · H`
compositing steps plus `Limits.maxImagePixels` downscale reads (decoding work is bounded
separately: `w · h · ncomp` sample steps and `w · h` pixel steps, with
`w · h ≤ Limits.maxImagePixels`). -/
theorem renderImage_steps_le (cfg : Config) (m : Aff) (W H : Nat) (tbl : ImageTable)
    (st : Clip.RState) (src : ImageSource) (ctm : Matrix) (fill : FillStyle) (clip : Clip) :
    (renderImage cfg m W H tbl st src ctm fill clip).steps ≤
      st.steps + Clip.clipCost cfg W H clip + W * H + tbl.limits.maxImagePixels := by
  unfold renderImage; split
  · omega
  · rename_i pm _
    have h0 := Clip.clipMaskC_steps_le cfg m W H st.cache clip
    have h1 := place_steps_le tbl.limits.maxImagePixels W H pm (Aff.ofMatrix ctm * m)
      (Clip.clipMaskC cfg m W H st.cache clip).1
      (Clip.deviceRGB fill.color) (Clip.compByte fill.alpha) st.buf true
    simp only
    omega

/-! ## 10. Checks -/

private def bytes (l : List Nat) : ByteArray := ByteArray.mk (l.map UInt8.ofNat).toArray

private def dev (w h : Nat) : ImgDict :=
  { w, h, bpc := some 8, mask := false, decode := none, interp := false, cs := none }

private def grayCS : Option CSInfo := some (.dev .gray (.gray Comp.zero))

#guard rowBytes 3 1 1 == 1 && rowBytes 9 1 1 == 2 && rowBytes 3 3 16 == 18
#guard sampleAt (bytes [0b10110000]) 0 0 1 == 1 && sampleAt (bytes [0b10110000]) 0 1 1 == 0 &&
  sampleAt (bytes [0b10110000]) 0 2 1 == 1 && sampleAt (bytes [0xA5]) 0 1 4 == 5 &&
  sampleAt (bytes [0x12, 0x34]) 0 0 16 == 0x12
-- 1-bit gray: samples 1 0 1 → 255 0 255 (row padded to one byte).
#guard match decodePixmap {} { dev 3 1 with bpc := some 1 } grayCS (bytes [0b10100000]) with
  | .ok pm => pm.data.toList.map UInt8.toNat == [255, 255, 255, 255, 0, 0, 0, 255, 255, 255, 255, 255]
  | .error _ => false
-- /Decode [1 0] inverts.
#guard match decodePixmap {} { dev 2 1 with decode := some [1, 0] } grayCS (bytes [0, 255]) with
  | .ok pm => pm.data.toList.map UInt8.toNat == [255, 255, 255, 255, 0, 0, 0, 255]
  | .error _ => false
-- Dimension limit.
#guard match decodePixmap { maxImagePixels := 3 } (dev 2 2) grayCS (bytes []) with
  | .error (.limitExceeded .imagePixels) => true
  | _ => false
-- No colour space → placeholder.
#guard match decodePixmap {} (dev 2 2) none (bytes []) with
  | .ok pm => pm.w == 1 && pm.h == 1
  | .error _ => false
-- Colour key [5 20]: sample 10 transparent, 200 opaque.
#guard match decodePixmap {} { dev 2 1 with key := some [5, 20] } grayCS (bytes [10, 200]) with
  | .ok pm => pm.data.toList.map UInt8.toNat == [10, 10, 10, 0, 200, 200, 200, 255]
  | .error _ => false
-- Box filter: a 2×2 checker averages to mid grey.
#guard match decodePixmap {} (dev 2 2) grayCS (bytes [0, 255, 255, 0]) with
  | .ok pm => (boxDown pm 1 1).data.toList.map UInt8.toNat == [128, 128, 128, 255]
  | .error _ => false
-- Downscale targets and grid fitting.
#guard targetSide 1 2 == 1 && targetSide 4 2 == 2 && targetSide (9 / 4) 600 == 2
#guard (gridfit ⟨2, 0, 0, 1, 1 / 2, 0⟩).e == 0 && (gridfit ⟨2, 0, 0, 1, 1 / 2, 0⟩).a == 3 &&
  (gridfit ⟨-2, 0, 0, -1, 5 / 2, 3⟩).e == 3 && (gridfit ⟨-2, 0, 0, -1, 5 / 2, 3⟩).a == -3
-- Edge coverage: half a pixel inside the edge → half covered.
#guard cov1 true 0 (4 * 4294967296) 4294967296 == 128 && cov1 true (4294967296 / 2) 100 4294967296 == 0

end SafePdf.Core.Raster.Image
