import SafePdf.Core.Raster.Shading
import SafePdf.Core.Content.Run
import SafePdf.Quarantine.DCT
import SafePdf.Quarantine.CCITT
import SafePdf.Quarantine.JPX

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
   predictors) are the core's byte filters. A terminal image codec follows the byte filters.
   Supported codecs run through their quarantine adapters. Unsupported codec chains use a
   1 × 1 opaque mid-grey placeholder, painted on the image's unit square.
   **`/JPXDecode`** (M10.2b) decodes a terminal JPX payload after bounded byte filters.
   The adapter validates the full SIZ against the PDF dimensions and selects mapped colour,
   literal indices and opacity. Ordinary PDF Decode and BitsPerComponent are ignored. A
   one-bit stencil uses Decode once. Embedded sRGB, Gray and enumerated CMYK use the raster
   device conversions. ICC GRAY/RGB/CMYK use device alternates without profile transforms.
   Other unsupported embedded profiles/spaces fall back by colour count (1/3/4). A supplied
   and unresolved PDF space is an error. A nonzero SMaskInData supersedes SMask and Mask.
   Associated samples are unblended in source component units before colour conversion.
   Categorical samples and embedded opacity prefer their native resolution. Continuous colours
   retain an extra wavelet level for the box filter. Preferred reductions clamp to nonempty levels shared by the tile-components.
   Byte limits try coarser available levels. An exhausted limit or invalid main JPX image
   returns a typed error and the page skips that placement. A malformed subsidiary mask
   is dropped, while a JPX mask budget failure propagates. The document render charges
   filter output, JPX sample/coverage/profile bytes and retained RGBA to the shared budget.
   **`/DCTDecode`** (task 7.6a) is decoded by `SafePdf.Quarantine.DCT` (baseline JPEG, pure
   Lean): a chain `pre ++ [/DCTDecode]` (`dctSplit`) is decoded up to the codec through the
   source (the stream with `/Filter`/`/DecodeParms` cut before it, so the session budget is
   charged), then `decodeDCT` decodes the JPEG (`/ColorTransform` from its parameters) and
   **re-validates** it against the image dictionary: the JPEG's component count must equal
   the colour space's (a missing `/ColorSpace` is taken from the JPEG: 1 gray, 3 RGB, 4 CMYK),
   and its samples are read as an 8-bit `/Width × /Height` raster of the dictionary (short
   data reads 0, extra data is ignored — MuPDF reads the decoded stream the same way), with
   the dictionary's `/Decode` (Adobe-inverted CMYK JPEGs carry `/Decode [1 0 1 0 1 0 1 0]`).
   Any decoder error (progressive, arithmetic, 12-bit, malformed, over a limit) or a
   component mismatch yields the placeholder (S7); a DCT soft mask that fails is dropped.
   DCT stencil masks (`/ImageMask true`) stay the placeholder.
   **Reduced-size JPEG decoding** (task 7.10): a JPEG XObject drawn on the page at a quarter of its
   size or less is decoded at `1 / 2^k` of its size, `k = dctScale (l2Factor …)` — MuPDF's
   `l2factor` (`fz_get_pixmap_from_image`) from the largest device extents of its uses
   (`imageExtents`, at the render's zoom), one step less (`dctScale`: the box filter needs two
   samples per pixel), as libjpeg's `scale_num = 8 / 2^k` — so
   the raster is `⌈/Width / 2^k⌉ × ⌈/Height / 2^k⌉` (`ImgDict.reduce`); the remaining
   reduction is the placement's area-averaging downscale.
   **Every image is decoded at its drawn size** (task 8.6): images are converted row by row
   (`Src`, `fused`) — no image-size sample or RGBA buffer — and box-filtered **while
   decoding** to the size the placement would box-filter them to (`Extent.t`: the
   `⌈√…⌉` of the grid-fitted device extents of the largest use, `imageExtents`, clamped to the
   image: `targetSide`), with the placement's own blocks and rounding, masks (`/SMask`,
   `/Mask` stencils, on `withMask`'s grid), colour key and `/Matte` applied per pixel in the
   old order — so the placement finds the pixmap at its target and paints the pixels it
   painted before (corpus: 2,445 of 2,450 pages byte-identical; the other 5 draw an image at
   two sizes, the smaller use now box-filtered twice, ≤ +0.004 points). Inline images get the
   target of their single use (`inlineExt`). Not reduced (decoded at full size, as before):
   images also drawn in tiling cells or Type 3 glyphs (their matrices are cell/glyph
   matrices, not page matrices: the target would need the pattern matrix and the tile
   raster; Type 3 glyph images go through MuPDF's own stencil scaler, `Type3`). A JPEG
   whose soft mask has a `/Matte` keeps its full-size JPEG decode (MuPDF), but is
   box-filtered like any image (exact: the matte is undone per pixel first).
   **Over a limit, a reduced decode instead of the placeholder** (task 8.6): a JPEG whose
   planes, coefficients or output exceed `maxDecodedStreamBytes` is decoded again at the next
   scale (up to 1/8, `dctSrc`); a pixmap whose RGBA (`4 · w · h`) would exceed it is decoded
   at the first `⌈n / 2^j⌉` that fits (`fitTarget`, `fitScale`). The page's image budget
   (`maxPageImagePixels`) lowers that cap for each further image (`ImageTable.add`). What
   stays full size: the decoded filter output of an XObject (`Source.decode`, at most
   `maxDecodedStreamBytes`; the byte filters are not streaming) and of a soft mask — decoded
   with `/DL` = `dataSize` (`withDL`, task 8.10), so the Flate output is reserved once
   rather than grown by doubling.
   **`/CCITTFaxDecode`** (task 7.8) is decoded by `SafePdf.Quarantine.CCITT` (MuPDF's
   `filter-fax.c` ported): a chain `pre ++ [/CCITTFaxDecode]` (`ccittSplit`) is decoded up to
   the codec, then `decodeCCITT` decodes at most `/Height` rows with the parameters of its
   `/DecodeParms` (`ccittParams`, MuPDF's defaults; references resolved through the source for
   XObjects) and the rows are read as ordinary sample data (`decodePixmap`: `/Decode`,
   stencil masks, short data padded with zeros as MuPDF pads). Errors yield the placeholder.
   dvips + Ghostscript Type 3 bitmap fonts draw every glyph as an inline CCITT stencil mask.
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
   grey). For JPX images a resolved Separation or DeviceN tint function maps the source
   components into its alternate device space before RGB conversion (decoder Plan §9, M10.2t).
   An inline image's resource-name colour space has been replaced by the runner with
   the definition from the resources of the content that shows it (page or form; task 7.3f,
   `Run.annotInline`). Inline JPX tint definitions retain their function references until
   the page image loader decodes them. A name left unresolved is looked up in the page's
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
   Since task 8.6 the samples are produced one row at a time (`rowRGBA`), never as an
   image-size buffer; the pixmap is capped instead: `4 · w · h ≤
   Limits.maxDecodedStreamBytes` (else a reduced decode, see 1).
5. **RGBA** (`fullRGBA`, `toRGBA`): `4 · w · h` bytes (`Pixmap.size_eq`, by construction). Stencil masks
   (`/ImageMask true`) keep the coverage `255 − byte(d)` in the alpha byte (default `/Decode
   [0 1]`: sample 0 paints) and take the fill colour at painting time.
6. **Masks** (§6b). *Colour key* (`applyKey`): a `/Mask` array of `2 · ncomp` integers makes
   pixels whose raw samples all lie in the ranges transparent. *Explicit mask* (a `/Mask`
   stream) and *soft mask* (`/SMask`, which wins and disables the colour key): decoded through
   the source like an image (`loadMask`: a stencil with its own `/Decode`, resp. `DeviceGray`
   with its own `/Decode`), then both images are resampled (nearest) to the finer of the two
   grids (when ≤ `maxDecodedStreamBytes / 4` pixels, else the image's grid) and the mask value multiplies
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
one page are capped at `maxPageImagePixels` pixels in total (256 MiB of RGBA; each XObject is
decoded under what is left, reduced to fit; once it is spent, further XObjects get the
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

/-- `2 ^ n` without the big-number library. `Nat.pow` with a run-time exponent calls
`lean_nat_pow` and `Nat.shiftLeft` calls `lean_nat_shiftl`; both go through GMP even for a
small result, which showed up as 10 % of an image-heavy page (task 13.18). A 64-bit shift is
a single instruction (`pow2_eq`). -/
def pow2 (n : Nat) : Nat := if n < 62 then ((1 : UInt64) <<< n.toUInt64).toNat else 2 ^ n

/-- `pow2` is `2 ^ n`. -/
theorem pow2_eq (n : Nat) : pow2 n = 2 ^ n := by
  unfold pow2
  split
  · rename_i h
    rw [UInt64.toNat_shiftLeft]
    simp only [Nat.toUInt64]
    have h1 : n % 18446744073709551616 = n := Nat.mod_eq_of_lt (by omega)
    have h2 : n % 64 = n := Nat.mod_eq_of_lt (by omega)
    simp [h1, h2, Nat.one_shiftLeft]
    exact Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide : 1 < 2) h) (by decide : 2 ^ 62 ≤ 2 ^ 64)
  · rfl

/-- Sample `k` of the row starting at byte `row`, at most 8 significant bits (16-bit samples:
the high byte). Short data reads as 0. The low `bpc` bits are masked
(`x % 2 ^ bpc = x &&& (2 ^ bpc - 1)`, `sampleAt_eq`; `pow2` avoids `lean_nat_pow`, task 13.18). -/
def sampleAt (data : ByteArray) (row k bpc : Nat) : Nat :=
  let byte := rd data (row + byteOff k bpc)
  if 8 ≤ bpc then byte
  else (byte >>> (8 - bpc - (k * bpc) % 8)) &&& (pow2 bpc - 1)

/-- `sampleAt` with the modulus `2 ^ bpc` written out. -/
theorem sampleAt_eq (data : ByteArray) (row k bpc : Nat) :
    sampleAt data row k bpc =
      if 8 ≤ bpc then rd data (row + byteOff k bpc)
      else (rd data (row + byteOff k bpc) >>> (8 - bpc - (k * bpc) % 8)) % (2 ^ bpc) := by
  unfold sampleAt
  split
  · rfl
  · rw [pow2_eq, Nat.and_two_pow_sub_one_eq_mod]

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
  let nv := pow2 bits
  samplesRows data lut (w * nc) bpc nv (nc * nv) (rowBytes w nc bpc) h 0
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
  /-- A parsed PDF tint function and its alternate device, as used for shadings. -/
  | tint (space : Shading.ShadeCS)
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
  | .tint space =>
    let xs := (List.range nc).map fun j => (rd smp (b + j) : Rat) / 255
    let (r, g, blue) := space.rgb xs
    (((acc.push (u8 r)).push (u8 g)).push (u8 blue)).push 255
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

/-- Resolve an entry and immediate array elements (filter, Decode, Matte and colour key). -/
private def resolvedEntry {σ : Type} (src : Source σ) (s : σ) (d : Dict) (k : String) :
    Option PdfObject × σ :=
  match entry src s d k with
  | (some (.array xs), s) =>
    let (rev, s) := xs.foldl (fun (acc : List PdfObject × σ) o =>
      let (v, s) := Content.Run.resolve src acc.2 o
      (v :: acc.1, s)) ([], s)
    (some (.array rev.reverse), s)
  | r => r

private def arrayEntry {σ : Type} (src : Source σ) (s : σ) (d : Dict) (k : String) :
    Option (List PdfObject) × σ :=
  match resolvedEntry src s d k with
  | (some (.array xs), s) => (some xs, s)
  | (_, s) => (none, s)

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
  let (dc, s) := arrayEntry src s d "Decode"
  let (ip, s) := entry src s d "Interpolate"
  let (cs, s) := entry src s d "ColorSpace"
  let (mk, s) := entry src s d "Mask"
  let dec : Option (List Rat) := dc.bind fun xs => (xs.mapM Content.Interp.num?).map (·.map Fixed.toRat)
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

/-- The dictionary of an image decoded at `1 / 2^k` of its size: `⌈/Width / 2^k⌉ ×
⌈/Height / 2^k⌉` (MuPDF `fz_decomp_image_from_stream`, `w = (w + f − 1) >> l2factor`). -/
def ImgDict.reduce (p : ImgDict) (k : Nat) : ImgDict :=
  let f := 2 ^ k
  { p with w := (p.w + f - 1) / f, h := (p.h + f - 1) / f }

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

/-! ### Streaming decode to the drawn size (task 8.6)

An image is converted **row by row** — never as an image-size sample or RGBA buffer — and,
when it is drawn smaller than its size, **box-filtered to its drawn size while decoding**:
exactly the placement's area-averaging downscale (`boxDown`, same blocks
`[o · n / t, (o + 1) · n / t)`, same `pushAvg` rounding, same alpha weighting) applied before
instead of after, so the placement then finds the pixmap at its target size and paints the same
pixels as before (`place` downscales only an image larger than its target). Masks take part
per pixel, in the old order: the image's colour key, then both images on the finer grid
(nearest, `withMask`'s rule), the mask multiplying the alpha, the `/Matte` un-premultiplied,
then the box filter. One output row needs one source row of the image and of its mask at a
time plus `tw` running sums (`Acc`).

`Src` is an image as sample data with its conversion plan; `fused` builds the pixmap of a
`Src` (optionally masked) on the grid `gw × gh` reduced to `tw × th`. -/

/-- An image ready for row-by-row conversion: `w × h` samples of `nc` components of `bpc`
bits in `data`, normalised through `lut` (`bits`-bit tables), converted by `cv`, colour-key
ranges `ks` (raw samples). -/
structure Src where
  /-- Width in samples. -/
  w : Nat
  /-- Height in samples. -/
  h : Nat
  /-- The sample data (short data reads 0). -/
  data : ByteArray
  /-- Lookup tables (`luts`). -/
  lut : ByteArray
  /-- Components per sample. -/
  nc : Nat
  /-- Bits per component. -/
  bpc : Nat
  /-- Significant bits per component (`min bpc 8`). -/
  bits : Nat
  /-- Colour conversion. -/
  cv : Conv
  /-- Colour-key ranges (`keyRanges`). -/
  ks : List (Nat × Nat)
  /-- `/ImageMask`. -/
  stencil : Bool
  /-- `/Interpolate`. -/
  interp : Bool

/-- The colour-key ranges of `p` in effect (`applyKey`'s rule). -/
def keyRanges (p : ImgDict) (bpc nc : Nat) : List (Nat × Nat) :=
  match p.key with
  | some k => if k.length = 2 * nc ∧ !p.mask then keyPairs bpc k else []
  | none => []

/-- The `Src` of image `p` with a known plan (as `finish` decodes it). -/
def Src.ofPlan (p : ImgDict) (bpc nc : Nat) (cv : Conv) (n : Norm) (data : ByteArray) : Src :=
  { w := p.w, h := p.h, data, lut := luts n nc bpc (min bpc 8) p.decode, nc, bpc,
    bits := min bpc 8, cv, ks := keyRanges p bpc nc, stencil := p.mask, interp := p.interp }

/-- The placeholder as a `Src`: one mid-grey (`128`) RGB sample. -/
def Src.grey : Src :=
  let p : ImgDict :=
    { w := 1, h := 1, bpc := some 8, mask := false, decode := none, interp := false, cs := none }
  Src.ofPlan p 8 3 .rgb .unit (ByteArray.mk #[128, 128, 128])

/-- Append source row `y` of the sample data as RGBA (`4 · w` bytes) to `acc`. -/
def rowRGBA (data lut : ByteArray) (w nc bpc bits : Nat) (cv : Conv) (y : Nat)
    (acc : ByteArray) : ByteArray :=
  let nv := pow2 bits
  let smp := samplesLoop data lut bpc nv (nc * nv) (y * rowBytes w nc bpc) (w * nc)
    0 0 (ByteArray.emptyWithCapacity (w * nc))
  rgbaLoop smp nc cv w 0 acc

/-- `rowRGBA` appends four bytes per pixel. -/
theorem rowRGBA_size (data lut : ByteArray) (w nc bpc bits : Nat) (cv : Conv) (y : Nat)
    (acc : ByteArray) : (rowRGBA data lut w nc bpc bits cv y acc).size = acc.size + 4 * w := by
  simp only [rowRGBA, rgbaLoop_size]

/-- Source row `y` of `s` as RGBA (colour key applied), resampled (nearest) to `gw`
pixels: `4 · gw` bytes. -/
def Src.row (s : Src) (gw y : Nat) : ByteArray :=
  let r := rowRGBA s.data s.lut s.w s.nc s.bpc s.bits s.cv y (ByteArray.emptyWithCapacity (4 * s.w))
  let r := if s.ks.isEmpty then r
    else keyLoop s.data s.w s.nc s.bpc (rowBytes s.w s.nc s.bpc) s.ks s.w 0 y 0 r
  if gw = s.w then r else resCols r s.w gw 0 gw 0 (ByteArray.emptyWithCapacity (4 * gw))

/-- A source row has `4 · gw` bytes. -/
theorem Src.row_size (s : Src) (gw y : Nat) : (s.row gw y).size = 4 * gw := by
  unfold Src.row
  dsimp only
  split
  · rename_i h
    subst h
    split <;> simp only [keyLoop_size, rowRGBA_size] <;> exact Nat.zero_add _
  · rw [resCols_size]; exact Nat.zero_add _

/-- Row `y` of the grid `gw × gh`: the image's row `y · h / gh`, its mask's row `y · h' / gh`
multiplying the alpha (channel `ch`), un-premultiplied against the matte colour. -/
def gridRow (img : Src) (mk : Option (Src × Nat)) (matte : Option (Nat × Nat × Nat))
    (gw gh y : Nat) : ByteArray :=
  let a := img.row gw (y * img.h / gh)
  let a := match mk with
    | some (m, ch) => alphaLoop (m.row gw (y * m.h / gh)) ch gw 0 a
    | none => a
  match matte with
  | some (r, g, b) => matteLoop r g b gw 0 a
  | none => a

/-- A grid row has `4 · gw` bytes. -/
theorem gridRow_size (img : Src) (mk : Option (Src × Nat)) (matte : Option (Nat × Nat × Nat))
    (gw gh y : Nat) : (gridRow img mk matte gw gh y).size = 4 * gw := by
  unfold gridRow
  dsimp only
  split <;> split <;> simp only [matteLoop_size, alphaLoop_size, Src.row_size]

/-- Grid rows `y, y + 1, …` (`fuel` of them), appended. -/
def gridRows (img : Src) (mk : Option (Src × Nat)) (matte : Option (Nat × Nat × Nat))
    (gw gh : Nat) : (fuel y : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, y, acc => gridRows img mk matte gw gh fuel (y + 1) (acc ++ gridRow img mk matte gw gh y)

/-- `gridRows` appends `4 · gw` bytes per row. -/
theorem gridRows_size (img : Src) (mk : Option (Src × Nat)) (matte : Option (Nat × Nat × Nat))
    (gw gh : Nat) : ∀ (fuel y : Nat) (acc : ByteArray),
      (gridRows img mk matte gw gh fuel y acc).size = acc.size + 4 * gw * fuel
  | 0, _, _ => rfl
  | fuel + 1, y, acc => by
    simp only [gridRows]
    rw [gridRows_size img mk matte gw gh fuel, ByteArray.size_append, gridRow_size, Nat.mul_succ]
    omega

/-- Add one grid row (`gw` pixels) to the running sums of output columns `ox, ox + 1, …`
(`fuel` of them; column `ox` sums the pixels `[ox · gw / tw, (ox + 1) · gw / tw)`). -/
def addRow (row : ByteArray) (gw tw : Nat) : (fuel ox : Nat) → Array Acc → Array Acc
  | 0, _, s => s
  | fuel + 1, ox, s =>
    let x0 := ox * gw / tw
    let x1 := (ox + 1) * gw / tw
    let a := s.getD ox ⟨0, 0, 0, 0⟩
    addRow row gw tw fuel (ox + 1) (s.setIfInBounds ox (blockRow row (x1 - x0) (4 * x0) a.r a.g a.b a.a))

/-- The sums of grid rows `y, y + 1, …` (`fuel` of them). -/
def bandSums (img : Src) (mk : Option (Src × Nat)) (matte : Option (Nat × Nat × Nat))
    (gw gh tw : Nat) : (fuel y : Nat) → Array Acc → Array Acc
  | 0, _, s => s
  | fuel + 1, y, s =>
    bandSums img mk matte gw gh tw fuel (y + 1) (addRow (gridRow img mk matte gw gh y) gw tw tw 0 s)

/-- Push the averages of output columns `ox, …` (`fuel` of them) over a band of `n` rows. -/
def pushSums (s : Array Acc) (gw tw n : Nat) : (fuel ox : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, ox, acc =>
    let x0 := ox * gw / tw
    let x1 := (ox + 1) * gw / tw
    pushSums s gw tw n fuel (ox + 1) (pushAvg acc (s.getD ox ⟨0, 0, 0, 0⟩) ((x1 - x0) * n))

/-- `pushSums` pushes four bytes per output pixel. -/
theorem pushSums_size (s : Array Acc) (gw tw n : Nat) :
    ∀ (fuel ox : Nat) (acc : ByteArray), (pushSums s gw tw n fuel ox acc).size = acc.size + 4 * fuel
  | 0, _, _ => rfl
  | fuel + 1, ox, acc => by
    simp only [pushSums]; rw [pushSums_size s gw tw n fuel, pushAvg_size]; omega

/-- Output rows `oy, oy + 1, …` (`fuel` of them) of the grid box-filtered to `tw × th`: row
`oy` averages the grid rows `[oy · gh / th, (oy + 1) · gh / th)` (`boxRows`' blocks). -/
def boxGrid (img : Src) (mk : Option (Src × Nat)) (matte : Option (Nat × Nat × Nat))
    (gw gh tw th : Nat) : (fuel oy : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, oy, acc =>
    let y0 := oy * gh / th
    let y1 := (oy + 1) * gh / th
    let s := bandSums img mk matte gw gh tw (y1 - y0) y0 (Array.replicate tw ⟨0, 0, 0, 0⟩)
    boxGrid img mk matte gw gh tw th fuel (oy + 1) (pushSums s gw tw (y1 - y0) tw 0 acc)

/-- `boxGrid` pushes `4 · tw` bytes per output row. -/
theorem boxGrid_size (img : Src) (mk : Option (Src × Nat)) (matte : Option (Nat × Nat × Nat))
    (gw gh tw th : Nat) : ∀ (fuel oy : Nat) (acc : ByteArray),
      (boxGrid img mk matte gw gh tw th fuel oy acc).size = acc.size + 4 * tw * fuel
  | 0, _, _ => rfl
  | fuel + 1, oy, acc => by
    simp only [boxGrid]
    rw [boxGrid_size img mk matte gw gh tw th fuel, pushSums_size, Nat.mul_succ]; omega

/-- **The pixmap of `img`** (masked by `mk`'s channel, un-premultiplied against `matte`) on
the grid `gw × gh`, box-filtered to `tw × th` when that is smaller (`1 ≤ tw ≤ gw`,
`1 ≤ th ≤ gh` for a true box filter). Equal to the former pipeline — `toRGBA (samples …)`,
`applyKey`, `withMask`, `unmatte` on the grid, then `boxDown` — without its buffers. -/
def fused (img : Src) (mk : Option (Src × Nat)) (matte : Option (Nat × Nat × Nat))
    (gw gh tw th : Nat) : Pixmap :=
  let solid := !img.stencil && img.ks.isEmpty && mk.isNone
  if h : tw = gw ∧ th = gh then
    { w := tw, h := th,
      data := gridRows img mk matte gw gh gh 0 (ByteArray.emptyWithCapacity (4 * gw * gh)),
      size_eq := by rw [gridRows_size, h.1, h.2]; exact Nat.zero_add _,
      stencil := img.stencil, interpolate := img.interp, solid }
  else
    { w := tw, h := th,
      data := boxGrid img mk matte gw gh tw th th 0 (ByteArray.emptyWithCapacity (4 * tw * th)),
      size_eq := by rw [boxGrid_size]; exact Nat.zero_add _,
      stencil := img.stencil, interpolate := img.interp, solid }

/-- The grid an image and its mask are combined on (`withMask`'s rule): the finer of both
when it has at most `cap` pixels, else the image's. -/
def gridOf (cap : Nat) (img : Src) (mk : Option (Src × Nat)) : Nat × Nat :=
  match mk with
  | none => (img.w, img.h)
  | some (m, _) =>
    let tw0 := max img.w m.w
    let th0 := max img.h m.h
    if tw0 * th0 ≤ cap then (tw0, th0) else (img.w, img.h)

/-- **The first reduction `k' ≥ k` whose pixmap fits `cap` bytes** (`4 · ⌈w/2^k'⌉ ·
⌈h/2^k'⌉ ≤ cap`), trying at most `fuel` halvings; `k + fuel` when none does. -/
def fitScale (cap w h : Nat) : (fuel k : Nat) → Nat
  | 0, k => k
  | fuel + 1, k =>
    let f := 2 ^ k
    if 4 * ((w + f - 1) / f) * ((h + f - 1) / f) ≤ cap then k else fitScale cap w h fuel (k + 1)

/-- At most this many halvings are tried to fit an image into the pixmap cap (task 8.6;
`2^32` exceeds any `/Width` or `/Height` within `maxImagePixels`). -/
def maxHalvings : Nat := 32

/-- **The decoded size** of a `gw × gh` grid: the drawn-size target `t` (`(⌈√…⌉, ⌈√…⌉)` of
the largest use, `imageExtents`) clamped to `[1, gw] × [1, gh]` (the placement's
`targetSide`), else the full grid; then, when its RGBA exceeds `cap` bytes, halved
(`fitScale`, MuPDF-style `⌈n / 2^j⌉`) until it fits — a reduced image instead of a failure. -/
def fitTarget (cap gw gh : Nat) (t : Option (Nat × Nat)) : Nat × Nat :=
  let (tw, th) := match t with
    | some (a, b) => (min gw (max 1 a), min gh (max 1 b))
    | none => (gw, gh)
  if 4 * tw * th ≤ cap then (tw, th) else
  let f := 2 ^ fitScale cap gw gh maxHalvings 0
  (min tw ((gw + f - 1) / f), min th ((gh + f - 1) / f))

/-- `fitTarget` never exceeds the grid. -/
theorem fitTarget_le (cap gw gh : Nat) (t : Option (Nat × Nat)) :
    (fitTarget cap gw gh t).1 ≤ gw ∧ (fitTarget cap gw gh t).2 ≤ gh := by
  unfold fitTarget
  cases t with
  | none => dsimp only; split <;> simp only [] <;> exact ⟨by omega, by omega⟩
  | some ab => dsimp only; split <;> simp only [] <;> exact ⟨by omega, by omega⟩

/-- Decode with a known plan (`bpc` bits, `nc` components, conversion, normalisation) to
`tw × th` (task 8.6; clamped to `[1, w] × [1, h]`; `tw = w`, `th = h`: full size): checks
`/BitsPerComponent` and the pixmap cap (`4 · tw · th ≤ Limits.maxDecodedStreamBytes`), then
converts row by row (`fused`: colour key, box filter). Too many components yield the
placeholder. -/
def finishTo (limits : Limits) (p : ImgDict) (bpc nc : Nat) (cv : Conv) (n : Norm)
    (data : ByteArray) (tw th : Nat) : Except Error Pixmap :=
  if !validBpc bpc then .error (.malformed 0 "image: invalid /BitsPerComponent")
  else if nc = 0 ∨ maxComps < nc then .ok placeholder
  else
    let tw := min p.w (max 1 tw)
    let th := min p.h (max 1 th)
    if limits.maxDecodedStreamBytes < 4 * tw * th then .error (.limitExceeded .decodedStreamBytes)
    else .ok (fused (Src.ofPlan p bpc nc cv n data) none none p.w p.h tw th)

/-- Decode with a known plan at full size (`finishTo … w h`). -/
def finish (limits : Limits) (p : ImgDict) (bpc nc : Nat) (cv : Conv) (n : Norm)
    (data : ByteArray) : Except Error Pixmap :=
  finishTo limits p bpc nc cv n data p.w p.h

/-- A pixmap from `finishTo` is the placeholder or has the clamped target dimensions. -/
theorem finishTo_dims {limits : Limits} {p : ImgDict} {bpc nc : Nat} {cv : Conv} {n : Norm}
    {data : ByteArray} {tw th : Nat} {pm : Pixmap}
    (h : finishTo limits p bpc nc cv n data tw th = .ok pm) :
    pm.w * pm.h = 1 ∨ (pm.w = min p.w (max 1 tw) ∧ pm.h = min p.h (max 1 th)) := by
  unfold finishTo at h
  by_cases h1 : (!validBpc bpc) = true
  · simp [h1] at h
  · by_cases h2 : nc = 0 ∨ maxComps < nc
    · simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] at h
      cases h; exact .inl rfl
    · by_cases h3 : limits.maxDecodedStreamBytes < 4 * min p.w (max 1 tw) * min p.h (max 1 th)
      · simp [h1, h2, h3] at h
      · simp only [h1, h2, h3, ite_false, Bool.false_eq_true] at h
        cases h; unfold fused; split <;> exact .inr ⟨rfl, rfl⟩

/-- A pixmap from `finish` is the placeholder or has the image's dimensions. -/
theorem finish_dims {limits : Limits} {p : ImgDict} {bpc nc : Nat} {cv : Conv} {n : Norm}
    {data : ByteArray} {pm : Pixmap} (h : finish limits p bpc nc cv n data = .ok pm) :
    pm.w * pm.h = 1 ∨ (pm.w = p.w ∧ pm.h = p.h) := by
  rcases finishTo_dims h with e | ⟨e1, e2⟩
  · exact .inl e
  · exact .inr ⟨by rw [e1]; omega, by rw [e2]; omega⟩

/-- The `Src` of an image (`decodePixmap`'s checks and plan): errors for empty or oversized
dimensions and invalid `/BitsPerComponent`; the grey placeholder for an undrawable colour space
or component count. -/
def srcOf (limits : Limits) (p : ImgDict) (info : Option CSInfo) (data : ByteArray) :
    Except Error Src :=
  if p.w = 0 ∨ p.h = 0 then .error (.malformed 0 "image: empty /Width or /Height")
  else if limits.maxImagePixels < p.w * p.h then .error (.limitExceeded .imagePixels)
  else
    let plan : Option (Nat × Nat × Conv × Norm) :=
      if p.mask then some (1, 1, .stencil, .unit)
      else match p.bpc, info.bind planOf with
        | some b, some (nc, cv, n) => some (b, nc, cv, n)
        | _, _ => none
    match plan with
    | none => .ok Src.grey
    | some (b, nc, cv, n) =>
      if !validBpc b then .error (.malformed 0 "image: invalid /BitsPerComponent")
      else if nc = 0 ∨ maxComps < nc then .ok Src.grey
      else .ok (Src.ofPlan p b nc cv n data)

/-- The size of an image's decoded data, `h · ⌈w · nc · bpc / 8⌉` bytes (`nc`, `bpc` as
`srcOf` reads them); `0` when they are unknown. -/
def dataSize (p : ImgDict) (info : Option CSInfo) : Nat :=
  let plan : Option (Nat × Nat) :=
    if p.mask then some (1, 1)
    else match p.bpc, info.bind planOf with
      | some b, some (nc, _, _) => some (b, nc)
      | _, _ => none
  match plan with
  | some (b, nc) => p.h * ((p.w * nc * b + 7) / 8)
  | none => 0

/-- A stream dictionary with `/DL n` (ISO 32000-2 Table 5: the decoded length, a hint) in place
of any `/DL` it has; unchanged for `n = 0`. Task 8.10: an image's data is decoded with its
`dataSize` as `/DL`, so `Filter.decodeStream` reserves the filter output once instead of
growing it by doubling (`Filter.declaredLength`; the decoded bytes do not depend on it,
`Filter.applyStages_cap`). -/
def withDL (d : Dict) (n : Nat) : Dict :=
  if n = 0 then d
  else (Name.ofString "DL", .int n) :: d.filter (·.1 != Name.ofString "DL")

/-- **Decode an image** from its parameters, resolved colour space (`none`: missing or not
understood) and decoded data. `tgt` (task 8.6): the drawn-size target of its largest use
(`imageExtents`, `inlineExt`): the pixmap is box-filtered to it while decoding (what the
placement would do after). The RGBA pixmap is capped by `maxDecodedStreamBytes` (4 bytes per
pixel): over it, a halved size that fits (`fitTarget`) instead of failing. Errors: empty or
oversized dimensions (`limitExceeded .imagePixels`: the source pixels bound the work), an
invalid `/BitsPerComponent`. An undrawable colour space yields the placeholder. -/
def decodePixmap (limits : Limits) (p : ImgDict) (info : Option CSInfo) (data : ByteArray)
    (tgt : Option (Nat × Nat) := none) : Except Error Pixmap :=
  if p.w = 0 ∨ p.h = 0 then .error (.malformed 0 "image: empty /Width or /Height")
  else if limits.maxImagePixels < p.w * p.h then .error (.limitExceeded .imagePixels)
  else
    let t := fitTarget limits.maxDecodedStreamBytes p.w p.h tgt
    if p.mask then finishTo limits p 1 1 .stencil .unit data t.1 t.2
    else
      match p.bpc, info.bind planOf with
      | some b, some (nc, cv, n) => finishTo limits p b nc cv n data t.1 t.2
      | _, _ => .ok placeholder

/-- A successfully decoded image is within `Limits.maxImagePixels` (or is the 1-pixel
placeholder). -/
theorem decodePixmap_pixels {limits : Limits} {p : ImgDict} {info : Option CSInfo}
    {data : ByteArray} {tgt : Option (Nat × Nat)} {pm : Pixmap}
    (h : decodePixmap limits p info data tgt = .ok pm) :
    pm.w * pm.h ≤ limits.maxImagePixels ∨ pm.w * pm.h = 1 := by
  unfold decodePixmap at h
  by_cases h1 : p.w = 0 ∨ p.h = 0
  · simp [h1] at h
  · by_cases h2 : limits.maxImagePixels < p.w * p.h
    · simp [h1, h2] at h
    · have hle : p.w * p.h ≤ limits.maxImagePixels := by omega
      have fin : ∀ b nc cv n tw th, finishTo limits p b nc cv n data tw th = .ok pm →
          pm.w * pm.h ≤ limits.maxImagePixels ∨ pm.w * pm.h = 1 := by
        intro b nc cv n tw th hf
        rcases finishTo_dims hf with e | ⟨e1, e2⟩
        · exact .inr e
        · rw [e1, e2]
          exact .inl (Nat.le_trans (Nat.mul_le_mul (Nat.min_le_left _ _) (Nat.min_le_left _ _)) hle)
      simp only [h1, h2, ite_false] at h
      split at h
      · exact fin _ _ _ _ _ _ h
      · split at h
        · exact fin _ _ _ _ _ _ h
        · cases h; exact .inr rfl

/-- Does the filter chain of `d` reach an image codec (DCT, JPX, JBIG2, CCITT)? -/
def hasCodec (limits : Limits) (d : Dict) : Bool :=
  match Filter.parseChain limits d with
  | .ok stages => stages.any fun st => match st.kind with
    | .image _ => true
    | .byte _ => false
  | .error _ => false

/-! ### `/DCTDecode` through the quarantine-zone decoder (task 7.6a) -/

/-- A `/Filter` chain ending in the image codec `c` after byte filters only: the stream
dictionary with that last stage removed from `/Filter` and `/DecodeParms` (a single filter:
both keys removed), and the codec stage's parameters. `none` for any other chain. -/
def codecSplit (c : Filter.ImageCodec) (limits : Limits) (d : Dict) : Option (Dict × Dict) :=
  match Filter.parseChain limits d with
  | .ok stages =>
    match stages.reverse with
    | ⟨.image c', parms⟩ :: pre =>
      if c' = c ∧ pre.all (fun st => match st.kind with | .byte _ => true | .image _ => false) then
        some (d.filterMap fun kv =>
          if kv.1 = Content.Run.nm "Filter" ∨ kv.1 = Content.Run.nm "DecodeParms" then
            match kv.2 with
            | .array xs => if xs.length ≤ 1 then none else some (kv.1, .array xs.dropLast)
            | _ => none
          else some kv, parms)
      else none
    | _ => none
  | .error _ => none

/-- `codecSplit` for `/DCTDecode`. -/
def dctSplit (limits : Limits) (d : Dict) : Option (Dict × Dict) := codecSplit .dct limits d

/-- `codecSplit` for `/CCITTFaxDecode`. -/
def ccittSplit (limits : Limits) (d : Dict) : Option (Dict × Dict) := codecSplit .ccitt limits d

/-- `/ColorTransform` of the DCT parameters (`none` when absent or not an integer). -/
def colorTransformOf (parms : Dict) : Option Int :=
  match Dict.get? parms (Content.Run.nm "ColorTransform") with
  | some (.int i) => some i
  | _ => none

/-- The device colour space of a JPEG by its component count (for a missing `/ColorSpace`). -/
def jpegSpace (nc : Nat) : Option CSInfo :=
  if nc = 1 then some (.dev .gray (.gray Comp.zero))
  else if nc = 3 then some (.dev .rgb (.gray Comp.zero))
  else if nc = 4 then some (.dev .cmyk (.gray Comp.zero))
  else none

/-- **The pixmap of a `Src`** (no mask) at the drawn-size target `tgt` (`fitTarget`: clamped,
halved to fit `maxDecodedStreamBytes`). -/
def Src.pixmap (limits : Limits) (s : Src) (tgt : Option (Nat × Nat) := none) :
    Except Error Pixmap :=
  let t := fitTarget limits.maxDecodedStreamBytes s.w s.h tgt
  if limits.maxDecodedStreamBytes < 4 * t.1 * t.2 then .error (.limitExceeded .decodedStreamBytes)
  else .ok (fused s none none s.w s.h t.1 t.2)

/-- **Decode DCT data and re-validate it against the image dictionary** (as a `Src`): the
JPEG's components must match the colour space (`info`, else `jpegSpace`); the samples become an
8-bit raster of the dictionary's dimensions (`srcOf`: `/Decode`, colour-key masking, limits).
Errors: the decoder's, a component mismatch, a stencil mask. `scale` (0–3, task 7.10) is a
reduced-size decode by `2^scale` (MuPDF's JPEG `l2factor`): the raster is then the reduced
dictionary (`ImgDict.reduce`). **Over a limit** (task 8.6: the planes, a progressive frame's
coefficients or the output above `maxDecodedStreamBytes`, all checked at the frame header) the
decode is retried at the next reduced scale, up to 1/8 (at most three retries), instead of
failing. -/
def dctSrc (limits : Limits) (p : ImgDict) (info : Option CSInfo) (parms : Dict)
    (jpeg : ByteArray) (scale : Nat := 0) : Except Error Src :=
  if p.mask then .error (.unsupported "DCT-encoded stencil mask") else go 4 scale
where
  /-- One attempt at `scale`, then (over a limit) at most `fuel − 1` more at larger scales. -/
  go : Nat → Nat → Except Error Src
    | 0, _ => .error (.limitExceeded .decodedStreamBytes)
    | fuel + 1, scale =>
      match Quarantine.DCT.decode limits (colorTransformOf parms) jpeg scale with
      | .error (.limitExceeded .decodedStreamBytes) =>
        if scale < 3 then go fuel (scale + 1) else .error (.limitExceeded .decodedStreamBytes)
      | .error e => .error e
      | .ok img =>
        let info := match info with
          | some i => some i
          | none => jpegSpace img.nc
        let p := if scale = 0 then p else p.reduce scale
        match info.bind planOf with
        | some (nc, _, _) =>
          if nc = img.nc then srcOf limits { p with bpc := some 8 } info img.data
          else .error (.malformed 0 s!"DCT: {img.nc} components for a {nc}-component colour space")
        | none => .error (.unsupported "DCT image without a drawable colour space")

/-- **Decode DCT data** to a pixmap (`dctSrc`, then `Src.pixmap` at the drawn-size target
`tgt`, task 8.6). -/
def decodeDCT (limits : Limits) (p : ImgDict) (info : Option CSInfo) (parms : Dict)
    (jpeg : ByteArray) (scale : Nat := 0) (tgt : Option (Nat × Nat) := none) :
    Except Error Pixmap :=
  (dctSrc limits p info parms jpeg scale).bind (·.pixmap limits tgt)

/-- `decodeDCT`, with every error drawn as the placeholder (S7). -/
def decodeDCTOr (limits : Limits) (p : ImgDict) (info : Option CSInfo) (parms : Dict)
    (jpeg : ByteArray) (scale : Nat := 0) (tgt : Option (Nat × Nat) := none) : Pixmap :=
  match decodeDCT limits p info parms jpeg scale tgt with
  | .ok pm => pm
  | .error _ => placeholder

/-! ### `/CCITTFaxDecode` through the quarantine-zone decoder (task 7.8) -/

/-- Resolve every value of a dictionary one level through the source. -/
def resolveDict {σ : Type} (src : Source σ) (s : σ) (d : Dict) : Dict × σ :=
  let (acc, s) := d.foldl (fun (acc : Dict × σ) kv =>
    let (o, s) := Content.Run.resolve src acc.2 kv.2
    ((kv.1, o) :: acc.1, s)) ([], s)
  (acc.reverse, s)

/-- The `/CCITTFaxDecode` parameters of a `/DecodeParms` dictionary with MuPDF's defaults
(`pdf_dict_get_int_default`/`_bool_default`: a value of the wrong type is the default; a real
is truncated toward zero). -/
def ccittParams (parms : Dict) : Quarantine.CCITT.Params :=
  let int (k : String) (dflt : Int) : Int :=
    match Dict.get? parms (Content.Run.nm k) with
    | some (.int i) => i
    | some (.real r) => r.mantissa.tdiv (10 ^ r.scale)
    | _ => dflt
  let bool (k : String) (dflt : Bool) : Bool :=
    match Dict.get? parms (Content.Run.nm k) with
    | some (.bool b) => b
    | _ => dflt
  { k := int "K" 0, endOfLine := bool "EndOfLine" false,
    byteAlign := bool "EncodedByteAlign" false,
    columns := (int "Columns" 1728).toNat, rows := (int "Rows" 0).toNat,
    endOfBlock := bool "EndOfBlock" true, blackIs1 := bool "BlackIs1" false }

/-- **Decode CCITT fax data and read it as the image's samples** (as a `Src`): at most
`/Height` rows (`Quarantine.CCITT.decode`), then `srcOf` (dimensions, `/Decode`, stencil
masks, limits). A negative `/Columns` (MuPDF: an error) is an error. -/
def ccittSrc (limits : Limits) (p : ImgDict) (info : Option CSInfo) (parms : Dict)
    (fax : ByteArray) : Except Error Src :=
  match Dict.get? parms (Content.Run.nm "Columns") with
  | some (.int i) => if i < 0 then .error (.malformed 0 "CCITTFax: negative /Columns") else go
  | _ => go
where
  /-- The decoding proper. -/
  go : Except Error Src :=
    match Quarantine.CCITT.decode limits (ccittParams parms) p.h fax with
    | .ok rows => srcOf limits p info rows
    | .error e => .error e

/-- **Decode CCITT fax data** to a pixmap (`ccittSrc`, then `Src.pixmap` at the drawn-size
target `tgt`, task 8.6). -/
def decodeCCITT (limits : Limits) (p : ImgDict) (info : Option CSInfo) (parms : Dict)
    (fax : ByteArray) (tgt : Option (Nat × Nat) := none) : Except Error Pixmap :=
  (ccittSrc limits p info parms fax).bind (·.pixmap limits tgt)

/-- `decodeCCITT`, with every error drawn as the placeholder (S7). -/
def decodeCCITTOr (limits : Limits) (p : ImgDict) (info : Option CSInfo) (parms : Dict)
    (fax : ByteArray) (tgt : Option (Nat × Nat) := none) : Pixmap :=
  match decodeCCITT limits p info parms fax tgt with
  | .ok pm => pm
  | .error _ => placeholder

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

/-! ### Reduced-size decoding of downscaled JPEGs (task 7.10) -/

/-- **MuPDF's `l2factor`** (`fz_get_pixmap_from_image`) for an `iw × ih` image drawn with
device extents `w = ⌊√qw⌋`, `h = ⌊√qh⌋` (`qw = a² + b²`, `qh = c² + d²` of the image's device
matrix; MuPDF truncates `sqrtf` to an integer): the largest `l ≤ 6` with
`iw >> l ≥ w + 2` and `ih >> l ≥ h + 2`, and 0 when `w` or `h` is 0. In exact arithmetic:
`iw >> l ≥ ⌊√qw⌋ + 2` ⟺ `iw >> l ≥ 2 ∧ qw < (iw >> l − 1)²`. -/
def l2Factor (iw ih : Nat) (qw qh : Rat) : Nat :=
  if qw < 1 ∨ qh < 1 then 0 else go 6 0
where
  /-- At most `fuel` more steps from factor `l`. -/
  go : Nat → Nat → Nat
    | 0, l => l
    | fuel + 1, l =>
      let kw := iw >>> (l + 1)
      let kh := ih >>> (l + 1)
      if 2 ≤ kw ∧ 2 ≤ kh ∧ qw < (((kw - 1) ^ 2 : Nat) : Rat) ∧ qh < (((kh - 1) ^ 2 : Nat) : Rat)
      then go fuel (l + 1) else l

/-- **The JPEG reduction actually used** for MuPDF's `l2factor` `l`: `min 3 (l − 1)` (0 for
`l = 0`). MuPDF decodes at `1 / 2^(min 3 l)` and then filters the rest of the way with a tent
filter; our placement downscales with an area-averaging box filter (the documented
approximation), which smooths too little when an image has fewer than two samples per device
pixel (noise-like images, e.g. sky maps, then differ visibly). One step less keeps at least
two samples per pixel for the box filter while still bounding the decode (an image drawn at
1/16 or less decodes at 1/8). Measured on the corpus: with `min 3 l`, 15 of 21 changed pages
got slightly worse (`arxiv-1105.2345` p8 0.78% → 1.08%); see `docs/raster.md`. -/
def dctScale (l : Nat) : Nat := min 3 (l - 1)

/-- **How an image is drawn on a page** (tasks 7.10, 8.6), over all its uses: the largest
squared device extents `q = (a² + b², c² + d²)` of its device matrices (MuPDF's `l2factor`, for
JPEG reduced-size decoding) and the largest placement targets `t = (⌈√…⌉, ⌈√…⌉)` of the
grid-fitted device matrices (the sizes `place` box-filters the image to, `targetSide`). -/
structure Extent where
  /-- Largest squared extents along the image's x and y axes. -/
  q : Rat × Rat
  /-- Largest placement targets (device pixels, before clamping to the image size). -/
  t : Nat × Nat
  deriving Repr, BEq

/-- The extent of one use with device matrix `dev` (image space → device). -/
def Extent.ofDev (dev : Aff) : Extent :=
  let g := gridfit dev
  { q := (dev.a * dev.a + dev.b * dev.b, dev.c * dev.c + dev.d * dev.d),
    t := (ceilSqrt (g.a * g.a + g.b * g.b), ceilSqrt (g.c * g.c + g.d * g.d)) }

/-- The extent serving two uses: componentwise maxima. -/
def Extent.max (a b : Extent) : Extent :=
  { q := (Max.max a.q.1 b.q.1, Max.max a.q.2 b.q.2), t := (Max.max a.t.1 b.t.1, Max.max a.t.2 b.t.2) }

/-- **The JPEG reduction** of an `iw × ih` image drawn with extent `e` (`none`: unknown, full
size): `dctScale (l2Factor …)` (task 7.10). -/
def scaleFor (iw ih : Nat) : Option Extent → Nat
  | some e => dctScale (l2Factor iw ih e.q.1 e.q.2)
  | none => 0

/-- `DeviceGray`, the colour space of soft-mask images. -/
def grayInfo : CSInfo := .dev .gray (.gray Comp.zero)

/-! ### JPEG 2000 image dictionaries (decoder integration plan §9, M10.2b) -/

/-- Document budget access for image codecs. Standalone raster callers use their supplied
limits. The confined render supplies the current Filter.Budget after each prefix and mask. -/
structure CodecBudget (σ : Type) where
  /-- Decoded bytes still available, capped by the supplied document limit. -/
  remaining : σ → Nat → Nat := fun _ n => n
  /-- Charge a completed codec or pixmap output. -/
  spend : σ → Nat → σ := fun s _ => s

/-- Use the document's live filter budget for codec and rendering output. -/
def CodecBudget.document : CodecBudget Filter.Budget :=
  ⟨fun b n => min b.remaining n, fun b n => ⟨b.remaining - n⟩⟩

private def CodecBudget.limits {σ : Type} (b : CodecBudget σ) (s : σ) (l : Limits) : Limits :=
  { l with maxDecodedTotalBytes := b.remaining s l.maxDecodedTotalBytes }

/-- PDF entries used specifically by the JPX filter. -/
private structure JPXDict where
  mode : Nat := 0
  matte : Option (List Fixed) := none
  key : List (Int × Int) := []
  tint : Option Shading.ShadeCS := none

/-- Match the tint and alternate component counts, including every single-input
subfunction of a stitching function, before evaluating the function per pixel. -/
private def tintArity : Nat → Nat → Nat → Shading.Fn → Bool
  | 0, _, _, _ => false
  | depth + 1, inputs, outputs, f =>
    match f with
    | .ps domain range _ | .sampled domain range .. =>
      domain.length == inputs && range.length == outputs
    | .exp _ range c0 _ _ =>
      inputs == 1 && c0.length == outputs && range.all (fun r => r.length == outputs)
    | .stitch _ range fns _ _ =>
      inputs == 1 && range.all (fun r => r.length == outputs) &&
        fns.all (tintArity depth 1 outputs)
    | .arr _ => false

/-- Recover the original function object while the document source can still decode its
stream. A named space may live in an indirect page resource dictionary. An unavailable
transform retains the ordinary image conversion. -/
private def imageTint {σ : Type} (src : Source σ) (s : σ) (resources : Dict)
    (space : Option PdfObject) (info : Option CSInfo) : Option Shading.ShadeCS × σ := Id.run do
  let some i := info | return (none, s)
  let n := match i with
    | .deviceN n _ => n
    | .separation .. => 1
    | _ => 0
  unless 0 < n && n ≤ maxComps do return (none, s)
  let (space, s) := match space with
    | some (.name name) => Content.Run.resEntry src s resources "ColorSpace" name
    | o => (o, s)
  let some o := space | return (none, s)
  let (raw, s) := Content.Run.resolve src s o
  let .array (_ :: _ :: alternate :: transform :: _) := raw | return (none, s)
  let (alternate, s) := Content.Run.baseDevice src s alternate
  let some alt := alternate | return (none, s)
  let (f, s) := Shading.loadFn src s transform
  let some f := f | return (none, s)
  unless tintArity (Shading.maxFnDepth + 1) n alt.nComps f do return (none, s)
  return (some { info := i, n, tint := some (f, alt) }, s)

private def nativeRanges : List PdfObject → Option (List (Int × Int))
  | [] => some []
  | .int lo :: .int hi :: rest => ((lo, hi) :: ·) <$> nativeRanges rest
  | _ => none

private def jpxDict {σ : Type} (src : Source σ) (s : σ) (d resources : Dict)
    (space : Option PdfObject) (info : Option CSInfo) : JPXDict × σ :=
  let (mode, s) := entry src s d "SMaskInData"
  let (mt, s) := arrayEntry src s d "Matte"
  let (key, s) := arrayEntry src s d "Mask"
  let (tint, s) := imageTint src s resources space info
  ({ tint, mode := if mode.isNone then 0 else (natOf mode).getD 3,
     matte := mt.bind (·.mapM Content.Interp.num?), key := (key.bind nativeRanges).getD [] }, s)

/-- Restricted ICC profiles use the ordinary PDF device alternate for their input signature.
Other signatures and enumerations have no colour transform in this renderer. Raw codestreams
without a colour declaration use the conventional 1/3/4 component fallback. -/
private def embeddedSpace (i : Quarantine.JPX.Image) : Option CSInfo :=
  match i.space with
  | some .sRGB => jpegSpace 3
  | some .greyscale => jpegSpace 1
  | some (.enumerated 12 _) => jpegSpace 4
  | some (.icc _) => do
    let profile ← i.iccProfile
    let sig := profile.extract 16 20
    if sig == "RGB ".toUTF8 then jpegSpace 3
    else if sig == "GRAY".toUTF8 then jpegSpace 1
    else if sig == "CMYK".toUTF8 then jpegSpace 4
    else jpegSpace i.nc
  | _ => jpegSpace i.nc

private structure JPXSource where
  img : Src
  mask : Option Src
  norm : Norm
  charge : Nat

/-- Remove preblending before converting from the source colour space (especially CMYK).
Opacity is applied once, later, in the common row compositor. -/
private def unblend (img : Src) (n : Norm) (mask : Src) (matte : List Fixed) : Src := Id.run do
  let bg := (List.range img.nc).map fun j =>
    let (lo, scale) := n.scaling j
    (clampByte (roundRat ((Fixed.toRat (matte.getD j Fixed.zero) - lo) * scale))).toNat
  let bg := bg.toArray
  let mut data := img.data
  for y in [0:img.h] do
    let row := mask.row img.w (y * mask.h / img.h)
    for x in [0:img.w] do
      let a := rd row (4 * x)
      if 0 < a && a < 255 then
        for c in [0:img.nc] do
          let i := (y * img.w + x) * img.nc + c
          data := Clip.setB data i (unmatteC (rd data i) (bg[c]?.getD 0) a)
  return { img with data }

private def jpxSource (l : Limits) (p : ImgDict) (j : JPXDict) (info : Option CSInfo)
    (bytes : ByteArray) (ext : Option Extent) (soft := false) : Except Error JPXSource := do
  let plan := info.bind fun cs =>
    if maxComps < Shading.csComps cs then none else
    match j.tint with
    | some resolved => some (resolved.n, Conv.tint resolved, Norm.unit)
    | none => planOf cs
  let colour ← if p.mask then pure .stencil else if soft then pure .mask else
    match info with
    | some (.indexed ..) => pure .indexed
    | some _ => match plan with
      | some (nc, _, _) => pure (.pdf nc)
      | none => throw (.unsupported "JPX: PDF colour space")
    | none => if p.cs.isNone then pure .embedded else throw (.unsupported "JPX: unresolved PDF colour space")
  -- Combine categorical samples and opacity on their source grid before the row box
  -- filter. For continuous colour retain one level of detail for its area average.
  let reduce := if p.mask || colour == .indexed || !j.key.isEmpty || j.mode != 0 then 0
    else ext.elim 0 fun e => l2Factor p.w p.h e.q.1 e.q.2 - 1
  let renderSpace : Quarantine.JPX.RenderSpace := match info with
    | some (.deviceN ..) => .deviceN
    | some (.dev ..) => .device
    | _ => .other
  let i ← Quarantine.JPX.decode l p.w p.h bytes
    { colour, smaskInData := if p.mask || soft then 0 else j.mode, reduce, fit := true,
      key := if j.mode == 0 then j.key else [],
      renderSpace := some renderSpace }
  let p := { p with w := i.w, h := i.h, key := none, decode := if p.mask then p.decode else none }
  let (nc, cv, n) ← if p.mask then pure (1, Conv.stencil, Norm.unit) else
    match plan <|> (embeddedSpace i).bind planOf with
    | some plan => pure plan
    | none => throw (.unsupported "JPX: embedded colour space or ICC profile")
  unless nc == i.nc do throw (.malformed 0 "JPX: colour component count")
  let img := Src.ofPlan p 8 nc cv n i.data
  let coverage := (i.alpha.map (·.data)) <|> i.keyMask
  let mask := coverage.map (Src.ofPlan { p with mask := false, decode := none } 8 1 .gray .unit)
  let img := match i.alpha, mask with
    | some a, some m => if a.premultiplied then unblend img n m (j.matte.getD []) else img
    | _, _ => img
  return { img, mask, norm := n, charge := i.data.size + (coverage.map (·.size)).getD 0 +
    (i.iccProfile.map (·.size)).getD 0 }

private def jpxPrefix {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (d : Dict) :
    Option Dict × σ := Id.run do
  let (filter, s) := resolvedEntry src s d "Filter"
  let codec := PdfObject.name (Content.Run.nm "JPXDecode")
  let terminal := match filter with
    | some (.array xs) => xs.getLast? == some codec
    | _ => filter == some codec
  unless terminal do return (none, s)
  let (parms, s) := resolvedEntry src s d "DecodeParms"
  let dict := d.map fun (k, v) =>
    if k == Content.Run.nm "Filter" then (k, filter.getD v)
    else if k == Content.Run.nm "DecodeParms" then (k, parms.getD v)
    else (k, v)
  return ((codecSplit .jpx limits dict).map (·.1), s)

/-- **Load a mask image** (`/SMask` when `soft`, else a `/Mask` stream) from its reference, as
a `Src` (task 8.6: converted row by row with its image) — decoded through the source like an
image XObject: a soft mask as `DeviceGray` with its own `/Decode` (the mask value is channel 0;
`/BitsPerComponent` required), an explicit mask as an `/ImageMask` stencil (`/Decode`
honoured, coverage in channel 3: sample 0 paints) — plus a soft mask's `/Matte` components; a
`/DCTDecode` mask goes through `dctSrc` (full size, as before). `none` for anything else (not a
stream, another image codec, a decode error): the image is then drawn unmasked. -/
private def loadMaskB {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (soft : Bool)
    (ref : Option PdfObject) (ext : Option Extent := none) (budget : CodecBudget σ := {}) :
    Except Error (Option (Src × Option (List Fixed))) × σ := Id.run do
  let some (.ref n g) := ref | return (.ok none, s)
  let (body, s) := src.fetch s n g
  let .ok (.stream st) := body | return (.ok none, s)
  let (jpx, s) := jpxPrefix limits src s st.dict
  let dct := dctSplit limits st.dict
  if hasCodec limits st.dict && dct.isNone && jpx.isNone then return (.ok none, s)
  let (p, s) := imgDictOf src s st.dict
  let (mt, s) := arrayEntry src s st.dict "Matte"
  let matte := if soft then mt.bind (·.mapM Content.Interp.num?) else none
  if soft && p.bpc.isNone && jpx.isNone then return (.ok none, s)
  let p := { p with mask := !soft, key := none }
  let d := (jpx <|> dct.map (·.1)).getD (withDL st.dict (dataSize p (some grayInfo)))
  let (r, s) := src.decode s n { st with dict := d }
  if jpx.isSome then
    match r.bind (fun bytes => jpxSource (budget.limits s limits) p {} (some grayInfo) bytes ext soft) with
    | .ok i => return (.ok (some (i.img, matte)), budget.spend s i.charge)
    | .error (.limitExceeded k) => return (.error (.limitExceeded k), s)
    | .error _ => return (.ok none, s)
  let r := r.bind fun bytes => match dct with
    | some (_, parms) => dctSrc limits p (some grayInfo) parms bytes
    | none => srcOf limits p (some grayInfo) bytes
  return (.ok (r.toOption.map fun m => (m, matte)), s)

/-- Read an external mask through a standalone source. The document path also propagates
JPX quota failures and charges the mask to its live budget. -/
def loadMask {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (soft : Bool)
    (ref : Option PdfObject) : Option (Src × Option (List Fixed)) × σ :=
  let (r, s) := loadMaskB limits src s soft ref
  (r.toOption.join, s)

/-- **Device extents of the image XObjects of a page**: for each `(num, gen)` drawn in
`items` (page content and annotations, inside soft masks too, `depth` levels) the `Extent`
serving all its uses (through `view`, the page → device matrix the items are rendered with;
the reductions are monotone in it). Images also drawn in `fixed` (tiling cells, Type 3 glyphs,
whose matrices are not page matrices) are left out, i.e. decoded at full size. -/
def imageExtents (depth : Nat) (view : Aff) (items fixed : DisplayList) :
    List ((Nat × Nat) × Extent) :=
  let used := Content.DisplayList.foldDeep (fun (acc : List ((Nat × Nat) × Extent)) it =>
    match it with
    | .image (.xobject _ n g) ctm _ _ =>
      let e := Extent.ofDev (Aff.ofMatrix ctm * view)
      match acc.find? (·.1 == (n, g)) with
      | some (_, e0) => acc.map fun x => if x.1 == (n, g) then (x.1, e0.max e) else x
      | none => ((n, g), e) :: acc
    | _ => acc) depth [] items
  let excl := Content.DisplayList.foldDeep (fun (acc : List (Nat × Nat)) it =>
    match it with
    | .image (.xobject _ n g) _ _ _ => (n, g) :: acc
    | _ => acc) depth [] fixed
  used.filter fun e => !excl.contains e.1

/-- **The pixmap of an image `Src` with its mask**: on the grid of both (`gridOf`, at most
`maxDecodedStreamBytes / 4` pixels), box-filtered to the drawn-size target (`fitTarget`), the
mask's channel `ch` multiplying the alpha, `/Matte` un-premultiplied (`fused`). A stencil image
is unmasked. -/
def maskedPixmap (limits : Limits) (img : Src) (mk : Option (Src × Nat))
    (matte : Option (Nat × Nat × Nat)) (tgt : Option (Nat × Nat)) : Except Error Pixmap :=
  let mk := if img.stencil then none else mk
  let matte := if mk.isSome then matte else none
  let g := gridOf (limits.maxDecodedStreamBytes / 4) img mk
  let t := fitTarget limits.maxDecodedStreamBytes g.1 g.2 tgt
  if limits.maxDecodedStreamBytes < 4 * t.1 * t.2 then .error (.limitExceeded .decodedStreamBytes)
  else .ok (fused img mk matte g.1 g.2 t.1 t.2)

private def jpxPixmap (l : Limits) (i : JPXSource) (mask : Option (Src × Nat))
    (matte : Option (List Fixed)) (ext : Option Extent) : Except Error Pixmap :=
  let img := match mask, matte with
    | some (m, 0), some ms => unblend i.img i.norm m ms
    | _, _ => i.img
  let mk := (i.mask.map fun m => (m, 0)) <|> mask
  (maskedPixmap (Filter.capped l l.maxDecodedTotalBytes) img mk none (ext.map (·.t))).mapError
    (Filter.budgetErr l l.maxDecodedTotalBytes)

/-- The codec output and RGBA result are separately bounded and charged. -/
private def renderJPX {σ : Type} (limits : Limits) (budget : CodecBudget σ) (s : σ)
    (p : ImgDict) (j : JPXDict) (info : Option CSInfo) (bytes : ByteArray)
    (mask : Option (Src × Nat)) (matte : Option (List Fixed)) (ext : Option Extent) :
    Except Error Pixmap × σ :=
  match jpxSource (budget.limits s limits) p j info bytes ext with
  | .error e => (.error e, s)
  | .ok i =>
    let s := budget.spend s i.charge
    let l := budget.limits s { limits with maxDecodedTotalBytes := limits.maxDecodedTotalBytes - i.charge }
    match jpxPixmap l i mask matte ext with
    | .ok pm => (.ok pm, budget.spend s pm.data.size)
    | .error e => (.error e, s)

private def loadXObjectIn {σ : Type} (limits : Limits) (src : Source σ) (s : σ)
    (named : List (Name × CSInfo)) (resources : Dict) (num gen : Nat) (ext : Option Extent)
    (budget : CodecBudget σ) : Except Error Pixmap × σ :=
  match src.fetch s num gen with
  | (.ok (.stream st), s) =>
    let (p, s) := imgDictOf src s st.dict
    let (jpx, s) := jpxPrefix limits src s st.dict
    let (info, s) := if jpx.isSome && p.mask then (none, s) else csOf src s named p.cs
    let (j, s) := if jpx.isSome then jpxDict src s st.dict resources p.cs info else ({}, s)
    let embedded := jpx.isSome && j.mode != 0
    let (sm, s) := if p.mask || embedded then (.ok none, s)
      else loadMaskB limits src s true (Dict.get? st.dict (Content.Run.nm "SMask")) ext budget
    match sm with
    | .error e => (.error e, s)
    | .ok sm =>
    let (mk, s) := if p.mask || embedded || sm.isSome then (.ok none, s)
      else loadMaskB limits src s false (Dict.get? st.dict (Content.Run.nm "Mask")) ext budget
    match mk with
    | .error e => (.error e, s)
    | .ok mk =>
    let p := if sm.isSome then { p with key := none } else p
    let mask : Option (Src × Nat) := match sm, mk with
      | some (m, _), _ => some (m, 0)
      | none, some (m, _) => some (m, 3)
      | none, none => none
    if let some d := jpx then
      match src.decode s num { st with dict := d } with
      | (.ok bytes, s) =>
        let j := if p.mask || embedded || mask.isSome then { j with key := [] } else j
        renderJPX limits budget s p j info bytes mask (sm.bind (·.2)) ext
      | (.error e, s) => (.error e, s)
    else
    let matte : Option (Nat × Nat × Nat) := match sm, info with
      | some (_, some ms), some i => some (Clip.deviceRGB (i.color ms))
      | _, _ => none
    let tgt := ext.map (·.t)
    let fin := fun (img : Src) => maskedPixmap limits img mask matte tgt
    let orGrey := fun (r : Except Error Src) => match r with
      | .ok i => i
      | .error _ => Src.grey
    match dctSplit limits st.dict with
    | some (d', parms) =>
      let hasMatte := match sm with
        | some (_, some _) => true
        | _ => false
      let k := if hasMatte then 0 else scaleFor p.w p.h ext
      match src.decode s num { st with dict := d' } with
      | (.ok bytes, s) => (fin (orGrey (dctSrc limits p info parms bytes k)), s)
      | (.error e, s) => (.error e, s)
    | none =>
    match ccittSplit limits st.dict with
    | some (d', parms) =>
      let (parms, s) := resolveDict src s parms
      match src.decode s num { st with dict := d' } with
      | (.ok bytes, s) => (fin (orGrey (ccittSrc limits p info parms bytes)), s)
      | (.error e, s) => (.error e, s)
    | none =>
    if hasCodec limits st.dict then (fin Src.grey, s) else
    match src.decode s num { st with dict := withDL st.dict (dataSize p info) } with
    | (.ok bytes, s) => ((srcOf limits p info bytes).bind fin, s)
    | (.error e, s) => (.error e, s)
  | (.ok (.obj _), s) => (.error (.malformed 0 "image XObject is not a stream"), s)
  | (.error e, s) => (.error e, s)

/-- **Decode an image XObject** `num gen` through the source (its filters, the session
budget); `/DCTDecode` through `dctSrc`, `/CCITTFaxDecode` through `ccittSrc` (their errors,
and unsupported image codecs, yield the grey placeholder), JPX through `renderJPX`, other data through `srcOf`. Its
`/SMask` (else its `/Mask` stream) is loaded (`loadMask`) and applied (`maskedPixmap`); a soft
mask disables colour-key masking (§8.9.6.4); `/Matte` un-premultiplies the colours (converted
through the image's colour space).
`ext` (tasks 7.10, 8.6): how the image is drawn on the page (`imageExtents`). A JPEG is decoded
at `1 / 2^k` of its size, `k = scaleFor …` (MuPDF's `l2factor`, one step less), except when its
soft mask has a `/Matte` (MuPDF decodes those at full size); then **every image** is converted
row by row and box-filtered to its placement target while decoding (`fused`), the pixels the
placement would have produced from the full pixmap. A decode over `maxDecodedStreamBytes` is
retried smaller (`dctSrc`, `fitTarget`). -/
def loadXObject {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (named : List (Name × CSInfo))
    (num gen : Nat) (ext : Option Extent := none) (budget : CodecBudget σ := {}) : Except Error Pixmap × σ :=
  loadXObjectIn limits src s named [] num gen ext budget

private def decodeInlineJPXB (src : Source Filter.Budget) (limits : Limits)
    (named : List (Name × CSInfo)) (params : Dict) (raw : ByteArray) (ext : Option Extent)
    (b : Filter.Budget) : Except Error Pixmap × Filter.Budget :=
  let (r, b) := Filter.decodeStreamB limits b params raw
  match r with
  | .ok (.image .jpx _ bytes) =>
    let (p, b) := imgDictOf src b params
    let (info, b) := if p.mask then (none, b) else csOf src b named p.cs
    let (j, b) := jpxDict src b params [] p.cs info
    renderJPX limits .document b p (if p.mask then { j with key := [] } else j) info bytes none none ext
  | .error e => (.error e, b)
  | _ => (.error (.malformed 0 "JPX: expected terminal codec"), b)

/-- **Decode an inline image** (`BI … ID … EI`): parameters already abbreviation-expanded
(5.2b), raw data decoded with `Filter.decodeStream` (bounded by
`Limits.maxDecodedStreamBytes`); named colour spaces from `named`. This standalone decoder
accepts self-contained parameters. The document loader resolves indirect JPX tint functions.
`ext` (task 8.6): how this use draws it (an inline image is drawn once,
`inlineExt`): a JPEG at its `scaleFor` reduction, every image box-filtered to its placement
target while decoding. -/
def decodeInline (limits : Limits) (named : List (Name × CSInfo)) (params : Dict)
    (raw : ByteArray) (ext : Option Extent := none) : Except Error Pixmap :=
  if (codecSplit .jpx limits params).isSome then
    (decodeInlineJPXB .emptyState limits named params raw ext (.init limits)).1
  else if hasCodec limits params ∧ (dctSplit limits params).isNone ∧ (ccittSplit limits params).isNone
  then .ok placeholder else
  let p := (imgDictOf Source.empty () params).1
  let info := (csOf Source.empty () named p.cs).1
  let tgt := ext.map (·.t)
  match Filter.decodeStream limits params raw with
  | .ok (.data b) => decodePixmap limits p info b tgt
  | .ok (.image .dct parms b) => .ok (decodeDCTOr limits p info parms b (scaleFor p.w p.h ext) tgt)
  | .ok (.image .ccitt parms b) => .ok (decodeCCITTOr limits p info parms b tgt)
  | .ok (.image ..) => .ok placeholder
  | .error e => .error e

/-! ## 7. Per-page image table -/

/-- Maximum number of decoded image pixels held for one page (all XObjects together; each
pixel is 4 bytes, so 256 MiB; task 8.6, was 1 GiB). An XObject is decoded under what is left
of it (`ImageTable.add`: reduced to fit when needed); once it is spent, further XObjects are
drawn as the placeholder. A local cap (no `Limits` field yet). -/
def maxPageImagePixels : Nat := 1 <<< 26

/-- The images of a page, decoded before rendering. -/
structure ImageTable where
  /-- Limits for decoding inline images. -/
  limits : Limits := {}
  /-- The page's named colour spaces (`/ColorSpace` resources), for inline images. -/
  named : List (Name × CSInfo) := []
  /-- Decoded image XObjects by `(num, gen)` (`none`: failed, drawn as nothing). -/
  xobjs : List ((Nat × Nat) × Option Pixmap) := []
  /-- Predecoded inline JPX placements in a document render. A missing extent denotes a
  pattern or glyph placement whose final device matrix is unknown when it is loaded. -/
  inlineJPX : List (Dict × ByteArray × Option Extent × Option Pixmap) := []
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

private def addImageIn {σ : Type} (src : Source σ) (acc : ImageTable × σ) (resources : Dict)
    (num gen : Nat) (exts : List ((Nat × Nat) × Extent)) (budget : CodecBudget σ) : ImageTable × σ :=
  let t := acc.1
  if t.xobjs.any (·.1 == (num, gen)) then acc else
  if maxPageImagePixels ≤ t.pixels then
    ({ t with xobjs := ((num, gen), some placeholder) :: t.xobjs }, acc.2) else
  let lim := { t.limits with
    maxDecodedStreamBytes := min t.limits.maxDecodedStreamBytes (4 * (maxPageImagePixels - t.pixels)) }
  let (r, s) := loadXObjectIn lim src acc.2 t.named resources num gen
    ((exts.find? (·.1 == (num, gen))).map (·.2)) budget
  match r with
  | .ok pm =>
    let n := pm.w * pm.h
    if maxPageImagePixels < t.pixels + n then
      ({ t with xobjs := ((num, gen), some placeholder) :: t.xobjs }, s)
    else ({ t with xobjs := ((num, gen), some pm) :: t.xobjs, pixels := t.pixels + n }, s)
  | .error _ => ({ t with xobjs := ((num, gen), none) :: t.xobjs }, s)

/-- Add image XObject `num gen` to the table (once); `exts` as in `loadImages`. The image is
decoded with `maxDecodedStreamBytes` lowered to the RGBA bytes left of the page's
`maxPageImagePixels` (task 8.6), so it is reduced to fit rather than replaced; with nothing
left it is the placeholder. -/
def ImageTable.add {σ : Type} (src : Source σ) (acc : ImageTable × σ) (num gen : Nat)
    (exts : List ((Nat × Nat) × Extent) := []) (budget : CodecBudget σ := {}) : ImageTable × σ :=
  addImageIn src acc [] num gen exts budget

/-- **Load the images of a display list**: every distinct image XObject decoded once (in
first-use order), including images inside soft-mask groups (`DisplayList.foldDeep`, task
7.3f), the page's named colour spaces resolved (`res`: the page resources). `exts` (task
7.10, `imageExtents`): device extents for reduced-size JPEG decoding; images not listed are
decoded at full size. -/
def loadImages {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (res : Dict)
    (items : DisplayList) (exts : List ((Nat × Nat) × Extent) := []) (budget : CodecBudget σ := {}) : ImageTable × σ :=
  let (named, s) := namedSpaces src s res
  Content.DisplayList.foldDeep (fun acc it =>
    match it with
    | .image (.xobject _ n g) _ _ _ => addImageIn src acc res n g exts budget
    | _ => acc) limits.maxXObjectDepth ({ limits, named }, s) items

/-- Decode inline JPX during document preparation under the document and page allowances.
The source decodes tint functions retained from the page or form that emitted the image. -/
def ImageTable.loadInlineJPXFrom (t : ImageTable) (src : Source Filter.Budget)
    (b : Filter.Budget) (view : Option Aff) (items : DisplayList) : ImageTable × Filter.Budget :=
  Content.DisplayList.foldDeep (fun (acc : ImageTable × Filter.Budget) it => Id.run do
    let .image (.inline d raw) ctm _ _ := it | return acc
    unless (codecSplit .jpx t.limits d).isSome do return acc
    let ext := view.map fun v => Extent.ofDev (Aff.ofMatrix ctm * v)
    let (tbl, b) := acc
    if tbl.inlineJPX.any (fun (dict, data, target, _) => target == ext && dict == d && data == raw) then
      return acc
    let cap := 4 * (maxPageImagePixels - tbl.pixels)
    let limits := { t.limits with maxDecodedStreamBytes := min cap t.limits.maxDecodedStreamBytes }
    let (r, b) := decodeInlineJPXB src limits t.named d raw ext b
    let pm := r.toOption
    return ({ tbl with
      inlineJPX := (d, raw, ext, pm) :: tbl.inlineJPX,
      pixels := tbl.pixels + pm.elim 0 (fun i => i.w * i.h) }, b)) t.limits.maxXObjectDepth (t, b) items

/-- Decode inline JPX with self-contained parameters under the document and page allowances.
Fixed pattern/glyph uses receive their full-size target. -/
def ImageTable.loadInlineJPX (t : ImageTable) (b : Filter.Budget) (view : Option Aff)
    (items : DisplayList) : ImageTable × Filter.Budget :=
  t.loadInlineJPXFrom .emptyState b view items

/-- The pixmap of an image source (`none`: nothing to draw). Inline images are decoded here,
reduced for the squared device extents `ext` of this use (task 8.6). -/
def ImageTable.pixmap (t : ImageTable) (src : ImageSource) (ext : Option Extent := none) :
    Option Pixmap :=
  match src with
  | .xobject _ n g => ((t.xobjs.find? (·.1 == (n, g))).map (·.2)).join
  | .inline params data =>
    let placements := t.inlineJPX.filter fun (dict, raw, _, _) => dict == params && raw == data
    let cached := placements.find? (fun (_, _, target, _) => target == ext) <|>
      placements.find? (fun (_, _, target, _) => target.isNone) <|> placements.head?
    if let some (_, _, _, pm) := cached then pm else
    match decodeInline t.limits t.named params data ext with
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

/-- `q` in fixed point (32 fractional bits), clamped to `±lim`. -/
def toFix (q : Rat) (lim : Int) : Int64 :=
  Int64.ofInt (max (-lim) (min lim (q * (fone : Rat)).floor))

/-- `q` in fixed point rounded to nearest (per-pixel steps: the drift over a row stays below
one unit per 2³² steps of error each way), clamped to `±lim`. -/
def toFixR (q : Rat) (lim : Int) : Int64 :=
  Int64.ofInt (max (-lim) (min lim (roundRat (q * (fone : Rat)))))

/-- `2⁴⁴`, the upper clamp of `fixLen`. Out of line (`noinline`): a literal of `2³²` or more
in a function body is parsed from its decimal string through GMP on every call
(`scripts/check-codegen.sh`, task 13.18). -/
@[noinline] def fixLenCap : Nat := 1 <<< 44

/-- `√len2` in fixed point, clamped to `[2, 2⁴⁴]` (one device pixel in image units). -/
def fixLen (len2 : Rat) : Int64 :=
  let s := Nat.sqrt (len2 * (fone : Rat) * (fone : Rat)).floor.toNat
  Int64.ofNat (max 2 (min s fixLenCap))

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

/-- The `Extent` of an inline image drawn with the device matrix `dev` (task 8.6: inline images
are decoded at their drawn size per use); `none` for XObjects (reduced once per page through
`imageExtents`). -/
def inlineExt (src : ImageSource) (dev : Aff) : Option Extent :=
  match src with
  | .inline .. => some (Extent.ofDev dev)
  | .xobject .. => none

/-- **Paint one image item** (`DisplayItem.image src ctm fill clip`) on a `W × H` page through
the page → device matrix `m`: the clip mask from `Clip.clipMaskC` (cached), the pixmap from
`tbl` (inline images decoded here), placed with `CTM × m` (`place`, smooth; downscale cap
`Limits.maxImagePixels`); `fill` gives the stencil colour and the constant alpha `ca`.
Nothing is drawn for an image that failed to decode. -/
def renderImage (cfg : Config) (m : Aff) (W H : Nat) (tbl : ImageTable) (st : Clip.RState)
    (src : ImageSource) (ctm : Matrix) (fill : FillStyle) (clip : Clip) : Clip.RState :=
  match tbl.pixmap src (inlineExt src (Aff.ofMatrix ctm * m)) with
  | none => st
  | some pm =>
    let c := Clip.clipMaskC cfg m W H st.room st.cache clip
    let p := place tbl.limits.maxImagePixels W H pm (Aff.ofMatrix ctm * m) c.1
      (Clip.deviceRGB fill.color) (Clip.compByte fill.alpha) st.buf
    { st with buf := p.1, cache := c.2.1, steps := st.steps + c.2.2 + p.2, smemo := none }

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
    have h0 := Clip.clipMaskC_steps_le cfg m W H st.room st.cache clip
    have h1 := place_steps_le tbl.limits.maxImagePixels W H pm (Aff.ofMatrix ctm * m)
      (Clip.clipMaskC cfg m W H st.room st.cache clip).1
      (Clip.deviceRGB fill.color) (Clip.compByte fill.alpha) st.buf true
    simp only
    omega

/-! ## 10. Checks -/

private def bytes (l : List Nat) : ByteArray := ByteArray.mk (l.map UInt8.ofNat).toArray

private def dev (w h : Nat) : ImgDict :=
  { w, h, bpc := some 8, mask := false, decode := none, interp := false, cs := none }

private def grayCS : Option CSInfo := some (.dev .gray (.gray Comp.zero))

#guard rowBytes 3 1 1 == 1 && rowBytes 9 1 1 == 2 && rowBytes 3 3 16 == 18
-- `/DL` of an image's data (task 8.10): rows of `⌈w · nc · bpc / 8⌉` bytes; `0` when unknown.
#guard dataSize { dev 3 2 with bpc := some 1 } grayCS == 2 &&
  dataSize (dev 5 2) (some (.dev .rgb (.gray Comp.zero))) == 30 &&
  dataSize (dev 5 2) none == 0 && dataSize { dev 9 2 with mask := true } none == 4
#guard withDL [(Name.ofString "DL", .int 1), (Name.ofString "W", .int 2)] 6 ==
    [(Name.ofString "DL", .int 6), (Name.ofString "W", .int 2)] &&
  withDL [(Name.ofString "W", .int 2)] 0 == [(Name.ofString "W", .int 2)]
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
