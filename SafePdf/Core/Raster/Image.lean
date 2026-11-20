import SafePdf.Core.Raster.Clip
import SafePdf.Core.Content.Run

/-!
# Images: decoding sample data and placing it on the page (task 7.3b)

Plan.md §6 Phase 7 ("images composited from quarantine-zone decodes"; "Proven: totality,
resource bounds"), §4 **S3**. ISO 32000-2 §8.9 (images): §8.9.3 (sample representation),
§8.9.5 (image dictionaries: `/Width`, `/Height`, `/BitsPerComponent`, `/ColorSpace`,
`/Decode`, `/ImageMask`, `/Interpolate`), §8.9.6.2 (stencil masks), §8.9.7 (inline images),
§8.3.3 / §8.9.4 (image space: the unit square, sample `(0, 0)` at its top-left corner).

## Pipeline

1. **Data.** An image XObject is fetched through `Source σ` (5.2b) and decoded with the
   source's `decode` (the document budget is charged, `Doc.decodeBodyB`); an inline image's
   still-encoded bytes are decoded here with `Filter.decodeStream` (bounded by
   `Limits.maxDecodedStreamBytes`). Flate, LZW, RunLength, ASCIIHex, ASCII85 (with
   predictors) are the core's byte filters. A chain that reaches an **image codec**
   (`/DCTDecode`, `/JPXDecode`, `/JBIG2Decode`, `/CCITTFaxDecode`, detected with
   `Filter.parseChain` before decoding) yields the **placeholder**: a 1 × 1 mid-grey
   (`128`) opaque pixmap, i.e. a grey box over the image's unit square. The codecs belong to
   the quarantine zone (Plan.md §6 Phase 3, S7) and replace the placeholder later.
2. **Parameters** (`ImgDict`, entries resolved one level through the source): `/Width`,
   `/Height` (both `≥ 1`; `w · h ≤ Limits.maxImagePixels`, else
   `Error.limitExceeded .imagePixels`), `/BitsPerComponent` ∈ {1, 2, 4, 8, 16} (else
   `malformed`; `1` for stencil masks), `/Decode` (used when it has `2 · ncomp` numbers),
   `/ImageMask`, `/Interpolate` (recorded, not used: sampling is nearest-neighbour).
3. **Colour space** (`Run.csInfo`, the interpreter's own resolution, so fills and images
   agree): `DeviceGray`/`RGB`/`CMYK`, `CalGray`/`CalRGB` and `ICCBased` (by `/N` or a matching
   `/Alternate`) as device spaces; `Indexed` (lookup string or stream; indices clamp to
   `hival`, and to 255); `Separation` (type 2 tint transform, else the interpreter's darkness
   placeholder); `DeviceN` (the interpreter's average-darkness placeholder); `Lab` (`L*` as
   grey). An inline image's resource-name colour space is looked up in the page's
   `/ColorSpace` resources (`ImageTable.named`; a form's own resources are not consulted — a
   gap). A missing or unknown space (and `Pattern`) yields the placeholder.
   Colour conversion to RGB is the same as `Clip.deviceRGB` (naive CMYK).
4. **Samples** (`samples`): rows padded to whole bytes (`rowBytes`), samples big-endian
   within bytes; 16-bit samples use their high byte. Each sample goes through a per-component
   lookup table (`lutComp`, ≤ 256 entries, computed exactly over `ℚ` once per image) that
   applies `/Decode` (`d = Dmin + s · (Dmax − Dmin) / (2^bpc − 1)`) and normalises to a byte:
   `round(255 · d)` for colour components, `round(d)` for `Indexed` indices,
   `round(255 · d / 100)` for `Lab` `L*`. The result has exactly `w · h · ncomp` bytes
   (`samples_size`). **Short data is padded with zeros** (as MuPDF does), so every read is
   the total `Clip.getB`; in-range reads hit the expected byte range (`sampleOffset_lt`).
   The sample buffer is also capped: `w · h · ncomp ≤ Limits.maxDecodedStreamBytes`, else
   `Error.limitExceeded .decodedStreamBytes` (a small stream with huge dimensions would
   otherwise allocate unboundedly).
5. **RGBA** (`toRGBA`): `4 · w · h` bytes (`Pixmap.size_eq`, by construction). Stencil masks
   (`/ImageMask true`) keep the coverage `255 − byte(d)` in the alpha byte (default `/Decode
   [0 1]`: sample 0 paints) and take the fill colour at painting time.
6. **Placement** (`place`): the device matrix is `CTM × view` (exact over `ℚ`); its inverse
   composed with `(x, y) ↦ (w·x, h·(1 − y))` maps a device point to continuous image
   coordinates (`col`, `row`). It is computed **once per image** (`Geom.Aff.inv`); per row
   the start of the row (pixel centre `(x0 + ½, y + ½)`) is evaluated exactly and floored to
   fixed point with 32 fractional bits; per pixel the coordinates advance by the rounded
   steps (no `ℚ` per pixel; the drift over 16384 pixels is below `2⁻¹⁸` image pixels). A
   device pixel is painted iff its centre maps inside the image, with the nearest sample
   (**nearest-neighbour**; edges are not anti-aliased and `/Interpolate` is ignored —
   documented degradations: MuPDF smooths downscaled images, so heavily minified images
   alias). The pixels visited are the device bounding box of the image ∩ the item's clip
   window (`Clip.itemWindow`), hence at most `W · H` (`place_steps_le`). A singular matrix
   paints nothing.
7. **Compositing**: per pixel `a = mul255(mul255(sampleAlpha, clipCoverage), ca)` and
   `putPx` (the source-over `Clip.blend` of path items, written directly when `a = 255`;
   clip coverage by `Mask.get` as in `Clip.covAt`). Compiled (`leanc -O3`), a full-page
   600 × 800 RGB image takes ≈ 52 ms to decode and ≈ 97 ms to place (≈ 200 ns per device
   pixel, like `Clip`'s compositing). Soft masks (`/SMask`), colour-key masking (`/Mask` arrays) and explicit
   masks (`/Mask` streams) are **not applied** (gap; Phase 7 soft masks).

## Wiring into `Glyph.renderPage`

`loadImages limits src s res items` decodes every distinct image XObject of a display list
once (by object number), under the session state `σ` (the document budget), and resolves the
page's named colour spaces; it returns an `ImageTable`. Decoded pixmaps on one page are
capped at `maxPageImagePixels` pixels in total (further XObjects get the placeholder).
`renderImage cfg m W H tbl st src ctm fill clip : Clip.RState` paints one image item
(clip mask through `Clip.clipMaskC` and its cache; inline images are decoded here, purely).
It preserves the buffer size (`renderImage_size`) and adds at most
`Clip.clipCost cfg W H clip + W · H` work (`renderImage_steps_le`).
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
  /-- The `/Interpolate` hint (recorded; sampling is nearest-neighbour). -/
  interpolate : Bool := false

/-- The **placeholder** for images the core does not decode (image codecs, unknown colour
spaces): one mid-grey (`128`) opaque sample, i.e. a grey box over the unit square. -/
def placeholder : Pixmap := ⟨1, 1, ByteArray.mk #[128, 128, 128, 255], rfl, false, false⟩

instance : Inhabited Pixmap := ⟨placeholder⟩

/-! ## 2. Sample unpacking -/

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
def clampByte (x : Int) : UInt8 := if x < 0 then 0 else UInt8.ofNatClamp x.toNat

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

/-- Fill the sample buffer from sample `i` on (`fuel` samples): sample `i` is component
`i % wn % nc` of row `i / wn` (`wn = w · nc` samples per row), through its lookup table. -/
def samplesLoop (data lut : ByteArray) (wn nc bpc nv stride : Nat) :
    (fuel i : Nat) → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    let k := i % wn
    let s := sampleAt data (i / wn * stride) k bpc
    samplesLoop data lut wn nc bpc nv stride fuel (i + 1)
      (acc.push (lut[(k % nc) * nv + s]?.getD 0))

/-- `samplesLoop` pushes exactly one byte per step. -/
theorem samplesLoop_size (data lut : ByteArray) (wn nc bpc nv stride : Nat) :
    ∀ (fuel i : Nat) (acc : ByteArray),
      (samplesLoop data lut wn nc bpc nv stride fuel i acc).size = acc.size + fuel
  | 0, _, _ => rfl
  | fuel + 1, i, acc => by
    simp only [samplesLoop]
    rw [samplesLoop_size data lut wn nc bpc nv stride fuel, ByteArray.size_push]; omega

/-- **Decoded samples** of a `w × h` image with `nc` components of `bpc` bits, through the
lookup tables `lut` (`2^bits` entries per component): one normalised byte per sample, row
by row. -/
def samples (data lut : ByteArray) (w h nc bpc bits : Nat) : ByteArray :=
  samplesLoop data lut (w * nc) nc bpc (2 ^ bits) (rowBytes w nc bpc) (w * h * nc) 0
    ByteArray.empty

/-- **The sample buffer has exactly `w · h · ncomp` bytes.** -/
theorem samples_size (data lut : ByteArray) (w h nc bpc bits : Nat) :
    (samples data lut w h nc bpc bits).size = w * h * nc := by
  simp only [samples, samplesLoop_size]; simp [ByteArray.size]

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
    ((acc.push (UInt8.ofNatClamp c.1)).push (UInt8.ofNatClamp c.2.1)).push
      (UInt8.ofNatClamp c.2.2)) ByteArray.empty

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
    let v := UInt8.ofNatClamp c0
    (((acc.push v).push v).push v).push 255
  | .rgb =>
    (((acc.push (UInt8.ofNatClamp c0)).push (UInt8.ofNatClamp (rd smp (b + 1)))).push
      (UInt8.ofNatClamp (rd smp (b + 2)))).push 255
  | .cmyk =>
    let k := rd smp (b + 3)
    (((acc.push (UInt8.ofNatClamp (255 - min 255 (c0 + k)))).push
      (UInt8.ofNatClamp (255 - min 255 (rd smp (b + 1) + k)))).push
      (UInt8.ofNatClamp (255 - min 255 (rd smp (b + 2) + k)))).push 255
  | .pal avg tbl =>
    let i := if avg then sumBytes smp nc b / max nc 1 else c0
    (((acc.push (UInt8.ofNatClamp (rd tbl (3 * i)))).push
      (UInt8.ofNatClamp (rd tbl (3 * i + 1)))).push
      (UInt8.ofNatClamp (rd tbl (3 * i + 2)))).push 255
  | .stencil => (((acc.push 0).push 0).push 0).push (UInt8.ofNatClamp (255 - c0))

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
  { w, h, data := rgbaLoop smp nc cv (w * h) 0 ByteArray.empty,
    size_eq := by rw [rgbaLoop_size]; simp [ByteArray.size, Nat.mul_assoc],
    stencil, interpolate := interp }

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
  let dec : Option (List Rat) := match dc with
    | some (.array xs) => (xs.mapM Content.Interp.num?).map (·.map Fixed.toRat)
    | _ => none
  ({ w := (natOf w).getD 0, h := (natOf h).getD 0, bpc := natOf b, mask := boolOf m,
     decode := dec, interp := boolOf ip, cs }, s)

/-- Valid `/BitsPerComponent` values. -/
def validBpc (b : Nat) : Bool := b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8 ∨ b = 16

/-- Maximum number of colour components of an image (`DeviceN` allows 32 colorants); more is
drawn as the placeholder. -/
def maxComps : Nat := 32

/-- Decode with a known plan (`bpc` bits, `nc` components, conversion, normalisation): checks
`/BitsPerComponent` and the sample-buffer cap, then samples and RGBA. Too many components
yield the placeholder. -/
def finish (limits : Limits) (p : ImgDict) (bpc nc : Nat) (cv : Conv) (n : Norm)
    (data : ByteArray) : Except Error Pixmap :=
  if !validBpc bpc then .error (.malformed 0 "image: invalid /BitsPerComponent")
  else if nc = 0 ∨ maxComps < nc then .ok placeholder
  else if limits.maxDecodedStreamBytes < p.w * p.h * nc then
    .error (.limitExceeded .decodedStreamBytes)
  else
    .ok (toRGBA (samples data (luts n nc bpc (min bpc 8) p.decode) p.w p.h nc bpc (min bpc 8))
      p.w p.h nc cv p.mask p.interp)

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

/-- **Decode an image XObject** `num gen` through the source (its filters, the session
budget); an image codec yields the placeholder. -/
def loadXObject {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (named : List (Name × CSInfo))
    (num gen : Nat) : Except Error Pixmap × σ :=
  match src.fetch s num gen with
  | (.ok (.stream st), s) =>
    if hasCodec limits st.dict then (.ok placeholder, s) else
    let (p, s) := imgDictOf src s st.dict
    let (info, s) := csOf src s named p.cs
    match src.decode s num st with
    | (.ok bytes, s) => (decodePixmap limits p info bytes, s)
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
first-use order), the page's named colour spaces resolved (`res`: the page resources). -/
def loadImages {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (res : Dict)
    (items : DisplayList) : ImageTable × σ :=
  let (named, s) := namedSpaces src s res
  items.foldl (fun acc it =>
    match it with
    | .image (.xobject _ n g) _ _ _ => ImageTable.add src acc n g
    | _ => acc) ({ limits, named }, s)

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
    Clip.setB (Clip.setB (Clip.setB buf j (UInt8.ofNatClamp r)) (j + 1) (UInt8.ofNatClamp g))
      (j + 2) (UInt8.ofNatClamp b)
  else
    let buf := Clip.setB buf j (Clip.blend r (rd buf j) a)
    let buf := Clip.setB buf (j + 1) (Clip.blend g (rd buf (j + 1)) a)
    Clip.setB buf (j + 2) (Clip.blend b (rd buf (j + 2)) a)

/-- `putPx` preserves the buffer size. -/
theorem putPx_size (buf : ByteArray) (j r g b a : Nat) : (putPx buf j r g b a).size = buf.size := by
  unfold putPx; split
  · rfl
  · split <;> simp only [Clip.setB_size]

/-- Paint one row: `fuel` device pixels from column `x` on row `y` of a page `W` pixels wide,
image coordinates `(u, v)` in fixed point advancing by `(du, dv)` per pixel. -/
def colLoop (W : Nat) (pm : Pixmap) (cm : Option Mask) (rgb : Nat × Nat × Nat) (alpha : Nat)
    (du dv y : Int) : (fuel : Nat) → (x u v : Int) → ByteArray → ByteArray
  | 0, _, _, _, buf => buf
  | fuel + 1, x, u, v, buf =>
    let col := u / fone
    let row := v / fone
    let buf :=
      if 0 ≤ col ∧ col < pm.w ∧ 0 ≤ row ∧ row < pm.h ∧ 0 ≤ x ∧ x < W ∧ 0 ≤ y then
        let i := 4 * (row.toNat * pm.w + col.toNat)
        let a0 := rd pm.data (i + 3)
        let cov := match cm with
          | none => a0
          | some c => Clip.mul255 a0 (c.get x y).toNat
        let a := Clip.mul255 cov alpha
        let j := 4 * (y.toNat * W + x.toNat)
        if pm.stencil then putPx buf j rgb.1 rgb.2.1 rgb.2.2 a
        else putPx buf j (rd pm.data i) (rd pm.data (i + 1))
          (rd pm.data (i + 2)) a
      else buf
    colLoop W pm cm rgb alpha du dv y fuel (x + 1) (u + du) (v + dv) buf

/-- A row preserves the buffer size. -/
theorem colLoop_size (W : Nat) (pm : Pixmap) (cm : Option Mask) (rgb : Nat × Nat × Nat)
    (alpha : Nat) (du dv y : Int) :
    ∀ (fuel : Nat) (x u v : Int) (buf : ByteArray),
      (colLoop W pm cm rgb alpha du dv y fuel x u v buf).size = buf.size
  | 0, _, _, _, _ => rfl
  | fuel + 1, x, u, v, buf => by
    simp only [colLoop]
    rw [colLoop_size W pm cm rgb alpha du dv y fuel]
    split
    · split <;> exact putPx_size _ _ _ _ _ _
    · rfl

/-- Paint `fuel` rows of rectangle `r` from row `y` on, through the device → image map `A`. -/
def rowLoop (W : Nat) (pm : Pixmap) (cm : Option Mask) (rgb : Nat × Nat × Nat) (alpha : Nat)
    (A : Aff) (r : IRect) (du dv : Int) : (fuel : Nat) → (y : Int) → ByteArray → ByteArray
  | 0, _, buf => buf
  | fuel + 1, y, buf =>
    let xc : Rat := (r.x0 : Rat) + 1 / 2
    let yc : Rat := (y : Rat) + 1 / 2
    let u0 := ((A.a * xc + A.c * yc + A.e) * (fone : Rat)).floor
    let v0 := ((A.b * xc + A.d * yc + A.f) * (fone : Rat)).floor
    rowLoop W pm cm rgb alpha A r du dv fuel (y + 1)
      (colLoop W pm cm rgb alpha du dv y r.width r.x0 u0 v0 buf)

/-- Rows preserve the buffer size. -/
theorem rowLoop_size (W : Nat) (pm : Pixmap) (cm : Option Mask) (rgb : Nat × Nat × Nat)
    (alpha : Nat) (A : Aff) (r : IRect) (du dv : Int) :
    ∀ (fuel : Nat) (y : Int) (buf : ByteArray),
      (rowLoop W pm cm rgb alpha A r du dv fuel y buf).size = buf.size
  | 0, _, _ => rfl
  | fuel + 1, y, buf => by
    simp only [rowLoop]; rw [rowLoop_size W pm cm rgb alpha A r du dv fuel, colLoop_size]

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

/-- **Place a pixmap** on a `W × H` RGBA page buffer: the unit square mapped by `dev` (image
space → device), clip mask `cm`, fill colour `rgb` (stencil masks), constant alpha `alpha`
(byte). Returns the buffer and the number of device pixels visited. -/
def place (W H : Nat) (pm : Pixmap) (dev : Aff) (cm : Option Mask) (rgb : Nat × Nat × Nat)
    (alpha : Nat) (buf : ByteArray) : ByteArray × Nat :=
  if dev.det = 0 then (buf, 0) else
  let A := Aff.inv dev * ⟨(pm.w : Rat), 0, 0, -(pm.h : Rat), 0, (pm.h : Rat)⟩
  let r := placeRect W H dev cm
  let du := roundRat (A.a * (fone : Rat))
  let dv := roundRat (A.b * (fone : Rat))
  (rowLoop W pm cm rgb alpha A r du dv r.height r.y0 buf, r.width * r.height)

/-- Placing preserves the buffer size. -/
theorem place_size (W H : Nat) (pm : Pixmap) (dev : Aff) (cm : Option Mask)
    (rgb : Nat × Nat × Nat) (alpha : Nat) (buf : ByteArray) :
    (place W H pm dev cm rgb alpha buf).1.size = buf.size := by
  unfold place; split
  · rfl
  · exact rowLoop_size _ _ _ _ _ _ _ _ _ _ _ _

/-- The visited rectangle lies inside the page. -/
theorem placeRect_area_le (W H : Nat) (dev : Aff) (cm : Option Mask) :
    (placeRect W H dev cm).width * (placeRect W H dev cm).height ≤ W * H := by
  have h1 := IRect.inter_width_le_right (deviceBox dev) (Clip.itemWindow W H cm)
  have h2 := IRect.inter_height_le_right (deviceBox dev) (Clip.itemWindow W H cm)
  have h3 := Clip.clipWindow_width_le W H cm
  have h4 := Clip.clipWindow_height_le W H cm
  simp only [placeRect, Clip.itemWindow] at h1 h2 ⊢
  exact Nat.mul_le_mul (by omega) (by omega)

/-- **S3 for placement.** Placing an image visits at most `W · H` device pixels (one constant
step each), whatever the image size or matrix. -/
theorem place_steps_le (W H : Nat) (pm : Pixmap) (dev : Aff) (cm : Option Mask)
    (rgb : Nat × Nat × Nat) (alpha : Nat) (buf : ByteArray) :
    (place W H pm dev cm rgb alpha buf).2 ≤ W * H := by
  unfold place; split
  · exact Nat.zero_le _
  · exact placeRect_area_le W H dev cm

/-! ## 9. Display items -/

/-- **Paint one image item** (`DisplayItem.image src ctm fill clip`) on a `W × H` page through
the page → device matrix `m`: the clip mask from `Clip.clipMaskC` (cached), the pixmap from
`tbl` (inline images decoded here), placed with `CTM × m`; `fill` gives the stencil colour
and the constant alpha `ca`. Nothing is drawn for an image that failed to decode. -/
def renderImage (cfg : Config) (m : Aff) (W H : Nat) (tbl : ImageTable) (st : Clip.RState)
    (src : ImageSource) (ctm : Matrix) (fill : FillStyle) (clip : Clip) : Clip.RState :=
  match tbl.pixmap src with
  | none => st
  | some pm =>
    let c := Clip.clipMaskC cfg m W H st.cache clip
    let p := place W H pm (Aff.ofMatrix ctm * m) c.1 (Clip.deviceRGB fill.color)
      (Clip.compByte fill.alpha) st.buf
    { buf := p.1, cache := c.2.1, steps := st.steps + c.2.2 + p.2 }

/-- Painting an image preserves the buffer size. -/
theorem renderImage_size (cfg : Config) (m : Aff) (W H : Nat) (tbl : ImageTable)
    (st : Clip.RState) (src : ImageSource) (ctm : Matrix) (fill : FillStyle) (clip : Clip) :
    (renderImage cfg m W H tbl st src ctm fill clip).buf.size = st.buf.size := by
  unfold renderImage; split
  · rfl
  · exact place_size _ _ _ _ _ _ _ _

/-- **S3 for an image item.** The counted work is at most the clip's cost plus `W · H`
compositing steps (decoding work is bounded separately: `w · h · ncomp` sample steps and
`w · h` pixel steps, with `w · h ≤ Limits.maxImagePixels`). -/
theorem renderImage_steps_le (cfg : Config) (m : Aff) (W H : Nat) (tbl : ImageTable)
    (st : Clip.RState) (src : ImageSource) (ctm : Matrix) (fill : FillStyle) (clip : Clip) :
    (renderImage cfg m W H tbl st src ctm fill clip).steps ≤
      st.steps + Clip.clipCost cfg W H clip + W * H := by
  unfold renderImage; split
  · omega
  · rename_i pm _
    have h0 := Clip.clipMaskC_steps_le cfg m W H st.cache clip
    have h1 := place_steps_le W H pm (Aff.ofMatrix ctm * m)
      (Clip.clipMaskC cfg m W H st.cache clip).1
      (Clip.deviceRGB fill.color) (Clip.compByte fill.alpha) st.buf
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

end SafePdf.Core.Raster.Image
