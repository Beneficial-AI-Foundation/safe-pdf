import SafePdf.Core.Limits
import SafePdf.Core.Error

/-!
# Baseline JPEG decoder (`/DCTDecode`, task 7.6a)

Plan.md §3 (the quarantine zone: "DCT (JPEG), JPEG 2000, JBIG2 decoding"; design rule 4: the
decoder's output is re-validated — dimensions, size — before it enters the core), §6 Phase 3
("DCT/JPX/JBIG2: not in trusted path — images decode in the quarantine zone (or late, in
Lean); a failed image renders as a placeholder box") and Phase 7 ("images composited from
quarantine-zone decodes"). This decoder is the "late, in Lean" option: pure Lean, written
under the rules of `Core/` (no `partial`, `unsafe`, `panic!`, `!` indexing, `sorry`); every
loop is a `for` over a range or a recursion on explicit fuel bounded by the input or the
output size.

ITU-T T.81 (ISO/IEC 10918-1), sequential DCT with Huffman coding:

* **Markers** (B.1, B.2): `SOI`, `APP0` (JFIF), `APP14` (Adobe: colour transform), other
  `APPn`/`COM` skipped, `DQT` (8- and 16-bit tables), `SOF0`/`SOF1` (8-bit precision, 1–4
  components, sampling factors 1–4), `DHT`, `SOS` (one or several scans; a scan of one
  component is non-interleaved), `DRI`/`RSTn` (restart intervals), `EOI`. Progressive
  (`SOF2`/`SOF6`/`SOF10`/`SOF14`), lossless, arithmetic-coded frames, 12-bit precision and
  `DNL` (height 0) are `Error.unsupported`: the image layer then draws the placeholder.
* **Entropy decoding** (F.2.2): canonical Huffman tables validated as libjpeg does
  (`jpeg_make_d_derived_tbl`: at most 256 symbols, no code overflow — the all-ones code is
  rejected — DC symbols ≤ 15), decoded through a 16-bit lookup table; byte stuffing
  `FF 00`, fill bytes `FF FF`; DC prediction reset at each restart. A marker or the end of
  the data inside a scan reads as zero bits (libjpeg: "premature end of data segment"), so a
  truncated image decodes to its end like MuPDF's.
* **Dequantisation, zig-zag, IDCT**: libjpeg's exact integer "islow" IDCT (`jidctint.c`,
  13-bit constants, 2 extra bits in pass 1, the 1024-entry range-limit table semantics).
* **Upsampling**: libjpeg-turbo 2.1's default ("fancy", `jdsample.c`): `h2v1` and `h2v2`
  triangle filters (downsampled width > 2), `h1v2` triangle filter, other integral ratios by
  replication; edge rows and columns are replicated. Non-integral ratios are
  `Error.unsupported` (libjpeg: "fractional sampling not implemented").
* **Colour conversion** (`jdcolor.c`, 16-bit fixed-point tables): YCbCr → RGB, YCCK → CMYK,
  or none. The source space follows libjpeg's `default_decompress_parms` with MuPDF's
  `/ColorTransform` rule (`filter-dct.c`): an Adobe `APP14` marker's transform overrides the
  PDF's `/ColorTransform`; transform 0 means no conversion (RGB, CMYK); otherwise 3
  components are YCbCr (unless no JFIF/Adobe marker and component ids `R G B`), 4 components
  are YCCK only with an Adobe marker of transform ≠ 0. CMYK is **not** inverted (MuPDF passes
  `invert_cmyk = 0` for JPEGs in PDF files; Adobe-inverted data relies on the image's
  `/Decode [1 0 1 0 1 0 1 0]`).

The reference is MuPDF 1.25.1 as installed (Debian's build links libjpeg-turbo 2.1.5:
`JDCT_ISLOW`, fancy upsampling, no merged upsampler). MuPDF's reduced-size decoding
(`scale_num = 8 / 2^l2factor` when an image is drawn much smaller than its size) is not
reproduced: this decoder always decodes at full size.

## Bounds

`/Width · /Height ≤ Limits.maxImagePixels` (else `Error.limitExceeded .imagePixels`); the
component planes (padded to whole MCUs) and the output buffer each hold at most
`Limits.maxDecodedStreamBytes` bytes (else `.decodedStreamBytes`); at most one scan per
component is decoded (a scan after every component has been decoded ends decoding, like a
sequential libjpeg stream); the marker loop runs at most once per input byte. The decoded
image carries its size law (`Image.size_eq`, `Image.nc_le`), and `decode_pixels` proves the
pixel bound.

## API

`decode limits colorTransform bytes : Except Error Image` — `colorTransform` is the PDF
`/ColorTransform` (`none` when absent); the result has `nc` interleaved 8-bit components per
pixel (1 gray, 3 RGB, 4 CMYK; 2 raw), row-major, top row first.
-/

namespace SafePdf.Quarantine.DCT

open SafePdf

/-! ## 1. Bytes -/

/-- Byte `i` of `b` (`0` out of range). -/
@[inline] def rd (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then (b.get i h).toNat else 0

/-- Big-endian 16-bit value at `i`. -/
@[inline] def rd16 (b : ByteArray) (i : Nat) : Nat := rd b i * 256 + rd b (i + 1)

/-- Write byte `v` at `i` (ignored out of range). -/
@[inline] def setB (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if h : i < b.size then b.set i v h else b

/-- A natural number clamped to a byte. -/
@[inline] def u8 (n : Nat) : UInt8 := if n < 256 then UInt8.ofNat n else 255

/-! ## 2. Markers and tables -/

/-- Zig-zag position → natural (row-major) position (T.81 Figure A.6), followed by 16 extra
entries `63` (libjpeg's `jpeg_natural_order` safety margin for corrupt run lengths). -/
def natural : Array Nat :=
  #[0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5,
    12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7, 14, 21, 28,
    35, 42, 49, 56, 57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51,
    58, 59, 52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63,
    63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63]

/-- A frame component (T.81 B.2.2). -/
structure Comp where
  /-- Component identifier `Cᵢ`. -/
  id : Nat
  /-- Horizontal sampling factor `Hᵢ` (1–4). -/
  h : Nat
  /-- Vertical sampling factor `Vᵢ` (1–4). -/
  v : Nat
  /-- Quantisation table selector `Tqᵢ` (0–3). -/
  tq : Nat
  deriving Inhabited, Repr

/-- A frame header (`SOF0`/`SOF1`). -/
structure Frame where
  /-- Samples per line `X`. -/
  w : Nat
  /-- Lines `Y`. -/
  h : Nat
  /-- The components (1–4). -/
  comps : Array Comp
  /-- `Hmax`. -/
  hmax : Nat
  /-- `Vmax`. -/
  vmax : Nat
  /-- MCUs per row of an interleaved scan, `⌈X / (8 · Hmax)⌉`. -/
  mcusX : Nat
  /-- MCU rows, `⌈Y / (8 · Vmax)⌉`. -/
  mcusY : Nat
  /-- Offset of each component's plane in the plane buffer. -/
  offs : Array Nat
  deriving Inhabited

/-- Width in samples of component `c`'s plane (whole MCUs). -/
def Frame.stride (f : Frame) (c : Comp) : Nat := f.mcusX * c.h * 8

/-- Height in samples of component `c`'s plane. -/
def Frame.rows (f : Frame) (c : Comp) : Nat := f.mcusY * c.v * 8

/-- Downsampled width `⌈X · Hᵢ / Hmax⌉` (libjpeg `downsampled_width`). -/
def Frame.dw (f : Frame) (c : Comp) : Nat := (f.w * c.h + f.hmax - 1) / f.hmax

/-- Downsampled height `⌈Y · Vᵢ / Vmax⌉`. -/
def Frame.dh (f : Frame) (c : Comp) : Nat := (f.h * c.v + f.vmax - 1) / f.vmax

/-- Decoder state between segments. -/
structure St where
  /-- Quantisation tables in natural order (`#[]`: undefined). -/
  qt : Array (Array Int) := Array.replicate 4 #[]
  /-- DC Huffman lookup tables (`#[]`: undefined). -/
  dc : Array (Array UInt32) := Array.replicate 4 #[]
  /-- AC Huffman lookup tables. -/
  ac : Array (Array UInt32) := Array.replicate 4 #[]
  /-- The frame, once `SOF` was read. -/
  frame : Option Frame := none
  /-- Restart interval in MCUs (`0`: none). -/
  ri : Nat := 0
  /-- Transform flag of an Adobe `APP14` marker. -/
  adobe : Option Nat := none
  /-- A JFIF `APP0` marker was seen. -/
  jfif : Bool := false
  /-- The component planes, concatenated (offsets `Frame.offs`). -/
  buf : ByteArray := ByteArray.empty
  /-- Which components have been decoded by a scan. -/
  done : Array Bool := #[]
  /-- Number of scans decoded. -/
  scans : Nat := 0

/-- Malformed-JPEG error. -/
def bad (off : Nat) (msg : String) : Error := .malformed off s!"DCT: {msg}"

/-! ### Huffman tables -/

/-- Fill `n` entries of the lookup table from index `i` with `e`. -/
def fillLut (e : UInt32) : (n i : Nat) → Array UInt32 → Array UInt32
  | 0, _, t => t
  | n + 1, i, t => fillLut e n (i + 1) (t.setIfInBounds i e)

/-- Build the 16-bit lookup table of a Huffman table from its 16 code-length counts and its
symbols (entry `len · 256 + symbol` for every 16-bit prefix starting with the code; `0` for
prefixes of no code), validating it like libjpeg (`jpeg_make_d_derived_tbl`): at most 256
symbols, canonical codes fit their lengths with the all-ones code excluded, DC symbols ≤ 15. -/
def buildHuff (counts : Array Nat) (syms : Array Nat) (isDC : Bool) : Except Error (Array UInt32) := do
  if 256 < syms.size then throw (bad 0 "Huffman table with more than 256 symbols")
  if isDC && syms.any (15 < ·) then throw (bad 0 "DC Huffman symbol above 15")
  let mut lut : Array UInt32 := Array.replicate 65536 0
  let mut code := 0
  let mut k := 0
  for l in [1:17] do
    let n := counts.getD (l - 1) 0
    for _ in [0:n] do
      let sym := syms.getD k 0
      let span := 2 ^ (16 - l)
      lut := fillLut (UInt32.ofNat (l * 256 + sym)) span (code * span) lut
      code := code + 1
      k := k + 1
    if 2 ^ l ≤ code then throw (bad 0 "bad Huffman table (code overflow)")
    code := code * 2
  return lut

/-! ## 3. Entropy-coded data -/

/-- Bit reader: the next byte position, a 64-bit accumulator holding `cnt` unread bits in its
low bits, and whether a marker (or the end of data) was reached — then only zero bits
follow, and `pos` is the marker's position. -/
structure BR where
  /-- Next byte to read. -/
  pos : Nat
  /-- Bit accumulator. -/
  acc : UInt64 := 0
  /-- Valid bits in `acc`. -/
  cnt : Nat := 0
  /-- A marker or the end of the data was reached. -/
  stop : Bool := false
  deriving Inhabited

/-- Skip a run of `FF` bytes from `i` (at most `fuel`): the first non-`FF` position. -/
def skipFF (d : ByteArray) : (fuel i : Nat) → Nat
  | 0, i => i
  | fuel + 1, i => if rd d i = 0xFF then skipFF d fuel (i + 1) else i

/-- Refill the accumulator a byte at a time while it holds at most 56 bits (`fuel` bytes):
`FF 00` is a stuffed `FF`, `FF FF …` fill bytes are skipped, any other `FF xx` is a marker
(then zero bits are supplied, libjpeg `jpeg_fill_bit_buffer`). -/
def fill (d : ByteArray) : (fuel : Nat) → BR → BR
  | 0, br => br
  | fuel + 1, br =>
    if 56 < br.cnt then br
    else if br.stop then fill d fuel { br with acc := br.acc <<< 8, cnt := br.cnt + 8 }
    else if d.size ≤ br.pos then
      fill d fuel { br with acc := br.acc <<< 8, cnt := br.cnt + 8, stop := true }
    else
      let b := rd d br.pos
      if b = 0xFF then
        let j := skipFF d d.size (br.pos + 1)
        if j < d.size ∧ rd d j = 0 then
          fill d fuel { br with pos := j + 1, acc := (br.acc <<< 8) ||| 0xFF, cnt := br.cnt + 8 }
        else fill d fuel { br with pos := j - 1, acc := br.acc <<< 8, cnt := br.cnt + 8, stop := true }
      else fill d fuel { br with pos := br.pos + 1, acc := (br.acc <<< 8) ||| b.toUInt64, cnt := br.cnt + 8 }

/-- Make at least 57 bits available (one Huffman code of ≤ 16 bits plus ≤ 15 extra bits fit). -/
@[inline] def refill (d : ByteArray) (br : BR) : BR := if br.cnt < 32 then fill d 8 br else br

/-- Take `s ≤ cnt` bits. -/
@[inline] def getBits (br : BR) (s : Nat) : Nat × BR :=
  let c := br.cnt - s
  (((br.acc >>> c.toUInt64) &&& ((1 <<< s.toUInt64) - 1)).toNat, { br with cnt := c })

/-- Decode one Huffman symbol (needs `cnt ≥ 16`). A prefix of no code yields symbol 0 and
consumes 16 bits (libjpeg: "corrupt JPEG data: bad Huffman code", a zero is faked). -/
@[inline] def decodeSym (lut : Array UInt32) (br : BR) : Nat × BR :=
  let c := br.cnt - 16
  let e := lut.getD ((br.acc >>> c.toUInt64) &&& 0xFFFF).toNat 0
  let len := (e >>> 8).toNat
  if len = 0 then (0, { br with cnt := c })
  else ((e &&& 0xFF).toNat, { br with cnt := br.cnt - len })

/-- `RECEIVE` and `EXTEND` (T.81 F.2.2.1): an `s`-bit magnitude category value. -/
@[inline] def receiveExtend (br : BR) (s : Nat) : Int × BR :=
  if s = 0 then (0, br) else
  let (x, br) := getBits br s
  if x < 2 ^ (s - 1) then ((x : Int) - (2 ^ s : Nat) + 1, br) else ((x : Int), br)

/-- The AC coefficients from zig-zag index `k` (at most `fuel` codes; each code advances `k`),
dequantised (`q` in natural order) into `coef` (natural order). -/
def acLoop (d : ByteArray) (lut : Array UInt32) (q : Array Int) :
    (fuel k : Nat) → BR → Array Int → BR × Array Int
  | 0, _, br, coef => (br, coef)
  | fuel + 1, k, br, coef =>
    if 63 < k then (br, coef) else
    let br := refill d br
    let (rs, br) := decodeSym lut br
    let r := rs / 16
    let s := rs % 16
    if s = 0 then
      if r = 15 then acLoop d lut q fuel (k + 16) br coef else (br, coef)
    else
      let k := k + r
      let (v, br) := receiveExtend br s
      let z := natural.getD k 63
      acLoop d lut q fuel (k + 1) br (coef.setIfInBounds z (v * q.getD z 0))

/-- Decode one 8×8 block: the DC difference (added to the prediction `pred`) and the AC
coefficients; returns the reader, the new prediction and the dequantised coefficients. -/
def decodeBlock (d : ByteArray) (dcT acT : Array UInt32) (q : Array Int) (br : BR) (pred : Int) :
    BR × Int × Array Int :=
  let br := refill d br
  let (s, br) := decodeSym dcT br
  let (diff, br) := receiveExtend br s
  let dc := pred + diff
  let coef := (Array.replicate 64 (0 : Int)).setIfInBounds 0 (dc * q.getD 0 0)
  let (br, coef) := acLoop d acT q 63 1 br coef
  (br, dc, coef)

/-! ## 4. Inverse DCT (libjpeg `jpeg_idct_islow`) -/

/-- Coefficient `i` (`0` out of range). -/
@[inline] def g (a : Array Int) (i : Nat) : Int := a.getD i 0

/-- `DESCALE(x, n)`: `x / 2ⁿ` rounded (arithmetic shift). -/
@[inline] def descale (x : Int) (n : Nat) : Int := (x + (2 ^ (n - 1) : Nat)) >>> n

/-- libjpeg's IDCT range limit: the low 10 bits of `x` index a table mapping `[-128, 127]`
to `0 … 255`, `[128, 511]` to 255 and `[-512, -129]` to 0 (`prepare_range_limit_table`). -/
@[inline] def rangeLimit (x : Int) : UInt8 :=
  let v := (x % 1024).toNat
  if v < 128 then UInt8.ofNat (v + 128)
  else if v < 512 then 255
  else if v < 896 then 0
  else UInt8.ofNat (v - 896)

/-- Pass 1 on column `col`: coefficients (stride 8) to the workspace, scaled by `2²`. -/
def pass1 (c : Array Int) (col : Nat) (ws : Array Int) : Array Int :=
  let i0 := g c col
  let i1 := g c (col + 8)
  let i2 := g c (col + 16)
  let i3 := g c (col + 24)
  let i4 := g c (col + 32)
  let i5 := g c (col + 40)
  let i6 := g c (col + 48)
  let i7 := g c (col + 56)
  if i1 == 0 && i2 == 0 && i3 == 0 && i4 == 0 && i5 == 0 && i6 == 0 && i7 == 0 then
    let dc := i0 * 4
    ((((((((ws.setIfInBounds col dc).setIfInBounds (col + 8) dc).setIfInBounds (col + 16) dc
      ).setIfInBounds (col + 24) dc).setIfInBounds (col + 32) dc).setIfInBounds (col + 40) dc
      ).setIfInBounds (col + 48) dc).setIfInBounds (col + 56) dc)
  else
    let z1 := (i2 + i6) * 4433
    let tmp2 := z1 - i6 * 15137
    let tmp3 := z1 + i2 * 6270
    let tmp0 := (i0 + i4) * 8192
    let tmp1 := (i0 - i4) * 8192
    let tmp10 := tmp0 + tmp3
    let tmp13 := tmp0 - tmp3
    let tmp11 := tmp1 + tmp2
    let tmp12 := tmp1 - tmp2
    let z1 := i7 + i1
    let z2 := i5 + i3
    let z3 := i7 + i3
    let z4 := i5 + i1
    let z5 := (z3 + z4) * 9633
    let z1 := z1 * (-7373)
    let z2 := z2 * (-20995)
    let z3 := z3 * (-16069) + z5
    let z4 := z4 * (-3196) + z5
    let t0 := i7 * 2446 + z1 + z3
    let t1 := i5 * 16819 + z2 + z4
    let t2 := i3 * 25172 + z2 + z3
    let t3 := i1 * 12299 + z1 + z4
    ((((((((ws.setIfInBounds col (descale (tmp10 + t3) 11)).setIfInBounds (col + 56)
      (descale (tmp10 - t3) 11)).setIfInBounds (col + 8) (descale (tmp11 + t2) 11)
      ).setIfInBounds (col + 48) (descale (tmp11 - t2) 11)).setIfInBounds (col + 16)
      (descale (tmp12 + t1) 11)).setIfInBounds (col + 40) (descale (tmp12 - t1) 11)
      ).setIfInBounds (col + 24) (descale (tmp13 + t0) 11)).setIfInBounds (col + 32)
      (descale (tmp13 - t0) 11))

/-- Pass 2 on workspace row `row`: eight samples written at byte `o` of `buf`. -/
def pass2 (ws : Array Int) (row : Nat) (buf : ByteArray) (o : Nat) : ByteArray :=
  let b := row * 8
  let i0 := g ws b
  let i1 := g ws (b + 1)
  let i2 := g ws (b + 2)
  let i3 := g ws (b + 3)
  let i4 := g ws (b + 4)
  let i5 := g ws (b + 5)
  let i6 := g ws (b + 6)
  let i7 := g ws (b + 7)
  if i1 == 0 && i2 == 0 && i3 == 0 && i4 == 0 && i5 == 0 && i6 == 0 && i7 == 0 then
    let v := rangeLimit (descale i0 5)
    setB (setB (setB (setB (setB (setB (setB (setB buf o v) (o + 1) v) (o + 2) v) (o + 3) v)
      (o + 4) v) (o + 5) v) (o + 6) v) (o + 7) v
  else
    let z1 := (i2 + i6) * 4433
    let tmp2 := z1 - i6 * 15137
    let tmp3 := z1 + i2 * 6270
    let tmp0 := (i0 + i4) * 8192
    let tmp1 := (i0 - i4) * 8192
    let tmp10 := tmp0 + tmp3
    let tmp13 := tmp0 - tmp3
    let tmp11 := tmp1 + tmp2
    let tmp12 := tmp1 - tmp2
    let z1 := i7 + i1
    let z2 := i5 + i3
    let z3 := i7 + i3
    let z4 := i5 + i1
    let z5 := (z3 + z4) * 9633
    let z1 := z1 * (-7373)
    let z2 := z2 * (-20995)
    let z3 := z3 * (-16069) + z5
    let z4 := z4 * (-3196) + z5
    let t0 := i7 * 2446 + z1 + z3
    let t1 := i5 * 16819 + z2 + z4
    let t2 := i3 * 25172 + z2 + z3
    let t3 := i1 * 12299 + z1 + z4
    let buf := setB buf o (rangeLimit (descale (tmp10 + t3) 18))
    let buf := setB buf (o + 7) (rangeLimit (descale (tmp10 - t3) 18))
    let buf := setB buf (o + 1) (rangeLimit (descale (tmp11 + t2) 18))
    let buf := setB buf (o + 6) (rangeLimit (descale (tmp11 - t2) 18))
    let buf := setB buf (o + 2) (rangeLimit (descale (tmp12 + t1) 18))
    let buf := setB buf (o + 5) (rangeLimit (descale (tmp12 - t1) 18))
    let buf := setB buf (o + 3) (rangeLimit (descale (tmp13 + t0) 18))
    setB buf (o + 4) (rangeLimit (descale (tmp13 - t0) 18))

/-- **Inverse DCT** of a dequantised block (natural order) into `buf` at byte `o`, rows
`stride` bytes apart (libjpeg `jpeg_idct_islow`, bit-exact). -/
def idctStore (coef : Array Int) (buf : ByteArray) (o stride : Nat) : ByteArray := Id.run do
  let mut ws : Array Int := Array.replicate 64 0
  for col in [0:8] do
    ws := pass1 coef col ws
  let mut buf := buf
  for row in [0:8] do
    buf := pass2 ws row buf (o + row * stride)
  return buf

/-! ## 5. Scans -/

/-- A component of a scan: plane offset and stride, blocks per MCU (`h × v`; `1 × 1` in a
non-interleaved scan), its Huffman and quantisation tables. -/
structure SComp where
  /-- Index in the frame. -/
  idx : Nat
  /-- Plane offset in the plane buffer. -/
  off : Nat
  /-- Plane stride. -/
  stride : Nat
  /-- Horizontal blocks per MCU. -/
  h : Nat
  /-- Vertical blocks per MCU. -/
  v : Nat
  /-- DC lookup table. -/
  dc : Array UInt32
  /-- AC lookup table. -/
  ac : Array UInt32
  /-- Quantisation table (natural order). -/
  q : Array Int
  deriving Inhabited

/-- Find the next marker from `i` (at most `fuel` bytes): skips data bytes, stuffed `FF 00`
and fill bytes; returns the marker code and the position after it. -/
def nextMarker (d : ByteArray) : (fuel i : Nat) → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, i =>
    if d.size ≤ i + 1 then none
    else if rd d i = 0xFF then
      let c := rd d (i + 1)
      if c = 0 then nextMarker d fuel (i + 2)
      else if c = 0xFF then nextMarker d fuel (i + 1)
      else some (c, i + 2)
    else nextMarker d fuel (i + 1)

/-- Process a restart: discard the buffered bits, find the next marker, and consume it when
it is an `RSTn` (any `n`); otherwise the reader stops at it (zero bits follow). -/
def restart (d : ByteArray) (br : BR) : BR :=
  match nextMarker d d.size br.pos with
  | some (c, after) =>
    if 0xD0 ≤ c ∧ c ≤ 0xD7 then { pos := after }
    else { pos := after - 2, stop := true }
  | none => { pos := d.size, stop := true }

/-- **Decode a scan** from byte `pos`: `mcusX × mcusY` MCUs (a non-interleaved scan: blocks),
each the blocks of every scan component in order, written into the plane buffer through the
IDCT; restart every `ri` MCUs. Returns the buffer and the position where the reader stopped. -/
def decodeScan (d : ByteArray) (cs : Array SComp) (mcusX mcusY ri pos : Nat) (buf : ByteArray) :
    ByteArray × Nat := Id.run do
  let mut br : BR := { pos }
  let mut preds : Array Int := Array.replicate cs.size 0
  let mut buf := buf
  let mut m := 0
  for my in [0:mcusY] do
    for mx in [0:mcusX] do
      if 0 < ri ∧ 0 < m ∧ m % ri = 0 then
        br := restart d br
        preds := Array.replicate cs.size 0
      m := m + 1
      for ci in [0:cs.size] do
        let c := cs.getD ci default
        for by_ in [0:c.v] do
          for bx in [0:c.h] do
            let r := decodeBlock d c.dc c.ac c.q br (preds.getD ci 0)
            br := r.1
            preds := preds.setIfInBounds ci r.2.1
            buf := idctStore r.2.2 buf
              (c.off + ((my * c.v + by_) * 8) * c.stride + (mx * c.h + bx) * 8) c.stride
  return (buf, br.pos)

/-! ## 6. Segments -/

/-- Parse a `DQT` segment body `[a, e)` (several tables). -/
def parseDQT (d : ByteArray) (a e : Nat) (qt : Array (Array Int)) : Except Error (Array (Array Int)) := do
  let mut p := a
  let mut qt := qt
  for _ in [0:4 * 16] do
    if e ≤ p then break
    let pq := rd d p / 16
    let tq := rd d p % 16
    if 1 < pq ∨ 3 < tq then throw (bad p "bad DQT table")
    let n := if pq = 0 then 64 else 128
    if e < p + 1 + n then throw (bad p "DQT segment too short")
    let mut t : Array Int := Array.replicate 64 0
    for k in [0:64] do
      let v := if pq = 0 then rd d (p + 1 + k) else rd16 d (p + 1 + 2 * k)
      t := t.setIfInBounds (natural.getD k 0) (v : Int)
    qt := qt.setIfInBounds tq t
    p := p + 1 + n
  return qt

/-- Parse a `DHT` segment body `[a, e)` (several tables). -/
def parseDHT (d : ByteArray) (a e : Nat) (st : St) : Except Error St := do
  let mut p := a
  let mut st := st
  for _ in [0:8 * 4] do
    if e ≤ p then break
    let tc := rd d p / 16
    let th := rd d p % 16
    if 1 < tc ∨ 3 < th then throw (bad p "bad DHT table class or index")
    if e < p + 17 then throw (bad p "DHT segment too short")
    let counts := (Array.range 16).map fun i => rd d (p + 1 + i)
    let total := counts.foldl (· + ·) 0
    if e < p + 17 + total then throw (bad p "DHT segment too short")
    let syms := (Array.range total).map fun i => rd d (p + 17 + i)
    let lut ← buildHuff counts syms (tc = 0)
    st := if tc = 0 then { st with dc := st.dc.setIfInBounds th lut }
      else { st with ac := st.ac.setIfInBounds th lut }
    p := p + 17 + total
  return st

/-- Parse a frame header body at `a` (length `len`), check it against the limits, and
allocate the component planes (filled with 128, the level of an all-zero block). -/
def parseSOF (limits : Limits) (d : ByteArray) (a len : Nat) (st : St) : Except Error St := do
  if st.frame.isSome then throw (bad a "several frame headers")
  if len < 6 then throw (bad a "SOF segment too short")
  let prec := rd d a
  let h := rd16 d (a + 1)
  let w := rd16 d (a + 3)
  let nf := rd d (a + 5)
  if prec ≠ 8 then throw (.unsupported s!"DCT: {prec}-bit samples")
  if h = 0 then throw (.unsupported "DCT: height defined by DNL")
  if w = 0 then throw (bad a "empty image")
  if nf = 0 ∨ 4 < nf then throw (.unsupported s!"DCT: {nf} components")
  if len < 6 + 3 * nf then throw (bad a "SOF segment too short")
  if limits.maxImagePixels < w * h then throw (.limitExceeded .imagePixels)
  let mut comps : Array Comp := #[]
  for i in [0:nf] do
    let b := a + 6 + 3 * i
    let hv := rd d (b + 1)
    let c : Comp := { id := rd d b, h := hv / 16, v := hv % 16, tq := rd d (b + 2) }
    if c.h = 0 ∨ 4 < c.h ∨ c.v = 0 ∨ 4 < c.v then throw (bad b "bad sampling factor")
    if 3 < c.tq then throw (bad b "bad quantisation table selector")
    comps := comps.push c
  let hmax := comps.foldl (fun m c => max m c.h) 1
  let vmax := comps.foldl (fun m c => max m c.v) 1
  if comps.any (fun c => hmax % c.h ≠ 0 ∨ vmax % c.v ≠ 0) then
    throw (.unsupported "DCT: fractional sampling")
  let mcusX := (w + 8 * hmax - 1) / (8 * hmax)
  let mcusY := (h + 8 * vmax - 1) / (8 * vmax)
  let mut offs : Array Nat := #[]
  let mut total := 0
  for c in comps do
    offs := offs.push total
    total := total + mcusX * c.h * 8 * (mcusY * c.v * 8)
  if limits.maxDecodedStreamBytes < total then throw (.limitExceeded .decodedStreamBytes)
  return { st with
    frame := some { w, h, comps, hmax, vmax, mcusX, mcusY, offs }
    buf := ByteArray.mk (Array.replicate total 128)
    done := Array.replicate nf false }

/-- Parse a scan header body at `a` (length `len`) and decode the scan that follows the
segment (at `e`); returns the new state and the position where decoding stopped. -/
def parseSOS (d : ByteArray) (a len e : Nat) (st : St) : Except Error (St × Nat) := do
  let some f := st.frame | throw (bad a "SOS before SOF")
  let ns := rd d a
  if ns = 0 ∨ 4 < ns ∨ len < 1 + 2 * ns + 3 then throw (bad a "bad scan header")
  let mut cs : Array SComp := #[]
  for i in [0:ns] do
    let b := a + 1 + 2 * i
    let cid := rd d b
    let some idx := f.comps.findIdx? (·.id = cid) | throw (bad b "scan component not in frame")
    let c := f.comps.getD idx default
    let td := rd d (b + 1) / 16
    let ta := rd d (b + 1) % 16
    let dcT := st.dc.getD td #[]
    let acT := st.ac.getD ta #[]
    if dcT.size ≠ 65536 ∨ acT.size ≠ 65536 then throw (bad b "Huffman table not defined")
    let q := st.qt.getD c.tq #[]
    if q.size ≠ 64 then throw (bad b "quantisation table not defined")
    cs := cs.push { idx, off := f.offs.getD idx 0, stride := f.stride c,
                    h := if ns = 1 then 1 else c.h, v := if ns = 1 then 1 else c.v,
                    dc := dcT, ac := acT, q }
  let (mx, my) : Nat × Nat :=
    if ns = 1 then
      let c := f.comps.getD ((cs.getD 0 default).idx) default
      ((f.dw c + 7) / 8, (f.dh c + 7) / 8)
    else (f.mcusX, f.mcusY)
  if 1 < ns ∧ 10 < cs.foldl (fun n c => n + c.h * c.v) 0 then
    throw (bad a "too many blocks in an MCU")
  let (buf, pos) := decodeScan d cs mx my st.ri e st.buf
  let done := cs.foldl (fun dn c => dn.setIfInBounds c.idx true) st.done
  return ({ st with buf, done, scans := st.scans + 1 }, pos)

/-- Is every frame component decoded? -/
def St.complete (st : St) : Bool := st.frame.isSome && st.done.all id

/-- **The marker loop** from byte `pos` (at most `fuel` segments): reads markers and
segments until `EOI`, the end of the data, or every component has been decoded. -/
def segLoop (limits : Limits) (d : ByteArray) : (fuel pos : Nat) → St → Except Error St
  | 0, _, st => .ok st
  | fuel + 1, pos, st =>
    if st.complete then .ok st else
    match nextMarker d d.size pos with
    | none => .ok st
    | some (m, p) =>
      if m = 0xD9 then .ok st
      else if (0xD0 ≤ m ∧ m ≤ 0xD8) ∨ m = 0x01 then segLoop limits d fuel p st
      else
        let len := rd16 d p
        let e := p + len
        if len < 2 ∨ d.size < e then .error (bad p "truncated segment")
        else
          let a := p + 2
          let body := len - 2
          if m = 0xC0 ∨ m = 0xC1 then
            match parseSOF limits d a body st with
            | .ok st => segLoop limits d fuel e st
            | .error err => .error err
          else if m = 0xC4 then
            match parseDHT d a e st with
            | .ok st => segLoop limits d fuel e st
            | .error err => .error err
          else if m = 0xDB then
            match parseDQT d a e st.qt with
            | .ok qt => segLoop limits d fuel e { st with qt }
            | .error err => .error err
          else if m = 0xDD then
            if body < 2 then .error (bad p "short DRI") else
            segLoop limits d fuel e { st with ri := rd16 d a }
          else if m = 0xDA then
            match parseSOS d a body e st with
            | .ok (st, q) => segLoop limits d fuel (max q e) st
            | .error err => .error err
          else if 0xC2 ≤ m ∧ m ≤ 0xCF ∧ m ≠ 0xC4 ∧ m ≠ 0xC8 ∧ m ≠ 0xCC then
            .error (.unsupported s!"DCT: SOF{m - 0xC0} (progressive, lossless or arithmetic)")
          else if m = 0xCC then .error (.unsupported "DCT: arithmetic coding")
          else if m = 0xE0 then
            let jfif := decide (14 ≤ body ∧ rd d a = 0x4A ∧ rd d (a + 1) = 0x46 ∧ rd d (a + 2) = 0x49 ∧
              rd d (a + 3) = 0x46 ∧ rd d (a + 4) = 0)
            segLoop limits d fuel e { st with jfif := st.jfif || jfif }
          else if m = 0xEE then
            let adobe := decide (12 ≤ body ∧ rd d a = 0x41 ∧ rd d (a + 1) = 0x64 ∧ rd d (a + 2) = 0x6F ∧
              rd d (a + 3) = 0x62 ∧ rd d (a + 4) = 0x65)
            segLoop limits d fuel e (if adobe then { st with adobe := some (rd d (a + 11)) } else st)
          else segLoop limits d fuel e st

/-! ## 7. Upsampling and colour conversion -/

/-- How a component is upsampled to full size (libjpeg-turbo `jinit_upsampler`). -/
inductive Up where
  /-- Full size. -/
  | full
  /-- `h2v1_fancy_upsample`. -/
  | h2v1
  /-- `h1v2_fancy_upsample`. -/
  | h1v2
  /-- `h2v2_fancy_upsample`. -/
  | h2v2
  /-- Replication by integral factors (`h2v1_upsample`, `h2v2_upsample`, `int_upsample`). -/
  | rep (hf vf : Nat)
  deriving Inhabited, DecidableEq

/-- The upsampling method of a component with expansion factors `hf × vf` and downsampled
width `dw`. -/
def upMode (hf vf dw : Nat) : Up :=
  if hf = 1 ∧ vf = 1 then .full
  else if hf = 2 ∧ vf = 1 ∧ 2 < dw then .h2v1
  else if hf = 1 ∧ vf = 2 then .h1v2
  else if hf = 2 ∧ vf = 2 ∧ 2 < dw then .h2v2
  else .rep hf vf

/-- **Upsample** component `c` of the plane buffer to a `w × h` plane. -/
def upsample (f : Frame) (buf : ByteArray) (ci : Nat) : ByteArray := Id.run do
  let c := f.comps.getD ci default
  let off := f.offs.getD ci 0
  let st := f.stride c
  let dw := f.dw c
  let dh := f.dh c
  let mode := upMode (f.hmax / c.h) (f.vmax / c.v) dw
  let px := fun (r i : Nat) => rd buf (off + r * st + i)
  let mut out := ByteArray.emptyWithCapacity (f.w * f.h)
  for y in [0:f.h] do
    match mode with
    | .full =>
      for x in [0:f.w] do
        out := out.push (UInt8.ofNat (px y x))
    | .h2v1 =>
      for x in [0:f.w] do
        let i := x / 2
        let v := 3 * px y i
        let o := if x % 2 = 0 then (v + px y (i - 1) + 1) / 4 else (v + px y (min (i + 1) (dw - 1)) + 2) / 4
        out := out.push (u8 o)
    | .h1v2 =>
      let j := y / 2
      let (nb, bias) := if y % 2 = 0 then (j - 1, 1) else (min (j + 1) (dh - 1), 2)
      for x in [0:f.w] do
        out := out.push (u8 ((3 * px j x + px nb x + bias) / 4))
    | .h2v2 =>
      let j := y / 2
      let nb := if y % 2 = 0 then j - 1 else min (j + 1) (dh - 1)
      let cs := fun (i : Nat) => 3 * px j i + px nb i
      for x in [0:f.w] do
        let i := x / 2
        let o := if x % 2 = 0 then (3 * cs i + cs (i - 1) + 8) / 16
          else (3 * cs i + cs (min (i + 1) (dw - 1)) + 7) / 16
        out := out.push (u8 o)
    | .rep hf vf =>
      for x in [0:f.w] do
        out := out.push (UInt8.ofNat (px (y / vf) (x / hf)))
  return out

/-- The colour conversion of the decoded components. -/
inductive Conv where
  /-- Samples as they are (gray, RGB, CMYK, two components). -/
  | none
  /-- YCbCr → RGB. -/
  | ycc
  /-- YCCK → CMYK. -/
  | ycck
  deriving Inhabited, DecidableEq, Repr

/-- The conversion libjpeg (`default_decompress_parms`) applies, with MuPDF's override: an
Adobe marker's transform replaces the PDF `/ColorTransform` `ct`, and transform 0 disables
conversion. -/
def convOf (nc : Nat) (ids : List Nat) (jfif : Bool) (adobe : Option Nat) (ct : Option Int) : Conv :=
  let ct := match adobe with
    | some t => some (t : Int)
    | none => ct
  if ct = some 0 then .none
  else if nc = 3 then
    if jfif then .ycc
    else if adobe.isSome then .ycc
    else if ids = [82, 71, 66] then .none
    else .ycc
  else if nc = 4 then (if adobe.isSome then .ycck else .none)
  else .none

/-- `Cr → R` table offset by 256: `⌊(91881 · (i − 128) + 2¹⁵) / 2¹⁶⌋ + 256`. -/
def crR : Array Nat := (Array.range 256).map fun (i : Nat) =>
  ((91881 * ((i : Int) - 128) + 32768) >>> 16 + 256).toNat

/-- `Cb → B` table offset by 256. -/
def cbB : Array Nat := (Array.range 256).map fun (i : Nat) =>
  ((116130 * ((i : Int) - 128) + 32768) >>> 16 + 256).toNat

/-- `Cr → G` term, offset by `2²³`: `−46802 · (i − 128) + 2²²`. -/
def crG : Array Nat := (Array.range 256).map fun (i : Nat) =>
  (-46802 * ((i : Int) - 128) + 8388608).toNat

/-- `Cb → G` term (with the rounding half), offset by `2²³`. -/
def cbG : Array Nat := (Array.range 256).map fun (i : Nat) =>
  (-22554 * ((i : Int) - 128) + 32768 + 8388608).toNat

/-- Clamp `v − 256` to a byte. -/
@[inline] def clampOff (v : Nat) : Nat := if v < 256 then 0 else min (v - 256) 255

/-- The three converted components of `(y, cb, cr)`: `(R, G, B)` (libjpeg `ycc_rgb_convert`;
the green term `⌊(cbG + crG) / 2¹⁶⌋` carries the offset `2²⁴ / 2¹⁶ = 256`). -/
@[inline] def yccPx (y cb cr : Nat) : Nat × Nat × Nat :=
  let r := clampOff (y + crR.getD cr 256)
  let gg := y + (cbG.getD cb 0 + crG.getD cr 0) / 65536
  let g := clampOff gg
  let b := clampOff (y + cbB.getD cb 256)
  (r, g, b)

/-- **Colour-convert** the upsampled planes (`w · h` bytes each) into interleaved output. -/
def convert (cv : Conv) (planes : Array ByteArray) (n : Nat) : ByteArray := Id.run do
  let nc := planes.size
  let p0 := planes.getD 0 ByteArray.empty
  let p1 := planes.getD 1 ByteArray.empty
  let p2 := planes.getD 2 ByteArray.empty
  let p3 := planes.getD 3 ByteArray.empty
  let mut out := ByteArray.emptyWithCapacity (n * nc)
  for i in [0:n] do
    match cv with
    | .ycc =>
      let (r, g, b) := yccPx (rd p0 i) (rd p1 i) (rd p2 i)
      out := ((out.push (UInt8.ofNat r)).push (UInt8.ofNat g)).push (UInt8.ofNat b)
    | .ycck =>
      let (r, g, b) := yccPx (rd p0 i) (rd p1 i) (rd p2 i)
      out := (((out.push (UInt8.ofNat (255 - r))).push (UInt8.ofNat (255 - g))).push
        (UInt8.ofNat (255 - b))).push (UInt8.ofNat (rd p3 i))
    | .none =>
      for j in [0:nc] do
        out := out.push (UInt8.ofNat (rd (planes.getD j ByteArray.empty) i))
  return out

/-! ## 8. Decoding -/

/-- A decoded JPEG: `nc` interleaved 8-bit components per pixel, row-major. -/
structure Image where
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat
  /-- Components per pixel (1–4). -/
  nc : Nat
  /-- The samples. -/
  data : ByteArray
  /-- One sample per component and pixel. -/
  size_eq : data.size = w * h * nc
  /-- At most four components. -/
  nc_le : nc ≤ 4

/-- Leading whitespace MuPDF skips before the `SOI` (`next_dctd`). -/
def skipWs (d : ByteArray) : (fuel i : Nat) → Nat
  | 0, i => i
  | fuel + 1, i =>
    let c := rd d i
    if i < d.size ∧ (c = 10 ∨ c = 13 ∨ c = 32) then skipWs d fuel (i + 1) else i

/-- Decode the planes of a JPEG stream: `SOI`, then the marker loop. -/
def decodePlanes (limits : Limits) (d : ByteArray) : Except Error St :=
  let p := skipWs d d.size 0
  if rd d p ≠ 0xFF ∨ rd d (p + 1) ≠ 0xD8 then .error (bad p "no SOI marker")
  else segLoop limits d d.size (p + 2) {}

/-- **Re-validate** the decoder's result: a frame with at least one decoded scan, at most
`Limits.maxImagePixels` pixels, and an output of exactly `w · h · nc` bytes, `nc ≤ 4`. -/
def finalize (limits : Limits) (ct : Option Int) (st : St) : Except Error Image :=
  match st.frame with
  | none => .error (bad 0 "no frame header")
  | some f =>
    if st.scans = 0 then .error (bad 0 "no scan")
    else if limits.maxImagePixels < f.w * f.h then .error (.limitExceeded .imagePixels)
    else if limits.maxDecodedStreamBytes < f.w * f.h * f.comps.size then
      .error (.limitExceeded .decodedStreamBytes)
    else
      let planes := (Array.range f.comps.size).map (upsample f st.buf)
      let cv := convOf f.comps.size (f.comps.toList.map (·.id)) st.jfif st.adobe ct
      let out := convert cv planes (f.w * f.h)
      if h1 : out.size = f.w * f.h * f.comps.size then
        if h2 : f.comps.size ≤ 4 then .ok ⟨f.w, f.h, f.comps.size, out, h1, h2⟩
        else .error (bad 0 "too many components")
      else .error (bad 0 "output size mismatch")

/-- **Decode a baseline JPEG** (`/DCTDecode` data, `ct` the PDF `/ColorTransform`). -/
def decode (limits : Limits) (ct : Option Int) (d : ByteArray) : Except Error Image :=
  (decodePlanes limits d).bind (finalize limits ct)

/-- `finalize` re-validates the pixel count. -/
theorem finalize_pixels {limits : Limits} {ct : Option Int} {st : St} {img : Image}
    (h : finalize limits ct st = .ok img) : img.w * img.h ≤ limits.maxImagePixels := by
  unfold finalize at h
  split at h
  · cases h
  · rename_i f _
    by_cases h1 : st.scans = 0
    · simp [h1] at h
    · by_cases h2 : limits.maxImagePixels < f.w * f.h
      · simp [h1, h2] at h
      · by_cases h3 : limits.maxDecodedStreamBytes < f.w * f.h * f.comps.size
        · simp [h1, h2, h3] at h
        · simp only [h1, h2, h3, ite_false] at h
          split at h
          · split at h
            · cases h; exact Nat.le_of_not_lt h2
            · cases h
          · cases h

/-- **A decoded JPEG has at most `Limits.maxImagePixels` pixels** (and, by construction,
`w · h · nc` samples with `nc ≤ 4`). -/
theorem decode_pixels {limits : Limits} {ct : Option Int} {d : ByteArray} {img : Image}
    (h : decode limits ct d = .ok img) : img.w * img.h ≤ limits.maxImagePixels := by
  unfold decode at h
  cases hp : decodePlanes limits d with
  | error e => rw [hp] at h; cases h
  | ok st => rw [hp] at h; exact finalize_pixels h

end SafePdf.Quarantine.DCT
