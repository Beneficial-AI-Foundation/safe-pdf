import JPEG2000.Image
import SafePdf.Core.Error
import SafePdf.Core.Limits

/-!
# JPEG 2000 image adapter (Plan.md §3, decoder integration plan §9, M10 task 10.2a)

`decode` takes the original PDF dimensions and the payload after preceding filters.
It uses the stages of the pinned pure JPEG2000 decoder, splitting header admission from
tile reconstruction to check the PDF dimensions first. Channel selection comes before
palette expansion and display scaling. This lets a PDF Indexed palette replace JP2
colour columns while still selecting an independently mapped JP2 opacity column.

The raster consumer passes the returned dimensions, `bpc := 8`, component count and
interleaved bytes to `Raster.Image.Src.ofPlan`. Use its resolved PDF conversion, or choose
one from the embedded space and profile. Indexed bytes use `Norm.index`. Mask bytes use
a separate one-component source; for a stencil use the stencil conversion with 8-bit
input. The caller owns PDF Decode, external masks, matte removal and compositing. In
particular the adapter reports associated colours unchanged so matte removal happens once.
`decodeChannels` also exposes exact signed samples and precisions for consumers that
need native sample units (e.g. colour keys or ICC conversion).
-/

namespace SafePdf.Quarantine.JPX

/-- Colour interpretation selected by the PDF image or mask dictionary. -/
inductive Colour where
  /-- Honour JP2 colour layout, palette, ICC or sYCC conversion. -/
  | embedded
  /-- Interpret mapped colour channels in the resolved PDF space, including DeviceN. -/
  | pdf (components : Nat)
  /-- Use the codestream index feeding the JP2 colour columns for the PDF's palette. -/
  | indexed
  /-- External soft mask or stencil: one colour channel, or a JP2 with only opacity. -/
  | mask
  /-- Extract the declared whole-image opacity from a JP2, even if it also has colours. -/
  | opacity
  deriving BEq, Inhabited

/-- PDF colour precedence, embedded soft-mask selection and wavelet reduction. -/
structure Options where
  colour : Colour := .embedded
  smaskInData : Nat := 0
  reduce : Nat := 0
  deriving Inhabited

/-- Reduced image geometry and colour metadata. Embedded space ranges refer to the input.
The embedded ICC profile bytes are retained only when the JP2 colour space governs. -/
structure Geometry where
  w : Nat
  h : Nat
  x0 : Nat
  y0 : Nat
  space : Option JPEG2000.Color.ColourSpace
  iccProfile : Option ByteArray

/-- Exact selected channels on the reduced reference grid. The optional soft mask records
whether the colours are premultiplied. -/
structure Channels extends Geometry where
  colours : Array JPEG2000.Channel
  indexed : Bool
  alpha : Option JPEG2000.SoftMask

/-- One byte of coverage per reduced pixel; associated colours require the PDF matte rule. -/
structure Alpha where
  data : ByteArray
  premultiplied : Bool

/-- Row-major eight-bit raster sources. Indexed bytes are literal indices, all other
colour and opacity samples are linearly scaled over their individual signed/depth ranges. -/
structure Image extends Geometry where
  nc : Nat
  data : ByteArray
  alpha : Option Alpha

private def byteCap (l : Limits) := min l.maxDecodedStreamBytes l.maxDecodedTotalBytes

private def byteLimit (l : Limits) : LimitKind :=
  if l.maxDecodedTotalBytes < l.maxDecodedStreamBytes then .decodedTotalBytes else .decodedStreamBytes

private def checkBytes (l : Limits) (n : Nat) : Except Error Unit :=
  if n ≤ byteCap l then pure () else throw (.limitExceeded (byteLimit l))

private def decoderLimits (l : Limits) : JPEG2000.Limits :=
  { maxInputBytes := l.maxInputBytes, maxImageArea := l.maxImagePixels,
    maxDecodedBytes := byteCap l }

private def translate (l : Limits) (e : JPEG2000.Error) : Error :=
  match e with
  | .malformed loc _ | .truncated loc _ => .malformed (loc.offset.getD 0) s!"JPX: {e}"
  | .unsupported .. => .unsupported s!"JPX: {e}"
  | .limitExceeded _ k _ _ => .limitExceeded (match k with
    | .inputBytes => .inputBytes
    | .imageSide | .imageArea => .imagePixels
    | .decodedBytes | .workSamples => byteLimit l
    -- No separate PDF limit kind exists for the decoder's packet and table quotas.
    | _ => .decodedStreamBytes)

private structure Selection where
  mapping : JPEG2000.Color.Mapping
  nc : Nat
  alphaAssociated : Option Bool

private def componentOf : JPEG2000.Color.Source → Nat
  | .direct c | .palette c _ => c

private def select (opts : Options) (mapping : JPEG2000.Color.Mapping)
    (layout : JPEG2000.Color.ChannelLayout) : Except Error Selection := do
  let source := fun (i : Nat) => mapping.sources[i]?.elim
    (throw (.malformed 0 "JPX: missing mapped channel")) pure
  let colours ← layout.colours.mapM source
  let alpha ← layout.alpha.mapM source
  let selected ← match opts.colour with
    | .pdf n =>
      if colours.size != n then
        throw (.malformed 0 s!"JPX: {colours.size} colours for {n}-component PDF colour space")
      pure colours
    | .indexed =>
      let some first := colours[0]? | throw (.malformed 0 "JPX: missing index channel")
      let index := componentOf first
      unless colours.all (fun c => componentOf c == index) do
        throw (.malformed 0 "JPX: Indexed colour channels use different codestream components")
      pure #[.direct index]
    | .mask =>
      if colours.size == 1 then pure colours
      else if colours.isEmpty && alpha.isSome then pure alpha.toArray
      else throw (.malformed 0 "JPX: mask needs one sample channel")
    | .opacity =>
      if alpha.isNone then throw (.malformed 0 "JPX: missing opacity channel")
      pure alpha.toArray
    | .embedded => pure colours
  if selected.isEmpty then throw (.malformed 0 "JPX: no colour channels")
  if selected.size > 32 then throw (.unsupported "JPX: raster supports at most 32 colour channels")
  let useAlpha := opts.smaskInData != 0 && opts.colour != .mask && opts.colour != .opacity
  let mask := if useAlpha then alpha else none
  return { mapping := { mapping with sources := selected ++ mask.toArray }, nc := selected.size,
           alphaAssociated := mask.map fun _ => opts.smaskInData == 2 || layout.premultiplied }

private def channelSelection (l : Limits) (L : JPEG2000.Limits) (opts : Options)
    (hdr : Option JPEG2000.Box.Jp2Header) (n : Nat) (known : Option Nat) :
    Except Error Selection := do
  let mapping ← match hdr with
    | some h => (JPEG2000.Color.resolveMapping L h n).mapError (translate l)
    | none => pure (JPEG2000.Color.identityMapping n)
  let defs := hdr.bind (·.cdef)
  -- CDEF identifies colour and opacity independently of COLR under a PDF override.
  -- Without CDEF, COLR can distinguish mapped colours from trailing auxiliary channels.
  let count := match opts.colour with
    | .embedded => known
    | .pdf k => if defs.isNone && known == some k then known else none
    | .indexed | .mask => if defs.isNone then known else none
    | .opacity => none
  let layout ← (JPEG2000.Color.channelLayout count mapping.sources.size defs).mapError (translate l)
  if opts.colour == .embedded && known.any (· != layout.colours.size) then
    throw (.malformed 0 "JPX: too few channels for embedded colour space")
  select opts mapping layout

/-- Decode selected channels at native precision. Both input forms use SIZ geometry.
Work-plane groups are bounded in cells using four bytes for compact samples and eight
when any native component needs wide storage. These and the decoder's logical byte
checks are per allocation group. The caller can pass the remaining document allowance
in `maxDecodedTotalBytes`; page and pixmap allocations are accounted for by raster. -/
def decodeChannels (l : Limits) (width height : Nat) (bytes : ByteArray) (opts : Options := {}) :
    Except Error Channels := do
  if width == 0 || height == 0 then throw (.malformed 0 "JPX: empty PDF image dimensions")
  if width * height > l.maxImagePixels then throw (.limitExceeded .imagePixels)
  if opts.smaskInData > 2 then throw (.malformed 0 "JPX: invalid /SMaskInData")
  let L := decoderLimits l
  let err := translate l
  (L.check JPEG2000.Decode.loc .decompLevels opts.reduce).mapError err
  let header ← (JPEG2000.Header.parse L bytes).mapError err
  let orig := JPEG2000.Header.imageRect header.siz
  if orig.width != width || orig.height != height then
    throw (.malformed 0 s!"JPX: SIZ {orig.width}×{orig.height} differs from PDF {width}×{height}")
  let rect := JPEG2000.Assemble.reduceRect orig opts.reduce
  if rect.width == 0 || rect.height == 0 then throw (.unsupported "JPX: empty reduced image grid")
  let area := rect.width * rect.height
  let cellBytes := if header.siz.components.all JPEG2000.NativeOutput.compact then 4 else 8
  let L := { L with maxWorkSamples := min L.maxWorkSamples (byteCap l / cellBytes) }
  let hdr := header.container.bind (·.header)
  let space := hdr.map JPEG2000.Color.resolveColourSpace |>.getD .unknown
  let selection ← channelSelection l L opts hdr header.siz.components.size (space.numColours bytes)
  let profile := match opts.colour, space with
    | .embedded, .icc range => some range
    | _, _ => none
  checkBytes l (area * selection.mapping.sources.size + (profile.map (·.len)).getD 0)
  let decoded ← (JPEG2000.Decode.nativeFromHeader L header bytes opts.reduce).mapError err
  let comps : Array JPEG2000.Color.Channel := decoded.comps.map fun c =>
    { plane := c.samples, format := { depth := c.depth, signed := c.signed, dx := c.dx, dy := c.dy } }
  let mapped ← (JPEG2000.Color.applyMapping L selection.mapping comps).mapError err
  let sycc := space == .sYCC || (space == .unknown && JPEG2000.Image.looksSycc decoded.comps)
  let (space, mapped) ←
    if opts.colour == .embedded && sycc then
      (JPEG2000.Image.convertSycc L rect.x0 rect.y0 (Array.range selection.nc) mapped).mapError err
    else pure (space, mapped)
  let fresh := mapped.foldl (fun cells c =>
    if JPEG2000.Image.atFullRes rect.width rect.height c then cells else cells + area) 0
  (L.check JPEG2000.Image.loc .workSamples fresh).mapError err
  checkBytes l (mapped.foldl (fun size c => size + area * JPEG2000.Header.bytesPerSample c.format.depth) 0)
  let full ← mapped.mapM fun c => do
    let plane ← (JPEG2000.Image.upsample rect.x0 rect.y0 rect.width rect.height c).mapError err
    pure ({ plane, depth := c.format.depth, signed := c.format.signed } : JPEG2000.Channel)
  let alpha ← selection.alphaAssociated.mapM fun premultiplied => do
    let channel ← (JPEG2000.Image.pick full selection.nc).mapError err
    pure ({ channel, premultiplied } : JPEG2000.SoftMask)
  return { w := rect.width, h := rect.height, x0 := rect.x0, y0 := rect.y0,
           space := if opts.colour == .embedded then some space else none,
           iccProfile := profile.map fun r => bytes.extract r.start (r.start + r.len),
           colours := full.extract 0 selection.nc, alpha, indexed := opts.colour == .indexed }

private def indexBytes (c : JPEG2000.Channel) (area : Nat) : Except Error ByteArray := do
  let mut out := ByteArray.emptyWithCapacity area
  for i in [0:area] do
    let some index := c.get? i | throw (.malformed 0 "JPX: missing index sample")
    -- PDF hival is at most 255. Preserve exact indices through that range; the PDF
    -- palette conversion subsequently clamps to its own hival.
    out := out.push (min 255 index.toNat).toUInt8
  return out

/-- Decode raster-ready source and mask bytes. Whole-image opacity is omitted for mode 0
and when the file has none. Mode 2 or an associated CDEF channel sets `premultiplied`. -/
def decode (l : Limits) (width height : Nat) (bytes : ByteArray) (opts : Options := {}) :
    Except Error Image := do
  let c ← decodeChannels l width height bytes opts
  let pack := fun cs => (JPEG2000.interleave (decoderLimits l) c.w c.h cs false).mapError (translate l)
  let data ← if c.indexed then do
      let some index := c.colours[0]? | throw (.malformed 0 "JPX: missing index channel")
      indexBytes index (c.w * c.h)
    else pack c.colours
  let alpha ← c.alpha.mapM fun m => do
    let data ← pack #[m.channel]
    pure ({ data, premultiplied := m.premultiplied } : Alpha)
  return { toGeometry := c.toGeometry, nc := c.colours.size, data, alpha }

end SafePdf.Quarantine.JPX
