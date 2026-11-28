import SafePdf.Quarantine.JPX
import SafePdf.Core.Raster.Image

/-!
# JPX quarantine adapter (Plan.md §3, decoder integration plan §9, M10 task 10.2a)

All streams are synthetic. Each nonempty packet below encodes four specified samples:
OpenJPEG 2.5.3, lossless raw input, one component, one resolution, no MCT. The tests
assemble those independent packets into codestreams and build the JP2 boxes in Lean.
They need no external codec, generated file or corpus download.
-/

namespace SafePdf.Tests.JPX

open SafePdf.Quarantine.JPX

private abbrev Bytes := List UInt8

private def be (n v : Nat) : Bytes :=
  (List.range n).reverse.map fun i => (v >>> (8 * i)).toUInt8

private def segment (tag : UInt8) (body : Bytes) : Bytes :=
  [255, tag] ++ be 2 (2 + body.length) ++ body

private def stream (depth : Nat) (signed : Bool) (packets : List Bytes)
    (odd : Bool := false) (size : Nat × Nat := (4, 1)) : ByteArray :=
  let origin := if odd then 1 else 0
  let yEnd := if odd then 4 else size.2
  let fmt := (depth - 1 + (if signed then 128 else 0)).toUInt8
  let siz := segment 0x51 ([0, 0] ++ ([size.1, yEnd, origin, origin, size.1, yEnd, 0, 0] : List Nat).flatMap
    (be 4) ++ be 2 packets.length ++ packets.flatMap fun _ => [fmt, 1, 1])
  let cod := segment 0x52 [0, 0, 0, 1, 0, (if odd then 1 else 0), 4, 4, 0, 1]
  let qcd := segment 0x5c ([0x40, (depth * 8).toUInt8] ++ (if odd then [72, 72, 80] else []))
  let body := packets.flatten
  let sot := segment 0x90 ([0, 0] ++ be 4 (14 + body.length) ++ [0, 1])
  ByteArray.mk ([255, 0x4f] ++ siz ++ cod ++ qcd ++ sot ++ [255, 0x93] ++ body ++ [255, 0xd9]).toArray

-- Unsigned four-bit [0,1,2,3] and [15,8,0,7]. Signed twelve-bit [-2048,-1,0,2047].
private def indices : Bytes := [0xdf, 0x20, 0x30, 0x06, 0x5e, 0x55]
private def coverage : Bytes := [0xdf, 0x20, 0x40, 0x0e, 0x5a, 0xc5, 0xaf]
private def signedRamp : Bytes := [0xdf, 0xe0, 0x18, 0x06, 0xcb, 8, 0xa5, 0x7f, 0xc4]

private def box (kind : String) (body : Bytes) : Bytes :=
  be 4 (body.length + 8) ++ kind.toUTF8.toList ++ body

private def colr (space : Nat) : Bytes := box "colr" ([1, 0, 0] ++ be 4 space)

private def cdef (entries : List (Nat × Nat × Nat)) : Bytes :=
  box "cdef" (be 2 entries.length ++ entries.flatMap fun (i, t, k) => be 2 i ++ be 2 t ++ be 2 k)

private def jp2 (packets : List Bytes) (boxes : Bytes) : ByteArray :=
  let ihdr := box "ihdr" (be 4 1 ++ be 4 4 ++ be 2 packets.length ++ [3, 7, 0, 0])
  let brand := "jp2 ".toUTF8.toList
  ByteArray.mk (box "jP  " [13, 10, 135, 10] ++ box "ftyp" (brand ++ be 4 0 ++ brand) ++
    box "jp2h" (ihdr ++ boxes) ++ box "jp2c" (stream 4 false packets).toList).toArray

-- One raw index plane supplies RGB palette columns and a fourth, separate opacity column.
private def palette : ByteArray :=
  let pclr := box "pclr" ([0, 4, 4, 7, 7, 7, 7] ++
    [10, 20, 30, 255, 11, 21, 31, 127, 12, 22, 32, 0, 13, 23, 33, 63])
  let cmap := box "cmap" ((List.range 4).flatMap fun i => [0, 0, 1, i.toUInt8])
  jp2 [indices] (colr 16 ++ pclr ++ cmap ++ cdef [(0, 0, 1), (1, 0, 2), (2, 0, 3), (3, 1, 0)])

private def read (b : ByteArray) (colour : Colour) (mode := 0) (l : Limits := {}) :=
  decode l 4 1 b { colour, smaskInData := mode }

private def require (label : String) (ok : Bool) : Except Error Unit :=
  unless ok do throw (.malformed 0 label)

private def nativeAndSpaces : Except Error Unit := do
  let raw := stream 12 true [signedRamp]
  let native ← decodeChannels {} 4 1 raw
  let some c := native.colours[0]? | throw (.malformed 0 "missing signed channel")
  require "native signed 12-bit samples" (c.signed && c.depth == 12 &&
    (List.range 4).mapM c.get? == some [-2048, -1, 0, 2047])
  let grey ← read raw (.pdf 1) 1
  require "signed display rounding; no inferred opacity" (grey.data.toList == [0, 127, 128, 255] &&
    grey.alpha.isNone && grey.space.isNone)
  -- An empty packet reconstructs zero before the unsigned DC shift, even for wide storage.
  let wide := stream 38 false [[0]]
  let exact ← decodeChannels { maxDecodedStreamBytes := 32 } 4 1 wide
  require "38-bit exact sample" ((exact.colours[0]?.bind (·.get? 0)) == some (2 ^ 37))
  require "wide backing uses eight bytes per cell" (match read wide .embedded 0 { maxDecodedStreamBytes := 31 } with
    | .error (.limitExceeded .decodedStreamBytes) => true | _ => false)
  let devN := jp2 [indices, coverage, indices, coverage, indices] (colr 16)
  let five ← read devN (.pdf 5)
  require "PDF DeviceN supersedes JP2's three colour channels" (five.nc == 5 && five.data.toList ==
    [0,255,0,255,0, 17,136,17,136,17, 34,0,34,0,34, 51,119,51,119,51])
  let ycc := jp2 [indices, coverage, indices] (colr 18)
  let rgb ← read ycc .embedded
  let pdf ← read ycc (.pdf 3)
  require "sYCC conversion only under embedded colour" (rgb.space == some .sRGB && rgb.data != pdf.data &&
    pdf.data.toList == [0,255,0, 17,136,17, 34,0,34, 51,119,51])
  -- A four-channel profile, including bytes beyond the colour signature.
  let profile := List.replicate 16 (0 : UInt8) ++ "CMYK".toUTF8.toList ++ List.replicate 108 0
  let icc := jp2 [indices, coverage, indices, coverage] (box "colr" ([2,0,0] ++ profile))
  let four ← read icc .embedded
  require "ICC bytes and four source channels" (four.nc == 4 && four.iccProfile.map ByteArray.toList ==
    some profile && four.data.toList == [0,255,0,255, 17,136,17,136, 34,0,34,0, 51,119,51,119])
  let ignored ← read icc (.pdf 4) 0 { maxDecodedStreamBytes := 64 }
  require "PDF override does not charge a discarded ICC profile" ignored.iccProfile.isNone
  -- 16 bytes of samples + 128 bytes of profile, independently of decoder work (64 bytes).
  require "combined returned byte budget" (match read icc .embedded 0 { maxDecodedStreamBytes := 143 } with
    | .error (.limitExceeded .decodedStreamBytes) => true | _ => false)
  let _ ← read icc .embedded 0 { maxDecodedStreamBytes := 144 }

private def indexed : Except Error Unit := do
  let embedded ← read palette .embedded
  require "embedded palette expanded" (embedded.data.toList == [10,20,30,11,21,31,12,22,32,13,23,33])
  let img ← read palette .indexed 1
  require "unscaled indices with mapped alpha" (img.nc == 1 && img.data.toList == [0,1,2,3] &&
    img.alpha.map (·.data.toList) == some [255,127,0,63])
  -- Feed literal byte indices through the actual row sampler and a different PDF palette.
  let dict : Core.Raster.Image.ImgDict :=
    { w := img.w, h := img.h, bpc := none, mask := false, decode := none, interp := false, cs := none }
  let table := ByteArray.mk #[1,2,3, 4,5,6, 7,8,9, 10,11,12]
  let src := Core.Raster.Image.Src.ofPlan dict 8 img.nc (.pal false table) .index img.data
  require "PDF Indexed survives Src.row" ((src.row 4 0).toList == [1,2,3,255,4,5,6,255,7,8,9,255,10,11,12,255])
  let _ ← read palette .indexed 0 { maxDecodedStreamBytes := 16 }
  let clipped ← read (stream 12 true [signedRamp]) .indexed
  require "signed and over-byte indices clamp in index units" (clipped.data.toList == [0,0,0,255])

private def opacity : Except Error Unit := do
  -- Deliberately put opacity first; channel association, not position, determines its role.
  let file := fun typ => jp2 [coverage, indices] (colr 17 ++ cdef [(0,typ,0), (1,0,1)])
  for (mode, typ, associated) in [(1,1,false), (2,1,true), (1,2,true)] do
    let img ← read (file typ) (.pdf 1) mode
    require "selected colours and opacity association" (img.data.toList == [0,17,34,51] &&
      img.alpha.map (·.data.toList) == some [255,136,0,119] && img.alpha.map (·.premultiplied) == some associated)
  let ordinary ← read (file 2) .embedded
  require "mode 0 ignores opacity" (ordinary.alpha.isNone && ordinary.data.toList == [0,17,34,51])
  let alpha ← read (file 1) .opacity
  require "four-bit soft-mask samples cannot serve as a stencil" (match read (file 1) .stencil with
    | .error (.malformed ..) => true | _ => false)
  let stencil ← read (stream 1 false [[0]]) .stencil
  require "one-bit stencil is represented at display depth" (stencil.data.toList == [255,255,255,255])
  let gray ← read (file 1) .mask
  let only ← read (jp2 [coverage] (colr 17 ++ cdef [(0,1,0)])) .mask
  require "mask stream and explicit opacity extraction" (alpha.data.toList == [255,136,0,119] &&
    only.data == alpha.data && gray.data == ordinary.data && only.alpha.isNone)
  let profile := List.replicate 16 (0 : UInt8) ++ "GRAY".toUTF8.toList ++ List.replicate 108 0
  let icc := jp2 [coverage, indices] (box "colr" ([2,0,0] ++ profile) ++ cdef [(0,1,0), (1,0,1)])
  let tight : Limits := { maxDecodedTotalBytes := 135 }
  let _ ← read icc .embedded 0 tight
  require "colour, opacity and profile share output allowance" (match read icc .embedded 1 tight with
    | .error (.limitExceeded .decodedTotalBytes) => true | _ => false)
  let _ ← read icc .embedded 1 { tight with maxDecodedTotalBytes := 136 }

private def geometryAndErrors : Except Error Unit := do
  let odd := stream 8 false [[128, 128]] true
  let opts : Options := { reduce := 1 }
  let small ← decode { maxImagePixels := 9, maxDecodedStreamBytes := 4 } 3 3 odd opts
  require "odd-origin reduced grid" ((small.x0, small.y0, small.w, small.h) == (1,1,1,1) &&
    small.data.toList == [128])
  let raw := stream 4 false [indices]
  let malformed := fun (r : Except Error Image) => match r with
    | .error (.malformed ..) => true | _ => false
  let limited := fun (r : Except Error Image) k => match r with
    | .error (.limitExceeded actual) => actual == k | _ => false
  require "dictionary matches reduced dimensions only" (malformed (decode {} 1 1 odd opts))
  require "component mismatch" (malformed (read raw (.pdf 2)))
  let badRGB := jp2 [indices] (colr 16)
  require "embedded RGB needs three channels" (malformed (read badRGB .embedded))
  let _ ← read badRGB (.pdf 1)
  require "Indexed colour needs one source component" (malformed
    (read (jp2 [indices, coverage, indices] (colr 16)) .indexed))
  require "invalid SMaskInData" (malformed (read raw (.pdf 1) 3))
  require "missing declared opacity" (malformed (read raw .opacity))
  require "truncated bytes" (malformed (read (raw.extract 0 13) .embedded))
  require "input bytes" (limited (read raw .embedded 0 { maxInputBytes := raw.size - 1 }) .inputBytes)
  require "full PDF area under reduction" (limited (decode { maxImagePixels := 8 } 3 3 odd opts) .imagePixels)
  require "full SIZ area under reduction" (limited (decode { maxImagePixels := 1 } 1 1 odd opts) .imagePixels)
  require "stream work budget, four four-byte cells" (limited
    (read raw .embedded 0 { maxDecodedStreamBytes := 15 }) .decodedStreamBytes)
  require "document work budget" (limited (read raw .embedded 0 { maxDecodedTotalBytes := 15 }) .decodedTotalBytes)
  let _ ← read raw .embedded 0 { maxDecodedStreamBytes := 16, maxInputBytes := raw.size }
  require "decoder unsupported reduction stays typed" (match decode {} 4 1 raw opts with
    | .error (.unsupported _) => true | _ => false)

open Core.Raster.Image (decodeInline loadXObject)
open Core.Content.Run (nm)

private def params (extras : Dict := []) : Dict :=
  let defaults : Dict := [(nm "Filter", .name (nm "JPXDecode")), (nm "Width", .int 4), (nm "Height", .int 1)]
  extras ++ defaults.filter fun kv => (Dict.get? extras kv.1).isNone

private def component (p : Core.Raster.Image.Pixmap) (n : Nat) :=
  (List.range (p.w * p.h)).map fun i => Core.Raster.Image.rd p.data (4 * i + n)

private def bareChannelRecovery : Except Error Unit := do
  let pair := stream 4 false [indices, coverage]
  let triple := stream 4 false [indices, coverage, indices]
  let undeclared ← decodeInline {} [] (params []) pair
  require "undeclared pair paints first channel as opaque gray" (undeclared.solid &&
    undeclared.data.toList == [0,0,0,255, 17,17,17,255, 34,34,34,255, 51,51,51,255])
  let withOpacity := fun space => params [(nm "ColorSpace", .name (nm space)), (nm "SMaskInData", .int 1)]
  let straight ← decodeInline {} [] (withOpacity "DeviceGray") pair
  require "declared gray with straight opacity keeps both planes" (straight.data.toList ==
    [0,0,0,255, 17,17,17,136, 34,34,34,0, 51,51,51,119])
  let rgb ← decodeInline {} [] (withOpacity "DeviceRGB") triple
  require "bare RGB with missing straight opacity paints opaque RGB" (rgb.solid &&
    rgb.data.toList == [0,255,0,255, 17,136,17,255, 34,0,34,255, 51,119,51,255])
  let opts := fun n => ({ colour := .pdf n, renderSpace := some .deviceN } : Options)
  let declared ← decode {} 4 1 pair (opts 2)
  let padded ← decode {} 4 1 pair (opts 4)
  require "all DeviceN tints stay in order with zeroes for absent inputs" (declared.data.toList ==
    [0,255, 17,136, 34,0, 51,119] && padded.data.toList ==
    [0,255,0,0, 17,136,0,0, 34,0,0,0, 51,119,0,0])
  let _ ← decode { maxDecodedTotalBytes := 128 } 4 1 pair (opts 32)
  require "padded output counts toward document budget" (match
      decode { maxDecodedTotalBytes := 127 } 4 1 pair (opts 32) with
    | .error (.limitExceeded .decodedTotalBytes) => true | _ => false)
  require "raster channel bound includes padded tints" (match decode {} 4 1 pair (opts 33) with
    | .error (.unsupported _) => true | _ => false)
  let malformed := fun {α : Type} (r : Except Error α) => match r with
    | .error (.malformed ..) => true | _ => false
  let raw ← read pair .embedded
  require "strict callers retain native arity and reject a mismatch" (raw.nc == 2 &&
    malformed (read pair (.pdf 4)) && malformed (read pair (.pdf 1) 1))
  require "missing device colours are not padded" (malformed
    (decode {} 4 1 pair { colour := .pdf 3, renderSpace := some .device }))
  require "JP2 layout still governs opacity and tints" (malformed
    (decodeInline {} [] (withOpacity "DeviceRGB") (jp2 [indices, coverage, indices] (colr 16))) &&
    malformed (decode {} 4 1 (jp2 [indices, coverage] (colr 17)) (opts 4)))

private def rasterColours : Except Error Unit := do
  let rev : PdfObject := .array [.int 1, .int 0]
  let ordinary ← decodeInline {} [] (params [(nm "BitsPerComponent", .int 1),
    (nm "Decode", rev), (nm "Interpolate", .bool true)]) (stream 4 false [indices])
  require "ordinary JPX ignores BPC and Decode" (ordinary.interpolate &&
    component ordinary 0 == [0,17,34,51] && ordinary.solid)
  let idx : PdfObject := .array [.name (nm "Indexed"), .name (nm "DeviceRGB"), .int 3,
    .string [1,2,3,4,5,6,7,8,9,10,11,12]]
  let pdf ← decodeInline {} [] (params [(nm "ColorSpace", idx)]) palette
  require "PDF Indexed overrides the JP2 palette" (component pdf 0 == [1,4,7,10])
  let embedded ← decodeInline {} [] (params [(nm "SMaskInData", .int 1)]) palette
  require "embedded palette and mapped opacity" (component embedded 0 == [10,11,12,13] &&
    component embedded 3 == [255,127,0,63])
  let keyed ← decodeInline {} [] (params [(nm "Mask", .array [.int (-1), .int 0])])
    (stream 12 true [signedRamp])
  require "key uses signed 12-bit units before scaling" (component keyed 3 == [255,0,0,255])
  let cmyk := jp2 [indices, coverage, indices, indices] (colr 12)
  let c ← decodeInline {} [] (params []) cmyk
  require "embedded enum 12 follows device CMYK" (component c 0 == [255,221,187,153] &&
    component c 1 == [0,102,221,85])
  let profile := List.replicate 16 (0 : UInt8) ++ "CMYK".toUTF8.toList ++ List.replicate 108 0
  let icc := jp2 [indices, coverage, indices, indices] (box "colr" ([2,0,0] ++ profile))
  let ci ← decodeInline {} [] (params []) icc
  require "embedded ICC CMYK device alternate" (ci.data == c.data)
  let dn : PdfObject := .array [.name (nm "DeviceN"), .array [.name (nm "A"), .name (nm "B")],
    .name (nm "DeviceGray"), .null]
  let d ← decodeInline {} [] (params [(nm "ColorSpace", dn)]) (jp2 [indices, coverage] (colr 16))
  require "DeviceN uses ordinary tint conversion" (component d 0 == [128,179,238,170])
  let mono := stream 1 false [[0]]
  let stencil := fun (ds : PdfObject) => params [(nm "ImageMask", .bool true), (nm "Decode", ds)]
  let normal ← decodeInline {} [] (stencil (.array [.int 0, .int 1])) mono
  let inverted ← decodeInline {} [] (stencil rev) mono
  require "stencil decode polarity once" (normal.stencil && inverted.stencil &&
    component normal 3 == [0,0,0,0] && component inverted 3 == [255,255,255,255])
  require "stencil rejects 4-bit data" (match decodeInline {} [] (stencil rev) (stream 4 false [indices]) with
    | .error (.malformed ..) => true | _ => false)

private def budgetSource (objs : List (Nat × IndirectBody)) : Core.Content.Source Core.Filter.Budget :=
  ⟨fun s n _ => ((objs.lookup n).elim (Except.error (.malformed 0 "missing object")) Except.ok, s),
   fun b _ st =>
     let (r, b) := Core.Filter.decodeStreamB {} b st.dict st.data
     (r.bind (fun | .data bytes => pure bytes | _ => throw (.malformed 0 "codec prefix")), b)⟩

private def rasterMasks : Except Error Unit := do
  let file := jp2 [coverage, indices] (colr 17 ++ cdef [(0,1,0), (1,0,1)])
  let sm := stream 4 false [indices]
  let reversed : PdfObject := .array [.int 1, .int 0]
  let mask : IndirectBody := .stream ⟨params [(nm "Decode", reversed)], sm⟩
  let main := fun (extra : Dict) => .stream ⟨params (extra ++ [(nm "Width", .ref 3 0),
      (nm "ColorSpace", .ref 4 0), (nm "Filter", .ref 5 0)]), file⟩
  let run := fun extra mode =>
    let src := budgetSource [(1, main extra), (2, mask), (3, .obj (.int 4)),
      (4, .obj (.name (nm "DeviceGray"))), (5, .obj (.name (nm "JPXDecode"))),
      (6, .obj (.int mode)), (7, .obj (.array [.ref 8 0])), (8, .obj (.int 1))]
    loadXObject {} src ⟨4096⟩ [] 1 0 none .document
  let smRef := (nm "SMask", PdfObject.ref 2 0)
  let ext ← (run [smRef] 0).1
  require "external JPX SMask omits BPC and ignores ordinary Decode"
    (component ext 3 == [0,17,34,51] && component ext 0 == [0,17,34,51])
  let prof : PdfObject := .array [.name (nm "ICCBased"), .ref 11 0]
  let iccSrc := budgetSource [(1, .stream ⟨params [(nm "ColorSpace", .ref 10 0)], file⟩),
    (10, .obj prof), (11, .stream ⟨[(nm "N", .ref 12 0), (nm "Alternate", .ref 4 0)], {}⟩),
    (12, .obj (.int 1)), (4, .obj (.name (nm "DeviceGray")))]
  let icc ← (loadXObject {} iccSrc ⟨4096⟩ [] 1 0 none .document).1
  require "indirect ICCBased /N and alternate" (icc.solid && component icc 0 == [0,17,34,51])
  let embedded := fun mode => run [smRef, (nm "SMaskInData", .ref 6 0), (nm "Matte", .ref 7 0)] mode
  let (r, remaining) := embedded 1
  let one ← r
  require "external stream skipped; prefix, planes and RGBA charged exactly once"
    (remaining.remaining == 4096 - file.size - 8 - 16 && component one 0 == component ext 0 &&
      component one 3 == [255,136,0,119])
  let two ← (embedded 2).1
  require "associated samples unblended once against indirect white matte"
    (component two 0 == [0,0,34,0] && component two 3 == [255,136,0,119])
  let black ← decodeInline {} [] (params [(nm "SMaskInData", .int 2)]) file
  require "associated samples without matte" (component black 0 == [0,31,34,109])
  let base := stream 4 false [indices]
  let ref := (nm "Mask", PdfObject.ref 2 0)
  let stencil : IndirectBody := .stream ⟨params [(nm "ImageMask", .bool true)], stream 1 false [[0]]⟩
  let st ← (loadXObject {} (budgetSource [(1, .stream ⟨params [ref], base⟩), (2, stencil)])
    ⟨4096⟩ [] 1 0 none .document).1
  require "external explicit JPX stencil reads coverage" (component st 3 == [0,0,0,0])

private def rasterBounds : Except Error Unit := do
  let raw := stream 4 false [indices]
  let limited := fun (r : Except Error Core.Raster.Image.Pixmap) k => match r with
    | .error (.limitExceeded actual) => actual == k | _ => false
  let source := budgetSource [(1, .stream ⟨params [], raw⟩)]
  require "document allowance after prefix" (limited
    (loadXObject {} source ⟨raw.size + 15⟩ [] 1 0 none .document).1 .decodedTotalBytes)
  require "inline prefix consumes document allowance" (limited
    (decodeInline { maxDecodedTotalBytes := raw.size + 15 } [] (params []) raw) .decodedTotalBytes)
  require "inline original image area" (limited (decodeInline { maxImagePixels := 3 } [] (params []) raw) .imagePixels)
  require "original dimensions checked" (match decodeInline {} [] (params [(nm "Width", .int 3)]) raw with
    | .error (.malformed ..) => true | _ => false)
  let odd := stream 8 false [[128,128]] true
  let small ← decode { maxDecodedStreamBytes := 4 } 3 3 odd { reduce := 5, fit := true }
  require "requested scale clamps to actual shared level and nonempty grid" (small.w == 1 && small.h == 1)
  let fallback ← decode { maxDecodedStreamBytes := 4 } 3 3 odd { fit := true }
  require "byte limit retries at an available coarser level" (fallback.data == small.data)
  let full ← decode {} 4 1 raw { reduce := 6, fit := true }
  require "wavelet-free stream still drawable" (full.w == 4 && full.data.toList == [0,17,34,51])

private def rasterPlacement : Except Error Unit := do
  -- One literal RunLength packet delivers a zero-decomposition codestream.
  let raw := stream 4 false [[0]] false (64, 64)
  let encoded := (ByteArray.mk #[(raw.size - 1).toUInt8] ++ raw).push 128
  let d := params [(nm "Width", .int 64), (nm "Height", .int 64),
    (nm "Filter", .array [.name (nm "RunLengthDecode"), .name (nm "JPXDecode")])]
  let src := budgetSource [(1, .stream ⟨d, encoded⟩)]
  let lim : Limits := {}
  let ext := Core.Raster.Image.Extent.ofDev Core.Raster.Geom.Aff.id
  let (xo, b) := loadXObject lim src ⟨100000⟩ [] 1 0 (some ext) .document
  let pm ← xo
  require "small projected XObject with no wavelet levels" (pm.w == 1 && pm.h == 1 &&
    pm.data.toList == [136,136,136,255] && b.remaining == 100000 - raw.size - 4096 - 4)
  let isrc := Core.Content.ImageSource.inline d encoded
  let item := Core.Content.DisplayItem.image isrc Core.Content.Matrix.identity
    { color := .gray Core.Content.Comp.zero, alpha := Core.Content.Comp.one } []
  let table : Core.Raster.Image.ImageTable := {}
  let (tab, b) := table.loadInlineJPX ⟨100000⟩ (some Core.Raster.Geom.Aff.id) #[item,item]
  let some cached := tab.pixmap isrc (some ext) | throw (.malformed 0 "missing inline JPX")
  require "inline JPX prefix, page charge and reuse" (cached.data == pm.data && tab.pixels == 1 &&
    tab.inlineJPX.length == 1 && b.remaining == 100000 - raw.size - 4096 - 4)
  let tight := { table with pixels := Core.Raster.Image.maxPageImagePixels - 1 }
  let (tight, _) := tight.loadInlineJPX ⟨100000⟩ (some Core.Raster.Geom.Aff.id) #[item]
  require "inline page quota survives cache lookup" ((tight.pixmap isrc (some ext)).isNone &&
    tight.pixels == Core.Raster.Image.maxPageImagePixels - 1)

/-- Run the deterministic JPX adapter tests and return the number of failed groups. -/
def run : IO Nat := do
  let mut failures := 0
  for (label, result) in [("native and colour", nativeAndSpaces), ("Indexed", indexed),
      ("opacity", opacity), ("geometry and errors", geometryAndErrors), ("bare channel recovery", bareChannelRecovery),
      ("raster colour", rasterColours), ("raster masks", rasterMasks), ("raster bounds", rasterBounds),
      ("raster placement", rasterPlacement)] do
    if let .error err := result then
      IO.eprintln s!"  FAIL JPX {label}: {repr err}"
      failures := failures + 1
  return failures

end SafePdf.Tests.JPX
