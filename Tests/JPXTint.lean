import SafePdf.Core.Raster.Image

/-!
# JPX tint transforms (decoder Plan.md §9, M10.2t)

Render synthetic four-pixel image XObjects through the page image table. The three
calculator programs are those of the reviewed colour-channel grid in docs/jpx-pages.md.
The resource dictionary, space, colorants, alternate and function are indirect, and
the function stream has a byte filter. No corpus files are needed.
-/

namespace SafePdf.Tests.JPXTint

open Core Core.Content
open Core.Content.Run (nm)
open Core.Raster.Image (loadImages)

private abbrev Bytes := List UInt8

-- Four unsigned 4-bit samples per packet, lossless OpenJPEG, one resolution, no MCT.
-- A = [0,1,2,3], B = [15,8,0,7], Z = [0,0,0,0], E = [3,2,1,0].
private def a : Bytes := [0xdf, 0x20, 0x30, 0x06, 0x5e, 0x55]
private def b : Bytes := [0xdf, 0x20, 0x40, 0x0e, 0x5a, 0xc5, 0xaf]
private def z : Bytes := [0xdf, 0x20, 0x20, 0x09, 0x47]

private def e : Bytes := [0xdf, 0x20, 0x40, 0x10, 0x1c, 0xcd, 0xc7]

private def be (n v : Nat) : Bytes :=
  (List.range n).reverse.map fun i => (v >>> (8 * i)).toUInt8

private def stream (planes : List Bytes) : ByteArray :=
  let size := [0, 0] ++ ([4, 1, 0, 0, 4, 1, 0, 0] : List Nat).flatMap (be 4) ++
    be 2 planes.length ++ planes.flatMap fun _ => [3, 1, 1]
  let packets := planes.flatten
  ByteArray.mk ([255, 79, 255, 81] ++ be 2 (size.length + 2) ++ size ++
    [255, 82, 0, 12, 0, 0, 0, 1, 0, 0, 4, 4, 0, 1, 255, 92, 0, 4, 64, 32,
     255, 144, 0, 10, 0, 0] ++ be 4 (packets.length + 14) ++ [0, 1, 255, 147] ++
    packets ++ [255, 217]).toArray

private def unitRanges (n : Nat) : PdfObject :=
  .array ((List.replicate n [.int 0, .int 1]).flatten)

private def render (planes : List Bytes) (alternate : DeviceSpace) (program : String)
    (domain : Option Nat := none) (separation := false) (inlineImage := false) : Except Error Bytes := do
  let ref := fun n => PdfObject.ref n 0
  let space := PdfObject.array [if separation then .name (nm "Separation") else .name (nm "DeviceN"),
    if separation then .name (nm "Spot") else ref 4, ref 5, ref 6]
  let img : Dict := [(nm "ColorSpace", .name (nm "Inks")), (nm "Filter", .name (nm "JPXDecode")),
    (nm "Width", .int 4), (nm "Height", .int 1)]
  let f : Dict := [(nm "FunctionType", .int 4), (nm "Filter", .name (nm "ASCIIHexDecode")),
    (nm "Domain", ref 7), (nm "Range", ref 8)]
  let raw := stream planes
  let objects : List (Nat × IndirectBody) := [(1, .stream ⟨img, raw⟩),
    (2, .obj (.dict [(nm "Inks", ref 3)])), (3, .obj space),
    (4, .obj (.array ((List.range planes.length).map fun i => .name (nm s!"C{i}")))),
    (5, .obj (.name (Run.devName alternate))),
    (6, .stream ⟨f, Filter.Ascii.asciiHexEncode program.toUTF8⟩),
    (7, .obj (unitRanges (domain.getD planes.length))), (8, .obj (unitRanges alternate.nComps))]
  let src : Source Filter.Budget := {
    fetch := fun s n _ => ((objects.lookup n).elim (.error (.malformed 0 "missing object")) .ok, s)
    decode := fun s _ st =>
      let (r, s) := Filter.decodeStreamB {} s st.dict st.data
      (r.bind (fun | .data bytes => pure bytes | _ => throw (.malformed 0 "unexpected codec")), s) }
  let resources := [(nm "ColorSpace", ref 2)]
  let item := fun image => DisplayItem.image image Matrix.identity ({} : GState).fillStyle []
  let initial : Filter.Budget := ⟨4096⟩
  let (pm, budget) := if inlineImage then
    -- The form owns the resource, and the page image table has no binding for /Inks.
    let (d, s) := Run.annotInline src initial (Frame.mk' resources [] 99 0 Matrix.identity) img
    let image := ImageSource.inline d raw
    let (table, s) := ({} : Raster.Image.ImageTable).loadInlineJPXFrom src s none #[item image, item image]
    (table.pixmap image, s)
  else
    let image := ImageSource.xobject (nm "Im") 1 0
    let (table, s) := loadImages {} src initial resources #[item image, item image] [] .document
    (table.pixmap image, s)
  unless budget.remaining == initial.remaining - program.toUTF8.size - raw.size - 4 * planes.length - 16 do
    throw (.malformed 0 s!"unexpected remaining budget {budget.remaining}")
  let some pm := pm | throw (.malformed 0 "missing image")
  return pm.data.toList

private def check (actual : Except Error Bytes) (expected : Bytes) : Except Error Unit := do
  let got ← actual
  unless got == expected do throw (.malformed 0 s!"expected {expected}, got {got}")

private def separationExp : Except Error Unit := do
  let f := PdfObject.dict [(nm "FunctionType", .int 2), (nm "Domain", unitRanges 1), (nm "N", .int 2),
    (nm "C0", .array [.int 1]), (nm "C1", .array [.int 0])]
  let space := PdfObject.array [.name (nm "Separation"), .name (nm "Spot"), .name (nm "DeviceGray"), f]
  let dict := [(nm "ColorSpace", space), (nm "Width", .int 4), (nm "Height", .int 1),
    (nm "BitsPerComponent", .int 8)]
  let pixels ← Raster.Image.decodeInline {} [] dict (ByteArray.mk #[0,17,34,51])
  let jpx ← Raster.Image.decodeInline {} [] ((nm "Filter", .name (nm "JPXDecode")) :: dict) (stream [a])
  check (.ok jpx.data.toList) [255,255,255,255, 254,254,254,255, 250,250,250,255, 245,245,245,255]
  unless pixels.data == jpx.data do throw (.malformed 0 "ordinary Separation differs")

private def componentLimit : Except Error Unit := do
  let names := PdfObject.array (List.replicate (Raster.Image.maxComps + 1) (.name (nm "Spot")))
  let space := PdfObject.array [.name (nm "DeviceN"), names, .name (nm "DeviceRGB"), .null]
  let dict := [(nm "ColorSpace", space), (nm "Width", .int 4), (nm "Height", .int 1),
    (nm "Filter", .name (nm "JPXDecode"))]
  unless (match Raster.Image.decodeInline {} [] dict (stream [a]) with
    | .error (.unsupported _) => true | _ => false) do throw (.malformed 0 "component limit")

/-- Check calculator inputs in native order, zero-filled inputs, device alternates and
the ordinary unsupported-transform fallback. Return the number of failed cases. -/
def run : IO Nat := do
  let cases := [
    ("grid 10 / subsampling 13", check (render [a,b] .rgb "{ 0 }")
      [0,255,0,255, 17,136,0,255, 34,0,0,255, 51,119,0,255]),
    ("form-local inline tint", check (render [a,b] .rgb "{ 0 }" (inlineImage := true))
      [0,255,0,255, 17,136,0,255, 34,0,0,255, 51,119,0,255]),
    ("grid 12 with missing planes supplied as zero", check (render [a,b,z,z] .rgb "{ pop 1 exch sub }")
      [0,255,255,255, 17,136,255,255, 34,0,255,255, 51,119,255,255]),
    ("grid 13", check (render [a,b,z,z,e] .rgb "{ exch pop exch pop }")
      [0,255,51,255, 17,136,34,255, 34,0,17,255, 51,119,0,255]),
    ("DeviceN with gray alternate", check (render [a,b] .gray "{ exch pop }")
      [255,255,255,255, 136,136,136,255, 0,0,0,255, 119,119,119,255]),
    ("Separation with CMYK alternate", check (render [a] .cmyk "{ 0 1 0 }" (separation := true))
      [255,255,0,255, 238,255,0,255, 221,255,0,255, 204,255,0,255]),
    ("type 2 Separation", separationExp),
    ("component limit", componentLimit),
    ("incompatible domain", check (render [a,b] .rgb "{ 0 }" (some 3))
      [128,128,128,255, 179,179,179,255, 238,238,238,255, 170,170,170,255])]
  let mut failures := 0
  for (label, result) in cases do
    if let .error err := result then
      IO.eprintln s!"  FAIL JPX tint {label}: {repr err}"
      failures := failures + 1
  return failures

end SafePdf.Tests.JPXTint
