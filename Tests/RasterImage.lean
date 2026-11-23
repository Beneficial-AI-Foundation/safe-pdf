import SafePdf.Core.Raster.Image
import SafePdf.Core.Content.Interp

/-!
# Image rendering suite (tasks 7.3b, 7.3e)

Plan.md §6 Phase 7 ("images composited from quarantine-zone decodes"), ISO 32000-2 §8.9.
The buffer shapes (`samples_size`, `Pixmap.size_eq`, `renderImage_size`), the read range
(`sampleOffset_lt`) and the work bounds (`place_steps_le`, `renderImage_steps_le`) are
theorems in `SafePdf.Core.Raster.Image`; this suite checks behaviour by evaluation, on small
pages with exact expected pixels:

* DeviceGray 8-bit and 1-bit (row padding), DeviceRGB 8-bit, 16-bit gray (high byte),
  `Indexed` with a lookup string, an `/ImageMask` stencil in the fill colour, `/Decode [1 0]`;
* placement: the view's y flip (sample row 0 at the top), a 90° rotation (hand-computed) and
  rotated/skewed matrices against an independent per-pixel `ℚ` reference;
* a clipped image, constant alpha `ca`, a `/DCTDecode` image drawn as the mid-grey placeholder
  through `loadImages`, an inline image (`BI … ID … EI`, `/ASCIIHexDecode`) through the
  interpreter, the `maxImagePixels` limit;
* 7.3e: bilinear sampling (2× upscale, hand-computed; 3×/4× nearest unless `/Interpolate`),
  `/SMask` (finer than the image: resampled), `/SMask` with `/Matte`, a `/Mask` stencil stream,
  a colour-key `/Mask` array, area-averaging downscales (2×2 checker → mid grey, 4:1 stripes),
  edge anti-aliasing of a rotated square, sub-pixel-thin images (skewed: partial coverage;
  axis-aligned: grid-fitted to a full pixel), grid fitting of fractional edges; the exact
  reference comparison runs `place … (smooth := false)` (plain nearest sampling);
* timing of a full-page 600 × 800 RGB image (decode + placement; printed).

Set `SAFEPDF_PPM_DIR=<dir>` to also write the rendered test pages as PPM files there.
-/

namespace SafePdf.Tests.RasterImage

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Image
open SafePdf.Core.Content (Fixed Comp Color Clip ClipPath DisplayItem DisplayList Path Matrix
  FillStyle Source)
open SafePdf.Core.Raster

/-- A name. -/
def nm (s : String) : Name := Name.ofString s

/-- Bytes from naturals. -/
def bytes (l : List Nat) : ByteArray := ByteArray.mk (l.map UInt8.ofNat).toArray

/-- An object source over an in-memory table; streams decoded with their filters. -/
def memSource (objs : List (Nat × IndirectBody)) : Source Unit :=
  ⟨fun s n _ => match objs.find? (·.1 == n) with
     | some (_, b) => (.ok b, s)
     | none => (.error (.malformed 0 "missing"), s),
   fun s _ st => (Filter.decodeBytes {} st.dict st.data (.unsupported "image codec"), s)⟩

/-- The integer matrix `[a b c d e f]`. -/
def mat (a b c d e f : Int) : Matrix :=
  ⟨Fixed.ofInt a, Fixed.ofInt b, Fixed.ofInt c, Fixed.ofInt d, Fixed.ofInt e, Fixed.ofInt f⟩

/-- Opaque black fill style. -/
def blackFill : FillStyle := { color := .gray Comp.zero, alpha := Comp.one }

/-- A component `n / 100`. -/
def comp (n : Nat) : Comp :=
  Comp.ofFixed (Fixed.div (Fixed.ofInt n) (Fixed.ofInt 100))

/-- View of a `W × H` page at zoom 1 (y flipped, origin top-left). -/
def view (W H : Nat) : Aff := viewMatrix 1 .r0 ⟨0, 0, W, H⟩

/-- Render the image items of a list onto a white `W × H` page. -/
def renderImgs (W H : Nat) (tbl : ImageTable) (items : List DisplayItem) : Clip.Image :=
  let st := items.foldl (fun st it =>
    match it with
    | .image s c f cl => renderImage {} (view W H) W H tbl st s c f cl
    | _ => st) ({ buf := Clip.whiteBuf W H } : Clip.RState)
  ⟨W, H, st.buf⟩

/-- An image item with an inline source. -/
def inlineItem (params : Dict) (data : ByteArray) (ctm : Matrix) (fill : FillStyle := blackFill)
    (clip : Clip := []) : DisplayItem :=
  .image (.inline params data) ctm fill clip

/-- Image parameters as an (uncompressed) inline dictionary. -/
def imgParams (w h bpc : Nat) (cs : PdfObject) (extra : Dict := []) : Dict :=
  [(nm "Width", .int w), (nm "Height", .int h), (nm "BitsPerComponent", .int bpc),
   (nm "ColorSpace", cs)] ++ extra

/-- RGB of pixel `(x, y)`. -/
def px (img : Clip.Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (Clip.getB img.data i, Clip.getB img.data (i + 1), Clip.getB img.data (i + 2))

/-- Gray value (red channel) of every pixel, row by row. -/
def grays (img : Clip.Image) : List (List Nat) :=
  (List.range img.h).map fun y => (List.range img.w).map fun x => (px img x y).1

/-- Independent reference: pixel `(x, y)` of a `W × H` page with one opaque gray image
`pm` placed by `ctm` through the view, by exact per-pixel inversion over `ℚ`. -/
def refGray (W H : Nat) (pm : Pixmap) (ctm : Matrix) (x y : Nat) : Nat :=
  let d := Aff.ofMatrix ctm * view W H
  let q := (Aff.inv d).apply ⟨(x : Rat) + 1 / 2, (y : Rat) + 1 / 2⟩
  if 0 ≤ q.x ∧ q.x < 1 ∧ 0 < q.y ∧ q.y ≤ 1 then
    let col := (q.x * pm.w).floor.toNat
    let row := ((1 - q.y) * pm.h).floor.toNat
    Clip.getB pm.data (4 * (row * pm.w + col))
  else 255

/-- Number of pixels where the fast placement in plain mode (`smooth := false`: nearest
sample at pixel centres) and the reference differ. -/
def refMismatches (W H : Nat) (pm : Pixmap) (ctm : Matrix) : Nat :=
  let buf := (place (1 <<< 28) W H pm (Aff.ofMatrix ctm * view W H) none (0, 0, 0) 255
    (Clip.whiteBuf W H) false).1
  let img : Clip.Image := ⟨W, H, buf⟩
  (List.range H).foldl (fun n y => (List.range W).foldl (fun n x =>
    if (px img x y).1 == refGray W H pm ctm x y then n else n + 1) n) 0

/-- A decoded 8-bit gray pixmap (the placeholder on error). -/
def grayPixmap (w h : Nat) (data : ByteArray) : Pixmap :=
  let p : ImgDict :=
    { w, h, bpc := some 8, mask := false, decode := none, interp := false, cs := none }
  match decodePixmap {} p (some (.dev .gray (.gray Comp.zero))) data with
  | .ok pm => pm
  | .error _ => placeholder

/-- Write an RGBA image as a binary PPM (alpha dropped). -/
def writePpm (path : System.FilePath) (img : Clip.Image) : IO Unit := do
  let mut rgb := ByteArray.empty
  for i in [0:img.w * img.h] do
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i)))
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i + 1)))
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i + 2)))
  IO.FS.writeBinFile path (s!"P6\n{img.w} {img.h}\n255\n".toUTF8 ++ rgb)

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL raster-image: {msg}"
  let mut dumps : Array (String × Clip.Image) := #[]
  let G := PdfObject.name (nm "DeviceGray")
  let RGB := PdfObject.name (nm "DeviceRGB")
  -- 1. Gray 8-bit 2×2 on a 6×6 page (3×, beyond MuPDF's 2× bilinear limit: nearest): 3×3
  -- blocks, sample row 0 at the top.
  let i1 := renderImgs 6 6 {} [inlineItem (imgParams 2 2 8 G) (bytes [0, 85, 170, 255]) (mat 6 0 0 6 0 0)]
  dumps := dumps.push ("gray8", i1)
  if grays i1 != [[0, 0, 0, 85, 85, 85], [0, 0, 0, 85, 85, 85], [0, 0, 0, 85, 85, 85],
      [170, 170, 170, 255, 255, 255], [170, 170, 170, 255, 255, 255], [170, 170, 170, 255, 255, 255]] then
    failures := failures + 1; report s!"gray 8-bit: {grays i1}"
  -- 1b. The same at 2× is bilinear (MuPDF `lerp`: half-pixel offset, edges clamped);
  -- hand-computed: row 0 = [a, ¾a+¼b, ¼a+¾b, b] with a = 0, b = 85, then rows likewise.
  let i1b := renderImgs 4 4 {} [inlineItem (imgParams 2 2 8 G) (bytes [0, 85, 170, 255]) (mat 4 0 0 4 0 0)]
  dumps := dumps.push ("gray8-bilinear", i1b)
  if grays i1b != [[0, 21, 63, 85], [42, 63, 105, 127], [127, 148, 190, 212], [170, 191, 233, 255]] then
    failures := failures + 1; report s!"gray 8-bit bilinear: {grays i1b}"
  -- 2. Gray 1-bit 3×2 (rows padded to a byte): 101 / 010.
  let i2 := renderImgs 3 2 {} [inlineItem (imgParams 3 2 1 G) (bytes [0b10100000, 0b01000000]) (mat 3 0 0 2 0 0)]
  if grays i2 != [[255, 0, 255], [0, 255, 0]] then
    failures := failures + 1; report s!"gray 1-bit: {grays i2}"
  -- 3. RGB 8-bit 2×1: red, blue.
  let i3 := renderImgs 2 1 {} [inlineItem (imgParams 2 1 8 RGB) (bytes [255, 0, 0, 0, 0, 255]) (mat 2 0 0 1 0 0)]
  if px i3 0 0 != (255, 0, 0) || px i3 1 0 != (0, 0, 255) then
    failures := failures + 1; report s!"rgb: {px i3 0 0} {px i3 1 0}"
  -- 4. 16-bit gray: 0x8000 → 128, 0xFFFF → 255, 0x0000 → 0.
  let i4 := renderImgs 3 1 {} [inlineItem (imgParams 3 1 16 G) (bytes [0x80, 0, 0xFF, 0xFF, 0, 0]) (mat 3 0 0 1 0 0)]
  if grays i4 != [[128, 255, 0]] then
    failures := failures + 1; report s!"16-bit: {grays i4}"
  -- 5. Indexed (1-bit, lookup string red / green); index 1 then 0.
  let idx := PdfObject.array [.name (nm "Indexed"), RGB, .int 1, .string [255, 0, 0, 0, 255, 0]]
  let i5 := renderImgs 2 1 {} [inlineItem (imgParams 2 1 1 idx) (bytes [0b10000000]) (mat 2 0 0 1 0 0)]
  if px i5 0 0 != (0, 255, 0) || px i5 1 0 != (255, 0, 0) then
    failures := failures + 1; report s!"indexed: {px i5 0 0} {px i5 1 0}"
  -- 6. Stencil mask in red: sample 0 paints, 1 does not; /Decode [1 0] swaps.
  let maskP : Dict := [(nm "Width", .int 2), (nm "Height", .int 1), (nm "ImageMask", .bool true)]
  let red : FillStyle := { color := .rgb Comp.one Comp.zero Comp.zero, alpha := Comp.one }
  let i6 := renderImgs 2 1 {} [inlineItem maskP (bytes [0b01000000]) (mat 2 0 0 1 0 0) red]
  let i6d := renderImgs 2 1 {} [inlineItem (maskP ++ [(nm "Decode", .array [.int 1, .int 0])])
    (bytes [0b01000000]) (mat 2 0 0 1 0 0) red]
  if px i6 0 0 != (255, 0, 0) || px i6 1 0 != (255, 255, 255) ||
      px i6d 0 0 != (255, 255, 255) || px i6d 1 0 != (255, 0, 0) then
    failures := failures + 1; report s!"stencil: {px i6 0 0} {px i6 1 0} / {px i6d 0 0} {px i6d 1 0}"
  -- 7. /Decode [1 0] on gray inverts.
  let i7 := renderImgs 2 1 {} [inlineItem (imgParams 2 1 8 G [(nm "Decode", .array [.int 1, .int 0])])
    (bytes [0, 200]) (mat 2 0 0 1 0 0)]
  if grays i7 != [[255, 55]] then
    failures := failures + 1; report s!"decode inversion: {grays i7}"
  -- 8. 90° rotation at 3× (hand-computed): screen rows B D / A C for samples A B / C D.
  let i8 := renderImgs 6 6 {} [inlineItem (imgParams 2 2 8 G) (bytes [10, 20, 30, 40]) (mat 0 6 (-6) 0 6 0)]
  dumps := dumps.push ("rot90", i8)
  if grays i8 != [[20, 20, 20, 40, 40, 40], [20, 20, 20, 40, 40, 40], [20, 20, 20, 40, 40, 40],
      [10, 10, 10, 30, 30, 30], [10, 10, 10, 30, 30, 30], [10, 10, 10, 30, 30, 30]] then
    failures := failures + 1; report s!"rotation: {grays i8}"
  -- 9. Rotated and skewed matrices against the exact reference (plain mode).
  let pm9 := grayPixmap 5 3 (bytes ((List.range 15).map (· * 17)))
  let ctms : List Matrix :=
    [⟨Fixed.ofInt 30, Fixed.ofInt 12, Fixed.ofInt (-9), Fixed.ofInt 25, Fixed.ofInt 15, Fixed.ofInt 3⟩,
     ⟨Fixed.ofInt 20, Fixed.zero, Fixed.ofInt 14, Fixed.ofInt 21, Fixed.ofInt 2, Fixed.ofInt 10⟩,
     ⟨Fixed.ofInt (-25), Fixed.ofInt (-7), Fixed.ofInt 5, Fixed.ofInt (-30), Fixed.ofInt 45,
      Fixed.ofInt 40⟩,
     ⟨Fixed.div (Fixed.ofInt 77) (Fixed.ofInt 3), Fixed.zero, Fixed.zero,
      Fixed.div (Fixed.ofInt 50) (Fixed.ofInt 7), Fixed.div (Fixed.ofInt 3) (Fixed.ofInt 2),
      Fixed.div (Fixed.ofInt 5) (Fixed.ofInt 4)⟩]
  for c in ctms do
    let n := refMismatches 48 48 pm9 c
    if n != 0 then
      failures := failures + 1; report s!"placement vs reference: {n} pixels differ"
  dumps := dumps.push ("skew", renderImgs 48 48 { xobjs := [((1, 0), some pm9)] }
    [.image (.xobject (nm "Im") 1 0) (ctms.headD Matrix.identity) blackFill []])
  -- 10. Clipped: only the left half [0, 2] of a 4×4 black image.
  let clipL : Clip := [⟨⟨#[.moveTo ⟨Fixed.zero, Fixed.zero⟩, .lineTo ⟨Fixed.ofInt 2, Fixed.zero⟩,
    .lineTo ⟨Fixed.ofInt 2, Fixed.ofInt 4⟩, .lineTo ⟨Fixed.zero, Fixed.ofInt 4⟩, .closePath]⟩,
    .nonzero⟩]
  let i10 := renderImgs 4 4 {} [inlineItem (imgParams 1 1 8 G) (bytes [0]) (mat 4 0 0 4 0 0) blackFill clipL]
  if grays i10 != List.replicate 4 [0, 0, 255, 255] then
    failures := failures + 1; report s!"clipped: {grays i10}"
  -- 11. Constant alpha 0.5: black over white → 128 ± 1.
  let i11 := renderImgs 1 1 {} [inlineItem (imgParams 1 1 8 G) (bytes [0]) (mat 1 0 0 1 0 0)
    { color := .gray Comp.zero, alpha := comp 50 }]
  if (px i11 0 0).1 < 127 || (px i11 0 0).1 > 129 then
    failures := failures + 1; report s!"alpha: {px i11 0 0}"
  -- 12. A /DCTDecode XObject → mid-grey placeholder; a Flate-free gray XObject decodes.
  let dctDict : Dict := imgParams 8 8 8 G [(nm "Subtype", .name (nm "Image")),
    (nm "Filter", .name (nm "DCTDecode"))]
  let rawDict : Dict := imgParams 2 1 8 G [(nm "Subtype", .name (nm "Image"))]
  let src := memSource [(7, .stream ⟨dctDict, bytes [0xFF, 0xD8]⟩), (8, .stream ⟨rawDict, bytes [0, 255]⟩)]
  let items12 : DisplayList := #[.image (.xobject (nm "Im1") 7 0) (mat 2 0 0 2 0 0) blackFill [],
    .image (.xobject (nm "Im2") 8 0) (mat 2 0 0 2 2 2) blackFill [],
    .image (.xobject (nm "Im1") 7 0) (mat 2 0 0 2 0 2) blackFill []]
  let (tbl, _) := loadImages {} src () [] items12
  let i12 := renderImgs 4 4 tbl items12.toList
  dumps := dumps.push ("xobjects", i12)
  if tbl.xobjs.length != 2 ||
      grays i12 != [[128, 128, 0, 255], [128, 128, 0, 255], [128, 128, 255, 255], [128, 128, 255, 255]] then
    failures := failures + 1; report s!"xobjects / DCT placeholder: {tbl.xobjs.length} {grays i12}"
  -- 13. Inline image through the interpreter (/ASCIIHexDecode, abbreviated keys).
  let content := "q 2 0 0 1 0 0 cm BI /W 2 /H 1 /CS /G /BPC 8 /F /AHx ID 00FF> EI Q"
  let r := Content.interpBytes {} content.toUTF8
  let i13 := renderImgs 2 1 {} r.items.toList
  if grays i13 != [[0, 255]] then
    failures := failures + 1; report s!"inline via interpreter: {grays i13} ({r.items.size} items)"
  -- 14. maxImagePixels.
  match decodeInline { maxImagePixels := 100 } [] (imgParams 20 20 8 G) (bytes []) with
  | .error (.limitExceeded .imagePixels) => pure ()
  | _ => failures := failures + 1; report "maxImagePixels not enforced"
  -- 15. /SMask (soft mask XObject, 4×1, finer than the 2×1 black base: resampled to 4×1):
  -- alpha 255, 128, 0, 255 → 0, 127, 255, 0 over white.
  let smDict : Dict := imgParams 4 1 8 G [(nm "Subtype", .name (nm "Image"))]
  let baseSm : Dict := imgParams 2 1 8 G [(nm "Subtype", .name (nm "Image")), (nm "SMask", .ref 21 0)]
  -- 16. /SMask with /Matte [1] (white): colours premultiplied against white,
  -- c' = 255 + α(0 − 255) = 127 for α = 128, un-premultiplied back to black.
  let smMatte : Dict := imgParams 1 1 8 G [(nm "Subtype", .name (nm "Image")),
    (nm "Matte", .array [.int 1])]
  let baseMatte : Dict := imgParams 1 1 8 G [(nm "Subtype", .name (nm "Image")), (nm "SMask", .ref 23 0)]
  -- 17. /Mask stencil stream (1-bit, sample 0 paints): red base, right pixel masked out.
  let mkDict : Dict := [(nm "Subtype", .name (nm "Image")), (nm "Width", .int 2), (nm "Height", .int 1),
    (nm "ImageMask", .bool true)]
  let baseMk : Dict := imgParams 2 1 8 RGB [(nm "Subtype", .name (nm "Image")), (nm "Mask", .ref 25 0)]
  let src2 := memSource [(20, .stream ⟨baseSm, bytes [0, 0]⟩), (21, .stream ⟨smDict, bytes [255, 128, 0, 255]⟩),
    (22, .stream ⟨baseMatte, bytes [127]⟩), (23, .stream ⟨smMatte, bytes [128]⟩),
    (24, .stream ⟨baseMk, bytes [255, 0, 0, 255, 0, 0]⟩), (25, .stream ⟨mkDict, bytes [0b01000000]⟩)]
  let items2 : DisplayList := #[.image (.xobject (nm "Sm") 20 0) (mat 4 0 0 1 0 0) blackFill [],
    .image (.xobject (nm "Mt") 22 0) (mat 1 0 0 1 0 1) blackFill [],
    .image (.xobject (nm "Mk") 24 0) (mat 2 0 0 1 0 2) blackFill []]
  let (tbl2, _) := loadImages {} src2 () [] items2
  let i15 := renderImgs 4 3 tbl2 items2.toList
  dumps := dumps.push ("masks", i15)
  let near := fun (a b : Nat) => a + 2 ≥ b && b + 2 ≥ a
  let g15 := grays i15
  let row0 := g15.getD 2 []
  if !(near (row0.getD 0 99) 0 && near (row0.getD 1 99) 127 && near (row0.getD 2 99) 255 &&
      near (row0.getD 3 99) 0) then
    failures := failures + 1; report s!"smask: {row0}"
  if !near (px i15 0 1).1 127 then
    failures := failures + 1; report s!"smask /Matte: {px i15 0 1}"
  if px i15 0 0 != (255, 0, 0) || px i15 1 0 != (255, 255, 255) then
    failures := failures + 1; report s!"stencil /Mask: {px i15 0 0} {px i15 1 0}"
  -- 18. Colour-key /Mask [5 20] on an inline gray image: sample 10 masked, 200 painted.
  let i18 := renderImgs 2 1 {} [inlineItem (imgParams 2 1 8 G [(nm "Mask", .array [.int 5, .int 20])])
    (bytes [10, 200]) (mat 2 0 0 1 0 0)]
  if grays i18 != [[255, 200]] then
    failures := failures + 1; report s!"colour key: {grays i18}"
  -- 19. Downscale averaging: a 2×2 black/white checker onto one device pixel → mid grey.
  let i19 := renderImgs 1 1 {} [inlineItem (imgParams 2 2 8 G) (bytes [0, 255, 255, 0]) (mat 1 0 0 1 0 0)]
  if !near (px i19 0 0).1 128 then
    failures := failures + 1; report s!"downscale average: {px i19 0 0}"
  -- 19b. 4:1 horizontal stripes (8×2, columns alternate) onto 2×2: every pixel ~128.
  let i19b := renderImgs 2 2 {} [inlineItem (imgParams 8 2 8 G)
    (bytes [0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 255]) (mat 2 0 0 2 0 0)]
  if !(grays i19b).all (·.all fun g => near g 128) then
    failures := failures + 1; report s!"downscale stripes: {grays i19b}"
  -- 20. Bilinear upscaling of a 2×1 image [0, 255]: 2× (default) → [0, 63, 191, 255]
  -- (hand-computed: weights ¼, ¾); 4× without /Interpolate → nearest; 4× with it → bilinear.
  let i20 := renderImgs 4 1 {} [inlineItem (imgParams 2 1 8 G) (bytes [0, 255]) (mat 4 0 0 1 0 0)]
  let i20n := renderImgs 8 1 {} [inlineItem (imgParams 2 1 8 G) (bytes [0, 255]) (mat 8 0 0 1 0 0)]
  let i20i := renderImgs 8 1 {} [inlineItem (imgParams 2 1 8 G [(nm "Interpolate", .bool true)])
    (bytes [0, 255]) (mat 8 0 0 1 0 0)]
  if grays i20 != [[0, 63, 191, 255]] || grays i20n != [[0, 0, 0, 0, 255, 255, 255, 255]] ||
      grays i20i != [[0, 0, 31, 95, 159, 223, 255, 255]] then
    failures := failures + 1; report s!"bilinear 2×1: {grays i20} {grays i20n} {grays i20i}"
  -- 21. Edge anti-aliasing: a black square rotated 45° (side 8√2... corners (8,0),(16,8),(8,16),(0,8))
  -- on 16×16: centre black, corners white, and partially covered pixels along the edges.
  let rot45 : Matrix := ⟨Fixed.ofInt 8, Fixed.ofInt 8, Fixed.ofInt (-8), Fixed.ofInt 8, Fixed.ofInt 8,
    Fixed.ofInt 0⟩
  let i21 := renderImgs 16 16 {} [inlineItem (imgParams 1 1 8 G) (bytes [0]) rot45]
  dumps := dumps.push ("aa45", i21)
  let g21 := (grays i21).flatten
  let part := g21.filter fun g => 0 < g && g < 255
  if (px i21 8 8).1 != 0 || (px i21 0 0).1 != 255 || (px i21 15 15).1 != 255 || part.length < 16 then
    failures := failures + 1; report s!"edge AA: centre {px i21 8 8} corner {px i21 0 0}, {part.length} partial"
  -- 22. Sub-pixel-thin images: a skewed 0.25-px-wide black image covers ≈ ¼ of the pixels it
  -- crosses (≈ 191, never black); an axis-aligned 0.3-px-wide one is grid-fitted to a full
  -- column (MuPDF).
  let thin : Matrix := ⟨Fixed.div (Fixed.ofInt 1) (Fixed.ofInt 4), Fixed.zero, Fixed.ofInt 2,
    Fixed.ofInt 8, Fixed.ofInt 1, Fixed.zero⟩
  let i22 := renderImgs 8 8 {} [inlineItem (imgParams 1 1 8 G) (bytes [0]) thin]
  let g22 := (grays i22).flatten.filter (· < 255)
  if g22.isEmpty || g22.any (· < 150) then
    failures := failures + 1; report s!"thin skewed: {grays i22}"
  let thinA : Matrix := ⟨Fixed.div (Fixed.ofInt 3) (Fixed.ofInt 10), Fixed.zero, Fixed.zero, Fixed.ofInt 2,
    Fixed.div (Fixed.ofInt 12) (Fixed.ofInt 10), Fixed.zero⟩
  let i22a := renderImgs 3 2 {} [inlineItem (imgParams 1 1 8 G) (bytes [0]) thinA]
  if grays i22a != [[255, 0, 255], [255, 0, 255]] then
    failures := failures + 1; report s!"thin axis-aligned: {grays i22a}"
  -- 23. Grid fitting: [0.5, 2.5] snaps outward to pixels 0–2.
  let i23 := renderImgs 4 1 {} [inlineItem (imgParams 1 1 8 G) (bytes [0]) ⟨Fixed.ofInt 2, Fixed.zero,
    Fixed.zero, Fixed.ofInt 1, Fixed.div (Fixed.ofInt 1) (Fixed.ofInt 2), Fixed.zero⟩]
  if grays i23 != [[0, 0, 0, 255]] then
    failures := failures + 1; report s!"grid fit: {grays i23}"
  -- 24. Timing: a full-page 600×800 RGB image on a 600×800 page.
  let W := 600
  let H := 800
  let data := ByteArray.mk ((Array.range (W * H * 3)).map fun i => UInt8.ofNat (i % 251))
  let t0 ← IO.monoMsNow
  let pmE := decodeInline {} [] (imgParams W H 8 RGB) data
  let n0 := match pmE with | .ok pm => pm.data.size | .error _ => 0
  let t1 ← IO.monoMsNow
  let st := renderImgs W H {} [inlineItem (imgParams W H 8 RGB) data (mat W 0 0 H 0 0)]
  let t2 ← IO.monoMsNow
  IO.println s!"  raster-image: 600×800 RGB decode {t1 - t0} ms ({n0} bytes), decode+place {t2 - t1} ms"
  if px st 10 0 != (30, 31, 32) then
    failures := failures + 1; report s!"full-page image pixel {px st 10 0}"
  if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
    IO.FS.createDirAll dir
    for (name, img) in dumps do
      writePpm (System.FilePath.mk dir / s!"image-{name}.ppm") img
  return failures

end SafePdf.Tests.RasterImage
