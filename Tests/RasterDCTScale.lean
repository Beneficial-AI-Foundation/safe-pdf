import SafePdf
import Tests.CFFText

/-!
# Reduced-size JPEG decoding of downscaled images (task 7.10)

Plan.md §6 Phase 7 (pixel faithfulness vs MuPDF). Regression for `arxiv-2501.12948` p16: an
11881 × 7646 RGB JPEG drawn 453 × 292 pt. Its full decode (272 MB) exceeded
`Limits.maxDecodedStreamBytes`, so the page showed the grey placeholder (26.2% of the page
differed from MuPDF). MuPDF decodes such an image at `1 / 2^l2factor` of its size through
libjpeg's scaled IDCT; so do we now (`Image.l2Factor`, `Image.imageExtents`,
`Quarantine.DCT.decode … scale`). Checks:

* `l2Factor` on MuPDF's rule (`fz_get_pixmap_from_image`), including the corpus case (4),
  and `dctScale` (one step less, at most 3);
* `imageExtents`: the largest extents over the uses; images used in `fixed` items left out;
* `loadImages` with extents decodes `Tests/images/psmooth.jpg` (96 × 72, 4:2:0) drawn
  10 × 7 px (`l2factor` 3) at 1/4 — exactly `psmooth-s2.ref` (`djpeg -scale 1/4`) — and at
  full size without;
* end to end (`renderDocPage`, a generated one-page PDF drawing the baseline 4:2:0
  `Tests/images/s420.jpg`, 45 × 31, at 9 × 5 pt: `l2factor` 2, decoded at 1/2): with
  `maxDecodedStreamBytes` = 2000 (below the 2304-byte full-size planes, above the 1152-byte
  reduced ones) the page equals the page rendered with the default limits, and the image
  area is not the placeholder's grey — the corpus failure in miniature.
-/

namespace SafePdf.Tests.RasterDCTScale

open SafePdf SafePdf.Core SafePdf.Core.Raster
open SafePdf.Tests.CFFText (mkPdf strmObj hex)

/-- A one-page 40 × 40 PDF drawing the RGB JPEG `jpg` (`w × h`) with `cm` matrix `m`. -/
def jpegPage (jpg : ByteArray) (w h : Nat) (m : String) : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 40 40] >>",
  "<< /Type /Page /Parent 2 0 R /Resources << /XObject << /Im1 5 0 R >> >> /Contents 4 0 R >>",
  strmObj "" s!"q {m} cm /Im1 Do Q",
  strmObj s!"/Type /XObject /Subtype /Image /Width {w} /Height {h} /BitsPerComponent 8 /ColorSpace /DeviceRGB /Filter [/ASCIIHexDecode /DCTDecode]"
    (hex jpg)]

/-- Render page 1 at zoom 1 under `limits`. -/
def render (limits : Limits) (b : ByteArray) : Option Clip.Image :=
  match Doc.openDoc limits b with
  | .ok d =>
    match d.pages.toList with
    | p :: _ =>
      match (Glyph.renderDocPage limits d p 1 .r0 (Filter.Budget.init limits)).1 with
      | .ok img => some img
      | .error _ => none
    | [] => none
  | .error _ => none

/-- Parse a reference file: header line `W H NC`, then the samples. -/
def parseRef (b : ByteArray) : Option (Nat × Nat × Nat × ByteArray) := do
  let nl ← (List.range (min b.size 64)).find? (fun i => b.get! i == 10)
  let hdr := String.fromUTF8! (b.extract 0 nl)
  match (hdr.splitOn " ").map String.toNat? with
  | [some w, some h, some nc] => some (w, h, nc, b.extract (nl + 1) b.size)
  | _ => none

/-- The image matrix of `w × h` device pixels at the origin. -/
def mat (w h : Int) : Content.Matrix :=
  ⟨Content.Fixed.ofInt w, Content.Fixed.zero, Content.Fixed.zero, Content.Fixed.ofInt h,
    Content.Fixed.zero, Content.Fixed.zero⟩

/-- Run the suite. -/
def run : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL raster-dct-scale: {msg}"
  -- 1. MuPDF's l2factor.
  let cases : List (Nat × Nat × Rat × Rat × Nat) :=
    [ (11881, 7646, 453 * 453, 291 * 291, 4),   -- the corpus image (453.5 × 291.8 px)
      (96, 72, 100, 49, 3),                     -- 10 × 7 px: 96 >> 3 = 12 ≥ 12
      (96, 72, 121, 49, 2),                     -- 11 px wide: 12 < 13
      (100, 100, 2500, 2500, 0),                -- half size: 50 < 52
      (100, 100, 2304, 2304, 1),                -- 48 px: 50 ≥ 50
      (1000, 1000, 1/4, 1, 0),                  -- under one pixel: no reduction
      (100000, 100000, 1, 1, 6) ]               -- capped at 6
  for (iw, ih, qw, qh, want) in cases do
    let got := Image.l2Factor iw ih qw qh
    if got != want then
      failures := failures + 1; report s!"l2Factor {iw} {ih} {qw} {qh} = {got}, want {want}"
  if [0, 1, 2, 3, 4, 5, 6].map Image.dctScale != [0, 0, 1, 2, 3, 3, 3] then
    failures := failures + 1; report "dctScale"
  -- 2. Extents: the largest over the uses; images of `fixed` items are excluded.
  let nm := fun (s : String) => Name.ofString s
  let fill : Content.FillStyle := { color := .gray Content.Comp.zero, alpha := Content.Comp.one }
  let img := fun (n : Nat) (m : Content.Matrix) =>
    (Content.DisplayItem.image (.xobject (nm "I") n 0) m fill [] : Content.DisplayItem)
  let ex := Image.imageExtents 8 2 #[img 5 (mat 3 4), img 5 (mat 5 1), img 6 (mat 1 1)]
    #[img 6 (mat 2 2)]
  if ex != [((5, 0), ((100 : Rat), (64 : Rat)))] then
    failures := failures + 1; report s!"imageExtents {repr ex}"
  -- 3. loadImages: psmooth.jpg drawn 10 × 7 px decodes at 1/8 (= djpeg -scale 1/8).
  let dir : System.FilePath := "Tests" / "images"
  let jpg ← IO.FS.readBinFile (dir / "psmooth.jpg")
  let ref := parseRef (← IO.FS.readBinFile (dir / "psmooth-s2.ref"))
  let xd : Dict := [(nm "Subtype", .name (nm "Image")), (nm "Width", .int 96),
    (nm "Height", .int 72), (nm "BitsPerComponent", .int 8),
    (nm "ColorSpace", .name (nm "DeviceRGB")), (nm "Filter", .name (nm "DCTDecode"))]
  let src : Content.Source Unit :=
    ⟨fun s n _ => (if n = 5 then .ok (.stream ⟨xd, jpg⟩) else .error (.malformed 0 "missing"), s),
     fun s _ st => (Filter.decodeBytes {} st.dict st.data (.unsupported "image codec"), s)⟩
  let items : Content.DisplayList := #[img 5 (mat 10 7)]
  let (small, _) := Image.loadImages {} src () [] items (Image.imageExtents 8 1 items #[])
  let (full, _) := Image.loadImages {} src () [] items
  match small.pixmap (.xobject (nm "I") 5 0), full.pixmap (.xobject (nm "I") 5 0), ref with
  | some a, some b, some (rw, rh, 3, rd) =>
    let same := (List.range (rw * rh)).all fun i =>
      (List.range 3).all fun c => a.data.get! (4 * i + c) == rd.get! (3 * i + c)
    if a.w != rw || a.h != rh || !same || b.w != 96 || b.h != 72 then
      failures := failures + 1; report s!"loadImages scaled {a.w}x{a.h} (same {same}), full {b.w}x{b.h}"
  | _, _, _ => failures := failures + 1; report "loadImages: missing pixmaps or reference"
  -- 4. End to end: a tight decoded-stream limit no longer turns the image grey.
  -- (A baseline JPEG: a progressive frame keeps its full-size coefficient buffer.)
  let s420 ← IO.FS.readBinFile (dir / "s420.jpg")
  let pdf := jpegPage s420 45 31 "9 0 0 5 5 5"
  let tight : Limits := { maxDecodedStreamBytes := 2000 }
  match render tight pdf, render {} pdf with
  | some a, some b =>
    -- the image covers device x 5..14, y 30..35 (40 − 5 − 5)
    let grey := (List.range 5).all fun y => (List.range 9).all fun x =>
      let i := 4 * ((30 + y) * a.w + 5 + x)
      Clip.getB a.data i == 128 && Clip.getB a.data (i + 1) == 128 && Clip.getB a.data (i + 2) == 128
    if a.data != b.data || grey then
      failures := failures + 1; report s!"end to end: equal {a.data == b.data}, placeholder grey {grey}"
  | _, _ => failures := failures + 1; report "end to end: render failed"
  IO.println s!"  raster-dct-scale: {cases.length} l2factor cases, scaled loadImages, end-to-end page"
  return failures

end SafePdf.Tests.RasterDCTScale
