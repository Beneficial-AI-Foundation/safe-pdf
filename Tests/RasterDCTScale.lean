import SafePdf
import Tests.CFFText

/-!
# Reduced-size decoding of downscaled images (tasks 7.10, 8.6)

Plan.md §6 Phase 7 (pixel faithfulness vs MuPDF). Regression for `arxiv-2501.12948` p16: an
11881 × 7646 RGB JPEG drawn 453 × 292 pt. Its full decode (272 MB) exceeded
`Limits.maxDecodedStreamBytes`, so the page showed the grey placeholder (26.2% of the page
differed from MuPDF). MuPDF decodes such an image at `1 / 2^l2factor` of its size through
libjpeg's scaled IDCT; so do we now (`Image.l2Factor`, `Image.imageExtents`,
`Quarantine.DCT.decode … scale`). Checks:

* `l2Factor` on MuPDF's rule (`fz_get_pixmap_from_image`), including the corpus case (4),
  and `dctScale` (one step less, at most 3);
* `imageExtents`: the largest extents and placement targets over the uses; images used in
  `fixed` items left out;
* `loadImages` with extents decodes `Tests/images/psmooth.jpg` (96 × 72, 4:2:0) drawn
  10 × 7 px (`l2factor` 3) at 1/4 — exactly `psmooth-s2.ref` (`djpeg -scale 1/4`) — then
  box-filtered to its 10 × 7 target (task 8.6: = `boxDown` of the reference), and at full
  size without;
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

/-- The device RGB colour space. -/
def rgbCS : Option Content.Run.CSInfo := some (.dev .rgb (.gray Content.Comp.zero))

/-- Interleaved 8-bit RGB samples of a `w × h` test pattern: `(x mod 256, y mod 256,
(x + 3y) mod 256)`. -/
def pattern (w h : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (3 * w * h)
  for y in [0:h] do
    for x in [0:w] do
      b := ((b.push (UInt8.ofNat (x % 256))).push (UInt8.ofNat (y % 256))).push
        (UInt8.ofNat ((x + 3 * y) % 256))
  return b

/-- An 8-bit image dictionary (`/DeviceRGB` unless `mask`). -/
def idict (w h : Nat) (bpc : Nat := 8) (mask : Bool := false) : Image.ImgDict :=
  { w, h, bpc := some bpc, mask, decode := none, interp := false, cs := none }

/-- Is `r` the error `limitExceeded .decodedStreamBytes`? -/
def overLimit {α : Type} : Except Error α → Bool
  | .error (.limitExceeded .decodedStreamBytes) => true
  | _ => false

/-- A one-page 100 × 100 PDF drawing the `w × h` 8-bit RGB raw image `data` (ASCIIHex) over
the whole page. -/
def rawPage (w h : Nat) (data : ByteArray) : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 100 100] >>",
  "<< /Type /Page /Parent 2 0 R /Resources << /XObject << /Im1 5 0 R >> >> /Contents 4 0 R >>",
  strmObj "" "q 100 0 0 100 0 0 cm /Im1 Do Q",
  strmObj s!"/Type /XObject /Subtype /Image /Width {w} /Height {h} /BitsPerComponent 8 /ColorSpace /DeviceRGB /Filter /ASCIIHexDecode"
    (hex data)]

/-- The former full-size pipeline of an 8-bit image with a plan (`samples`, `toRGBA`,
colour key): the reference the streaming decode must reproduce. -/
def oldPixmap (p : Image.ImgDict) (bpc nc : Nat) (cv : Image.Conv) (data : ByteArray) :
    Image.Pixmap :=
  Image.applyKey p bpc nc data
    (Image.toRGBA (Image.samples data (Image.luts .unit nc bpc (min bpc 8) p.decode) p.w p.h nc bpc
      (min bpc 8)) p.w p.h nc cv p.mask p.interp)

/-- **Task 8.6 checks**: bounded memory for huge images.

* **Progressive coefficient store**: `Tests/images/phuge.jpg` (2048 × 1536 4:2:0
  progressive, `gen_phuge.py`) under `maxDecodedStreamBytes` = 2 MiB: the full-size decode
  is over the limit (planes 4.7 MB), the 1/8 decode fits — its coefficient store is 1.9 MB
  (10 bytes per luma block, 58 per chroma block; the old store, 8 bytes per coefficient at
  every scale, was 25 MB) — and `decodeDCT` from scale 0 retries up to 1/8: the result
  equals the direct 1/8 decode under the default limits.
* **Streaming conversion** (`finishTo … w h`) gives exactly the bytes of the former
  `toRGBA (samples …)` + `applyKey` path, for every bit depth, gray/RGB/CMYK and colour keys.
* **Huge raw image drawn small**: a 2000 × 1500 RGB image decoded to its drawn size 250 × 188
  (`decodePixmap … (some (250, 188))`, row by row) equals the former full decode followed by
  the placement's `boxDown` to 250 × 188, byte for byte.
* **Retry instead of failing**: under `maxDecodedStreamBytes` = 4 MiB the same image at full
  size (12 MB of RGBA) is decoded at 1/2 (1000 × 750) instead of failing; end to end, a raw
  64 × 64 image drawn larger than its size, whose RGBA (16 KiB) is over a 14000-byte limit,
  renders the same page as with the default limits (a flat image) instead of nothing.
* **Soft masks**: a 64 × 64 image with a 64 × 64 `/SMask` drawn 4 × 4 px decodes to 4 × 4,
  equal to the former `withMask` + `boxDown`; **inline images** decode at their drawn size. -/
def memoryChecks (dir : System.FilePath) : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL raster-dct-scale (8.6): {msg}"
  let nm := fun (s : String) => Name.ofString s
  -- 1. Progressive coefficient store and retry.
  let ph ← IO.FS.readBinFile (dir / "phuge.jpg")
  let tight : Limits := { maxDecodedStreamBytes := 2 <<< 20 }
  let pd := idict 2048 1536
  if !overLimit (Quarantine.DCT.decode tight none ph 0) then
    failures := failures + 1; report "phuge: full-size decode within 2 MiB"
  match Quarantine.DCT.decode tight none ph 3 with
  | .ok img => if img.w != 256 || img.h != 192 then
      failures := failures + 1; report s!"phuge 1/8: {img.w}x{img.h}"
  | .error e => failures := failures + 1; report s!"phuge 1/8 under 2 MiB: {repr e}"
  match Image.decodeDCT tight pd rgbCS [] ph 0, Image.decodeDCT {} pd rgbCS [] ph 3 with
  | .ok a, .ok b =>
    if a.w != 256 || a.h != 192 || a.data != b.data then
      failures := failures + 1; report s!"phuge retry: {a.w}x{a.h}, same {a.data == b.data}"
  | .error e, _ => failures := failures + 1; report s!"phuge retry failed: {repr e}"
  | _, .error e => failures := failures + 1; report s!"phuge direct 1/8 failed: {repr e}"
  -- 2. Streaming conversion = the former sample-buffer path, byte for byte.
  let rnd := (List.range 4096).foldl (fun (acc : ByteArray × Nat) _ =>
    let x := (1103515245 * acc.2 + 12345) % 2147483648
    (acc.1.push (UInt8.ofNat (x / 65536 % 256)), x)) (ByteArray.empty, 7)
  let rb := rnd.1
  for (bpc, nc, cv) in [(1, 1, Image.Conv.gray), (2, 1, .gray), (4, 3, .rgb), (8, 3, .rgb),
      (16, 3, .rgb), (8, 4, .cmyk), (8, 1, .gray)] do
    for key in [none, some ((List.range nc).flatMap fun _ => [0, 2 ^ (min bpc 8) / 2])] do
      let p := { idict 13 7 bpc with key }
      let old := oldPixmap p bpc nc cv rb
      match Image.finishTo {} p bpc nc cv .unit rb 13 7 with
      | .ok pm =>
        if pm.data != old.data || pm.w != 13 || pm.h != 7 || pm.solid != old.solid then
          failures := failures + 1; report s!"streaming conversion bpc {bpc} nc {nc} key {key.isSome}"
      | .error _ => failures := failures + 1; report s!"streaming conversion bpc {bpc} failed"
  -- 3. A huge raw image drawn small: decoded to its drawn size = full decode + boxDown.
  let big := pattern 2000 1500
  match Image.decodePixmap {} (idict 2000 1500) rgbCS big (some (250, 188)) with
  | .ok pm =>
    let ref := Image.boxDown (oldPixmap (idict 2000 1500) 8 3 .rgb big) 250 188
    if pm.w != 250 || pm.h != 188 || pm.data != ref.data || !pm.solid then
      failures := failures + 1; report s!"raw drawn small: {pm.w}x{pm.h}, = boxDown {pm.data == ref.data}"
  | .error e => failures := failures + 1; report s!"raw drawn small failed: {repr e}"
  -- 4. Retry: over the pixmap cap at full size, decoded at 1/2.
  match Image.decodePixmap { maxDecodedStreamBytes := 4 <<< 20 } (idict 2000 1500) rgbCS big with
  | .ok pm => if pm.w != 1000 || pm.h != 750 then
      failures := failures + 1; report s!"raw retry: {pm.w}x{pm.h}"
  | .error e => failures := failures + 1; report s!"raw retry failed: {repr e}"
  let flat := (List.range (64 * 64)).foldl (fun (b : ByteArray) _ =>
    ((b.push 200).push 30).push 90) ByteArray.empty
  let pdf := rawPage 64 64 flat
  match render { maxDecodedStreamBytes := 14000 } pdf, render {} pdf with
  | some a, some b =>
    let red := Clip.getB a.data (4 * (50 * a.w + 50)) == 200
    if a.data != b.data || !red then
      failures := failures + 1; report s!"raw retry end to end: equal {a.data == b.data}, painted {red}"
  | _, _ => failures := failures + 1; report "raw retry end to end: render failed"
  -- 5. A soft-masked image drawn small: = withMask + boxDown; inline images at drawn size.
  let gray64 := (List.range (64 * 64)).foldl (fun (b : ByteArray) i => b.push (UInt8.ofNat (i % 251)))
    ByteArray.empty
  let imgD : Dict := [(nm "Subtype", .name (nm "Image")), (nm "Width", .int 64),
    (nm "Height", .int 64), (nm "BitsPerComponent", .int 8),
    (nm "ColorSpace", .name (nm "DeviceRGB")), (nm "SMask", .ref 6 0)]
  let smD : Dict := [(nm "Subtype", .name (nm "Image")), (nm "Width", .int 64),
    (nm "Height", .int 64), (nm "BitsPerComponent", .int 8),
    (nm "ColorSpace", .name (nm "DeviceGray"))]
  let src : Content.Source Unit :=
    ⟨fun s n _ => (if n = 5 then .ok (.stream ⟨imgD, pattern 64 64⟩)
        else if n = 6 then .ok (.stream ⟨smD, gray64⟩) else .error (.malformed 0 "missing"), s),
     fun s _ st => (.ok st.data, s)⟩
  let fill : Content.FillStyle := { color := .gray Content.Comp.zero, alpha := Content.Comp.one }
  let items : Content.DisplayList :=
    #[Content.DisplayItem.image (.xobject (nm "I") 5 0) (mat 4 4) fill []]
  let (small, _) := Image.loadImages {} src () [] items (Image.imageExtents 8 Geom.Aff.id items #[])
  let oldImg := oldPixmap (idict 64 64) 8 3 .rgb (pattern 64 64)
  let oldMask := oldPixmap { idict 64 64 with cs := none } 8 1 .gray gray64
  let ref := Image.boxDown (Image.withMask (1 <<< 26) oldImg oldMask 0) 4 4
  match small.pixmap (.xobject (nm "I") 5 0) with
  | some pm => if pm.w != 4 || pm.h != 4 || pm.solid || pm.data != ref.data then
      failures := failures + 1; report s!"soft-masked image drawn small: {pm.w}x{pm.h}, = old {pm.data == ref.data}"
  | none => failures := failures + 1; report "soft-masked image: missing"
  let ip : Dict := [(nm "Width", .int 64), (nm "Height", .int 64),
    (nm "BitsPerComponent", .int 8), (nm "ColorSpace", .name (nm "DeviceRGB"))]
  match Image.decodeInline {} [] ip (pattern 64 64) (some { q := (256, 256), t := (16, 16) }),
      Image.decodeInline {} [] ip (pattern 64 64) with
  | .ok a, .ok b => if a.w != 16 || b.w != 64 then
      failures := failures + 1; report s!"inline image: drawn size {a.w}, full {b.w}"
  | _, _ => failures := failures + 1; report "inline image failed"
  IO.println "  raster-dct-scale (8.6): progressive store + retry, streaming = old, drawn size = boxDown, retry, soft mask, inline"
  return failures

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
  let ex := Image.imageExtents 8 (Geom.Aff.scale 2 2)
    #[img 5 (mat 3 4), img 5 (mat 5 1), img 6 (mat 1 1)] #[img 6 (mat 2 2)]
  if ex != [((5, 0), { q := ((100 : Rat), (64 : Rat)), t := (10, 8) })] then
    failures := failures + 1; report s!"imageExtents {repr ex}"
  -- 3. loadImages: psmooth.jpg drawn 10 × 7 px decodes at 1/4 (= djpeg -scale 1/4), then is
  -- box-filtered to its 10 × 7 target while decoding (task 8.6).
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
  let (small, _) := Image.loadImages {} src () [] items (Image.imageExtents 8 Geom.Aff.id items #[])
  let (full, _) := Image.loadImages {} src () [] items
  match small.pixmap (.xobject (nm "I") 5 0), full.pixmap (.xobject (nm "I") 5 0), ref with
  | some a, some b, some (rw, rh, 3, rd) =>
    let exp := Image.boxDown (Image.toRGBA rd rw rh 3 .rgb false false) 10 7
    let same := rw == 24 && rh == 18 && a.data == exp.data
    if a.w != 10 || a.h != 7 || !same || b.w != 96 || b.h != 72 then
      failures := failures + 1; report s!"loadImages scaled {a.w}x{a.h} (same {same}), full {b.w}x{b.h}"
  | _, _, _ => failures := failures + 1; report "loadImages: missing pixmaps or reference"
  -- 4. End to end: a tight decoded-stream limit no longer turns the image grey.
  -- (A baseline JPEG; the progressive case is `memoryChecks` §1.)
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
  failures := failures + (← memoryChecks dir)
  IO.println s!"  raster-dct-scale: {cases.length} l2factor cases, scaled loadImages, end-to-end page"
  return failures

end SafePdf.Tests.RasterDCTScale
