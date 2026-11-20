import SafePdf
import Tests.CFFText

/-!
# Glyph outlines and text rendering (task 7.3a)

Plan.md §6 Phase 7 ("glyph outlines through the same path code"). Checks, over the font
fixtures of Phase 6 (`Tests/fonts/`):

* a TrueType glyph (`tiny.ttf` `A`: a quadratic arch over a 600-unit base, control point at
  height 700, so its area is `2/3 · 600 · 700 / 2 = 140000` units²) rendered at 100 px per em:
  coverage within 1.5% of 1400 px;
* Type 1 (`tiny.t1`) and CFF (`tiny.cff`) outlines from the files: non-empty with the expected
  control boxes;
* end-to-end pages (`Raster.Glyph.renderDocPage`) embedding `tiny.ttf` (`/FontFile2`) and
  `tiny.t1` (`/FontFile`) as ASCIIHex streams: ink = glyph area at 100 pt, zoom 1; render modes
  3 (nothing), 1 (stroke only), 2 (fill + stroke ≥ fill); a non-embedded Helvetica paints
  nothing (no substitute fonts: documented gap); a CFF page renders without failure.

Set `SAFEPDF_PPM_DIR=<dir>` to also write the rendered pages as PPM files there.
-/

namespace SafePdf.Tests.RasterGlyph

open SafePdf.Core
open SafePdf.Core.Raster
open SafePdf.Core.Raster.Glyph
open SafePdf.Tests.CFFText (mkPdf strmObj hex)

/-- Ink of an image: `Σ (255 − R)` over all pixels (`255` per fully black pixel). -/
def ink (img : Clip.Image) : Nat := Id.run do
  let mut n := 0
  for i in [0:img.w * img.h] do
    n := n + (255 - Clip.getB img.data (4 * i))
  return n

/-- Write an RGBA image as a binary PPM (alpha dropped). -/
def writePpm (path : System.FilePath) (img : Clip.Image) : IO Unit := do
  let mut rgb := ByteArray.empty
  for i in [0:img.w * img.h] do
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i)))
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i + 1)))
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i + 2)))
  IO.FS.writeBinFile path (s!"P6\n{img.w} {img.h}\n255\n".toUTF8 ++ rgb)

/-- A one-page 200 × 200 PDF showing content `c` with font `/F1` = object 5 (`font`); further
objects from 6 on. -/
def page (font c : String) (extra : List String) : ByteArray := mkPdf ([
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] >>",
  "<< /Type /Page /Parent 2 0 R /Resources << /Font << /F1 5 0 R >> >> /Contents 4 0 R >>",
  strmObj "" c, font] ++ extra)

/-- A simple TrueType font over `tiny.ttf`. -/
def ttPage (ttf : ByteArray) (c : String) : ByteArray :=
  page "<< /Type /Font /Subtype /TrueType /BaseFont /SafePdfTiny /FirstChar 65 /LastChar 65 /Widths [600] /Encoding /WinAnsiEncoding /FontDescriptor 6 0 R >>"
    c [ "<< /Type /FontDescriptor /FontName /SafePdfTiny /Flags 32 /FontFile2 7 0 R >>",
        strmObj "/Filter /ASCIIHexDecode" (hex ttf) ]

/-- A simple Type 1 font over `tiny.t1` (`/Length1 568 /Length2 696`). -/
def t1Page (t1 : ByteArray) (c : String) : ByteArray :=
  page "<< /Type /Font /Subtype /Type1 /BaseFont /SafePdfTiny /FirstChar 65 /LastChar 67 /Widths [600 650 700] /FontDescriptor 6 0 R >>"
    c [ "<< /Type /FontDescriptor /FontName /SafePdfTiny /Flags 4 /FontFile 7 0 R >>",
        strmObj "/Length1 568 /Length2 696 /Length3 0 /Filter /ASCIIHexDecode" (hex t1) ]

/-- A simple Type1C font over `tiny.cff`. -/
def cffPage (cff : ByteArray) (c : String) : ByteArray :=
  page "<< /Type /Font /Subtype /Type1 /BaseFont /SafePdfTinyCFF /FontDescriptor 6 0 R >>"
    c [ "<< /Type /FontDescriptor /FontName /SafePdfTinyCFF /Flags 4 /FontFile3 7 0 R >>",
        strmObj "/Subtype /Type1C /Filter /ASCIIHexDecode" (hex cff) ]

/-- A non-embedded Helvetica. -/
def helvPage (c : String) : ByteArray :=
  page "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>" c []

/-- Render page 1 at zoom 1. -/
def render (b : ByteArray) : Option Clip.Image :=
  match Doc.openDoc {} b with
  | .ok d =>
    match d.pages.toList with
    | p :: _ =>
      match (renderDocPage {} d p 1 .r0 (Filter.Budget.init {})).1 with
      | .ok img => some img
      | .error _ => none
    | [] => none
  | .error _ => none

/-- `x` within `pct`% of `want`. -/
def near (x want pct : Nat) : Bool := x * 100 ≤ want * (100 + pct) && want * (100 - pct) ≤ x * 100

/-- Run the checks; the number of failures. -/
def run : IO Nat := do
  let ttf ← IO.FS.readBinFile "Tests/fonts/tiny.ttf"
  let t1 ← IO.FS.readBinFile "Tests/fonts/tiny.t1"
  let cff ← IO.FS.readBinFile "Tests/fonts/tiny.cff"
  let mut failures := 0
  let mut dumps : Array (String × Clip.Image) := #[]
  let report (s : String) : IO Unit := IO.println s!"  FAIL raster-glyph: {s}"
  -- 1. a TrueType glyph at 100 px per em: area 1400 px
  match Font.TrueType.parse {} ttf with
  | .ok f =>
    match f.glyphOutline 2 with
    | some o =>
      let m := ttMatrix f * Geom.Aff.scale 100 100 * Geom.Aff.translate 10 10
      let mask := Fill.fillDPath (outlineToD 1073741824 m o) .nonzero ⟨0, 0, 100, 100⟩
      if !near mask.total (1400 * 255) 2 then
        failures := failures + 1; report s!"TrueType A coverage {mask.total} vs {1400 * 255}"
    | none => failures := failures + 1; report "TrueType A: no outline"
  | .error _ => failures := failures + 1; report "tiny.ttf does not parse"
  -- 2. Type 1 and CFF outlines from the files
  match Font.Type1.parse {} t1 (some 568) (some 696) with
  | .ok f =>
    let got := ["A", "B", "C"].map fun n => (f.outline n).bind (·.bboxUnits)
    if got != [some (10, 0, 610, 700), some (20, 0, 120, 100), some (10, 0, 610, 700)] then
      failures := failures + 1; report s!"Type 1 outlines {got}"
  | .error _ => failures := failures + 1; report "tiny.t1 does not parse"
  match Font.CFF.parse {} cff with
  | .ok f =>
    let got := [2, 3, 4].map fun g => (f.outline g).bind (·.bboxUnits)
    if got != [some (5, 5, 5, 5), some (10, 20, 10, 120), some (5, 5, 10, 120)] then
      failures := failures + 1; report s!"CFF outlines {got}"
  | .error _ => failures := failures + 1; report "tiny.cff does not parse"
  -- 3. end-to-end pages
  let cases : List (String × ByteArray × (Nat → Bool)) :=
    [ ("tt-fill", ttPage ttf "BT /F1 100 Tf 20 20 Td (A) Tj ET", fun n => near n (1400 * 255) 2),
      ("tt-invisible", ttPage ttf "BT /F1 100 Tf 3 Tr 20 20 Td (A) Tj ET", (· == 0)),
      ("tt-clip-mode", ttPage ttf "BT /F1 100 Tf 7 Tr 20 20 Td (A) Tj ET", (· == 0)),
      ("tt-stroke", ttPage ttf "BT /F1 100 Tf 1 Tr 2 w 20 20 Td (A) Tj ET",
        fun n => 0 < n && n < 1400 * 255),
      ("tt-fill-stroke", ttPage ttf "BT /F1 100 Tf 2 Tr 2 w 20 20 Td (A) Tj ET",
        fun n => 1400 * 255 < n),
      ("tt-fill-clip-mode", ttPage ttf "BT /F1 100 Tf 4 Tr 20 20 Td (A) Tj ET",
        fun n => near n (1400 * 255) 2),
      -- A triangle 600 × 700 units: 2100 px; C = A + B with B inside A: 2100 px again
      ("t1-AC", t1Page t1 "BT /F1 100 Tf 20 20 Td (AC) Tj ET", fun n => near n (4200 * 255) 2),
      ("t1-scaled", t1Page t1 "BT /F1 50 Tf 50 Tz 20 20 Td (A) Tj ET",
        fun n => near n (2100 * 255 / 8) 3),
      ("helvetica-not-embedded", helvPage "BT /F1 100 Tf 20 20 Td (A) Tj ET", (· == 0)),
      ("cff", cffPage cff "BT /F1 100 Tf 20 20 Td (ABC) Tj ET", fun _ => true) ]
  for (name, pdf, ok) in cases do
    match render pdf with
    | some img =>
      dumps := dumps.push (name, img)
      if img.w != 200 || img.h != 200 || !ok (ink img) then
        failures := failures + 1; report s!"{name}: {img.w}×{img.h}, ink {ink img}"
    | none => failures := failures + 1; report s!"{name}: render failed"
  if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
    IO.FS.createDirAll dir
    for (name, img) in dumps do
      writePpm (System.FilePath.mk dir / s!"glyph-{name}.ppm") img
  return failures

end SafePdf.Tests.RasterGlyph
