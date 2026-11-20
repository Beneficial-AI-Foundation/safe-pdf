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
  nothing (no substitute fonts: documented gap); a CFF page renders without failure;
* task 7.3f (end to end): `sh` with `ca 0.5` and `/BM /Multiply`, an image inside a
  luminosity soft-mask group, an inline image with a named colour space inside a form,
  text filled with a shading pattern;
* task 7.3j (Type 3 fonts, a hand-built font, `type3Cases`): a coloured `d0` path glyph keeps
  its own colour; an uncoloured `d1` inline stencil image mask and a `d1` path take the fill
  colour (the charproc's colour operators ignored); positions with `TJ`; a rotated CTM; modes
  3 and 7; a clip; fill alpha; a glyph that shows its own font terminates (depth cap).

Set `SAFEPDF_PPM_DIR=<dir>` to also write the rendered pages as PPM files there (and the
Type 3 pages as `glyph-t3-*.pdf`, for a pixel comparison with `mutool draw`).
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

/-- A one-page 200 × 200 PDF with page resources `res` (a dictionary string) showing `c`;
further objects from 5 on (task 7.3f fixtures). -/
def resPage (res c : String) (objs : List String) : ByteArray := mkPdf ([
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] >>",
  s!"<< /Type /Page /Parent 2 0 R /Resources {res} /Contents 4 0 R >>",
  strmObj "" c] ++ objs)

/-- RGB of pixel `(x, y)`. -/
def pxAt (img : Clip.Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (Clip.getB img.data i, Clip.getB img.data (i + 1), Clip.getB img.data (i + 2))

/-- Number of red pixels (`R > 200`, `G, B < 50`). -/
def redCount (img : Clip.Image) : Nat := Id.run do
  let mut n := 0
  for i in [0:img.w * img.h] do
    let p := pxAt img (i % img.w) (i / img.w)
    if p.1 > 200 && p.2.1 < 50 && p.2.2 < 50 then n := n + 1
  return n

/-- Task 7.3f end-to-end pages (through `renderDocPage`): `sh` with `ca` and a blend mode, an
image inside a soft-mask group, an inline image with a named colour space inside a form,
pattern-coloured text: name, rendered page, check. -/
def displayListGaps (ttf : ByteArray) : List (String × Option Clip.Image × (Clip.Image → Bool)) :=
  let grayFn := "<< /FunctionType 2 /Domain [0 1] /C0 [0.5] /C1 [0.5] /N 1 >>"
  let shA := resPage
    ("<< /ExtGState << /G << /ca 0.5 /BM /Multiply >> >> /Shading << /Sh << /ShadingType 2 " ++
      s!"/ColorSpace /DeviceGray /Coords [0 0 200 0] /Function {grayFn} /Extend [true true] >> >> >>")
    "1 0 0 rg 0 0 200 200 re f /G gs /Sh sh" []
  let smImg := resPage "<< /ExtGState << /M << /SMask << /S /Luminosity /G 5 0 R >> >> >> >>"
    "/M gs 0 0 200 200 re f"
    [strmObj ("/Type /XObject /Subtype /Form /BBox [0 0 200 200] /Resources << /XObject << /Im 6 0 R >> >> " ++
        "/Group << /S /Transparency >>") "q 200 0 0 200 0 0 cm /Im Do Q",
     strmObj "/Type /XObject /Subtype /Image /Width 1 /Height 1 /ColorSpace /DeviceGray /BitsPerComponent 8 /Filter /ASCIIHexDecode" "ff>"]
  let inl := resPage "<< /XObject << /Fm 5 0 R >> >>" "/Fm Do"
    [strmObj ("/Type /XObject /Subtype /Form /BBox [0 0 200 200] " ++
        "/Resources << /ColorSpace << /Ix [/Indexed /DeviceRGB 1 <FF000000FF00>] >> >>")
      "q 200 0 0 200 0 0 cm BI /W 1 /H 1 /CS /Ix /BPC 8 /F /AHx ID 01> EI Q"]
  let txt := resPage "<< /Font << /F1 5 0 R >> /Pattern << /P0 8 0 R >> >>"
    "BT /F1 100 Tf /Pattern cs /P0 scn 20 20 Td (A) Tj ET"
    ["<< /Type /Font /Subtype /TrueType /BaseFont /SafePdfTiny /FirstChar 65 /LastChar 65 /Widths [600] /Encoding /WinAnsiEncoding /FontDescriptor 6 0 R >>",
     "<< /Type /FontDescriptor /FontName /SafePdfTiny /Flags 32 /FontFile2 7 0 R >>",
     strmObj "/Filter /ASCIIHexDecode" (hex ttf),
     "<< /PatternType 2 /Shading << /ShadingType 2 /ColorSpace /DeviceRGB /Coords [0 0 200 0] " ++
       "/Function << /FunctionType 2 /Domain [0 1] /C0 [1 0 0] /C1 [1 0 0] /N 1 >> /Extend [true true] >> >>"]
  -- Multiply: red × grey 128 = (128, 0, 0), at ca 0.5 over red → (191, 0, 0) (Normal would
  -- give G = 64).
  [ ("sh-ca-multiply", render shA, fun img =>
      let p := pxAt img 100 100
      191 ≤ p.1 + 3 && p.1 ≤ 194 && p.2.1 ≤ 2 && p.2.2 ≤ 2),
    -- A white image in the luminosity mask group: mask 1, so the black fill shows.
    ("image-in-softmask", render smImg, fun img => pxAt img 100 100 == (0, 0, 0)),
    -- Index 1 of the form's own /Ix: green.
    ("inline-named-cs-in-form", render inl, fun img => pxAt img 100 100 == (0, 255, 0)),
    -- The glyph (≈ 1400 px) filled with the red shading pattern.
    ("pattern-text", render txt, fun img => near (redCount img) 1400 5) ]

/-- Number of green pixels (`G > 200`, `R, B < 50`). -/
def greenCount (img : Clip.Image) : Nat := Id.run do
  let mut n := 0
  for i in [0:img.w * img.h] do
    let p := pxAt img (i % img.w) (i / img.w)
    if p.2.1 > 200 && p.1 < 50 && p.2.2 < 50 then n := n + 1
  return n

/-- A hand-built Type 3 font (task 7.3j) as object 5, its charprocs 6–8: `A` a coloured (`d0`)
red square filling the em, `B` an uncoloured (`d1`) 4 × 4 stencil image mask whose top half
paints (its `1 0 0 rg` must be ignored), `C` (`d1`) a path triangle; `/FontMatrix` 0.01, so
1 em = 100 glyph units. `extraRes`: more font resources (`/Resources` of the font). -/
def type3Font (extraRes : String := "") : List String :=
  [ "<< /Type /Font /Subtype /Type3 /FontBBox [0 0 100 100] /FontMatrix [0.01 0 0 0.01 0 0] " ++
      "/CharProcs << /sq 6 0 R /im 7 0 R /tri 8 0 R >> " ++
      "/Encoding << /Type /Encoding /Differences [65 /sq /im /tri] >> /FirstChar 65 /LastChar 67 " ++
      s!"/Widths [100 100 100] /Resources << {extraRes} >> >>",
    strmObj "" "100 0 d0 1 0 0 rg 0 0 100 100 re f",
    strmObj "" ("100 0 0 0 100 100 d1 1 0 0 rg q 100 0 0 100 0 0 cm " ++
      "BI /W 4 /H 4 /IM true /BPC 1 /F /AHx ID 00 00 F0 F0> EI Q"),
    strmObj "" "100 0 0 0 100 100 d1 0 0 m 100 0 l 0 100 l h f" ]

/-- A page showing `c` with the Type 3 font as `/F3`. -/
def type3Page (c : String) (extraRes : String := "") : ByteArray :=
  resPage "<< /Font << /F3 5 0 R >> >>" c (type3Font extraRes)

/-- Task 7.3j end-to-end Type 3 pages: name, rendered page, check. At 50 pt, one glyph is a
50 × 50 px em. -/
def type3Cases : List (String × ByteArray × (Clip.Image → Bool)) :=
  [ -- d0: the glyph's own red, not the green fill colour: 2500 px.
    ("t3-d0-coloured", (type3Page "BT /F3 50 Tf 0 1 0 rg 20 20 Td (A) Tj ET"),
      fun img => near (redCount img) 2500 2 && greenCount img == 0),
    -- d1 stencil: the top half (50 × 25 px) in the fill colour green, no red.
    ("t3-d1-image-mask", (type3Page "BT /F3 50 Tf 0 1 0 rg 20 20 Td (B) Tj ET"),
      fun img => near (greenCount img) 1250 3 && redCount img == 0 &&
        pxAt img 45 (200 - 60) == (0, 255, 0) && pxAt img 45 (200 - 30) == (255, 255, 255)),
    -- d1 path: the triangle (1250 px) in green.
    ("t3-d1-path", (type3Page "BT /F3 50 Tf 0 1 0 rg 20 20 Td (C) Tj ET"),
      fun img => near (greenCount img) 1250 3 && redCount img == 0),
    -- Positions: `ABC` side by side (advance 1 em), then a TJ gap of 1 em before `A`.
    ("t3-run", (type3Page "BT /F3 30 Tf 0 1 0 rg 10 20 Td [(ABC) -1000 (A)] TJ ET"),
      fun img => near (redCount img) 1800 3 && near (greenCount img) 900 4 &&
        pxAt img 145 (200 - 30) == (255, 0, 0) && pxAt img 115 (200 - 30) == (255, 255, 255)),
    -- Scaled and rotated by the CTM: still 2500 px of red at 0.5 scale × 100 pt.
    ("t3-ctm", (type3Page "q 0 0.5 -0.5 0 150 20 cm BT /F3 100 Tf (A) Tj ET Q"),
      fun img => near (redCount img) 2500 3),
    -- Modes 3 and 7 paint nothing.
    ("t3-invisible", (type3Page "BT /F3 50 Tf 3 Tr 20 20 Td (AB) Tj ET"),
      fun img => redCount img == 0 && ink img == 0),
    ("t3-clip-mode", (type3Page "BT /F3 50 Tf 7 Tr 20 20 Td (AB) Tj ET"),
      fun img => ink img == 0),
    -- Clipped to the left half of the square.
    ("t3-clipped", (type3Page "0 0 45 200 re W n BT /F3 50 Tf 20 20 Td (A) Tj ET"),
      fun img => near (redCount img) 1250 3),
    -- Fill alpha 0.5 over white: the stencil half is (127/128, 255, 127/128).
    ("t3-alpha", (resPage "<< /Font << /F3 5 0 R >> /ExtGState << /G << /ca 0.5 >> >> >>"
        "/G gs BT /F3 50 Tf 0 1 0 rg 20 20 Td (B) Tj ET" (type3Font)),
      fun img => let p := pxAt img 45 (200 - 60); 126 ≤ p.1 && p.1 ≤ 129 && p.2.1 == 255),
    -- A glyph showing its own font (`A` inside `A`'s charproc via the font's resources): the
    -- nesting stops at the depth cap; the page renders.
    ("t3-recursive", (resPage "<< /Font << /F3 5 0 R >> >>"
        "BT /F3 50 Tf 20 20 Td (A) Tj ET"
        [ "<< /Type /Font /Subtype /Type3 /FontBBox [0 0 100 100] /FontMatrix [0.01 0 0 0.01 0 0] " ++
            "/CharProcs << /sq 6 0 R >> /Encoding << /Differences [65 /sq] >> /FirstChar 65 " ++
            "/LastChar 65 /Widths [100] /Resources << /Font << /F3 5 0 R >> >> >>",
          strmObj "" "100 0 d0 1 0 0 rg 0 0 100 50 re f BT /F3 50 Tf 0 50 Td (A) Tj ET" ]),
      fun img => 0 < redCount img) ]

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
  -- 4. display-list gaps (task 7.3f)
  for (name, img?, ok) in displayListGaps ttf do
    match img? with
    | some img =>
      dumps := dumps.push (name, img)
      if !ok img then
        failures := failures + 1
        report s!"{name}: {pxAt img 100 100}, red {redCount img}"
    | none => failures := failures + 1; report s!"{name}: render failed"
  -- 5. Type 3 fonts (task 7.3j)
  let mut pdfs : Array (String × ByteArray) := #[]
  for (name, pdf, ok) in type3Cases do
    pdfs := pdfs.push (name, pdf)
    match render pdf with
    | some img =>
      dumps := dumps.push (name, img)
      if !ok img then
        failures := failures + 1
        report s!"{name}: red {redCount img}, green {greenCount img}, ink {ink img}"
    | none => failures := failures + 1; report s!"{name}: render failed"
  if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
    IO.FS.createDirAll dir
    for (name, img) in dumps do
      writePpm (System.FilePath.mk dir / s!"glyph-{name}.ppm") img
    -- the Type 3 pages too, for a pixel comparison with `mutool draw`
    for (name, pdf) in pdfs do
      IO.FS.writeBinFile (System.FilePath.mk dir / s!"glyph-{name}.pdf") pdf
  return failures

end SafePdf.Tests.RasterGlyph
