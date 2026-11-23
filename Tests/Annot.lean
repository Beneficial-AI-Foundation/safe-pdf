import SafePdf
import SafePdf.Core.Annot
import Tests.CFFText

/-!
# Annotation appearance streams (task 8.3)

Plan.md §6 Phase 8 ("display existing annotations via appearance streams"), ISO 32000-2
§12.5. One hand-built page (200 × 200, a blue page square at the origin) with:

* (a) a `/Square` whose `/AP /N` stream fills its 10 × 10 `/BBox` red, mapped into a 20 × 20
  `/Rect` (scale 2);
* (b) a `/Widget` (`/FT`, `/T` inherited from its `/Parent`) with `/AS /On` and
  `/AP /N << /On … /Off … >>`: only the green `/On` appearance is drawn, and it is drawn
  **after** the other annotations although it comes first in `/Annots` (MuPDF order);
* (c) a Hidden (`/F 2`) and a NoView (`/F 32`) annotation: skipped;
* (d) a `/Stamp` whose `/BBox` and rotating `/Matrix` need A (§12.5.5) to fit its `/Rect`;
* (e) a `/FreeText` showing text with a font of its own appearance resources (an embedded
  TrueType font object the page does not use): glyph positions with the font's advances;
* skips: `/Link`, `/Popup`, a `/Watermark` without `/AP` (not synthesised; MuPDF cannot
  either), a widget without `/FT`, a duplicate reference;
* the shared operator budget (a tiny budget truncates; `Budget.after` leaves the page run's
  remainder);
* pixels of the full render (`Glyph.renderPage` over page items ++ annotation items).
  Set `SAFEPDF_PPM_DIR=<dir>` to write the render (`annot.ppm`) and the PDF (`annot.pdf`).

Task 8.3b adds:

* annotation text in extraction (`Annot.extractDocPageAnnots`): the free text's glyphs follow
  the page's, item indices continuing after the page's items (MuPDF `-F txt` prints `AA`);
* synthesised appearances (`synthFixture`, nine annotations without `/AP`: Square with `/RD`
  and CMYK interior, Circle, Line with leader lines and a dash, Ink, Highlight over a gray
  box, Underline, StrikeOut with `/CA`): recomputed rectangles, the Multiply `/H` ExtGState,
  and pixels sampled from `mutool draw -r 72` (MuPDF 1.25.1) within 32 per channel. The whole
  page differs from MuPDF in 0.21% of pixels (84 of 40,000; thin-line anti-aliasing) under
  `run.py --comparator pixels` (`SAFEPDF_PPM_DIR` writes `synth.pdf`).

Task 8.3c adds (`run83c`):

* optional content `/OC` (`ocFixture`, three configurations: `/D`, `/Configs [0]` winning over
  `/D`, no groups): which squares are drawn, sampled pixels identical to `mutool draw -r 72`
  (including MuPDF's literal `AllOn`/`AnyOff` arithmetic);
* synthesised Polygon, PolyLine, all nine line endings, Squiggly, Caret and Text/FileAttachment/
  Sound icons (`synth2Fixture`, 17 annotations): recomputed rectangles, the form box of Caret
  and icons, pixels sampled from `mutool draw -r 72`; the whole page differs from MuPDF in
  0.024% of pixels (22 of 90,000) under `pixels.py` (`SAFEPDF_PPM_DIR` writes `synth2.pdf`).

Task 8.3e adds (`run83e`):

* the catalog's `/AcroForm /DA` as FreeText fallback, and rich text (`/DS`, `/RC`; MuPDF's HTML
  story) (`richFixture`): CSS colour/style parsing, `/RC` markup to text, fonts, the first glyph
  of every line against MuPDF's `-F stext` char origins (within 0.002 pt), the lines of
  `mutool draw -F txt`, border pixels from `mutool draw -r 72`.

Task 8.3d adds (`run83d`):

* NoRotate on pages with `/Rotate` 0, 90, 180, 270 (`noRotFixture`): the flagged annotation stays
  upright, hanging from its rectangle's upper-left corner; sampled pixels identical to
  `mutool draw -r 72`, and the whole renders identical (0 of 40,000 pixels differ, each rotation).
* synthesised FreeText and Stamp (`textFixture`, seven annotations): `/DA` fonts, sizes and
  colours, `/Q` alignment, `/RD`, a callout, `/Rotate 90`, three stamps; rectangles, the
  pseudo-owner base-14 font resources, the first line's offsets (equal to MuPDF's
  `-F stext` line origins), the text lines of `mutool draw -F txt`, and pixels away from the
  text sampled from `mutool draw -r 72`. Every differing pixel of the whole page lies in a text
  run (the rasterizer does not draw non-embedded base-14 glyphs yet) or on a 1-pixel edge of the
  turned stamp frames (`SAFEPDF_PPM_DIR` writes `text.pdf`).
* Line `/Cap` captions (`capFixture`: inline, `/CP /Top`, too long, `/CO`): the inline origin
  and line gap against MuPDF's `-F stext`, pixels; every differing pixel lies in a text run.
-/

namespace SafePdf.Tests.Annot

open SafePdf SafePdf.Core
open SafePdf.Core.Raster
open SafePdf.Tests.CFFText (mkPdf strmObj hex)

/-- Annotation fixture objects (see the module doc); `ttf` is `Tests/fonts/tiny.ttf`. -/
def fixture (ttf : ByteArray) : ByteArray := mkPdf [
  -- 1–4: catalog, pages, page, content
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] >>",
  "<< /Type /Page /Parent 2 0 R /Resources << /Font << /F1 5 0 R >> >> /Contents 4 0 R " ++
    "/Annots [10 0 R 11 0 R 12 0 R 13 0 R 14 0 R 15 0 R 16 0 R 17 0 R 22 0 R 23 0 R 10 0 R] >>",
  strmObj "" "0 0 1 rg 0 0 20 20 re f",
  -- 5–7: the page's font (tiny.ttf)
  "<< /Type /Font /Subtype /TrueType /BaseFont /SafePdfTiny /FirstChar 65 /LastChar 65 /Widths [600] /Encoding /WinAnsiEncoding /FontDescriptor 6 0 R >>",
  "<< /Type /FontDescriptor /FontName /SafePdfTiny /Flags 32 /FontFile2 7 0 R >>",
  strmObj "/Filter /ASCIIHexDecode" (hex ttf),
  -- 8: red 10 × 10 appearance; 9: green /On appearance
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 10 10]" "1 0 0 rg 0 0 10 10 re f",
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 20 20]" "0 1 0 rg 0 0 20 20 re f",
  -- 10: widget (field entries on its parent 24)
  "<< /Type /Annot /Subtype /Widget /Parent 24 0 R /Rect [150 150 170 170] /AS /On " ++
    "/AP << /N << /On 9 0 R /Off 18 0 R >> >> >>",
  -- 11: square (a)
  "<< /Type /Annot /Subtype /Square /Rect [60 60 40 40] /AP << /N 8 0 R >> >>",
  -- 12: hidden (c)
  "<< /Type /Annot /Subtype /Square /F 2 /Rect [0 100 50 150] /AP << /N 8 0 R >> >>",
  -- 13: stamp with a rotating matrix (d)
  "<< /Type /Annot /Subtype /Stamp /Rect [100 20 120 60] /AP << /N 19 0 R >> >>",
  -- 14: free text (e)
  "<< /Type /Annot /Subtype /FreeText /Rect [20 150 120 170] /AP << /N 20 0 R >> >>",
  -- 15: link, 16: popup, 17: watermark without /AP: not synthesised
  "<< /Type /Annot /Subtype /Link /Rect [0 0 10 10] /AP << /N 8 0 R >> >>",
  "<< /Type /Annot /Subtype /Popup /Rect [0 0 10 10] /AP << /N 8 0 R >> >>",
  "<< /Type /Annot /Subtype /Watermark /Rect [0 0 10 10] >>",
  -- 18: blue /Off appearance (never drawn here)
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 20 20]" "0 0 1 rg 0 0 20 20 re f",
  -- 19: BBox 40 × 20 rotated by 90°; fills form y ∈ [0, 10]
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 40 20] /Matrix [0 1 -1 0 0 0]"
    "0 0 0 rg 0 0 40 10 re f",
  -- 20: free-text appearance with its own font /FA = 21
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 100 20] /Resources << /Font << /FA 21 0 R >> >>"
    "BT 0 g /FA 12 Tf 2 4 Td (AA) Tj ET",
  "<< /Type /Font /Subtype /TrueType /BaseFont /SafePdfTiny /FirstChar 65 /LastChar 65 /Widths [600] /Encoding /WinAnsiEncoding /FontDescriptor 6 0 R >>",
  -- 22: widget without /FT; 23: NoView
  "<< /Type /Annot /Subtype /Widget /T (x) /Rect [0 0 10 10] /AP << /N 8 0 R >> >>",
  "<< /Type /Annot /Subtype /Square /F 32 /Rect [0 0 10 10] /AP << /N 8 0 R >> >>",
  -- 24: the widget's field
  "<< /FT /Btn /T (cb) /Kids [10 0 R] >>"]

/-- Everything a check needs from page 1. -/
structure Out where
  /-- The page. -/
  page : Doc.Page
  /-- The page's text run. -/
  pt : Text.PageText
  /-- The annotations. -/
  ap : Annot.AnnotPage
  /-- The full render at zoom 1. -/
  img : Clip.Image

/-- Open, extract, run the annotations under `bud`, render page items ++ annotation items. -/
def process (b : ByteArray) (bud : Annot.Budget := { ops := 1000000, forms := 1000 }) :
    Option Out :=
  match Doc.openDoc {} b with
  | .error _ => none
  | .ok d =>
    match d.pages.toList with
    | [] => none
    | p :: _ =>
      let lim : Limits := {}
      match Text.extractDocPage lim d p (Filter.Budget.init {}) with
      | (.error _, _) => none
      | (.ok pt, b0) =>
        let (ap, b1) := Annot.docAnnots lim d p pt.fonts bud b0
        let src := Text.docSource lim d
        let items := pt.items ++ ap.items
        let (srcs, b2) := Glyph.loadSources lim src b1 (p.resources.getD [])
        -- glyph sources of the appearance fonts (indirect fonts: keys do not depend on owner)
        let (srcs, _) := ap.roots.foldl (fun (acc : Glyph.SourceTable × Filter.Budget) r =>
          let (t, b) := Glyph.loadSources lim src acc.2 r.2 r.1
          (acc.1 ++ t, b)) (srcs, b2)
        let img := Glyph.renderPage p 1 .r0 { fonts := ap.fonts, sources := srcs } items
        some ⟨p, pt, ap, img⟩

/-- RGB at device pixel `(x, y)`. -/
def pxAt (img : Clip.Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (Clip.getB img.data i, Clip.getB img.data (i + 1), Clip.getB img.data (i + 2))

/-- Write an RGBA image as a binary PPM (alpha dropped). -/
def writePpm (path : System.FilePath) (img : Clip.Image) : IO Unit := do
  let mut rgb := ByteArray.empty
  for i in [0:img.w * img.h] do
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i)))
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i + 1)))
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i + 2)))
  IO.FS.writeBinFile path (s!"P6\n{img.w} {img.h}\n255\n".toUTF8 ++ rgb)

/-- Corner points of the fill paths of a display list, as integers (page space). -/
def fillBoxes (items : Content.DisplayList) : List (List (Int × Int)) :=
  items.toList.filterMap fun it =>
    match it with
    | .fillPath p _ _ _ => some (p.segs.toList.filterMap fun s =>
        match s with
        | .moveTo q => some ((q.x.raw / 1000000), (q.y.raw / 1000000))
        | .lineTo q => some ((q.x.raw / 1000000), (q.y.raw / 1000000))
        | _ => none)
    | _ => none

/-- Fill colours of a display list. -/
def fillColors (items : Content.DisplayList) : List Content.Color :=
  items.toList.filterMap fun it =>
    match it with
    | .fillPath _ _ st _ => some st.color
    | _ => none

/-- Report a failed check. -/
def check (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"annot: FAILED {name}"
  return 1

/-- Annotations without `/AP` whose appearances are synthesised (see the module doc; the PDF
`mutool draw` was compared against). -/
def synthFixture : ByteArray := mkPdf ([
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R " ++
    "/Annots [5 0 R 6 0 R 7 0 R 8 0 R 9 0 R 10 0 R 11 0 R 12 0 R 13 0 R] >>",
  strmObj "" "0.9 g 100 170 60 15 re f",
  "<< /Type /Annot /Subtype /Square /Rect [20 20 80 60] /C [1 0 0] /IC [0 0 1] /BS << /W 3 >> >>",
  "<< /Type /Annot /Subtype /Circle /Rect [100 20 180 80] /C [0 0.5 0] /Border [0 0 2] >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [20 100 180 120] /C [0 0 1] /BS << /W 2 >> >>",
  "<< /Type /Annot /Subtype /Ink /Rect [0 0 1 1] /InkList [[20 140 40 170 60 150] [70 140 90 175]] " ++
    "/C [1 0 1] /BS << /W 4 >> >>",
  "<< /Type /Annot /Subtype /Highlight /Rect [0 0 1 1] " ++
    "/QuadPoints [100 185 160 185 100 170 160 170] /C [1 1 0] >>",
  "<< /Type /Annot /Subtype /Underline /Rect [0 0 1 1] " ++
    "/QuadPoints [100 165 160 165 100 150 160 150] /C [0 0 1] >>",
  "<< /Type /Annot /Subtype /StrikeOut /Rect [0 0 1 1] " ++
    "/QuadPoints [100 145 160 145 100 130 160 130] /C [1 0 0] /CA 0.7 >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [120 90 190 90] /LL 8 /LLE 3 /LLO 2 " ++
    "/C [0 0 0] /Border [0 0 1 [3 2]] >>",
  "<< /Type /Annot /Subtype /Square /Rect [150 100 195 125] /C [0.2] /IC [0 1 0 0] /RD [5 2 5 2] >>"])

/-- Page 1 of a PDF. -/
def firstPage (b : ByteArray) : Option (Doc.Doc × Doc.Page) :=
  match Doc.openDoc {} b with
  | .error _ => none
  | .ok d => d.pages.toList.head?.map (d, ·)

/-- `/Resources /ExtGState /H /BM` of a (direct) stream dictionary. -/
def bmOf (d : Dict) : Option PdfObject :=
  let sub := fun (o : Option PdfObject) (k : String) => match o with
    | some (.dict e) => Dict.get? e (Name.ofString k)
    | _ => none
  sub (sub (sub (Dict.get? d (Name.ofString "Resources")) "ExtGState") "H") "BM"

/-- Whether `s` contains `pat`. -/
def has (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- Whether two pixels are within 32 per channel. -/
def near (a b : Nat × Nat × Nat) : Bool :=
  let d := fun (x y : Nat) => x - y + (y - x)
  d a.1 b.1 ≤ 32 && d a.2.1 b.2.1 ≤ 32 && d a.2.2 b.2.2 ≤ 32

/-- Task 8.3b checks: shared budget, annotation text, synthesised appearances. -/
def run83b (pdf : ByteArray) : IO Nat := do
  let mut failures := 0
  -- (1) the page run's counts and what is left for the annotations
  match process pdf with
  | none => failures := failures + 1
  | some o =>
    failures := failures + (← check "page run counts" (o.pt.ops == 3 && o.pt.forms == 0))
    let lim : Limits := { maxOpsPerPage := o.pt.ops + 2, maxFormsPerPage := 7 }
    let bud := Annot.Budget.after lim o.pt
    failures := failures + (← check "budget after" (bud.ops == 2 && bud.forms == 7))
    match process pdf bud with
    | none => failures := failures + 1
    | some o2 => failures := failures + (← check "shared budget truncates"
        (o2.ap.truncated && o.pt.ops + o2.ap.ops ≤ lim.maxOpsPerPage))
  -- (2) annotation text in extraction
  match firstPage pdf with
  | none => failures := failures + 1
  | some (d, p) =>
    match (Text.extractDocPage {} d p (Filter.Budget.init {})).1,
        (Annot.extractDocPageAnnots {} d p (Filter.Budget.init {})).1 with
    | .ok pt, .ok t =>
      failures := failures + (← check "annot text" (pt.text == "" && t.text == "AA"))
      failures := failures + (← check "annot glyph items continue"
        (t.glyphs.length == 2 && t.glyphs.all (·.item ≥ pt.items.size)))
      failures := failures + (← check "annot text counts" (t.ops > pt.ops && t.forms == 4))
    | _, _ => failures := failures + (← check "annot text extracts" false)
  -- (3) synthesised appearances
  match process synthFixture with
  | none => failures := failures + (← check "synth fixture processes" false)
  | some o =>
    let ds := o.ap.collected.drawn
    failures := failures + (← check "synth all drawn"
      (ds.length == 9 && ds.all (·.synth) && o.ap.collected.skipped.isEmpty))
    let rects := ds.map (·.rect)
    failures := failures + (← check "synth square rect" (rects[0]? == some ⟨20, 20, 80, 60⟩))
    failures := failures + (← check "synth line rect" (rects[2]? == some ⟨18, 98, 182, 122⟩))
    failures := failures + (← check "synth ink rect" (rects[3]? == some ⟨10, 130, 100, 185⟩))
    failures := failures + (← check "synth rd square rect"
      (rects[8]? == some ⟨150, 100, 195, 125⟩))
    failures := failures + (← check "synth highlight rect"
      (match rects[4]? with
       | some r => 96 < r.x0 && r.x0 < 97 && 163 < r.x1 && r.x1 < 164
       | none => false))
    let hl := ds[4]?
    failures := failures + (← check "synth highlight multiply"
      (match hl with
       | some d => has ((String.fromUTF8? d.ap.data).getD "") "/H gs" &&
           bmOf d.ap.dict == some (.name (Name.ofString "Multiply"))
       | none => false))
    failures := failures + (← check "synth matrix identity"
      (ds.all (·.matrix == Content.Matrix.identity)))
    -- pixels sampled from `mutool draw -r 72` (device y = 200 − page y)
    let img := o.img
    let samples : List (String × Nat × Nat × (Nat × Nat × Nat)) := [
      ("square interior", 50, 160, (0, 0, 255)), ("square border", 21, 160, (255, 0, 0)),
      ("outside square", 19, 160, (255, 255, 255)), ("highlight multiply", 130, 22, (229, 229, 0)),
      ("circle", 140, 120, (0, 127, 0)), ("circle right", 179, 150, (14, 134, 14)),
      ("rd square cmyk", 170, 85, (255, 0, 255)), ("strike out alpha", 130, 63, (255, 88, 88)),
      ("strike out edge", 130, 64, (255, 244, 244)), ("white", 100, 99, (255, 255, 255))]
    for (n, x, y, c) in samples do
      failures := failures + (← check s!"synth px {n}" (near (pxAt img x y) c))
    if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
      writePpm (System.FilePath.mk dir / "synth.ppm") img
      IO.FS.writeBinFile (System.FilePath.mk dir / "synth.pdf") synthFixture
  return failures

/-- Task 8.3c (1): optional content. Eight red squares (`/AP` 8) with `/OC`: group 5 (ON),
6 (OFF in `/D`), 7 (`/Usage /View /ViewState /OFF`), membership dictionaries `AllOn [5 6]`,
`AnyOn [5 6]`, `AllOff 6`, a `/VE` array (visible, as MuPDF), `AnyOff [5]`. `ocProps` is the
catalog's `/OCProperties`. -/
def ocFixture (ocProps : String) : ByteArray := mkPdf [
  s!"<< /Type /Catalog /Pages 2 0 R /OCProperties {ocProps} >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R " ++
    "/Annots [9 0 R 10 0 R 11 0 R 12 0 R 13 0 R 14 0 R 15 0 R 16 0 R] >>",
  strmObj "" "",
  "<< /Type /OCG /Name (on) >>",
  "<< /Type /OCG /Name (off) >>",
  "<< /Type /OCG /Name (u) /Usage << /View << /ViewState /OFF >> >> >>",
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 10 10]" "1 0 0 rg 0 0 10 10 re f",
  "<< /Type /Annot /Subtype /Square /Rect [10 10 30 30] /AP << /N 8 0 R >> /OC 5 0 R >>",
  "<< /Type /Annot /Subtype /Square /Rect [40 10 60 30] /AP << /N 8 0 R >> /OC 6 0 R >>",
  "<< /Type /Annot /Subtype /Square /Rect [70 10 90 30] /AP << /N 8 0 R >> " ++
    "/OC << /Type /OCMD /OCGs [5 0 R 6 0 R] /P /AllOn >> >>",
  "<< /Type /Annot /Subtype /Square /Rect [100 10 120 30] /AP << /N 8 0 R >> " ++
    "/OC << /Type /OCMD /OCGs [5 0 R 6 0 R] >> >>",
  "<< /Type /Annot /Subtype /Square /Rect [130 10 150 30] /AP << /N 8 0 R >> " ++
    "/OC << /Type /OCMD /OCGs 6 0 R /P /AllOff >> >>",
  "<< /Type /Annot /Subtype /Square /Rect [160 10 180 30] /AP << /N 8 0 R >> /OC 7 0 R >>",
  "<< /Type /Annot /Subtype /Square /Rect [10 40 30 60] /AP << /N 8 0 R >> " ++
    "/OC << /Type /OCMD /OCGs 6 0 R /VE [/And 6 0 R] >> >>",
  "<< /Type /Annot /Subtype /Square /Rect [40 40 60 60] /AP << /N 8 0 R >> " ++
    "/OC << /Type /OCMD /OCGs [5 0 R] /P /AnyOff >> >>"]

/-- Centres of the eight squares of `ocFixture` in device pixels (zoom 1, y = 200 − page y). -/
def ocCentres : List (Nat × Nat) :=
  [(20, 180), (50, 180), (80, 180), (110, 180), (140, 180), (170, 180), (20, 150), (50, 150)]

/-- Task 8.3c (2, 3): annotations without `/AP` synthesised like MuPDF: Polygon, PolyLine with
line endings, Lines with every `/LE` style, Squiggly, Caret, Text icons (Note; Comment on a dark
fill), FileAttachment (default PushPin), Sound with an unknown name (star). -/
def synth2Fixture : ByteArray := mkPdf ([
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 300 300] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Annots [" ++
    " ".intercalate ((List.range 17).map fun i => s!"{i + 5} 0 R") ++ "] >>",
  strmObj "" "",
  -- 5 polygon (filled), 6 polyline with endings
  "<< /Type /Annot /Subtype /Polygon /Rect [0 0 1 1] /Vertices [20 20 80 20 90 60 40 80] " ++
    "/C [0 0 1] /IC [1 1 0] /BS << /W 2 >> >>",
  "<< /Type /Annot /Subtype /PolyLine /Rect [0 0 1 1] /Vertices [110 20 150 60 190 30 230 70] " ++
    "/C [1 0 0] /IC [0 1 0] /LE [/ClosedArrow /Circle] /BS << /W 1.5 >> >>",
  -- 7–11 lines with endings
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [20 110 120 110] /C [0 0 0] " ++
    "/LE [/Square /Diamond] /IC [0 0.6 1] >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [150 110 260 130] /C [0 0.5 0] " ++
    "/LE [/OpenArrow /ROpenArrow] /BS << /W 2 >> >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [20 140 120 160] /C [0.5 0 0.5] " ++
    "/LE [/Butt /Slash] /BS << /W 1 >> >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [150 150 260 150] /C [0 0 1] " ++
    "/LE [/RClosedArrow /None] /IC [1 0 0] >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [20 180 120 200] /C [1 0.5 0] /LL 10 " ++
    "/LE [/Circle /ClosedArrow] >>",
  -- 12 squiggly over a gray box
  "<< /Type /Annot /Subtype /Squiggly /Rect [0 0 1 1] " ++
    "/QuadPoints [150 195 260 195 150 180 260 180] /C [1 0 0] >>",
  -- 13 caret
  "<< /Type /Annot /Subtype /Caret /Rect [20 220 50 240] /C [0 0 1] >>",
  -- 14–19 icons
  "<< /Type /Annot /Subtype /Text /Rect [70 220 90 240] /C [1 1 0] >>",
  "<< /Type /Annot /Subtype /Text /Rect [110 220 130 240] /Name /Comment /C [0 0 0.4] >>",
  "<< /Type /Annot /Subtype /FileAttachment /Rect [150 220 170 240] /C [0.8 0.9 1] >>",
  "<< /Type /Annot /Subtype /Sound /Rect [190 220 210 240] /Name /Whatever >>",
  "<< /Type /Annot /Subtype /Text /Rect [230 220 250 240] /Name /Help /C [0.2 0.1 0 0] >>",
  "<< /Type /Annot /Subtype /Text /Rect [20 260 40 280] /Name /Key /C [1 0.8 0.8] /CA 0.5 >>",
  -- 20, 21: polygon given clockwise (written reversed), dashed polyline with butt ends
  "<< /Type /Annot /Subtype /Polygon /Rect [0 0 1 1] /Vertices [180 250 220 290 260 250] " ++
    "/C [0 0 0] /IC [0.5 0.5 1] >>",
  "<< /Type /Annot /Subtype /PolyLine /Rect [0 0 1 1] /Vertices [60 260 140 270] " ++
    "/C [0 0 0] /LE [/Butt /Square] /Border [0 0 2 [4 2]] >>"])

/-- Task 8.3c checks (`SAFEPDF_PPM_DIR` writes `oc-d.pdf`, `oc-configs.pdf` and their renders). -/
def run83c : IO Nat := do
  let mut failures := 0
  -- (1) /D: 6 off. (2) /Configs [0] wins over /D: everything on except 5.
  let cases : List (String × String × List Nat) := [
    ("oc-d", "<< /OCGs [5 0 R 6 0 R 7 0 R] /D << /OFF [6 0 R] >> >>", [0, 2, 3, 4, 6]),
    ("oc-configs", "<< /OCGs [5 0 R 6 0 R 7 0 R] /D << /BaseState /OFF /ON [5 0 R] >> " ++
      "/Configs [<< /OFF [5 0 R] >>] >>", [1, 2, 3, 6]),
    ("oc-none", "<< /OCGs [] /D << >> >>", [0, 1, 2, 3, 4, 5, 6, 7])]
  for (name, props, drawn) in cases do
    let pdf := ocFixture props
    match process pdf with
    | none => failures := failures + (← check s!"{name} processes" false)
    | some o =>
      let c := o.ap.collected
      failures := failures + (← check s!"{name} drawn" (c.drawn.map (·.index) == drawn))
      failures := failures + (← check s!"{name} skipped"
        (c.skipped == ((List.range 8).filter (!drawn.contains ·)).map (·, .ocHidden)))
      for (i, (x, y)) in (List.range 8).zip ocCentres do
        let want := if drawn.contains i then (255, 0, 0) else (255, 255, 255)
        failures := failures + (← check s!"{name} px {i}" (pxAt o.img x y == want))
      if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
        writePpm (System.FilePath.mk dir / s!"{name}.ppm") o.img
        IO.FS.writeBinFile (System.FilePath.mk dir / s!"{name}.pdf") pdf
  -- (3) Polygon, PolyLine, line endings, Squiggly, Caret, icons
  match process synth2Fixture with
  | none => failures := failures + (← check "synth2 processes" false)
  | some o =>
    let ds := o.ap.collected.drawn
    failures := failures + (← check "synth2 all drawn"
      (ds.length == 17 && ds.all (·.synth) && o.ap.collected.skipped.isEmpty))
    -- caret: 20 × 14 centred on /Rect, form box [0 0 20 14] mapped by a translation
    failures := failures + (← check "synth2 caret rect"
      ((ds[8]?.map (·.rect)) == some ⟨25, 223, 45, 237⟩ &&
       (ds[8]?.map (·.matrix)) == some (Annot.aOf ⟨25, 223, 45, 237⟩ ⟨0, 0, 20, 14⟩).matrix))
    -- icon: 18 × 18 centred on /Rect, form box 16 × 16 (scale 9/8)
    failures := failures + (← check "synth2 icon rect"
      ((ds[9]?.map (·.rect)) == some ⟨71, 221, 89, 239⟩ &&
       (ds[9]?.map (·.ap.dict)).bind Content.Run.bboxOf ==
         some (Content.Fixed.zero, Content.Fixed.zero, Content.Fixed.ofInt 16, Content.Fixed.ofInt 16)))
    -- pixels sampled from `mutool draw -r 72` (device y = 300 − page y)
    let samples : List (String × Nat × Nat × (Nat × Nat × Nat)) := [
      ("polygon interior", 50, 260, (255, 255, 0)), ("closed arrow interior", 115, 272, (0, 255, 0)),
      ("reversed polygon", 220, 30, (127, 127, 255)), ("square ending", 20, 190, (0, 153, 255)),
      ("diamond ending", 120, 190, (0, 153, 255)), ("note stripe", 80, 70, (0, 0, 0)),
      ("attachment fill", 160, 70, (204, 229, 255)), ("star", 200, 70, (0, 0, 0)),
      ("help cmyk fill", 240, 70, (71, 80, 89)), ("white", 260, 190, (255, 255, 255))]
    for (n, x, y, c) in samples do
      failures := failures + (← check s!"synth2 px {n}" (near (pxAt o.img x y) c))
    if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
      writePpm (System.FilePath.mk dir / "synth2.ppm") o.img
      IO.FS.writeBinFile (System.FilePath.mk dir / "synth2.pdf") synth2Fixture
  return failures

/-- Task 8.3d (1): NoRotate on a page with `/Rotate rot`. Two 40 × 20 annotations whose
appearance fills the left half red (`/BBox [0 0 40 20]`): (0) with `/F 16` (NoRotate),
(1) without. -/
def noRotFixture (rot : Nat) : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  s!"<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 200] /Rotate {rot} >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Annots [6 0 R 7 0 R] >>",
  strmObj "" "",
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 40 20]" "1 0 0 rg 0 0 20 20 re f",
  "<< /Type /Annot /Subtype /Square /F 16 /Rect [40 100 80 120] /AP << /N 5 0 R >> >>",
  "<< /Type /Annot /Subtype /Square /Rect [120 100 160 120] /AP << /N 5 0 R >> >>"]

/-- Task 8.3d (2, 3): FreeText and Stamp without `/AP`: (0) centred, wrapping Helvetica on a
filled box with a 2-point border; (1) right-aligned Times at `/DA` size 0 (→ 12) with a line
break and `/RD`; (2) a callout with an open arrow, Courier; (3) text turned by `/Rotate 90`;
(4) an `Approved` stamp; (5) the default `Draft` stamp at half opacity; (6) a two-line stamp. -/
def textFixture : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 300 300] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R " ++
    "/Annots [5 0 R 6 0 R 7 0 R 8 0 R 9 0 R 10 0 R 11 0 R] >>",
  strmObj "" "",
  "<< /Type /Annot /Subtype /FreeText /Rect [20 20 180 80] /C [1 1 0.8] /BS << /W 2 >> /Q 1 " ++
    "/DA (/Helv 12 Tf 0 0 1 rg) /Contents (Hello world, this text is long enough to wrap) >>",
  "<< /Type /Annot /Subtype /FreeText /Rect [200 20 290 80] /C [0.9] /Q 2 /RD [2 2 2 2] " ++
    "/DA (/TiRo 0 Tf 1 0 0 rg) /Contents (First line\\nSecond) >>",
  "<< /Type /Annot /Subtype /FreeText /Rect [20 100 100 140] /IT /FreeTextCallout " ++
    "/CL [150 170 120 150 100 120] /LE /OpenArrow /DA (/Cour 9 Tf 0 g) /Contents (Callout) >>",
  "<< /Type /Annot /Subtype /FreeText /Rect [200 100 240 180] /Rotate 90 /C [0.8 0.9 1] " ++
    "/DA (/Helv 10 Tf 0 g) /Contents (Turned) >>",
  "<< /Type /Annot /Subtype /Stamp /Rect [20 200 160 280] /Name /Approved /C [0 0.5 0] >>",
  "<< /Type /Annot /Subtype /Stamp /Rect [180 200 290 240] /CA 0.5 >>",
  "<< /Type /Annot /Subtype /Stamp /Rect [180 250 290 290] /Name /NotForPublicRelease " ++
    "/C [0.8 0 0] >>"]

/-- Task 8.3d (4): Line `/Cap` captions: (0) inline (the line broken by the gap), (1) `/CP /Top`
on a slanted line, (2) too long for its line (drawn on top), (3) an offset `/CO` with endings. -/
def capFixture : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 300 300] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Annots [5 0 R 6 0 R 7 0 R 8 0 R] >>",
  strmObj "" "",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [20 50 280 50] /Cap true " ++
    "/Contents (Inline caption) /C [0 0 1] >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [20 100 280 140] /Cap true /CP /Top " ++
    "/Contents (Top caption) /C [1 0 0] /BS << /W 2 >> >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [20 180 60 180] /Cap true " ++
    "/Contents (Too long to fit) /C [0 0.5 0] >>",
  "<< /Type /Annot /Subtype /Line /Rect [0 0 1 1] /L [100 220 280 220] /Cap true /CO [10 -5] " ++
    "/Contents (Offset) /LE [/OpenArrow /Circle] /C [0 0 0] >>"]

/-- Task 8.3d checks. -/
def run83d : IO Nat := do
  let mut failures := 0
  -- (1) NoRotate: pixels sampled from `mutool draw -r 72` (device space of the rotated page)
  let cases : List (Nat × List (Nat × Nat × (Nat × Nat × Nat))) := [
    (0, [(50, 90, (255, 0, 0)), (70, 90, (255, 255, 255))]),
    (90, [(130, 50, (255, 0, 0)), (150, 50, (255, 255, 255)), (110, 130, (255, 0, 0))]),
    (180, [(170, 130, (255, 0, 0)), (190, 130, (255, 255, 255)), (70, 110, (255, 0, 0))]),
    (270, [(90, 170, (255, 0, 0)), (110, 170, (255, 255, 255)), (90, 70, (255, 0, 0))])]
  for (rot, samples) in cases do
    let pdf := noRotFixture rot
    match process pdf with
    | none => failures := failures + (← check s!"norot {rot} processes" false)
    | some o =>
      for (x, y, c) in samples do
        failures := failures + (← check s!"norot {rot} px ({x}, {y})" (pxAt o.img x y == c))
      if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
        writePpm (System.FilePath.mk dir / s!"norot{rot}.ppm") o.img
        IO.FS.writeBinFile (System.FilePath.mk dir / s!"norot{rot}.pdf") pdf
  -- (2, 3) FreeText and Stamp
  match process textFixture with
  | none => failures := failures + (← check "text fixture processes" false)
  | some o =>
    let ds := o.ap.collected.drawn
    failures := failures + (← check "text all drawn"
      (ds.length == 7 && ds.all (·.synth) && o.ap.collected.skipped.isEmpty))
    let rects := ds.map (·.rect)
    -- /RD insets the rectangle; the callout grows it; the stamp keeps the 190 : 50 aspect
    failures := failures + (← check "freetext rd rect" (rects[1]? == some ⟨202, 22, 288, 78⟩))
    failures := failures + (← check "freetext callout rect"
      (rects[2]? == some ⟨19, 99, 151, 171⟩))
    failures := failures + (← check "stamp rect"
      (rects[4]? == some ⟨20, 4210 / 19, 160, 4910 / 19⟩ &&
       (ds[4]?.map (·.matrix)) == some (Annot.aOf ⟨20, 4210 / 19, 160, 4910 / 19⟩
         ⟨0, 0, 190, 50⟩).matrix))
    -- the synthesised base-14 fonts are in the annotation font table (pseudo owner)
    failures := failures + (← check "synth fonts"
      ([(0, "Helv"), (1, "TiRo"), (2, "Cour"), (4, "Times")].all fun (i, n) =>
        o.ap.fonts.any fun (k, _) => k == .res (Annot.synthNum i) (Name.ofString n)))
    -- content: centred first line (MuPDF's `mutool draw -F stext` line starts at x 27.31)
    failures := failures + (← check "freetext layout"
      (match ds[0]? with
       | some d => has ((String.fromUTF8? d.ap.data).getD "")
           "4.000000 60.800000 Td\n3.310000 -14.400000 Td\n/Helv 12.000000 Tf\n"
       | none => false))
    -- pixels sampled from `mutool draw -r 72` away from the text (device y = 300 − page y)
    let samples : List (String × Nat × Nat × (Nat × Nat × Nat)) := [
      ("fill", 100, 270, (255, 255, 204)), ("border", 100, 279, (0, 0, 255)),
      ("gray rd fill", 245, 270, (229, 229, 229)), ("da border", 202, 250, (255, 0, 0)),
      ("rotated fill", 230, 150, (204, 229, 255)), ("rotated border", 200, 190, (0, 0, 0)),
      ("callout", 135, 140, (184, 184, 184)), ("stamp frame", 100, 76, (33, 144, 33)),
      ("stamp half opacity", 230, 92, (154, 154, 154)), ("white", 235, 30, (255, 255, 255))]
    for (n, x, y, c) in samples do
      failures := failures + (← check s!"text px {n}" (near (pxAt o.img x y) c))
    if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
      writePpm (System.FilePath.mk dir / "text.ppm") o.img
      IO.FS.writeBinFile (System.FilePath.mk dir / "text.pdf") textFixture
    -- text: the lines of `mutool draw -F txt` (MuPDF 1.25.1), blank lines aside
    match firstPage textFixture with
    | none => failures := failures + 1
    | some (d, p) =>
      match (Annot.extractDocPageAnnots {} d p (Filter.Budget.init {})).1 with
      | .ok t =>
        failures := failures + (← check "freetext/stamp text"
          ((t.text.splitOn "\n").filter (· != "") == ["Hello world, this text is long ",
            "enough to wrap", "First line", "Second", "Callout", "Turned", "APPROVED", "DRAFT",
            "NOT FOR", "PUBLIC RELEASE"]))
      | .error _ => failures := failures + (← check "text extracts" false)
  -- (4) line captions
  match process capFixture with
  | none => failures := failures + (← check "cap fixture processes" false)
  | some o =>
    let ds := o.ap.collected.drawn
    failures := failures + (← check "cap all drawn" (ds.length == 4 && ds.all (·.synth)))
    failures := failures + (← check "cap inline rect"
      ((ds[0]?.map (·.rect)) == some ⟨7, 167 / 5, 293, 63⟩))
    -- the inline caption starts where MuPDF's `-F stext` line does (x 114.648); the line is
    -- broken by the gap `(tw + 6) / 2` about the middle
    failures := failures + (← check "cap inline content"
      (match ds[0]? with
       | some d =>
         let c := (String.fromUTF8? d.ap.data).getD ""
         has c "114.648000 46.400000 cm\n0 g\nBT\n/Helv 12.000000 Tf\n(Inline caption) Tj" &&
           has c "20.000000 50.000000 m\n111.648000 50.000000 l\n188.352000 50.000000 m"
       | none => false))
    failures := failures + (← check "cap font" (o.ap.fonts.any fun (k, _) =>
      k == .res (Annot.synthNum 0) (Name.ofString "Helv")))
    -- pixels from `mutool draw -r 72` (device y = 300 − page y): line, gap, slanted top line
    let samples : List (String × Nat × Nat × (Nat × Nat × Nat)) := [
      ("line", 100, 250, (118, 118, 255)), ("gap", 113, 250, (255, 255, 255)),
      ("line after gap", 190, 250, (118, 118, 255)), ("no gap when on top", 40, 120,
        (118, 186, 118)), ("offset line", 250, 80, (118, 118, 118)),
      ("white", 150, 200, (255, 255, 255))]
    for (n, x, y, c) in samples do
      failures := failures + (← check s!"cap px {n}" (near (pxAt o.img x y) c))
    if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
      writePpm (System.FilePath.mk dir / "cap.ppm") o.img
      IO.FS.writeBinFile (System.FilePath.mk dir / "cap.pdf") capFixture
    match firstPage capFixture with
    | none => failures := failures + 1
    | some (d, p) =>
      match (Annot.extractDocPageAnnots {} d p (Filter.Budget.init {})).1 with
      | .ok t =>
        -- MuPDF prints "Inline caption", "Top caption", "Too long to fi", "Offset" (our layout
        -- splits the slanted line; MuPDF drops the last glyph of the third)
        failures := failures + (← check "cap text"
          (String.join ((t.text.splitOn "\n")) ==
            "Inline captionTop captionToo long to fitOffset"))
      | .error _ => failures := failures + (← check "cap text extracts" false)
  return failures

/-- Task 8.3e (1, 2): FreeText default appearance and rich text. The catalog's `/AcroForm /DA`
is red 14-point Courier. (0) no `/DA`: the `/AcroForm /DA` fallback; (1) `/DS` Times 18 pt
blue, wrapping, no `/DA` (the border still takes the fallback's red); (2) `/DS` Helvetica 12 pt
centred over `/DA` Helvetica 10 black; (3) `/RC` markup (two paragraphs, an entity, a bold
span, a whitespace run) with a blue `/DA` (the text stays black; only the border is blue). -/
def richFixture : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R /AcroForm << /DA (/Cour 14 Tf 1 0 0 rg) >> >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 300 300] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Annots [5 0 R 6 0 R 7 0 R 8 0 R] >>",
  strmObj "" "",
  "<< /Type /Annot /Subtype /FreeText /Rect [20 230 280 290] /Contents (Fallback DA text) >>",
  "<< /Type /Annot /Subtype /FreeText /Rect [20 120 120 220] " ++
    "/DS (font: 18pt Times; color: #0000FF) /Contents (Styled text here and more) >>",
  "<< /Type /Annot /Subtype /FreeText /Rect [150 120 280 220] /DA (/Helv 10 Tf 0 g) " ++
    "/DS (font-size: 12pt; font-family: Helvetica; text-align: center) " ++
    "/Contents (Sans text that wraps around) >>",
  "<< /Type /Annot /Subtype /FreeText /Rect [20 20 280 100] /DA (/Helv 10 Tf 0 0 1 rg) " ++
    "/RC (<?xml version=\"1.0\"?><body><p>Rich &amp; <b>bold</b></p><p>Second   para</p>" ++
    "</body>) /Contents (Plain contents) >>"]

/-- Task 8.3e (3): cloudy borders (`/BE /S /C`): (0) a stroked square, intensity 1; (1) a filled
square, intensity 2, width 2; (2) a filled circle; (3) a stroked polygon. -/
def cloudFixture : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 300 300] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Annots [5 0 R 6 0 R 7 0 R 8 0 R] >>",
  strmObj "" "",
  "<< /Type /Annot /Subtype /Square /Rect [20 180 140 280] /BE << /S /C /I 1 >> /C [1 0 0] >>",
  "<< /Type /Annot /Subtype /Square /Rect [160 180 280 280] /BE << /S /C /I 2 >> /C [0 0 1] " ++
    "/IC [1 1 0] /BS << /W 2 >> >>",
  "<< /Type /Annot /Subtype /Circle /Rect [20 20 140 140] /BE << /S /C /I 1 >> /C [0 0.5 0] " ++
    "/IC [0.8 0.8 1] >>",
  "<< /Type /Annot /Subtype /Polygon /Rect [0 0 1 1] /Vertices [170 30 280 40 260 150 180 120] " ++
    "/BE << /S /C /I 1 >> /C [0 0 0] >>"]

/-- Task 8.3e checks. -/
def run83e : IO Nat := do
  let mut failures := 0
  -- (3) cloudy borders
  match process cloudFixture with
  | none => failures := failures + (← check "cloud fixture processes" false)
  | some o =>
    let ds := o.ap.collected.drawn
    failures := failures + (← check "cloud all drawn" (ds.length == 4 && ds.all (·.synth)))
    -- rectangles grow by the cloud radius (MuPDF's `getRect` is these less `/RD`, 5 or 10)
    failures := failures + (← check "cloud rects"
      ((ds.map (·.rect)).take 3 == [⟨31 / 2, 351 / 2, 289 / 2, 569 / 2⟩, ⟨151, 171, 289, 289⟩,
        ⟨31 / 2, 31 / 2, 289 / 2, 289 / 2⟩]))
    -- the first arc of the first square: MuPDF 1.25.1's content (`mutool run`, `update()`)
    failures := failures + (← check "cloud content"
      (match ds[0]? with
       | some d => has ((String.fromUTF8? d.ap.data).getD "")
           ("2 j\n18.012532 184.250000 m\n17.393706 184.660482 16.886082 185.217728 " ++
            "16.534927 185.872044 c\n")
       | none => false))
    -- pixels sampled from `mutool draw -r 72` (device y = 300 − page y): scallops and fills
    -- (the whole page differs from MuPDF in 0.234% of pixels, 211 of 90,000: anti-aliasing of
    -- the 1-point arcs)
    let samples : List (String × Nat × Nat × (Nat × Nat × Nat)) := [
      ("square scallop", 16, 112, (255, 115, 115)), ("filled square", 220, 70, (255, 255, 0)),
      ("filled scallop outside /Rect", 152, 104, (0, 0, 255)),
      ("circle fill", 80, 220, (204, 204, 255)), ("polygon scallop", 283, 260, (63, 63, 63)),
      ("white", 150, 150, (255, 255, 255))]
    for (n, x, y, c) in samples do
      failures := failures + (← check s!"cloud px {n}" (near (pxAt o.img x y) c))
    -- trigonometry to 10⁻⁸
    let close := fun (a b : Rat) => decide (a - b ≤ 1 / 100000000 ∧ b - a ≤ 1 / 100000000)
    failures := failures + (← check "cloud trig"
      (close (Annot.sinR (Annot.piR / 6)) (1 / 2) && close (Annot.cosR (Annot.piR / 3)) (1 / 2) &&
       close (Annot.sinR (-7 * Annot.piR / 2)) 1 && close (Annot.atan2R 1 1) (Annot.piR / 4) &&
       close (Annot.atan2R (-1) (-1)) (-3 * Annot.piR / 4) &&
       close (Annot.atanR 3) (1249045772 / 1000000000) &&
       close (Annot.sqrtR 2) (1414213562 / 1000000000)))
    if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
      writePpm (System.FilePath.mk dir / "cloud.ppm") o.img
      IO.FS.writeBinFile (System.FilePath.mk dir / "cloud.pdf") cloudFixture
  -- CSS pieces
  failures := failures + (← check "css colour" (Annot.cssColor "#00f".toList == some [0, 0, 1] &&
    Annot.cssColor "rgb(255, 0, 51)".toList == some [1, 0, 1 / 5] &&
    Annot.cssColor " Teal".toList == some (Annot.rgb255 0 128 128) &&
    Annot.cssColor "bogus".toList == none))
  let rs := Annot.richStyle 10 "font: italic 2em Courier New; color: red; text-align: right".toList
  failures := failures + (← check "css style"
    (rs.da.font == "Cour" && rs.da.size == 20 && rs.da.color == [1, 0, 0] && rs.align == 2))
  failures := failures + (← check "rc text"
    (String.ofList (Annot.richText true "<p>a &lt;b&gt;</p>\n<p> c  <br/>d&#65;</p>".toList) ==
      "a <b>\nc\ndA"))
  failures := failures + (← check "ds contents collapse"
    (String.ofList (Annot.richText false "a\nb   c ".toList) == "a b c"))
  match process richFixture with
  | none => failures := failures + (← check "rich fixture processes" false)
  | some o =>
    let ds := o.ap.collected.drawn
    failures := failures + (← check "rich all drawn" (ds.length == 4 && ds.all (·.synth)))
    -- fonts: the fallback's Courier, the rich Times / Helvetica
    failures := failures + (← check "rich fonts"
      ([(0, "Cour"), (1, "TiRo"), (2, "Helv"), (3, "TiRo")].all fun (i, n) =>
        o.ap.fonts.any fun (k, _) => k == .res (Annot.synthNum i) (Name.ofString n)))
    -- first glyph of each line: MuPDF 1.25.1 `-F stext` char origins (page y = 300 − y)
    let gs := Text.extractItems o.ap.fonts o.ap.items.toList
    let starts := [(22000000, 276800000), (22000000, 201800000), (22000000, 180200000),
      (22000000, 158600000), (159640000, 207200000), (195322000, 192800000),
      (22000000, 89000000), (22000000, 77000000)]
    failures := failures + (← check "rich line origins" (starts.all fun (x, y) =>
      gs.any fun g => (g.x.raw - x).natAbs ≤ 2000 && g.y.raw == y))
    -- pixels sampled from `mutool draw -r 72`: borders take the `/DA` (or fallback) colour
    let samples : List (String × Nat × Nat × (Nat × Nat × Nat)) := [
      ("fallback border", 150, 10, (255, 0, 0)), ("ds border (fallback)", 70, 80, (255, 0, 0)),
      ("ds left border", 20, 150, (255, 0, 0)), ("da border", 200, 80, (0, 0, 0)),
      ("rc da border", 150, 279, (0, 0, 255)), ("white", 150, 220, (255, 255, 255))]
    for (n, x, y, c) in samples do
      failures := failures + (← check s!"rich px {n}" (near (pxAt o.img x y) c))
    if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
      writePpm (System.FilePath.mk dir / "rich.ppm") o.img
      IO.FS.writeBinFile (System.FilePath.mk dir / "rich.pdf") richFixture
  -- text: the lines of `mutool draw -F txt` (MuPDF 1.25.1)
  match firstPage richFixture with
  | none => failures := failures + 1
  | some (d, p) =>
    match (Annot.extractDocPageAnnots {} d p (Filter.Budget.init {})).1 with
    | .ok t =>
      failures := failures + (← check "rich text"
        ((t.text.splitOn "\n").filter (· != "") == ["Fallback DA text", "Styled text",
          "here and", "more", "Sans text that wraps", "around", "Rich & bold", "Second para"]))
    | .error _ => failures := failures + (← check "rich text extracts" false)
  return failures

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let ttf ← IO.FS.readBinFile "Tests/fonts/tiny.ttf"
  let pdf := fixture ttf
  let mut failures := 0
  match process pdf with
  | none => IO.eprintln "annot: FAILED fixture does not process"; return 1
  | some o =>
    let c := o.ap.collected
    -- drawn: square (1), stamp (3), free text (4), then the widget (0)
    failures := failures + (← check "order" (c.drawn.map (·.index) == [1, 3, 4, 0]))
    failures := failures + (← check "skips" (c.skipped ==
      [(2, .hidden), (5, .link), (6, .popup), (7, .noAppearance), (8, .noField), (9, .noView),
       (10, .duplicate)]))
    -- (a) the square's A: scale 2, translate (40, 40) (the /Rect was given reversed)
    let boxes := fillBoxes o.ap.items
    failures := failures + (← check "square box"
      (boxes.head? == some [(40, 40), (60, 40), (60, 60), (40, 60)]))
    -- (d) the stamp: form (x, y) ↦ (120 − y, 20 + x); filled form y ∈ [0, 10]
    failures := failures + (← check "stamp box"
      (boxes[1]? == some [(120, 20), (120, 60), (110, 60), (110, 20)]))
    -- (b) the widget's /On appearance, last
    failures := failures + (← check "widget box"
      (boxes[2]? == some [(150, 150), (170, 150), (170, 170), (150, 170)]))
    failures := failures + (← check "colours" (fillColors o.ap.items ==
      [.rgb Content.Comp.one Content.Comp.zero Content.Comp.zero,
       .rgb Content.Comp.zero Content.Comp.zero Content.Comp.zero,
       .rgb Content.Comp.zero Content.Comp.one Content.Comp.zero]))
    -- (e) the free text: glyphs at (22, 154) and (22 + 12 · 0.6, 154) = (29.2, 154)
    let gs := Text.extractItems o.ap.fonts o.ap.items.toList
    failures := failures + (← check "free text glyphs"
      (gs.map (fun g => (g.text, g.x.raw, g.y.raw)) ==
        [("A", 22000000, 154000000), ("A", 29200000, 154000000)]))
    failures := failures + (← check "free text font from AP resources"
      (o.ap.fonts.any fun (k, _) => k == .obj 21 0))
    failures := failures + (← check "budget"
      (o.ap.ops ≤ 1000000 && !o.ap.truncated && o.ap.forms == 4))
    -- pixels (device y = 200 − page y)
    let img := o.img
    failures := failures + (← check "px page blue" (pxAt img 10 190 == (0, 0, 255)))
    failures := failures + (← check "px square red" (pxAt img 50 150 == (255, 0, 0)))
    failures := failures + (← check "px widget green" (pxAt img 160 40 == (0, 255, 0)))
    failures := failures + (← check "px hidden white" (pxAt img 25 75 == (255, 255, 255)))
    failures := failures + (← check "px stamp black" (pxAt img 115 160 == (0, 0, 0)))
    failures := failures + (← check "px stamp white half" (pxAt img 105 160 == (255, 255, 255)))
    -- the text's first glyph (tiny.ttf `A`: an arch over 600 units, height 700 → 7.2 × 8.4 px
    -- at 12 pt) has ink near its base centre
    let (r, _, _) := pxAt img 25 44
    failures := failures + (← check "px free text ink" (r < 128))
    if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
      writePpm (System.FilePath.mk dir / "annot.ppm") img
      IO.FS.writeBinFile (System.FilePath.mk dir / "annot.pdf") pdf
  -- a tiny shared budget truncates: 2 operators in all
  match process pdf { ops := 2, forms := 1000 } with
  | none => failures := failures + 1
  | some o =>
    failures := failures + (← check "tiny budget" (o.ap.truncated && o.ap.ops ≤ 2))
  failures := failures + (← run83b pdf)
  failures := failures + (← run83c)
  failures := failures + (← run83d)
  failures := failures + (← run83e)
  return failures

end SafePdf.Tests.Annot
