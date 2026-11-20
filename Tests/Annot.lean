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
* skips: `/Link`, `/Popup`, a `/Square` without `/AP`, a widget without `/FT`, a duplicate
  reference;
* the shared operator budget (a tiny budget truncates);
* pixels of the full render (`Glyph.renderPage` over page items ++ annotation items).
  Set `SAFEPDF_PPM_DIR=<dir>` to write the render (`annot.ppm`) and the PDF (`annot.pdf`).
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
  -- 15: link, 16: popup, 17: square without /AP
  "<< /Type /Annot /Subtype /Link /Rect [0 0 10 10] /AP << /N 8 0 R >> >>",
  "<< /Type /Annot /Subtype /Popup /Rect [0 0 10 10] /AP << /N 8 0 R >> >>",
  "<< /Type /Annot /Subtype /Square /Rect [0 0 10 10] >>",
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
          let (t, b) := Glyph.loadSources lim src acc.2 r.2
          (acc.1 ++ t, b)) (srcs, b2)
        let img := Glyph.renderPage p 1 .r0 ⟨ap.fonts, srcs, {}, {}⟩ items
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
  return failures

end SafePdf.Tests.Annot
