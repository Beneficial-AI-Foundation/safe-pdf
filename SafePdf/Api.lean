import SafePdf.Core.Parse
import SafePdf.Core.Doc
import SafePdf.Core.Doc.Nav
import SafePdf.Core.Font.Encoding
import SafePdf.Core.Font.CMap
import SafePdf.Core.Text
import SafePdf.Core.Annot
import SafePdf.Core.Raster.Geom
import SafePdf.Core.Raster.Glyph

/-!
# `safe-pdf-core`: the public library API (task 8.4; Plan.md §6 Phase 8, §4, §10)

Plan.md §6 Phase 8: "Package: library API (`safe-pdf-core`) + minimal GUI. The core as a
library is the real deliverable — e.g. as a drop-in verified backend for a Zotero-class
reference manager (annotation anchoring, text indexing: exactly C2/C3/C6)." This module is
that API: a small, **pure** facade over the verified core (`SafePdf.Core.*`), with one
optional `IO` helper (`openFile`). It adds no new algorithms; every function delegates to the
core entry points the viewer and the inspector use, and its docstring names the guarantees
it inherits. `docs/api.md` is the user guide (Lake `require`, examples, stability, limits).

| Function | Delegates to | Guarantees |
|---|---|---|
| `openBytes`, `openFile` | `SafePdf.parseWith`, `Core.Doc.ofSession` | S1 totality, S3 limits, S7 strict/repair flag (`openBytes_strict`) |
| `Document.pageCount`, `pageInfo` | `Core.Doc.Doc.pages`, `Core.Doc.Nav.pageLabel` | total page access (Phase 4); CropBox ⊆ MediaBox |
| `pageText` | `Core.Annot.extractDocPageAnnots` / `Core.Text.extractDocPage` | C6 extracted = displayed, C3 text ↔ position (`glyph_provenance`, `glyph_codes`, `pageText_glyphs`) |
| `renderPage` | `Core.Raster.Glyph.renderDocPage` | total, bounded (`Limits`), RGBA shape (`renderPage_size`) |
| `outline`, `pageLinks`, `pageAnnotations` | `Core.Doc.Nav.outline`, `Nav.targetOf`, `/Annots` | cycle-safe walks (`outline_bounded`) |
| `toScreen`, `toPage` | `Core.Raster.Geom.toScreenView`/`toPageView` | C2 round trips (`toPage_toScreen`, `toScreen_toPage`) |

Every per-page call runs with a **fresh** decoded-bytes budget (`Filter.Budget.init`, as the
viewer and the inspector's views do), so pages are independent and a call's cost is bounded
by `Limits` alone. Results are plain data (`Rat` coordinates in PDF page space, `String`s in
Unicode, RGBA bytes); the core types stay reachable (`Document.doc`, `PageText.core`) for
callers that want to apply the core theorems directly.

Unverified-shell rules do not apply here: this file follows the `Core/` rules (no `IO`
except `openFile`, no `partial`, no `!` indexing, no `sorry`).
-/

namespace SafePdf.Api

open SafePdf.Core
open SafePdf.Core.Raster (Geom.Pt Geom.Box)

/-! ## Basic types -/

/-- A point in PDF page space (or screen space), exact rational coordinates. -/
abbrev Pt := Raster.Geom.Pt

/-- An axis-aligned rectangle `[llx lly urx ury]` over ℚ. -/
abbrev Box := Raster.Geom.Box

/-- A clockwise rotation by a multiple of 90°. -/
abbrev Rotation := Doc.Rotation

/-- A rendered page: width and height in pixels and `4 · w · h` RGBA bytes, row-major, top row
first, non-premultiplied, opaque white background (`renderPage_size`). -/
abbrev Image := Raster.Clip.Image

/-- Resource limits (Plan.md §4 S3); `{}` is `Limits.default`. -/
abbrev Limits := SafePdf.Limits

/-- Errors of the API. -/
inductive Error where
  /-- An error of the core (malformed input, limit exceeded, unsupported feature, reference
  cycle, undecryptable file). -/
  | pdf (e : SafePdf.Error)
  /-- The file opened only through the repair path (Plan.md §4 S7) and strict mode was asked
  for (`OpenOptions.allowRepair := false`). -/
  | repairRefused
  /-- A page index past the end of the document (`count` pages). -/
  | pageOutOfRange (index count : Nat)
  /-- A zoom that is not positive. -/
  | badZoom (zoom : Rat)
  deriving Repr, Inhabited

/-- A one-line English description of an error. -/
def Error.message : Error → String
  | .pdf (.malformed off msg) => s!"malformed input at byte {off}: {msg}"
  | .pdf (.limitExceeded k) => s!"resource limit exceeded: {reprStr k}"
  | .pdf (.unsupported what) => s!"unsupported: {what}"
  | .pdf (.cycle off what) => s!"reference cycle at byte {off}: {what}"
  | .pdf (.encryption what) => s!"encryption: {what}"
  | .repairRefused => "the file is damaged and opens only through the repair path (strict mode)"
  | .pageOutOfRange i n => s!"page index {i} out of range (the document has {n} pages)"
  | .badZoom z => s!"zoom must be positive (got {z})"

instance : ToString Error := ⟨Error.message⟩

/-! ## Text strings -/

/-- Decode a PDF text string (ISO 32000-2 §7.9.2.2): UTF-16BE after the `FE FF` byte-order
mark, UTF-8 after `EF BB BF` (PDF 2.0), otherwise PDFDocEncoding (Annex D) through the glyph
list; tab, line feed and carriage return are kept, other undefined bytes become U+FFFD. -/
def textString (bs : List UInt8) : String :=
  match bs with
  | 0xFE :: 0xFF :: rest => Font.CMap.ofUtf16 rest
  | 0xEF :: 0xBB :: 0xBF :: rest =>
    match String.fromUTF8? ⟨rest.toArray⟩ with
    | some s => s
    | none => pdfDoc rest
  | _ => pdfDoc bs
where
  /-- PDFDocEncoding, byte by byte. -/
  pdfDoc (bs : List UInt8) : String :=
    String.join (bs.map fun (b : UInt8) =>
      if b == 9 || b == 10 || b == 13 then String.singleton (Char.ofNat b.toNat)
      else match (Font.pdfDocEncoding.glyph b.toNat).bind Font.glyphToUnicode with
        | some s => s
        | none => String.singleton Font.CMap.replacement)

/-! ## Opening -/

/-- Options for opening a document. -/
structure OpenOptions where
  /-- Resource limits for parsing and every later call on the document. -/
  limits : Limits := {}
  /-- Accept files that open only through the repair path (Plan.md §5.4). `false`: strict
  mode, such files are rejected with `Error.repairRefused`. -/
  allowRepair : Bool := true

/-- An opened document. -/
structure Document where
  /-- The limits every call on this document runs under. -/
  limits : Limits
  /-- The parse result (header, opened cross-reference structure, session). -/
  parsed : SafePdf.Document
  /-- The page tree, flattened (`Core.Doc.Doc`). -/
  doc : Doc.Doc

/-- **Open a PDF from its bytes.** Size check (`Limits.maxInputBytes`), header, strict xref
chain else the repair path (`SafePdf.parseWith`), decryption (empty user password), page
tree (`Core.Doc.ofSession`, in the same decoded-bytes budget as the open). Pure and total:
every input gives a document or an `Error`, within `limits` (S1, S3). Cyclic files are
rejected, never repaired (`Error.pdf (.cycle …)`). -/
def openBytes (bytes : ByteArray) (o : OpenOptions := {}) : Except Error Document :=
  match SafePdf.parseWith o.limits bytes with
  | .error e => .error (.pdf e)
  | .ok d =>
    if d.repaired && !o.allowRepair then .error .repairRefused
    else
      match (Doc.ofSession d.session o.limits).1 with
      | .error e => .error (.pdf e)
      | .ok doc => .ok ⟨o.limits, d, doc⟩

/-- **Open a PDF file** (the only `IO` in this module): reads at most
`Limits.maxInputBytes + 1` bytes (a larger file is rejected before reading), then
`openBytes`. File-system errors are thrown as `IO` errors. -/
def openFile (path : System.FilePath) (o : OpenOptions := {}) : IO (Except Error Document) := do
  let md ← path.metadata
  if md.byteSize.toNat > o.limits.maxInputBytes then
    return .error (.pdf (.limitExceeded .inputBytes))
  let bytes ← IO.FS.readBinFile path
  return openBytes bytes o

namespace Document

/-- Number of pages (the page-tree walk's leaves, `Core.Doc.Doc.pageCount`). -/
def pageCount (d : Document) : Nat := d.doc.pageCount

/-- `true` iff the file was opened by the repair path (Plan.md §4 S7). -/
def repaired (d : Document) : Bool := d.parsed.repaired

/-- `true` iff the trailer has `/Encrypt` (the document was decrypted with the empty user
password). -/
def encrypted (d : Document) : Bool := d.parsed.encrypted

/-- `(major, minor)` of the `%PDF-` header, if it parses. -/
def version (d : Document) : Option (Nat × Nat) := d.parsed.version

/-- The core page at index `i`, or `Error.pageOutOfRange`. -/
def page (d : Document) (i : Nat) : Except Error Doc.Page :=
  if h : i < d.doc.pages.size then .ok d.doc.pages[i] else .error (.pageOutOfRange i d.pageCount)

end Document

/-- **Strict mode (S7)**: a document opened with `allowRepair := false` was not repaired. -/
theorem openBytes_strict {bytes : ByteArray} {o : OpenOptions} {d : Document}
    (hs : o.allowRepair = false) (h : openBytes bytes o = .ok d) : d.repaired = false := by
  unfold openBytes at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hc
      split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        subst h
        simp only [hs, Bool.not_false, Bool.and_true] at hc
        simpa [Document.repaired] using hc

/-! ## Pages -/

/-- What a page looks like before rendering. -/
structure PageInfo where
  /-- 0-based index. -/
  index : Nat
  /-- The page label (`/PageLabels`, §12.4.2), or the 1-based page number as text when the
  document has none for this page. -/
  label : String
  /-- Effective MediaBox (inherited; US Letter when missing). -/
  mediaBox : Box
  /-- Effective CropBox, inside the MediaBox: the visible region, the box `renderPage`,
  `toScreen` and `toPage` use. -/
  cropBox : Box
  /-- Effective `/Rotate`. -/
  rotation : Rotation
  /-- Width and height in points of the displayed CropBox (swapped for 90°/270°). -/
  size : Rat × Rat
  deriving Repr

/-- **Page information** of page `i` (0-based): boxes, rotation, label. Total page access
(Plan.md §6 Phase 4; `Core.Doc.cropBox_sub_media`: CropBox ⊆ MediaBox). The label walk is
cycle-safe (`Core.Doc.Nav.labelTable_nodup`). -/
def pageInfo (d : Document) (i : Nat) : Except Error PageInfo := do
  let p ← d.page i
  let lbl := Doc.Nav.pageLabel d.doc d.limits i
  let crop := Raster.Geom.Box.ofRect p.cropBox
  return { index := i
           label := if lbl.isEmpty then toString (i + 1) else textString lbl
           mediaBox := Raster.Geom.Box.ofRect p.mediaBox
           cropBox := crop
           rotation := p.rotate
           size := Raster.Geom.screenSize 1 p.rotate crop }

/-! ## Coordinates (C2) -/

/-- **Page space → screen space** for page `info` shown at `zoom` pixels per point with an
extra clockwise `rot` (added to the page's `/Rotate`): screen origin at the top-left of the
rendered image, `y` downward. Exactly the transform `renderPage` draws with
(`Core.Raster.Glyph.renderPage`: `viewMatrix zoom (rotAdd page.rotate rot) cropBox`). -/
def toScreen (info : PageInfo) (zoom : Rat) (rot : Rotation) (p : Pt) : Pt :=
  Raster.Geom.toScreenView zoom info.rotation rot info.cropBox p

/-- **Screen space → page space**, the inverse of `toScreen` (C2). Use it to anchor a click,
a selection or an annotation drawn on the image in page coordinates, independent of zoom
and rotation. -/
def toPage (info : PageInfo) (zoom : Rat) (rot : Rotation) (q : Pt) : Pt :=
  Raster.Geom.toPageView zoom info.rotation rot info.cropBox q

/-- **C2 (page → screen → page)** over the API's types: for every positive zoom and every
rotation, `toPage ∘ toScreen = id` (`Core.Raster.Geom.toPageView_toScreenView`). -/
theorem toPage_toScreen (info : PageInfo) {zoom : Rat} (hz : 0 < zoom) (rot : Rotation) (p : Pt) :
    toPage info zoom rot (toScreen info zoom rot p) = p :=
  Raster.Geom.toPageView_toScreenView hz _ _ _ p

/-- **C2 (screen → page → screen)**: `toScreen ∘ toPage = id`. -/
theorem toScreen_toPage (info : PageInfo) {zoom : Rat} (hz : 0 < zoom) (rot : Rotation) (q : Pt) :
    toScreen info zoom rot (toPage info zoom rot q) = q :=
  Raster.Geom.toScreenView_toPageView hz _ _ _ q

/-- `toScreen` is the renderer's view matrix (`Core.Raster.Geom.viewMatrix`) of the combined
rotation on the CropBox. -/
theorem toScreen_eq (info : PageInfo) (zoom : Rat) (rot : Rotation) (p : Pt) :
    toScreen info zoom rot p =
      (Raster.Geom.viewMatrix zoom (Raster.Geom.rotAdd info.rotation rot) info.cropBox).apply p :=
  rfl

/-! ## Text (C3, C6) -/

/-- One extracted glyph. -/
structure Glyph where
  /-- Unicode text (normalised: ligatures decomposed; U+FFFD when the font has no mapping). -/
  text : String
  /-- Origin on the baseline, page space. -/
  origin : Pt
  /-- Page-space box: the advance along the baseline, 0.2 em below to 0.8 em above it, in the
  glyph's direction, made axis-aligned (the viewer's selection boxes). -/
  box : Box
  /-- Page-space font size. -/
  fontSize : Rat
  /-- Baseline direction in quarter turns (0 left-to-right, 1 upwards, 2 upside down,
  3 downwards). -/
  dir : Nat
  /-- Whether the glyph paints (not text render mode 3/7, e.g. an OCR layer). -/
  visible : Bool
  /-- Provenance: index of the `glyphRun` item in the page's display list (C3). -/
  item : Nat
  /-- Provenance: index of the glyph within that run (C3). -/
  seq : Nat
  deriving Repr, Inhabited

/-- A `Fixed` as an exact rational. -/
def fr (x : Content.Fixed) : Rat := Raster.Geom.Fixed.toRat x

/-- Page coordinates of a point given in a baseline direction's frame (inverse of
`Text.rotFrame`). -/
def unFrame (dir : Nat) (u v : Rat) : Rat × Rat :=
  match dir with
  | 1 => (-v, u)
  | 2 => (-u, -v)
  | 3 => (v, -u)
  | _ => (u, v)

/-- The page-space box of a core glyph (see `Glyph.box`). -/
def glyphBox (g : Text.Glyph) : Box :=
  let u0 := fr g.u
  let u1 := fr g.uEnd
  let v := fr g.v
  let s0 := fr g.fontSize
  let s := if s0 < 0 then -s0 else s0
  let (x0, y0) := unFrame g.dir (min u0 u1) (v - s / 5)
  let (x1, y1) := unFrame g.dir (max u0 u1) (v + 4 * s / 5)
  ⟨min x0 x1, min y0 y1, max x0 x1, max y0 y1⟩

/-- The API view of a core glyph. -/
def Glyph.ofCore (g : Text.Glyph) : Glyph where
  text := g.text
  origin := ⟨fr g.x, fr g.y⟩
  box := glyphBox g
  fontSize := fr g.fontSize
  dir := g.dir
  visible := g.visible
  item := g.item
  seq := g.seq

/-- The smallest box containing both. -/
def Box.union (a b : Box) : Box :=
  ⟨min a.llx b.llx, min a.lly b.lly, max a.urx b.urx, max a.ury b.ury⟩

/-- A line of text in reading order. -/
structure TextLine where
  /-- The line's text (word gaps as spaces, overprinted duplicates dropped). -/
  text : String
  /-- Union of its glyph boxes. -/
  box : Box
  /-- Its glyphs, left to right in the line's direction (`Text.lineOrder`). -/
  glyphs : Array Glyph
  deriving Repr, Inhabited

/-- The text of a page. -/
structure PageText where
  /-- The page text in reading order (lines separated by `\n`, paragraphs by a blank line). -/
  text : String
  /-- Lines in reading order. -/
  lines : Array TextLine
  /-- All glyphs in content-stream order (`core.glyphs`, converted). -/
  glyphs : Array Glyph
  /-- The core result (fonts, display list, glyphs): the objects the C3/C6 theorems are
  stated over. -/
  core : Text.PageText

/-- Options for `pageText`. -/
structure TextOptions where
  /-- Layout parameters of the reading-order heuristic (tested, not proved). -/
  layout : Text.Options := {}
  /-- Include the text of annotation appearances (FreeText, form fields …), as the viewer
  and the inspector's text view do. `false`: page content only. -/
  withAnnots : Bool := true

/-- The API view of a core page text. -/
def PageText.ofCore (o : Text.Options) (pt : Text.PageText) : PageText where
  text := pt.text
  lines := pt.lines.map fun l =>
    let gs := (Text.lineOrder o l).toArray.map Glyph.ofCore
    let box := match gs[0]? with
      | some g0 => gs.foldl (fun b g => Box.union b g.box) g0.box
      | none => ⟨0, 0, 0, 0⟩
    { text := Text.lineText o l, box, glyphs := gs }
  glyphs := pt.glyphs.toArray.map Glyph.ofCore
  core := pt

/-- The core text extraction behind `pageText`. -/
def pageTextCore (d : Document) (i : Nat) (o : TextOptions := {}) : Except Error Text.PageText := do
  let p ← d.page i
  let b := Filter.Budget.init d.limits
  let r := if o.withAnnots then (Annot.extractDocPageAnnots d.limits d.doc p b o.layout).1
    else (Text.extractDocPage d.limits d.doc p b o.layout).1
  match r with
  | .ok pt => .ok pt
  | .error e => .error (.pdf e)

/-- **The text of page `i`** with glyph positions, for indexing, search and anchoring.
Guarantees (Plan.md §4): **C6** extracted = displayed — the glyphs are read from the display
list of the same interpreter pass that `renderPage` draws (`pageText_glyphs`,
`Core.Text.extractPage_glyphs`); **C3** text ↔ position — each glyph's `(item, seq)`
recomputes exactly that glyph from the display list (`glyph_provenance`) and a run's glyph
code bytes concatenate to the bytes it showed (`glyph_codes`). Line grouping and reading
order are a heuristic (tested against MuPDF, not proved). -/
def pageText (d : Document) (i : Nat) (o : TextOptions := {}) : Except Error PageText :=
  (pageTextCore d i o).map (PageText.ofCore o.layout)

/-- The API glyphs are the core glyphs, converted one to one, in the same order. -/
theorem pageText_glyphs_ofCore {d : Document} {i : Nat} {o : TextOptions} {t : PageText}
    (h : pageText d i o = .ok t) : t.glyphs = t.core.glyphs.toArray.map Glyph.ofCore := by
  unfold pageText at h
  cases hc : pageTextCore d i o with
  | error e => simp [hc, Except.map] at h
  | ok pt => simp only [hc, Except.map, Except.ok.injEq] at h; subst h; rfl

/-- **C6 over the API** (page content only): the glyphs of `pageText` are exactly the
extraction of the page's own display list under its own fonts. -/
theorem pageText_glyphs {d : Document} {i : Nat} {o : TextOptions} {t : PageText}
    (ho : o.withAnnots = false) (h : pageText d i o = .ok t) :
    t.core.glyphs = Text.extractItems t.core.fonts t.core.items.toList := by
  unfold pageText pageTextCore at h
  cases hp : d.page i with
  | error e => simp [hp, bind, Except.bind, Except.map] at h
  | ok p =>
    simp only [hp, ho, bind, Except.bind, Bool.false_eq_true, ite_false] at h
    unfold Text.extractDocPage at h
    cases hdc : d.doc.decodeContentsB d.limits (Filter.Budget.init d.limits) p with
    | mk r b =>
      cases r with
      | error e => simp [hdc, Except.map] at h
      | ok parts =>
        simp only [hdc, Except.map, Except.ok.injEq] at h
        subst h
        exact Text.extractPage_glyphs ..

/-- **C3/C6 provenance** (re-export of `Core.Text.extract_from_items`): every glyph extracted
from a display list comes from a `glyphRun` item at index `g.item`, and recomputing that
item's glyphs from the display list alone gives back exactly `g` at position `g.seq`. -/
theorem glyph_provenance (fonts : Text.FontTable) (items : List Content.DisplayItem)
    (g : Text.Glyph) (h : g ∈ Text.extractItems fonts items) :
    ∃ r clip, items[g.item]? = some (.glyphRun r clip) ∧
      (Text.runGlyphs fonts g.item r)[g.seq]? = some g :=
  Text.extract_from_items fonts items g h

/-- **C3 (bytes)** (re-export of `Core.Text.runGlyphs_codes`): the code bytes of a run's
glyphs concatenate to exactly the bytes the run showed — none dropped or invented. -/
theorem glyph_codes (fonts : Text.FontTable) (i : Nat) (r : Content.GlyphRun) :
    ((Text.runGlyphs fonts i r).map Text.Glyph.code).flatten = (Text.strParts r.parts).flatten :=
  Text.runGlyphs_codes fonts i r

/-! ## Rendering -/

/-- **Render page `i`** at `zoom` pixels per point (1 = 72 dpi) with an extra clockwise
rotation `rot`, onto its CropBox, white background: the verified full-page renderer
(`Core.Raster.Glyph.renderDocPage`: paths, text with embedded or standard-14 glyph outlines,
images, shadings, patterns, transparency groups, annotation appearances). Total and bounded
by `Limits` (decoded bytes, operators, path segments; a side above `Limits.maxPageSide`
pixels is cropped). Pixel `(x, y)` of the image is screen point `(x, y)` of `toScreen`. -/
def renderPage (d : Document) (i : Nat) (zoom : Rat) (rot : Rotation := .r0) :
    Except Error Image :=
  match d.page i with
  | .error e => .error e
  | .ok p =>
    if zoom ≤ 0 then .error (.badZoom zoom)
    else
      match (Raster.Glyph.renderDocPage d.limits d.doc p zoom rot (Filter.Budget.init d.limits)).1 with
      | .ok img => .ok img
      | .error e => .error (.pdf e)

/-- **RGBA shape**: a rendered page has exactly `4 · w · h` bytes
(`Core.Raster.Glyph.renderPage_size`). -/
theorem renderPage_size {d : Document} {i : Nat} {zoom : Rat} {rot : Rotation} {img : Image}
    (h : renderPage d i zoom rot = .ok img) : img.data.size = 4 * img.w * img.h := by
  unfold renderPage at h
  split at h
  · cases h
  · rename_i p _
    split at h
    · cases h
    · unfold Raster.Glyph.renderDocPage at h
      cases hx : Text.extractDocPage d.limits d.doc p (Filter.Budget.init d.limits) with
      | mk r b =>
        cases r with
        | error e => simp [hx] at h
        | ok pt =>
          simp only [hx, Except.ok.injEq] at h
          subst h
          exact Raster.Glyph.renderPage_size ..

/-! ## Navigation: outline, links, annotations -/

/-- Where an outline item or a link leads. -/
inductive Target where
  /-- Nothing (no destination or action, or a malformed one). -/
  | none
  /-- A page of this document (0-based) with its fit specification (`/XYZ`, `/Fit`, …). -/
  | page (index : Nat) (fitSpec : Doc.Nav.Fit)
  /-- An explicit destination whose page is not a page of this document. -/
  | danglingDest (fitSpec : Doc.Nav.Fit)
  /-- A named destination that was not found. -/
  | unresolved (name : String)
  /-- A URI action (`/S /URI`): the URI as written (never followed by the library). -/
  | uri (uri : String)
  /-- Another action, by its `/S` name (`GoToR`, `Launch`, `JavaScript`, …; never run). -/
  | action (kind : String)
  deriving Repr, Inhabited

/-- The API target of a core target. -/
def Target.ofCore {n : Nat} : Doc.Nav.Target n → Target
  | .none => .none
  | .dest dst =>
    match dst.page with
    | some i => .page i.val dst.fit
    | Option.none => .danglingDest dst.fit
  | .unresolved nm => .unresolved (textString nm)
  | .uri u => .uri (textString u)
  | .action k => .action (String.fromUTF8? ⟨k.toArray⟩ |>.getD "?")

/-- The target of an outline item or annotation dictionary: `Core.Doc.Nav.targetOf` (`/Dest`,
else `/A`, rule N5); a `/URI` action carries its URI. -/
def targetOfDict (d : Document) (nd : SafePdf.Dict) : Target :=
  Target.ofCore (Doc.Nav.targetOf d.doc d.limits nd)

/-- One outline (bookmark) item. -/
structure OutlineItem where
  /-- Title, decoded (§7.9.2.2). -/
  title : String
  /-- Nesting depth, 0 for top-level items. -/
  depth : Nat
  /-- Where it leads. -/
  target : Target
  /-- `/Count`: positive when open, negative when closed. -/
  count : Option Int
  deriving Repr, Inhabited

/-- **The document outline** in preorder with depths (`Core.Doc.Nav.outline`, rule N6):
cycles and repeated items are cut, the walk visits each object at most once and at most
`objectCount` items are returned (`outline_bounded`). Empty when there is none. -/
def outline (d : Document) : List OutlineItem :=
  (Doc.Nav.outline d.doc d.limits).items.map fun it =>
    { title := textString it.title, depth := it.depth
      target := match Doc.Nav.fetchDict d.doc d.limits it.num it.gen with
        | some nd => targetOfDict d nd
        | Option.none => Target.ofCore it.target
      count := it.count }

/-- **Outline work bound** (re-export of `Core.Doc.Nav.outline_items_le`). -/
theorem outline_bounded (d : Document) : (outline d).length ≤ d.doc.file.objectCount := by
  simp only [outline, List.length_map]
  exact Doc.Nav.outline_items_le d.doc d.limits

/-- Cap on the `/Annots` entries read per page (as the renderer, `Core.Annot.maxAnnots`). -/
def maxAnnots : Nat := Annot.maxAnnots

/-- One annotation of a page (§12.5). -/
structure Annotation where
  /-- `/Subtype` (`Text`, `Link`, `Highlight`, `FreeText`, `Widget`, …; `""` if missing). -/
  subtype : String
  /-- `/Rect`, normalised, page space. -/
  rect : Box
  /-- `/Contents`, decoded, if present. -/
  contents : Option String
  /-- `/NM` (the annotation's unique name), if present. -/
  name : Option String
  /-- `/T` (author, for markup annotations), if present. -/
  author : Option String
  /-- `/F` flags (bit 2 = hidden, bit 3 = print, …); 0 if missing. -/
  flags : Nat
  /-- `/QuadPoints` (text markup, links): 8 numbers per quadrilateral, page space. -/
  quadPoints : List Rat
  /-- The annotation's object `(num, gen)` when `/Annots` refers to it indirectly (a stable
  key for anchoring). -/
  ref : Option (Nat × Nat)
  /-- The target, for a `Link` (`/Dest` or `/A`; URI actions with their URI). -/
  target : Target
  deriving Repr, Inhabited

/-- A string value as text. -/
def strOf : SafePdf.PdfObject → Option String
  | .string s => some (textString s)
  | _ => none

/-- A number as an exact rational. -/
def ratOf (o : SafePdf.PdfObject) : Option Rat := (Doc.numOf o).map Raster.Geom.decimalToRat


/-- The annotation of one `/Annots` element; `none` when it is not a dictionary with a valid
`/Rect`. -/
def annotOf (d : Document) (a : SafePdf.PdfObject) : Option Annotation :=
  let ref := match a with
    | .ref n g => some (n, g)
    | _ => none
  match Doc.Nav.res d.doc d.limits a with
  | .dict ad =>
    let get := Doc.Nav.getL d.doc d.limits ad
    (Doc.rectOf (get "Rect")).map fun r =>
      { subtype := match get "Subtype" with
          | .name s => String.fromUTF8? ⟨s.bytes.toArray⟩ |>.getD "?"
          | _ => ""
        rect := Raster.Geom.Box.ofRect r
        contents := strOf (get "Contents")
        name := strOf (get "NM")
        author := strOf (get "T")
        flags := match get "F" with
          | .int f => f.toNat
          | _ => 0
        quadPoints := match get "QuadPoints" with
          | .array xs => xs.filterMap ratOf
          | _ => []
        ref
        target := targetOfDict d ad }
  | _ => none

/-- **The annotations of page `i`** in `/Annots` order (at most `maxAnnots`): subtype,
rectangle, contents, author, flags, quad points, object reference and link target. Lenient
(rule N1): an entry that is not a dictionary with a valid `/Rect` is skipped. Fetches are
bounded by `Limits`; nothing is followed or executed. For drawing them use `renderPage`
(appearance streams). -/
def pageAnnotations (d : Document) (i : Nat) : Except Error (List Annotation) := do
  let p ← d.page i
  match Doc.Nav.fetchDict d.doc d.limits p.num p.gen with
  | none => return []
  | some pd =>
    match Doc.Nav.getL d.doc d.limits pd "Annots" with
    | .array xs => return (xs.take maxAnnots).filterMap (annotOf d)
    | _ => return []

/-- A link of a page. -/
structure Link where
  /-- `/Rect`, page space. -/
  rect : Box
  /-- Where it leads. -/
  target : Target
  deriving Repr, Inhabited

/-- **The links of page `i`** (`/Subtype /Link` annotations, rule N7): rectangle and target;
URI actions carry their URI (shown, never followed). -/
def pageLinks (d : Document) (i : Nat) : Except Error (List Link) := do
  let as ← pageAnnotations d i
  return (as.filter (·.subtype == "Link")).map fun a => ⟨a.rect, a.target⟩

/-! ## Checks over a tiny embedded PDF -/

/-- A PDF whose objects `1 …` are the given bodies, with a correct xref table. -/
private def mkPdf (objs : List String) : ByteArray := Id.run do
  let mut body := "%PDF-1.7\n"
  let mut offs : List Nat := []
  let mut i := 1
  for o in objs do
    offs := offs ++ [body.utf8ByteSize]
    body := body ++ s!"{i} 0 obj\n{o}\nendobj\n"
    i := i + 1
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  let x := body.utf8ByteSize
  let rows := String.join (offs.map row)
  (body ++ s!"xref\n0 {objs.length + 1}\n0000000000 65535 f \n" ++ rows ++
    s!"trailer\n<< /Size {objs.length + 1} /Root 1 0 R >>\nstartxref\n{x}\n%%EOF\n").toUTF8

/-- The test document: one 200 × 100 page showing "Hello" in Helvetica, an outline item, a
URI link and a text note; page labels `i, ii, …`. A function so that it is not evaluated at
program start. -/
private def tiny (_ : Unit) : ByteArray :=
  let content := "BT /F1 10 Tf 20 50 Td (Hello) Tj ET"
  mkPdf [
    "<< /Type /Catalog /Pages 2 0 R /Outlines 6 0 R /PageLabels << /Nums [0 << /S /r >>] >> >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 200 100] >>",
    "<< /Type /Page /Parent 2 0 R /Resources << /Font << /F1 5 0 R >> >> /Contents 4 0 R " ++
      "/Annots [8 0 R 9 0 R] >>",
    s!"<< /Length {content.utf8ByteSize} >>\nstream\n{content}\nendstream",
    "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
    "<< /Type /Outlines /First 7 0 R /Last 7 0 R /Count 1 >>",
    "<< /Title <FEFF0049006E00740072006F> /Parent 6 0 R /Dest [3 0 R /Fit] >>",
    "<< /Type /Annot /Subtype /Link /Rect [60 45 20 60] /A << /S /URI /URI (https://example.org) >> >>",
    "<< /Type /Annot /Subtype /Text /Rect [150 80 170 95] /Contents (Note) /NM (n1) /F 4 >>"]

private def tinyDoc (_ : Unit) : Except Error Document := openBytes (tiny ())

#guard match tinyDoc () with
  | .ok d => d.pageCount == 1 && !d.repaired && d.version == some (1, 7)
  | .error _ => false
#guard match tinyDoc () with
  | .ok d => match pageInfo d 0 with
    | .ok i => i.label == "i" && i.cropBox == ⟨0, 0, 200, 100⟩ && i.size == (200, 100) &&
        i.rotation == .r0
    | .error _ => false
  | .error _ => false
#guard match tinyDoc () with
  | .ok d => match pageInfo d 1 with
    | .error (.pageOutOfRange 1 1) => true
    | _ => false
  | .error _ => false
-- Text: content text with origins; the first glyph's origin is (20, 50).
#guard match tinyDoc () with
  | .ok d => match pageText d 0 { withAnnots := false } with
    | .ok t => t.text == "Hello" && t.glyphs.size == 5 && t.lines.size == 1 &&
        (t.glyphs[0]?.map (·.origin)) == some ⟨20, 50⟩ &&
        (t.lines[0]?.map (·.text)) == some "Hello"
    | .error _ => false
  | .error _ => false
-- Glyph boxes: 0.2 em below to 0.8 em above the baseline (size 10).
#guard match tinyDoc () with
  | .ok d => match pageText d 0 with
    | .ok t => (t.glyphs[0]?.map fun g => (g.box.lly, g.box.ury, g.box.llx)) == some (48, 58, 20)
    | .error _ => false
  | .error _ => false
-- Outline: a UTF-16 title, leading to page 0.
#guard match tinyDoc () with
  | .ok d => match outline d with
    | [it] => it.title == "Intro" && it.depth == 0 &&
        (match it.target with | .page 0 .fit => true | _ => false)
    | _ => false
  | .error _ => false
-- Links (rectangle normalised) and annotations.
#guard match tinyDoc () with
  | .ok d => match pageLinks d 0 with
    | .ok [l] => l.rect == ⟨20, 45, 60, 60⟩ &&
        (match l.target with | .uri u => u == "https://example.org" | _ => false)
    | _ => false
  | .error _ => false
#guard match tinyDoc () with
  | .ok d => match pageAnnotations d 0 with
    | .ok [a, b] => a.subtype == "Link" && a.ref == some (8, 0) && b.subtype == "Text" &&
        b.contents == some "Note" && b.name == some "n1" && b.flags == 4
    | _ => false
  | .error _ => false
-- Rendering: 200 × 100 at zoom 1, 100 × 200 rotated; some ink; bad zoom rejected.
#guard match tinyDoc () with
  | .ok d => match renderPage d 0 1, renderPage d 0 1 .r90 with
    | .ok a, .ok b => a.w == 200 && a.h == 100 && a.data.size == 80000 && b.w == 100 &&
        b.h == 200 && a.data.toList.any (· < 128)
    | _, _ => false
  | .error _ => false
#guard match tinyDoc () with
  | .ok d => match renderPage d 0 0 with
    | .error (.badZoom _) => true
    | _ => false
  | .error _ => false
-- C2 on the API types: the page point (20, 50) is pixel (20, 50) at zoom 1, and back.
#guard match tinyDoc () with
  | .ok d => match pageInfo d 0 with
    | .ok i => toScreen i 1 .r0 ⟨20, 50⟩ == ⟨20, 50⟩ && toPage i 2 .r90 (toScreen i 2 .r90 ⟨7, 3⟩) == ⟨7, 3⟩
    | .error _ => false
  | .error _ => false
-- Text strings.
#guard textString [0xFE, 0xFF, 0, 0x41, 0x20, 0xAC] == "A€" && textString "abc".toUTF8.toList == "abc" &&
  textString [0xA0] == "€" && textString [0xEF, 0xBB, 0xBF, 0xC3, 0xA9] == "é"
-- Strict mode refuses a damaged file (no xref at all) that the repair path opens.
#guard match openBytes ("%PDF-1.4\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n" ++
    "2 0 obj\n<< /Type /Pages /Kids [] /Count 0 >>\nendobj\ntrailer\n<< /Root 1 0 R >>\n%%EOF\n").toUTF8,
    openBytes ("%PDF-1.4\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n" ++
    "2 0 obj\n<< /Type /Pages /Kids [] /Count 0 >>\nendobj\ntrailer\n<< /Root 1 0 R >>\n%%EOF\n").toUTF8
    { allowRepair := false } with
  | .ok d, .error .repairRefused => d.repaired
  | _, _ => false

end SafePdf.Api
