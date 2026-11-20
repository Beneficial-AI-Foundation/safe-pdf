import SafePdf.Shell.Views.Common
import SafePdf.Core.Annot
import SafePdf.Shell.Views.Summary
import SafePdf.Shell.Views.Pages
import SafePdf.Shell.Views.Svg

/-!
# `text` view: text browser over the verified extraction (task 6.6)

Plan.md §6 Phase 6 (exit M6: "text extraction ≥ 98% similarity vs pdfium/MuPDF on corpus
(normalized edit distance); all glyph positions within tolerance"), the M6 row of the MVP /
visibility track, and §7 (measured success on the corpus: the differential comparator
`Tests/differential/text.py` reads the `--json` form of this view).

The document is opened in the parse's session (`Pages.docOf`, as the `pages` and `svg` views);
the text of a page is `Core.Text.extractDocPage limits doc page budget` with the default
`Core.Text.Options` (reading-order heuristic, invisible text kept). All pages are extracted in
document order under **one document budget** (`Filter.Budget.init`, threaded from page to
page, as `svg` with `SAFEPDF_SVG_DIR`); `SAFEPDF_PAGE=N` (1-based) selects one page, extracted
with a fresh budget (as `svg`). A page whose contents do not decode is reported with its error
and empty text.

## Text form

A header (`file`, `open`, `pages`), then per page a line
`--- page N: C chars, G glyphs, F U+FFFD, W warnings` (plus `, error: …`) followed by the page
text as extracted (newlines are the layout's line breaks). With `SAFEPDF_TEXT_GLYPHS=1` each
page is followed by `--- glyphs page N (item seq x y width size text)` and one line per glyph
in content order: display-list item index, index in the run, page-space origin, width, font
size (exact decimals, `Fixed.toDecimal`) and the glyph's text as a JSON string literal. Then a
`total:` line.

## `--json`

One object per page `{"page","chars","glyphs","replacement","warnings","error","text"}`
(`chars` counts Unicode scalar values of `text`, `replacement` the U+FFFD among them, `error`
is `null` or a message), with `"glyphList": [[item, seq, x, y, width, size, text], …]` added
when `SAFEPDF_TEXT_GLYPHS=1`; then `{"summary": {"path","open","pages","extracted","chars",
"glyphs","replacement","warnings","errors"}}` (`pages` is the document's page count,
`extracted` the number of pages printed), or `{"summary": {"path","open","error"}}` when the
document does not open. Strings are UTF-8 JSON (`Common.jsonString`: control characters
escaped, other characters verbatim), so `json.loads` reads them.
-/

namespace SafePdf.Shell.Views.Text

open SafePdf.Shell
open SafePdf.Core.Doc
open SafePdf.Core.Filter (Budget)
open SafePdf.Core.Text (PageText Glyph)

/-- What the view prints for one page. -/
structure PageOut where
  /-- 1-based page number. -/
  number : Nat
  /-- Page text (empty on error). -/
  text : String := ""
  /-- Extracted glyphs, content order. -/
  glyphs : List Glyph := []
  /-- Interpreter warnings. -/
  warnings : Nat := 0
  /-- Error decoding the page contents. -/
  error : Option Error := none

/-- Number of Unicode scalar values of the text. -/
def PageOut.chars (p : PageOut) : Nat := p.text.length

/-- Number of U+FFFD in the text. -/
def PageOut.replacement (p : PageOut) : Nat :=
  (p.text.toList.filter (· == SafePdf.Core.Font.CMap.replacement)).length

/-- The view's record of an extraction result. -/
def pageOut (number : Nat) : Except Error PageText → PageOut
  | .ok pt => { number, text := pt.text, glyphs := pt.glyphs, warnings := pt.warnings }
  | .error e => { number, error := some e }

/-- Extract every page in document order under one document budget. -/
def extractAll (limits : Limits) (doc : Doc) : Array PageOut := Id.run do
  let mut budget := Budget.init limits
  let mut out := #[]
  for h : k in [0:doc.pages.size] do
    let (r, b) := SafePdf.Core.Annot.extractDocPageAnnots limits doc (doc.pages[k]'h.upper) budget
    budget := b
    out := out.push (pageOut (k + 1) r)
  return out

/-- Extract page `n` (1-based) with a fresh budget; `none` when out of range. -/
def extractOne (limits : Limits) (doc : Doc) (n : Nat) : Option PageOut :=
  match n with
  | 0 => none
  | k + 1 =>
    if h : k < doc.pages.size then
      some (pageOut n (SafePdf.Core.Annot.extractDocPageAnnots limits doc doc.pages[k]
        (Budget.init limits)).1)
    else none

/-- Exact decimal text of a `Fixed`. -/
def num (x : SafePdf.Core.Content.Fixed) : String := Svg.num x

/-- One text line per glyph: `item seq x y width size "text"`. -/
def glyphText (g : Glyph) : String :=
  s!"{g.item} {g.seq} {num g.x} {num g.y} {num g.width} {num g.fontSize} {jsonString g.text}"

/-- One glyph as a JSON array. -/
def glyphJson (g : Glyph) : String :=
  s!"[{g.item}, {g.seq}, {num g.x}, {num g.y}, {num g.width}, {num g.fontSize}, {jsonString g.text}]"

/-- Header line of a page in the text form. -/
def pageHeader (p : PageOut) : String :=
  let err := match p.error with
    | some e => s!", error: {renderError e}"
    | none => ""
  s!"--- page {p.number}: {p.chars} chars, {p.glyphs.length} glyphs, {p.replacement} U+FFFD, {p.warnings} warnings{err}"

/-- Text form of one page. -/
def pageLines (glyphs : Bool) (p : PageOut) : List String :=
  [pageHeader p] ++ (if p.text.isEmpty then [] else [p.text]) ++
  (if glyphs then
    [s!"--- glyphs page {p.number} (item seq x y width size text)"] ++ p.glyphs.map glyphText
  else [])

/-- JSON line of one page. -/
def pageJson (glyphs : Bool) (p : PageOut) : String :=
  jsonObject (
    [ ("page", toString p.number), ("chars", toString p.chars),
      ("glyphs", toString p.glyphs.length), ("replacement", toString p.replacement),
      ("warnings", toString p.warnings),
      ("error", match p.error with
        | some e => jsonString (renderError e)
        | none => "null"),
      ("text", jsonString p.text) ] ++
    (if glyphs then [("glyphList", "[" ++ ", ".intercalate (p.glyphs.map glyphJson) ++ "]")]
     else []))

/-- Totals over the printed pages: chars, glyphs, U+FFFD, warnings, errors. -/
def totals (ps : Array PageOut) : Nat × Nat × Nat × Nat × Nat :=
  ps.foldl (fun (c, g, r, w, e) p =>
    (c + p.chars, g + p.glyphs.length, r + p.replacement, w + p.warnings,
     e + (if p.error.isSome then 1 else 0))) (0, 0, 0, 0, 0)

/-- Text form of the view. -/
def textLines (path : String) (result : Except Error Document) (pageCount : Nat)
    (ps : Array PageOut) (glyphs : Bool) : List String :=
  let (c, g, r, w, e) := totals ps
  [ s!"file:       {path}", s!"open:       {Summary.openMode result}",
    s!"pages:      {pageCount}" ] ++
  ps.toList.flatMap (pageLines glyphs) ++
  [ s!"total:      {ps.size} page(s), {c} chars, {g} glyphs, {r} U+FFFD, {w} warnings, {e} page error(s)" ]

/-- JSON lines of the view. -/
def jsonLines (path : String) (result : Except Error Document) (pageCount : Nat)
    (ps : Array PageOut) (glyphs : Bool) : List String :=
  let (c, g, r, w, e) := totals ps
  ps.toList.map (pageJson glyphs) ++
  [ jsonObject [ ("summary", jsonObject
    [ ("path", jsonString path), ("open", jsonString (Summary.openMode result)),
      ("pages", toString pageCount), ("extracted", toString ps.size), ("chars", toString c),
      ("glyphs", toString g), ("replacement", toString r), ("warnings", toString w),
      ("errors", toString e) ]) ] ]

/-- Output lines for a document: all pages, or page `page` (1-based) when given. `none` when the
page is out of range. -/
def render (cfg : Config) (path : String) (result : Except Error Document) (doc : Doc)
    (page : Option Nat) (glyphs : Bool) : Option (List String) :=
  let ps? : Option (Array PageOut) := match page with
    | none => some (extractAll cfg.limits doc)
    | some n => (extractOne cfg.limits doc n).map (#[·])
  ps?.map fun ps =>
    if cfg.json then jsonLines path result doc.pages.size ps glyphs
    else textLines path result doc.pages.size ps glyphs

/-- Output lines when the document does not open. -/
def errorLines (cfg : Config) (path : String) (result : Except Error Document) (e : Error) :
    List String :=
  if cfg.json then
    [ jsonObject [ ("summary", jsonObject
      [ ("path", jsonString path), ("open", jsonString (Summary.openMode result)),
        ("error", jsonString (renderError e)) ]) ] ]
  else
    [ s!"file:       {path}", s!"open:       {Summary.openMode result}",
      s!"error:      {renderError e}" ]

/-- The `text` view. -/
def view : View where
  name := "text"
  description := "extracted page text (SAFEPDF_PAGE=N for one page; SAFEPDF_TEXT_GLYPHS=1 adds per-glyph positions)"
  run cfg i := do
    match Pages.docOf cfg.limits i.result with
    | .error e => (errorLines cfg i.path i.result e).forM IO.println
    | .ok doc =>
      let glyphs := (← IO.getEnv "SAFEPDF_TEXT_GLYPHS") == some "1"
      let page ← match ← IO.getEnv "SAFEPDF_PAGE" with
        | none => pure none
        | some s =>
          match s.trimAscii.toString.toNat? with
          | some n => pure (some n)
          | none =>
            IO.eprintln s!"inspect: SAFEPDF_PAGE='{s}' is not a page number; showing all pages"
            pure none
      match render cfg i.path i.result doc page glyphs with
      | some ls => ls.forM IO.println
      | none =>
        IO.eprintln s!"inspect: {i.path}: page {page.getD 0} out of range (1..{doc.pages.size})"

end SafePdf.Shell.Views.Text
