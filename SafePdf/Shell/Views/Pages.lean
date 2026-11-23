import SafePdf.Shell.Views.Common
import SafePdf.Shell.Views.Summary
import SafePdf.Shell.Views.Objects

/-!
# `pages` and `outline` views: page-tree and outline browser (task 4.4)

Plan.md §6 Phase 4 (page tree with inheritance, Tier 1 navigation; exit M4 "page count + page
boxes match `qpdf` on corpus") and the M4 row of the MVP / visibility track ("Page-tree +
outline browser"). Both views walk the page tree with the verified core in the session the
document was opened in (`Core.Doc.ofSession d.session limits`, task 4.5: `Core.Doc.openDocS`
without parsing the file a second time, since the inspector's `SafePdf.parseWith` already ran
`Open.Session.open`), so the walk's object-stream and `/Length` decodes are charged to the
same budget as the open; with enough budget left the document is `Core.Doc.ofOpen`'s
(`Core.Doc.ofSession_eq`). Not charged: the navigation walks of `Core.Doc.Nav` (page labels,
links, outline), which fetch with the unbudgeted `OpenDoc.getObject` (each fetch bounded by
`Open.getObject_work`).

## `pages`

A header (page count, root `/Count` and whether it disagrees, dangling `/Kids` skipped,
page-label warnings), then one line per page: index, object reference, MediaBox, CropBox
(after clipping to the MediaBox: `Core.Doc.cropOf`), whether the MediaBox was defaulted to US
Letter, rotation, page label (`Core.Doc.Nav.pageLabels`, one number-tree walk for all pages)
and the number of link annotations (`Core.Doc.Nav.pageLinks`).

`--json`: one object per page
`{"index","num","gen","mediaBox":[llx,lly,urx,ury],"cropBox":[...],"mediaBoxDefaulted",
"rotate","label","links"}` then `{"summary": {...}}`. Box coordinates are JSON numbers
printed as **exact canonical decimals** (`612`, `595.276`, `-0.5`; never an exponent), so a
consumer parsing them as decimals (Python `parse_float=Decimal`) gets the core's values
exactly. The differential comparator `Tests/differential/pages.py` reads this form.

## `outline`

The outline (`Core.Doc.Nav.outline`) as an indented tree in preorder, one item per line:
title, destination, object reference; then the number of warnings (cut cycles, repeated or
malformed items). Destinations: `page N` (0-based index) with the fit name, `page ref N G (not
a page)`, `page index I (out of range)`, `named "…" -> …` when reached through a named
destination, `unresolved "…"`, `action KIND`, or `none`.

## Byte strings

Titles, labels and names are raw bytes (text decoding is phase 6). `safeBytes` renders them
deterministically: printable ASCII (0x20–0x7E, except `\`) as-is, every other byte as `\xNN`;
a string starting with the UTF-16BE byte-order mark `FE FF` is rendered `<utf16:HEX>` with the
hex of the bytes after the mark.
-/

namespace SafePdf.Shell.Views.Pages

open SafePdf.Shell
open SafePdf.Core.Doc
open SafePdf.Core.Doc.Nav

/-! ## Rendering helpers -/

/-- Safe rendering of raw string bytes (see the module doc). -/
def safeBytes (bs : List UInt8) : String :=
  match bs with
  | 0xFE :: 0xFF :: rest => "<utf16:" ++ Objects.hexText rest ++ ">"
  | _ =>
    String.join (bs.map fun b =>
      if 0x20 ≤ b && b ≤ 0x7E && b != 0x5C then (Char.ofNat b.toNat).toString
      else "\\x" ++ Objects.hexByte b)

/-- Exact canonical decimal text, valid as a JSON number: `612`, `595.276`, `-0.5`. -/
def numText (d : Decimal) : String :=
  let d := d.normalize
  if d.scale == 0 then toString d.mantissa else Objects.decimalText d

/-- A rectangle as `[llx lly urx ury]`. -/
def rectText (r : Rect) : String :=
  s!"[{numText r.llx} {numText r.lly} {numText r.urx} {numText r.ury}]"

/-- A rectangle as a JSON array of numbers. -/
def rectJson (r : Rect) : String :=
  s!"[{numText r.llx}, {numText r.lly}, {numText r.urx}, {numText r.ury}]"

/-- Degrees of a rotation. -/
def degrees : Rotation → Nat
  | .r0 => 0
  | .r90 => 90
  | .r180 => 180
  | .r270 => 270

/-- An optional JSON value. -/
def jsonOpt : Option String → String
  | some s => s
  | none => "null"

/-! ## `pages` -/

/-- What the `pages` view reports for one page. -/
structure PageRow where
  /-- 0-based index. -/
  index : Nat
  /-- The page object. -/
  page : Page
  /-- The page label bytes. -/
  label : List UInt8
  /-- Number of link annotations. -/
  links : Nat

/-- The page rows of a document. -/
def rows (doc : Doc) (limits : Limits) : List PageRow :=
  let labels := (pageLabels doc limits).toArray
  (List.range doc.pages.size).filterMap fun i =>
    if h : i < doc.pages.size then
      some { index := i, page := doc.pages[i], label := labels[i]?.getD [],
             links := (pageLinks doc limits ⟨i, h⟩).length }
    else none

/-- One text line per page. -/
def rowText (r : PageRow) : String :=
  let p := r.page
  let dflt := if p.mediaBoxDefaulted then " (defaulted)" else ""
  s!"  #{r.index}  {p.num} {p.gen} R  media {rectText p.mediaBox}{dflt}  crop {rectText p.cropBox}  rotate {degrees p.rotate}  label \"{safeBytes r.label}\"  links {r.links}"

/-- One JSON line per page. -/
def rowJson (r : PageRow) : String :=
  let p := r.page
  jsonObject
    [ ("index", toString r.index), ("num", toString p.num), ("gen", toString p.gen),
      ("mediaBox", rectJson p.mediaBox), ("cropBox", rectJson p.cropBox),
      ("mediaBoxDefaulted", toString p.mediaBoxDefaulted),
      ("rotate", toString (degrees p.rotate)), ("label", jsonString (safeBytes r.label)),
      ("links", toString r.links) ]

/-- The `/Count` text of a document. -/
def countText (doc : Doc) : String :=
  match doc.declaredCount with
  | some c => s!"declared /Count {c}{if doc.countMismatch then " (MISMATCH)" else ""}"
  | none => "no integer /Count"

/-- The document of a parse result. -/
def docOf (limits : Limits) (result : Except Error Document) : Except Error Doc :=
  match result with
  | .error e => .error e
  | .ok d => (ofSession d.session limits).1

/-- Text form of the `pages` view. -/
def pagesText (path : String) (limits : Limits) (result : Except Error Document) :
    List String :=
  let head := [ s!"file:       {path}", s!"open:       {Summary.openMode result}" ]
  match docOf limits result with
  | .error e => head ++ [ s!"error:      {renderError e}" ]
  | .ok doc =>
    let rs := rows doc limits
    let lt := labelTable doc limits
    let dflt := (rs.filter (·.page.mediaBoxDefaulted)).length
    head ++
    [ s!"pages:      {doc.pageCount} ({countText doc})",
      s!"skipped:    {doc.skippedKids} dangling /Kids reference(s)",
      s!"defaulted:  {dflt} page(s) without a MediaBox (US Letter used)",
      s!"labels:     {lt.ranges.length} range(s), {lt.warnings} warning(s)" ] ++
    rs.map rowText

/-- JSON lines of the `pages` view: one per page, then the summary. -/
def pagesJson (path : String) (limits : Limits) (result : Except Error Document) :
    List String :=
  let base := [ ("path", jsonString path), ("open", jsonString (Summary.openMode result)) ]
  match docOf limits result with
  | .error e => [ jsonObject [ ("summary", jsonObject (base ++
      [ ("error", jsonString (renderError e)) ])) ] ]
  | .ok doc =>
    let rs := rows doc limits
    let lt := labelTable doc limits
    let dflt := (rs.filter (·.page.mediaBoxDefaulted)).length
    rs.map rowJson ++
    [ jsonObject [ ("summary", jsonObject (base ++
      [ ("pages", toString doc.pageCount),
        ("declaredCount", jsonOpt (doc.declaredCount.map toString)),
        ("countMismatch", toString doc.countMismatch),
        ("skippedKids", toString doc.skippedKids),
        ("mediaBoxDefaulted", toString dflt),
        ("labelRanges", toString lt.ranges.length),
        ("labelWarnings", toString lt.warnings),
        ("links", toString (rs.foldl (· + ·.links) 0)) ])) ] ]

/-- The `pages` view. -/
def view : View where
  name := "pages"
  description := "page tree: count, /Count check, per page ref, MediaBox, CropBox, Rotate, label, links"
  run cfg i :=
    if cfg.json then (pagesJson i.path cfg.limits i.result).forM IO.println
    else (pagesText i.path cfg.limits i.result).forM IO.println

/-! ## `outline` -/

/-- The name of a fit specification. -/
def fitName : Fit → String
  | .xyz .. => "XYZ"
  | .fit => "Fit"
  | .fitH _ => "FitH"
  | .fitV _ => "FitV"
  | .fitR .. => "FitR"
  | .fitB => "FitB"
  | .fitBH _ => "FitBH"
  | .fitBV _ => "FitBV"
  | .unknown nm => "?" ++ safeBytes nm

/-- The page part of an explicit destination. -/
def destPageText {n : Nat} (d : Dest n) : String :=
  match d.page, d.target with
  | some i, _ => s!"page {i.val}"
  | none, .ref a b => s!"page ref {a} {b} R (not a page)"
  | none, .index k => s!"page index {k} (out of range)"
  | none, .other => "page ? (malformed)"

/-- Text of a target. -/
def targetText {n : Nat} : Target n → String
  | .none => "none"
  | .dest d =>
    let core := s!"{destPageText d} /{fitName d.fit}"
    match d.name with
    | some nm => s!"named \"{safeBytes nm}\" -> {core}"
    | none => core
  | .unresolved nm => s!"unresolved \"{safeBytes nm}\""
  | .uri _ => "action URI"
  | .action k => s!"action {safeBytes k}"

/-- JSON fields of a target. -/
def targetJson {n : Nat} : Target n → List (String × String)
  | .none => [ ("target", jsonString "none") ]
  | .dest d =>
    [ ("target", jsonString "dest"), ("page", jsonOpt (d.page.map (toString ·.val))),
      ("pageRef", match d.target with
        | .ref a b => jsonString s!"{a} {b} R"
        | .index k => toString k
        | .other => "null"),
      ("fit", jsonString (fitName d.fit)),
      ("name", jsonOpt (d.name.map (jsonString ∘ safeBytes))) ]
  | .unresolved nm => [ ("target", jsonString "unresolved"), ("name", jsonString (safeBytes nm)) ]
  | .uri _ => [ ("target", jsonString "action"), ("action", jsonString "URI") ]
  | .action k => [ ("target", jsonString "action"), ("action", jsonString (safeBytes k)) ]

/-- One text line per outline item, indented by depth. -/
def itemText {n : Nat} (it : OutlineItem n) : String :=
  let ind := String.ofList (List.replicate (2 * it.depth) ' ')
  s!"  {ind}- \"{safeBytes it.title}\" -> {targetText it.target}  [{it.num} {it.gen} R]"

/-- One JSON line per outline item. -/
def itemJson {n : Nat} (it : OutlineItem n) : String :=
  jsonObject ([ ("num", toString it.num), ("gen", toString it.gen),
    ("depth", toString it.depth), ("title", jsonString (safeBytes it.title)),
    ("count", jsonOpt (it.count.map toString)) ] ++ targetJson it.target)

/-- Text form of the `outline` view. -/
def outlineText (path : String) (limits : Limits) (result : Except Error Document) :
    List String :=
  let head := [ s!"file:       {path}", s!"open:       {Summary.openMode result}" ]
  match docOf limits result with
  | .error e => head ++ [ s!"error:      {renderError e}" ]
  | .ok doc =>
    let o := outline doc limits
    let depth := o.items.foldl (fun m it => max m it.depth) 0
    head ++
    [ s!"outline:    {o.items.length} item(s), max depth {depth}, {o.warnings} warning(s)" ] ++
    o.items.map itemText

/-- JSON lines of the `outline` view: one per item, then the summary. -/
def outlineJson (path : String) (limits : Limits) (result : Except Error Document) :
    List String :=
  let base := [ ("path", jsonString path), ("open", jsonString (Summary.openMode result)) ]
  match docOf limits result with
  | .error e => [ jsonObject [ ("summary", jsonObject (base ++
      [ ("error", jsonString (renderError e)) ])) ] ]
  | .ok doc =>
    let o := outline doc limits
    let depth := o.items.foldl (fun m it => max m it.depth) 0
    o.items.map itemJson ++
    [ jsonObject [ ("summary", jsonObject (base ++
      [ ("items", toString o.items.length), ("maxDepth", toString depth),
        ("warnings", toString o.warnings) ])) ] ]

/-- The `outline` view. -/
def outlineView : View where
  name := "outline"
  description := "document outline as an indented tree: titles, destinations, warnings"
  run cfg i :=
    if cfg.json then (outlineJson i.path cfg.limits i.result).forM IO.println
    else (outlineText i.path cfg.limits i.result).forM IO.println

end SafePdf.Shell.Views.Pages
