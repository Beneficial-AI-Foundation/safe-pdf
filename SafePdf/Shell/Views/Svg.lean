import SafePdf.Shell.Views.Common
import SafePdf.Shell.Views.Summary
import SafePdf.Shell.Views.Objects
import SafePdf.Shell.Views.Pages
import SafePdf.Core.Text

/-!
# `ops` and `svg` views: operator coverage and SVG export from the display list (task 5.4)

Plan.md §6 Phase 5 (exit M5: "operator coverage report ≥ 99% of corpus ops; interpreter never
fails on corpus; inspector exports pages as SVG rendered from the DisplayList — the first
visible pages, two phases before the rasterizer") and the M5 row of the MVP / visibility
track.

Both views open the document with the verified core (`Core.Doc.ofOpen`, see `Views.Pages`),
decode each page's `/Contents` with `Doc.decodeContentsB` under **one document budget**
(`Filter.Budget.init`, threaded from page to page in document order), concatenate the parts
with one space byte between them (ISO 32000-2 §7.8.2: the division into streams is not
significant, but a token must not run across a boundary), tokenize with
`Core.Content.Ops.tokenize` and run the content with the page's `/Resources` through
`Core.Content.runPage` (task 5.2b: forms expanded, images, ExtGState and named colour spaces
resolved) with the default `Core.Content.Config` (zero glyph advance: fonts are phase 6). The
runner's `Source` is `Core.Text.docSource`: objects fetched with `OpenDoc.getObject`, form contents and
`Indexed` lookup streams decoded with `decodeBodyB` from the **same** document budget.

## Coverage: definition

The views run `Core.Content.runPage` with an observer (`Env.observe`) that the runner calls
once per executed operator with that operator's warning and unknown-operator counts, so every
operator occurrence is attributed, **including the operators inside form XObjects** (since
task 5.2b; each expansion of a form counts its operators again). The golden test checks that
the item count, warning and unsupported totals equal `Core.Content.runBytes` without an
observer.

* An operator occurrence is **unsupported** iff `exec` reports a non-zero unknown-operator
  count for it — equivalently, it emitted a `DisplayItem.unsupported` item. (Outside
  `BX … EX` this is also the occurrence that carries the "unknown operator" warning; inside,
  the interpreter ignores it silently but it is still unsupported.)
* Every other occurrence is **covered**: the interpreter recognised the operator and executed
  it. Covered occurrences that `exec` skipped or repaired with a warning (malformed operands,
  `Q` on an empty stack, `q` at the depth limit, text shown without a font, …) are counted in
  addition as **warned**; they are still covered (the operator is known, the input was bad).
* Covered also includes the operators the interpreter deliberately treats as placeholders or
  no-ops in phase 5: `sh` (placeholder shading), `d0`/`d1`, marked content.
  `scripts/corpus/opcoverage.py` reports a second, stricter fraction excluding those. (`gs`
  and `Do` are resolved since task 5.2b.)
* Coverage = covered / all operator occurrences. Tokenizer recoveries (dropped operands,
  stray delimiters) are not operators; they are reported as tokenizer warnings, and a page
  whose operator count reached `Limits.maxOpsPerPage` is reported as truncated.

## `ops`

Text: header, document totals, one line per page (operators, covered, unsupported, warned,
interpreter and tokenizer warnings, items by kind, time), then the operator histogram (count,
unsupported, warned; by decreasing count). A page whose contents cannot be decoded shows the
error (it has no operators). `--json`: one object per page then `{"summary": {…}}` with the
histogram (`"histogram": {"re": {"count", "unsupported", "warned"}, …}`). Operator names are
rendered with `Pages.safeBytes`.

## `svg`

Renders one page to SVG on stdout: page `SAFEPDF_PAGE` (1-based, default 1). With
`SAFEPDF_SVG_DIR=<dir>` every page is written to `<dir>/page-N.svg` instead and one status line
per page is printed (JSON with `--json`). The SVG is produced from the `DisplayList` only:

* **Page frame.** `width`/`height`/`viewBox` are the CropBox size (swapped for `/Rotate` 90 and
  270); a white background rect; then one top-level `<g transform="matrix(…)">` mapping page
  space (origin bottom-left, y up) to SVG space (y down) and applying `/Rotate` (clockwise):
  0° `(x − llx, ury − y)`, 90° `(y − lly, x − llx)`, 180° `(urx − x, y − lly)`,
  270° `(ury − y, urx − x)`. All drawing is inside it, in page space.
* **Numbers** are `Fixed` values printed exactly (`Fixed.toDecimal`, canonical decimal, never
  an exponent, no floats); box coordinates go through `Fixed.ofDecimal` (exact up to 6
  fractional digits).
* **`fillPath`** → `<path d fill fill-rule [fill-opacity]>` with page-space coordinates.
* **`strokePath`** → `<path fill="none" stroke stroke-width stroke-linecap stroke-linejoin
  stroke-miterlimit [stroke-dasharray stroke-dashoffset] [stroke-opacity]>`. Line width and
  dashes are in user space, so the element carries `transform="matrix(CTM)"` and its
  coordinates are the page-space points mapped back to user space with the exact inverse
  (rounded half up once per coordinate to 6 digits); then the SVG renderer draws the true
  (possibly elliptical) pen. Identity CTM: page-space coordinates, no transform. Singular CTM
  (determinant 0): page-space coordinates with the unscaled width and
  `data-ctm="singular"`. Width 0 (the thinnest line, ISO 32000-2 §8.4.3.2) → width 1 with
  `vector-effect="non-scaling-stroke"` (one device pixel). The miter limit is raised to SVG's
  minimum of 1.
* **Clipping.** Every painting item carries its clip (`List ClipPath`, newest first). Each
  distinct clip list becomes one `<clipPath id="cN" clipPathUnits="userSpaceOnUse">` holding
  its newest path (with `clip-rule`) and referencing the clip of the rest of the list with its
  own `clip-path` attribute (intersection); clips are deduplicated structurally (hash, then
  `==`). Consecutive items with the same clip share one `<g clip-path="url(#cN)">`. Stroke
  elements carry their own `transform`, so the clip is attached to the wrapping group, which
  is in page space. `clip` items themselves draw nothing. Definitions go in a `<defs>` at the
  end of the top-level group.
* **`glyphRun`** → `<text>` placeholder: the shown strings' bytes as Latin-1 characters (XML
  control characters become U+FFFD; `TJ` adjustments are ignored), placed with
  `transform="matrix(GlyphRun.startMatrix) scale(1 -1)"` and `font-size="1"` (the font size
  is part of the text rendering matrix), `font-family="sans-serif"`, `data-font` (resource
  name) and `data-size`. Fill: the fill colour when the render mode fills, the stroke colour
  for stroke-only modes, `none` for invisible/clip modes (`data-render-mode` is then set).
  Real glyphs are phase 6.
* **`image`** → a grey `<rect>` over the unit square with `transform="matrix(CTM)"` and
  `data-image` (resource name, or `inline`), plus a summary of the image dictionary
  (`data-width`, `data-height`, `data-bpc`, `data-colorspace`, and `data-object` for
  XObjects; read from the document, data not decoded); stencil masks (`/ImageMask true`) use
  the fill colour (`data-mask="stencil"`). Inline image data is decoded with
  `Filter.decodeStream` (strict, per-stream limit) and the outcome recorded in
  `data-decoded` (`N bytes`, the image codec left for the quarantine, or `error`).
* **`shading`** → a translucent grey rect over the CropBox, clipped by the item's clip,
  `data-shading` = resource name.
* **`unsupported`** → an XML comment naming the operator.
* **Colours** become `rgb(R%,G%,B%)` with exact decimal percentages: gray `g` → `(g,g,g)`;
  CMYK naively `R = (1 − c)(1 − k)` (likewise G with m, B with y), no colour management;
  pattern colours → mid grey with `data-pattern`. Alpha below 1 → `fill-opacity` /
  `stroke-opacity`.
* **Text overlay** (`SAFEPDF_SVG_TEXT=1`, task 6.6, for visual checking of text extraction):
  after the page content, a `<g data-overlay="text">` with one translucent `<rect>` per glyph
  extracted by `Core.Text.extractDocPage` (fresh budget; a separate run of the page content
  with font advances, while the drawing above uses the zero-advance phase-5 configuration):
  along the baseline over the glyph's width, across it from 0.2 em below to 0.8 em above
  the baseline (nominal; no glyph bounding boxes yet), blue for visible and green for invisible
  glyphs, `data-item`/`data-seq` (provenance) and `data-text`.
* XML text and attribute values are escaped (`&`, `<`, `>`, `"`), XML-invalid control
  characters replaced; comments never contain `--`.
-/

namespace SafePdf.Shell.Views.Svg

open SafePdf.Shell
open SafePdf.Core.Doc
open SafePdf.Core.Content (Fixed Matrix Point Segment Path Clip ClipPath FillRule Color Comp
  DisplayItem DisplayList GlyphRun TextPart StrokeStyle FillStyle LineCap LineJoin
  TextRenderMode ImageSource Op Machine fixedScale roundDiv)

/-- The interpreter configuration used by both views: default, with the run's limits. -/
def interpConfig (limits : Limits) : SafePdf.Core.Content.Config := { limits }

open SafePdf.Core.Filter (Budget)

-- The runner's document access and the concatenation of content parts are shared with text
-- extraction (`Core.Text.docSource`: `OpenDoc.getObject`, stream decoding under the document
-- budget with `decodeBodyB`, rules D1–D3; `Core.Text.joinParts`: one space byte between parts,
-- §7.8.2).
export SafePdf.Core.Text (docSource joinParts)

/-! ## Page content -/

/-- Per-operator counters. -/
structure OpStat where
  /-- Operator bytes. -/
  op : List UInt8
  /-- Occurrences. -/
  count : Nat := 0
  /-- Occurrences reported unknown by the interpreter. -/
  unsupported : Nat := 0
  /-- Covered occurrences executed with a warning. -/
  warned : Nat := 0
  deriving Inhabited

/-- An operator histogram: 256 buckets by first byte, each a short association list. -/
structure Hist where
  /-- The buckets. -/
  buckets : Array (List OpStat) := Array.replicate 256 []
  deriving Inhabited

/-- Bucket of an operator. -/
def bucketOf : List UInt8 → Nat
  | b :: _ => b.toNat
  | [] => 0

/-- Add counts for `op` to an association list. -/
def bumpList (op : List UInt8) (n u w : Nat) : List OpStat → List OpStat
  | [] => [{ op, count := n, unsupported := u, warned := w }]
  | s :: rest =>
    if s.op == op then
      { s with count := s.count + n, unsupported := s.unsupported + u, warned := s.warned + w }
        :: rest
    else s :: bumpList op n u w rest

/-- Add counts for `op`. -/
def Hist.add (h : Hist) (op : List UInt8) (n u w : Nat) : Hist :=
  { buckets := h.buckets.modify (bucketOf op) (bumpList op n u w) }

/-- Merge `g` into `h`. -/
def Hist.merge (h g : Hist) : Hist :=
  g.buckets.foldl (fun h l => l.foldl (fun h s => h.add s.op s.count s.unsupported s.warned) h) h

/-- Printable operator name. -/
def opName (op : List UInt8) : String := Pages.safeBytes op

/-- All entries, by decreasing count then name. -/
def Hist.sorted (h : Hist) : Array OpStat :=
  let all := h.buckets.foldl (fun acc l => l.foldl (fun acc s => acc.push s) acc) #[]
  all.qsort fun a b => a.count > b.count || (a.count == b.count && opName a.op < opName b.op)

/-- Number of display-item kinds. -/
def nKinds : Nat := 10

/-- Index of an item's kind. -/
def kindIndex : DisplayItem → Nat
  | .fillPath .. => 0
  | .strokePath .. => 1
  | .clip .. => 2
  | .glyphRun .. => 3
  | .image .. => 4
  | .shading .. => 5
  | .unsupported _ => 6
  | .groupBegin _ => 7
  | .groupEnd => 8
  | .softMask .. => 9

/-- Kind names, in index order (as `DisplayItem.kind`). -/
def kindNames : List String :=
  ["fillPath", "strokePath", "clip", "glyphRun", "image", "shading", "unsupported",
   "groupBegin", "groupEnd", "softMask"]

/-- What the views know about one page's content. -/
structure PageOps where
  /-- 0-based page index. -/
  index : Nat
  /-- Contents decoding error (then no operators). -/
  error : Option Error := none
  /-- Number of decoded content parts. -/
  parts : Nat := 0
  /-- Concatenated content length. -/
  bytes : Nat := 0
  /-- Operators executed: the page's and those of its forms (each expansion counted). -/
  ops : Nat := 0
  /-- Form XObjects expanded. -/
  forms : Nat := 0
  /-- Unsupported occurrences. -/
  unsupported : Nat := 0
  /-- Covered occurrences executed with a warning. -/
  warned : Nat := 0
  /-- Interpreter warnings (`Result.warnings`). -/
  interpWarnings : Nat := 0
  /-- Tokenizer warnings. -/
  tokWarnings : Nat := 0
  /-- Tokenizing or execution stopped at `Limits.maxOpsPerPage`. -/
  truncated : Bool := false
  /-- Histogram of this page. -/
  hist : Hist := {}
  /-- Item counts by kind. -/
  kinds : Array Nat := Array.replicate nKinds 0
  /-- Total items. -/
  itemCount : Nat := 0
  /-- The display list (kept only when asked for). -/
  items : DisplayList := #[]
  deriving Inhabited

/-- Covered occurrences. -/
def PageOps.covered (p : PageOps) : Nat := p.ops - p.unsupported

/-- Observer state of the attributed run. -/
structure Obs where
  /-- Histogram. -/
  hist : Hist := {}
  /-- Covered occurrences with warnings. -/
  warned : Nat := 0
  deriving Inhabited

/-- Record one executed operator with its warning and unknown counts. -/
def observe (o : Obs) (op : Op) (w u : Nat) : Obs :=
  let warned := if u == 0 && w > 0 then 1 else 0
  { hist := o.hist.add op.op 1 (if u > 0 then 1 else 0) warned, warned := o.warned + warned }

/-- The runner environment of the views. -/
def runEnv (limits : Limits) (doc : Doc) : SafePdf.Core.Content.Env Budget Obs :=
  { cfg := interpConfig limits, src := docSource limits doc, observe }

/-- Analyse one page from its decoded contents, running forms under `budget`; returns the
analysis and the budget left. -/
def analyze (limits : Limits) (doc : Doc) (page : Page) (index : Nat) (keepItems : Bool)
    (decoded : Except Error (List ByteArray)) (budget : Budget) : PageOps × Budget :=
  match decoded with
  | .error e => ({ index, error := some e }, budget)
  | .ok parts =>
    let bytes := joinParts parts
    let t := SafePdf.Core.Content.Ops.tokenize limits bytes
    let st := SafePdf.Core.Content.runPage (runEnv limits doc) (page.resources.getD []) t.ops
      budget {}
    let kinds := st.items.foldl (fun k it => k.modify (kindIndex it) (· + 1))
      (Array.replicate nKinds 0)
    ({ index, parts := parts.length, bytes := bytes.size, ops := st.ops, forms := st.forms,
       unsupported := st.unsupported, warned := st.obs.warned, interpWarnings := st.warnings,
       tokWarnings := t.warnings, truncated := t.truncated || st.truncated, hist := st.obs.hist,
       kinds, itemCount := st.items.size, items := if keepItems then st.items else #[] }, st.s)

/-- Analyse every page, threading the document budget (pure; no timings). -/
def analyzeDoc (limits : Limits) (doc : Doc) (keepItems : Bool) : Array PageOps := Id.run do
  let mut budget := Budget.init limits
  let mut out : Array PageOps := #[]
  for h : i in [0:doc.pages.size] do
    let page := doc.pages[i]'h.upper
    let (r, b) := doc.decodeContentsB limits budget page
    let (po, b) := analyze limits doc page i keepItems r b
    budget := b
    out := out.push po
  return out

/-- Analyse every page with per-page wall time (decode + tokenize + run). -/
def analyzeDocTimed (limits : Limits) (doc : Doc) : IO (Array (PageOps × Nat)) := do
  let mut budget := Budget.init limits
  let mut out : Array (PageOps × Nat) := #[]
  for h : i in [0:doc.pages.size] do
    let page := doc.pages[i]'h.upper
    let b0 := budget
    let t0 ← IO.monoNanosNow
    -- `lazyPure` evaluates the (strict) pair when this action runs, between the clock reads.
    let r ← IO.lazyPure fun _ =>
      let (d, b) := doc.decodeContentsB limits b0 page
      analyze limits doc page i false d b
    match r with
    | (po, b) =>
      let t1 ← IO.monoNanosNow
      budget := b
      out := out.push (po, t1 - t0)
  return out

/-! ## `ops` rendering -/

/-- `n / d` as a percentage with two decimals, rounded down; `n/a` when `d = 0`. -/
def pctText (n d : Nat) : String :=
  if d == 0 then "n/a"
  else
    let x := n * 10000 / d
    s!"{x / 100}.{padLeft 2 '0' (toString (x % 100))}%"

/-- `kind=count` pairs, non-zero only. -/
def kindsText (k : Array Nat) : String :=
  let l := (kindNames.zip k.toList).filter (·.2 > 0)
  if l.isEmpty then "none" else " ".intercalate (l.map fun (n, c) => s!"{n}={c}")

/-- Item counts as a JSON object (all kinds). -/
def kindsJson (k : Array Nat) : String :=
  jsonObject ((kindNames.zip k.toList).map fun (n, c) => (n, toString c))

/-- Document totals. -/
structure Totals where
  /-- Pages. -/
  pages : Nat := 0
  /-- Operators. -/
  ops : Nat := 0
  /-- Form expansions. -/
  forms : Nat := 0
  /-- Unsupported. -/
  unsupported : Nat := 0
  /-- Warned. -/
  warned : Nat := 0
  /-- Interpreter warnings. -/
  interpWarnings : Nat := 0
  /-- Tokenizer warnings. -/
  tokWarnings : Nat := 0
  /-- Truncated pages. -/
  truncated : Nat := 0
  /-- Pages whose contents could not be decoded. -/
  errors : Nat := 0
  /-- Items by kind. -/
  kinds : Array Nat := Array.replicate nKinds 0
  /-- Histogram. -/
  hist : Hist := {}
  /-- Largest per-page operator count. -/
  maxOps : Nat := 0

/-- Totals over pages. -/
def totals (ps : Array PageOps) : Totals :=
  ps.foldl (fun t p =>
    { pages := t.pages + 1, ops := t.ops + p.ops, forms := t.forms + p.forms, unsupported := t.unsupported + p.unsupported,
      warned := t.warned + p.warned, interpWarnings := t.interpWarnings + p.interpWarnings,
      tokWarnings := t.tokWarnings + p.tokWarnings,
      truncated := t.truncated + (if p.truncated then 1 else 0),
      errors := t.errors + (if p.error.isSome then 1 else 0),
      kinds := (List.range nKinds).toArray.map fun k => t.kinds[k]?.getD 0 + p.kinds[k]?.getD 0,
      hist := t.hist.merge p.hist, maxOps := max t.maxOps p.ops }) {}

/-- One text line per page. -/
def pageText (p : PageOps) (nanos : Option Nat) : String :=
  let ms := match nanos with
    | some n => s!"  {formatMs n} ms"
    | none => ""
  match p.error with
  | some e => s!"  #{p.index}  error: {renderError e}{ms}"
  | none =>
    let tr := if p.truncated then "  TRUNCATED" else ""
    s!"  #{p.index}  ops {p.ops}  forms {p.forms}  covered {p.covered}  unsupported {p.unsupported}  warned {p.warned}  warnings {p.interpWarnings}+{p.tokWarnings}  items {kindsText p.kinds}{tr}{ms}"

/-- Histogram lines. -/
def histText (h : Hist) : List String :=
  let rows := h.sorted.toList
  let w := rows.foldl (fun w s => max w (opName s.op).length) 2
  rows.map fun s =>
    let n := opName s.op
    let pad := String.ofList (List.replicate (w - n.length) ' ')
    let flag := if s.unsupported > 0 then "  UNSUPPORTED" else ""
    s!"  {n}{pad}  {padLeft 9 ' ' (toString s.count)}  warned {s.warned}{flag}"

/-- Text form of the `ops` view. -/
def opsText (path : String) (limits : Limits) (result : Except Error Document)
    (pages : Array PageOps) (nanos : Option (Array Nat)) : List String :=
  let head := [ s!"file:       {path}", s!"open:       {Summary.openMode result}" ]
  match Pages.docOf limits result with
  | .error e => head ++ [ s!"error:      {renderError e}" ]
  | .ok _ =>
    let t := totals pages
    let time := match nanos with
      | some ns => [ s!"time:       {formatMs (ns.foldl (· + ·) 0)} ms" ]
      | none => []
    head ++
    [ s!"pages:      {t.pages} ({t.errors} with undecodable contents, {t.truncated} truncated)",
      s!"forms:      {t.forms} expanded",
      s!"operators:  {t.ops}, covered {t.ops - t.unsupported} ({pctText (t.ops - t.unsupported) t.ops}), unsupported {t.unsupported}, warned {t.warned}",
      s!"warnings:   interpreter {t.interpWarnings}, tokenizer {t.tokWarnings}",
      s!"items:      {kindsText t.kinds}" ] ++ time ++
    (pages.toList.zipIdx.map fun (p, k) => pageText p (nanos.bind (·[k]?))) ++
    [ "histogram:" ] ++ histText t.hist

/-- Histogram as a JSON object. -/
def histJson (h : Hist) : String :=
  jsonObject (h.sorted.toList.map fun s =>
    (opName s.op, jsonObject [ ("count", toString s.count),
      ("unsupported", toString s.unsupported), ("warned", toString s.warned) ]))

/-- Unsupported operators of a page as a JSON object `{name: count}`. -/
def unsupportedJson (h : Hist) : String :=
  jsonObject ((h.sorted.toList.filter (·.unsupported > 0)).map fun s =>
    (opName s.op, toString s.unsupported))

/-- One JSON line per page. -/
def pageJson (p : PageOps) (nanos : Option Nat) : String :=
  jsonObject ([ ("page", toString p.index),
    ("error", match p.error with
      | some e => jsonString (renderError e)
      | none => "null"),
    ("parts", toString p.parts), ("contentBytes", toString p.bytes),
    ("ops", toString p.ops), ("forms", toString p.forms), ("covered", toString p.covered),
    ("unsupported", toString p.unsupported), ("warned", toString p.warned),
    ("interpWarnings", toString p.interpWarnings), ("tokWarnings", toString p.tokWarnings),
    ("truncated", toString p.truncated), ("items", kindsJson p.kinds),
    ("unsupportedOps", unsupportedJson p.hist) ] ++
    match nanos with
    | some n => [ ("ms", formatMs n) ]
    | none => [])

/-- JSON lines of the `ops` view: one per page, then the summary. -/
def opsJson (path : String) (limits : Limits) (result : Except Error Document)
    (pages : Array PageOps) (nanos : Option (Array Nat)) : List String :=
  let base := [ ("path", jsonString path), ("open", jsonString (Summary.openMode result)) ]
  match Pages.docOf limits result with
  | .error e => [ jsonObject [ ("summary", jsonObject (base ++
      [ ("error", jsonString (renderError e)) ])) ] ]
  | .ok _ =>
    let t := totals pages
    let time := match nanos with
      | some ns => [ ("ms", formatMs (ns.foldl (· + ·) 0)),
                     ("maxPageMs", formatMs (ns.foldl max 0)) ]
      | none => []
    (pages.toList.zipIdx.map fun (p, k) => pageJson p (nanos.bind (·[k]?))) ++
    [ jsonObject [ ("summary", jsonObject (base ++
      [ ("pages", toString t.pages), ("errorPages", toString t.errors),
        ("truncatedPages", toString t.truncated), ("ops", toString t.ops),
        ("forms", toString t.forms),
        ("covered", toString (t.ops - t.unsupported)),
        ("unsupported", toString t.unsupported), ("warned", toString t.warned),
        ("interpWarnings", toString t.interpWarnings), ("tokWarnings", toString t.tokWarnings),
        ("maxPageOps", toString t.maxOps), ("items", kindsJson t.kinds),
        ("histogram", histJson t.hist) ] ++ time)) ] ]

/-- The `ops` view. -/
def opsView : View where
  name := "ops"
  description := "content-stream operators per page: histogram, coverage, warnings, display items"
  run cfg i := do
    let timed ← match Pages.docOf cfg.limits i.result with
      | .ok doc => analyzeDocTimed cfg.limits doc
      | .error _ => pure #[]
    let pages := timed.map (·.1)
    let nanos := some (timed.map (·.2))
    if cfg.json then (opsJson i.path cfg.limits i.result pages nanos).forM IO.println
    else (opsText i.path cfg.limits i.result pages nanos).forM IO.println

/-! ## SVG rendering -/

/-- Exact decimal text of a `Fixed`. -/
def num (x : Fixed) : String := Pages.numText x.toDecimal

/-- `x y`. -/
def ptText (p : Point) : String := num p.x ++ " " ++ num p.y

/-- One path segment in SVG path syntax. -/
def segText : Segment → String
  | .moveTo p => "M" ++ ptText p
  | .lineTo p => "L" ++ ptText p
  | .curveTo a b c => "C" ++ ptText a ++ " " ++ ptText b ++ " " ++ ptText c
  | .closePath => "Z"

/-- SVG path data. -/
def pathD (p : Path) : String := " ".intercalate (p.segs.toList.map segText)

/-- `matrix(a b c d e f)`. -/
def matrixText (m : Matrix) : String :=
  s!"matrix({num m.a} {num m.b} {num m.c} {num m.d} {num m.e} {num m.f})"

/-- Rounded division (half up) for any non-zero divisor sign. -/
def divRound (p q : Int) : Int := if q < 0 then roundDiv (-p) (-q) else roundDiv p q

/-- Determinant of the linear part, at scale 10¹². -/
def det (m : Matrix) : Int := m.a.raw * m.d.raw - m.b.raw * m.c.raw

/-- Map a page-space point back to user space with the inverse of `m` (`dt = det m ≠ 0`). -/
def toUser (m : Matrix) (dt : Int) (p : Point) : Point :=
  let x := p.x.raw - m.e.raw
  let y := p.y.raw - m.f.raw
  ⟨Fixed.clamp (divRound ((x * m.d.raw - y * m.c.raw) * fixedScale) dt),
   Fixed.clamp (divRound ((y * m.a.raw - x * m.b.raw) * fixedScale) dt)⟩

/-- Map every point of a path. -/
def mapPath (f : Point → Point) (p : Path) : Path :=
  ⟨p.segs.map fun
    | .moveTo a => .moveTo (f a)
    | .lineTo a => .lineTo (f a)
    | .curveTo a b c => .curveTo (f a) (f b) (f c)
    | .closePath => .closePath⟩

/-- Is a character valid in XML 1.0 content? (Only checks the C0 range we can produce.) -/
def xmlChar (c : Char) : Char :=
  if c.toNat < 0x20 && c != '\t' && c != '\n' && c != '\r' then '�' else c

/-- Escape text content. -/
def escText (s : String) : String :=
  String.join (s.toList.map fun c =>
    match xmlChar c with
    | '&' => "&amp;"
    | '<' => "&lt;"
    | '>' => "&gt;"
    | '\t' => "&#9;"
    | '\n' => "&#10;"
    | '\r' => "&#13;"
    | c => c.toString)

/-- Escape an attribute value (double-quoted). -/
def escAttr (s : String) : String :=
  String.join (s.toList.map fun c =>
    match xmlChar c with
    | '"' => "&quot;"
    | '&' => "&amp;"
    | '<' => "&lt;"
    | '>' => "&gt;"
    | '\t' => "&#9;"
    | '\n' => "&#10;"
    | '\r' => "&#13;"
    | c => c.toString)

/-- A comment body: printable ASCII only, never `--`. -/
def commentSafe (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '-' then "_" else if c.toNat < 0x20 || c.toNat > 0x7E then "?" else c.toString)

/-- Name text of a resource name. -/
def nameText (n : SafePdf.Name) : String := Pages.safeBytes n.bytes

/-- A percentage from a value at scale `10^s` (value 1 = 100%): exact decimal. -/
def pctOf (v : Int) (s : Nat) : String :=
  -- value · 100 = v · 10^(2 - s)
  Pages.numText ⟨v, s - 2⟩ ++ "%"

/-- `rgb(R%,G%,B%)` and an optional pattern name. -/
def colorText : Color → String
  | .gray g => let p := pctOf g.raw 6; s!"rgb({p},{p},{p})"
  | .rgb r g b => s!"rgb({pctOf r.raw 6},{pctOf g.raw 6},{pctOf b.raw 6})"
  | .cmyk c m y k =>
    let ch (x : Comp) : String := pctOf ((fixedScale - x.raw) * (fixedScale - k.raw)) 12
    s!"rgb({ch c},{ch m},{ch y})"
  | .pattern _ => "rgb(50%,50%,50%)"

/-- `data-pattern` for pattern colours. -/
def patternAttr : Color → String
  | .pattern n => s!" data-pattern=\"{escAttr (nameText n)}\""
  | _ => ""

/-- An opacity attribute when alpha < 1. -/
def alphaAttr (attr : String) (a : Comp) : String :=
  if a.raw == fixedScale then "" else s!" {attr}=\"{Pages.numText ⟨a.raw, 6⟩}\""

/-- Fill rule keyword. -/
def ruleText : FillRule → String
  | .nonzero => "nonzero"
  | .evenOdd => "evenodd"

/-- Line cap keyword. -/
def capText : LineCap → String
  | .butt => "butt"
  | .round => "round"
  | .square => "square"

/-- Line join keyword. -/
def joinText : LineJoin → String
  | .miter => "miter"
  | .round => "round"
  | .bevel => "bevel"

/-- Stroke style attributes (user-space width and dashes). -/
def strokeAttrs (s : StrokeStyle) : String :=
  let l := s.line
  let width :=
    if l.width.raw == 0 then " stroke-width=\"1\" vector-effect=\"non-scaling-stroke\""
    else s!" stroke-width=\"{num l.width}\""
  let ml := if l.miterLimit.raw < fixedScale then Fixed.one else l.miterLimit
  let dash :=
    if l.dash.array.isEmpty then ""
    else s!" stroke-dasharray=\"{" ".intercalate (l.dash.array.map num)}\" stroke-dashoffset=\"{num l.dash.phase}\""
  s!" fill=\"none\" stroke=\"{colorText s.color}\"{patternAttr s.color}{alphaAttr "stroke-opacity" s.alpha}{width} stroke-linecap=\"{capText l.cap}\" stroke-linejoin=\"{joinText l.join}\" stroke-miterlimit=\"{num ml}\"{dash}"

/-- A stroke element (see the module doc for the CTM handling). -/
def strokeElem (path : Path) (s : StrokeStyle) : String :=
  let m := s.ctm
  if m == Matrix.identity then s!"<path d=\"{pathD path}\"{strokeAttrs s}/>"
  else
    let dt := det m
    if dt == 0 then s!"<path d=\"{pathD path}\" data-ctm=\"singular\"{strokeAttrs s}/>"
    else
      s!"<path transform=\"{matrixText m}\" d=\"{pathD (mapPath (toUser m dt) path)}\"{strokeAttrs s}/>"

/-- A fill element. -/
def fillElem (path : Path) (rule : FillRule) (s : FillStyle) : String :=
  s!"<path d=\"{pathD path}\" fill=\"{colorText s.color}\"{patternAttr s.color}{alphaAttr "fill-opacity" s.alpha} fill-rule=\"{ruleText rule}\"/>"

/-- Shown bytes of a run as Latin-1 text (adjustments dropped). -/
def runText (parts : List TextPart) : String :=
  String.join (parts.map fun
    | .str bs => String.ofList (bs.map fun b => Char.ofNat b.toNat)
    | .adjust _ => "")

/-- Does a render mode fill? -/
def modeFills : TextRenderMode → Bool
  | .fill | .fillStroke | .fillClip | .fillStrokeClip => true
  | _ => false

/-- Mode name for `data-render-mode`. -/
def modeName : TextRenderMode → String
  | .fill => "fill"
  | .stroke => "stroke"
  | .fillStroke => "fillStroke"
  | .invisible => "invisible"
  | .fillClip => "fillClip"
  | .strokeClip => "strokeClip"
  | .fillStrokeClip => "fillStrokeClip"
  | .clip => "clip"

/-- A text placeholder element. -/
def textElem (r : GlyphRun) : String :=
  let paint :=
    if !r.renderMode.paints then
      s!" fill=\"none\" data-render-mode=\"{modeName r.renderMode}\""
    else if modeFills r.renderMode then
      s!" fill=\"{colorText r.fill.color}\"{patternAttr r.fill.color}{alphaAttr "fill-opacity" r.fill.alpha}"
    else
      s!" fill=\"{colorText r.stroke.color}\"{patternAttr r.stroke.color}{alphaAttr "fill-opacity" r.stroke.alpha} data-render-mode=\"{modeName r.renderMode}\""
  s!"<text transform=\"{matrixText r.startMatrix} scale(1 -1)\" font-family=\"sans-serif\" font-size=\"1\" xml:space=\"preserve\" data-font=\"{escAttr (nameText r.font.name)}\" data-size=\"{num r.font.size}\"{paint}>{escText (runText r.parts)}</text>"

/-- A summary attribute from an image dictionary entry (numbers and names only). -/
def dictAttr (d : SafePdf.Dict) (key attr : String) : String :=
  match SafePdf.Dict.get? d (SafePdf.Name.ofString key) with
  | some (.int i) => s!" {attr}=\"{i}\""
  | some (.name n) => s!" {attr}=\"{escAttr (nameText n)}\""
  | some (.array (.name n :: _)) => s!" {attr}=\"{escAttr (nameText n)}\""
  | some (.ref n g) => s!" {attr}=\"{n} {g} R\""
  | _ => ""

/-- Whether an image dictionary is a stencil mask. -/
def isMask (d : SafePdf.Dict) : Bool :=
  SafePdf.Dict.get? d (SafePdf.Name.ofString "ImageMask") == some (.bool true)

/-- Name of an image codec. -/
def codecName : SafePdf.Core.Filter.ImageCodec → String
  | .dct => "DCT"
  | .jpx => "JPX"
  | .jbig2 => "JBIG2"
  | .ccitt => "CCITTFax"

/-- Outcome of decoding inline image data (`Filter.decodeStream`, strict). -/
def inlineDecoded (limits : Limits) (d : SafePdf.Dict) (data : ByteArray) : String :=
  match SafePdf.Core.Filter.decodeStream limits d data with
  | .ok (.data b) => s!"{b.size} bytes"
  | .ok (.image c _ b) => s!"codec {codecName c} ({b.size} bytes)"
  | .error _ => "error"

/-- An image placeholder element; `imgDict num gen` is the dictionary of an image XObject. -/
def imageElem (limits : Limits) (imgDict : Nat → Nat → SafePdf.Dict) (src : ImageSource)
    (ctm : Matrix) (fill : FillStyle) : String :=
  let (name, d, extra) := match src with
    | .xobject n num gen => (nameText n, imgDict num gen, s!" data-object=\"{num} {gen}\"")
    | .inline d data =>
      ("inline", d, s!" data-decoded=\"{escAttr (inlineDecoded limits d data)}\"")
  let summary := dictAttr d "Width" "data-width" ++ dictAttr d "Height" "data-height" ++
    dictAttr d "BitsPerComponent" "data-bpc" ++ dictAttr d "ColorSpace" "data-colorspace"
  let mask := isMask d
  let color := if mask then colorText fill.color else "rgb(80%,80%,80%)"
  let maskAttr := if mask then " data-mask=\"stencil\"" else ""
  s!"<rect x=\"0\" y=\"0\" width=\"1\" height=\"1\" transform=\"{matrixText ctm}\" fill=\"{color}\" data-image=\"{escAttr name}\"{extra}{summary}{maskAttr}/>"

/-! ## Clip registry -/

/-- Hash of a clip list (structure and coordinates). -/
def clipHash (c : Clip) : UInt64 :=
  let hp (h : UInt64) (p : Point) : UInt64 := mixHash (mixHash h (hash p.x.raw)) (hash p.y.raw)
  c.foldl (fun h cp =>
    let h := mixHash h (if cp.rule == .evenOdd then 2 else 1)
    cp.path.segs.foldl (fun h s =>
      match s with
      | .moveTo p => hp (mixHash h 3) p
      | .lineTo p => hp (mixHash h 5) p
      | .curveTo a b e => hp (hp (hp (mixHash h 7) a) b) e
      | .closePath => mixHash h 11) h) 17

/-- Distinct clips seen so far and their `<clipPath>` definitions. -/
structure ClipReg where
  /-- `(hash, clip, id)`. -/
  entries : Array (UInt64 × Clip × Nat) := #[]
  /-- Definitions, in id order. -/
  defs : Array String := #[]
  /-- Last clip looked up (fast path). -/
  last : Option (Clip × Nat) := none

/-- The id of a non-empty clip, registering it (and its tail) if new. -/
def ClipReg.idOf (reg : ClipReg) : Clip → ClipReg × Option Nat
  | [] => (reg, none)
  | c@(cp :: rest) =>
    let hit := match reg.last with
      | some (lc, id) => if lc == c then some id else none
      | none => none
    match hit with
    | some id => (reg, some id)
    | none =>
      let h := clipHash c
      match reg.entries.find? (fun (h', c', _) => h' == h && c' == c) with
      | some (_, _, id) => ({ reg with last := some (c, id) }, some id)
      | none =>
        let (reg, parent) := ClipReg.idOf reg rest
        let id := reg.entries.size
        let pAttr := match parent with
          | some p => s!" clip-path=\"url(#c{p})\""
          | none => ""
        let d := s!"<clipPath id=\"c{id}\" clipPathUnits=\"userSpaceOnUse\"{pAttr}><path d=\"{pathD cp.path}\" clip-rule=\"{ruleText cp.rule}\"/></clipPath>"
        ({ entries := reg.entries.push (h, c, id), defs := reg.defs.push d,
           last := some (c, id) }, some id)

/-! ## Page frame -/

/-- SVG width, height and the page-to-SVG matrix for a CropBox and rotation. -/
def frame (crop : Rect) (rot : Rotation) : Fixed × Fixed × Matrix :=
  let llx := Fixed.ofDecimal crop.llx
  let lly := Fixed.ofDecimal crop.lly
  let urx := Fixed.ofDecimal crop.urx
  let ury := Fixed.ofDecimal crop.ury
  let w := Fixed.sub urx llx
  let h := Fixed.sub ury lly
  let z := Fixed.zero
  let o := Fixed.one
  let mo := Fixed.neg o
  match rot with
  | .r0 => (w, h, ⟨o, z, z, mo, Fixed.neg llx, ury⟩)
  | .r90 => (h, w, ⟨z, o, o, z, Fixed.neg lly, Fixed.neg llx⟩)
  | .r180 => (w, h, ⟨mo, z, z, o, urx, Fixed.neg lly⟩)
  | .r270 => (h, w, ⟨z, mo, mo, z, ury, urx⟩)

/-- The clip carried by an item (`none` for items that draw nothing). -/
def itemClip : DisplayItem → Option Clip
  | .fillPath _ _ _ c | .strokePath _ _ c | .glyphRun _ c | .image _ _ _ c | .shading _ _ _ _ c =>
    some c
  | _ => none

/-- The stream dictionary of object `num gen` (`[]` if it is not a stream). -/
def streamDict (limits : Limits) (doc : Doc) (num gen : Nat) : SafePdf.Dict :=
  match doc.file.getObject limits num gen with
  | .ok (.stream s) => s.dict
  | _ => []

/-! ## Text overlay (`SAFEPDF_SVG_TEXT=1`, task 6.6) -/

/-- Page-space point of a point given in a baseline direction's frame (`u` along the baseline,
`v` across it): the inverse of `Core.Text.rotFrame`. -/
def unrot (dir : Nat) (u v : Fixed) : Fixed × Fixed :=
  match dir with
  | 1 => (Fixed.neg v, u)
  | 2 => (Fixed.neg u, Fixed.neg v)
  | 3 => (v, Fixed.neg u)
  | _ => (u, v)

/-- Smaller of two values. -/
def fmin (x y : Fixed) : Fixed := if x.raw ≤ y.raw then x else y

/-- Larger of two values. -/
def fmax (x y : Fixed) : Fixed := if x.raw ≤ y.raw then y else x

/-- The overlay box of an extracted glyph, as a page-space `<rect>`: along the baseline from
the origin over the glyph width, across it from 0.2 em below the baseline to 0.8 em above
(a nominal descent/ascent; the extraction carries no glyph bounding box), mapped back from the
glyph's baseline frame and normalised to an axis-aligned rectangle. -/
def glyphRect (g : SafePdf.Core.Text.Glyph) : String :=
  let (u0, v0) := SafePdf.Core.Text.rotFrame g.dir g.x g.y
  let lo := Fixed.sub v0 (Fixed.mul g.fontSize (Fixed.ofDecimal ⟨2, 1⟩))
  let hi := Fixed.add v0 (Fixed.mul g.fontSize (Fixed.ofDecimal ⟨8, 1⟩))
  let (ax, ay) := unrot g.dir u0 lo
  let (bx, by_) := unrot g.dir (Fixed.add u0 g.width) hi
  let x0 := fmin ax bx
  let y0 := fmin ay by_
  let fill := if g.visible then "rgb(0%,0%,100%)" else "rgb(0%,60%,0%)"
  s!"<rect x=\"{num x0}\" y=\"{num y0}\" width=\"{num (Fixed.sub (fmax ax bx) x0)}\" height=\"{num (Fixed.sub (fmax ay by_) y0)}\" fill=\"{fill}\" fill-opacity=\"0.15\" stroke=\"rgb(100%,0%,0%)\" stroke-width=\"0.2\" stroke-opacity=\"0.6\" data-item=\"{g.item}\" data-seq=\"{g.seq}\" data-text=\"{escAttr g.text}\"/>"

/-- The text overlay of a page: one group of glyph boxes (`glyphRect`) from
`Core.Text.extractDocPage` with a fresh budget, or a comment when the contents do not decode. -/
def textOverlay (limits : Limits) (doc : Doc) (page : Page) : List String :=
  match (SafePdf.Core.Text.extractDocPage limits doc page (Budget.init limits)).1 with
  | .error e => [s!"<!-- text overlay: {commentSafe (renderError e)} -->"]
  | .ok pt =>
    ["<g data-overlay=\"text\">"] ++ pt.glyphs.map glyphRect ++ ["</g>"]

/-- Render a page's display list as an SVG document (`index` is 0-based). `overlay` lines are
appended last inside the page-space group (the `SAFEPDF_SVG_TEXT` glyph boxes). -/
def renderPage (limits : Limits) (doc : Doc) (page : Page) (index : Nat) (po : PageOps)
    (overlay : List String := []) : String := Id.run do
  let (w, h, m) := frame page.cropBox page.rotate
  let mut out : Array String := #[
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    s!"<svg xmlns=\"http://www.w3.org/2000/svg\" version=\"1.1\" width=\"{num w}\" height=\"{num h}\" viewBox=\"0 0 {num w} {num h}\" data-page=\"{index + 1}\">",
    s!"<rect x=\"0\" y=\"0\" width=\"{num w}\" height=\"{num h}\" fill=\"white\"/>",
    s!"<g transform=\"{matrixText m}\">" ]
  if let some e := po.error then
    out := out.push s!"<!-- contents not decoded: {commentSafe (renderError e)} -->"
  let crop := page.cropBox
  let cropRect := s!"x=\"{num (Fixed.ofDecimal crop.llx)}\" y=\"{num (Fixed.ofDecimal crop.lly)}\" width=\"{num (Fixed.sub (Fixed.ofDecimal crop.urx) (Fixed.ofDecimal crop.llx))}\" height=\"{num (Fixed.sub (Fixed.ofDecimal crop.ury) (Fixed.ofDecimal crop.lly))}\""
  let mut reg : ClipReg := {}
  let mut cur : Option Nat := none
  for it in po.items do
    -- Switch clip groups when the item's clip changes.
    if let some c := itemClip it then
      let (reg', id) := reg.idOf c
      reg := reg'
      if id != cur then
        if cur.isSome then out := out.push "</g>"
        if let some k := id then out := out.push s!"<g clip-path=\"url(#c{k})\">"
        cur := id
    match it with
    | .fillPath p r s _ => out := out.push (fillElem p r s)
    | .strokePath p s _ => out := out.push (strokeElem p s)
    | .clip _ _ => pure ()
    | .glyphRun r _ => out := out.push (textElem r)
    | .image src ctm fill _ =>
      out := out.push (imageElem limits (streamDict limits doc) src ctm fill)
    | .shading n _ _ _ _ =>
      out := out.push s!"<rect {cropRect} fill=\"rgb(70%,70%,70%)\" fill-opacity=\"0.5\" data-shading=\"{escAttr (nameText n)}\"/>"
    | .unsupported op => out := out.push s!"<!-- unsupported operator: {commentSafe (opName op)} -->"
    -- transparency (7.3c) is not exported: groups paint their items plainly, masks are skipped
    | .groupBegin _ | .groupEnd | .softMask .. => pure ()
  if cur.isSome then out := out.push "</g>"
  if !reg.defs.isEmpty then
    out := out.push "<defs>"
    out := out ++ reg.defs
    out := out.push "</defs>"
  out := out ++ overlay.toArray
  out := out.push "</g>"
  out := out.push "</svg>"
  return "\n".intercalate out.toList ++ "\n"

/-- Render page `i` (0-based) with a fresh budget; `text` adds the glyph-box overlay. -/
def renderIndex (limits : Limits) (doc : Doc) (i : Nat) (text : Bool := false) :
    Option String :=
  if h : i < doc.pages.size then
    let page := doc.pages[i]
    let (r, b) := doc.decodeContentsB limits (Budget.init limits) page
    some (renderPage limits doc page i (analyze limits doc page i true r b).1
      (if text then textOverlay limits doc page else []))
  else none

/-- The `svg` view. -/
def svgView : View where
  name := "svg"
  description := "render a page to SVG from the display list (SAFEPDF_PAGE=N, default 1; SAFEPDF_SVG_DIR=dir writes all pages; SAFEPDF_SVG_TEXT=1 overlays extracted glyph boxes)"
  run cfg i := do
    match Pages.docOf cfg.limits i.result with
    | .error e => IO.eprintln s!"inspect: {i.path}: {renderError e}"
    | .ok doc =>
      let text := (← IO.getEnv "SAFEPDF_SVG_TEXT") == some "1"
      match ← IO.getEnv "SAFEPDF_SVG_DIR" with
      | some dir =>
        let dir : System.FilePath := dir
        IO.FS.createDirAll dir
        let mut budget := Budget.init cfg.limits
        for h : k in [0:doc.pages.size] do
          let page := doc.pages[k]'h.upper
          let (r, b) := doc.decodeContentsB cfg.limits budget page
          let (po, b) := analyze cfg.limits doc page k true r b
          budget := b
          let svg := renderPage cfg.limits doc page k po
            (if text then textOverlay cfg.limits doc page else [])
          let out := dir / s!"page-{k + 1}.svg"
          IO.FS.writeFile out svg
          let err := match po.error with
            | some e => some (renderError e)
            | none => none
          if cfg.json then
            IO.println (jsonObject [ ("page", toString (k + 1)), ("file", jsonString out.toString),
              ("items", toString po.itemCount), ("bytes", toString svg.utf8ByteSize),
              ("error", match err with
                | some e => jsonString e
                | none => "null") ])
          else
            IO.println s!"page {k + 1}: {po.itemCount} items, {svg.utf8ByteSize} bytes -> {out}{match err with | some e => s!" (contents: {e})" | none => ""}"
      | none =>
        let n ← match ← IO.getEnv "SAFEPDF_PAGE" with
          | none => pure 1
          | some s =>
            match s.trimAscii.toString.toNat? with
            | some n => pure n
            | none =>
              IO.eprintln s!"inspect: SAFEPDF_PAGE='{s}' is not a page number; using 1"
              pure 1
        if n == 0 then
          IO.eprintln s!"inspect: {i.path}: SAFEPDF_PAGE is 1-based"
        else
          match renderIndex cfg.limits doc (n - 1) text with
          | some svg => IO.print svg
          | none =>
            IO.eprintln s!"inspect: {i.path}: page {n} out of range (1..{doc.pages.size})"

end SafePdf.Shell.Views.Svg
