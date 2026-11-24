import SafePdf.Api
import SafePdf.Shell.Worker.Wire
import SafePdf.Shell.Worker.TestHooks
import SafePdf.Core.Annot
import SafePdf.Shell.App.Select
import SafePdf.Shell.App.Links
import SafePdf.Shell.Views.Common

/-!
# The document worker: request handling and loop (task 12.2a)

Plan.md §6 Phase 12, "Restricted, stoppable document worker": a separate process that holds
the open document and does the work on untrusted bytes (parsing, rendering, text extraction),
so that the GUI can stop it (kill) at any time and, in task 12.2b, run it in a sandbox.

* **Input is bytes, never a path.** The worker opens no document file: the client sends the
  document in a `Request.openDoc` frame (`SafePdf.Api.openBytes`, strict mode available). The
  only files it reads are the substitute fonts in the fixed system font directories
  (`Worker.workerFaces`), read once at startup **before** the worker confines itself (task
  12.2b, `SafePdf.Shell.Worker.Sandbox`); the loop receives them as the initial `State` and
  does no file or environment access of its own.
* **No environment needed.** Nothing reads environment variables or the working directory;
  the client starts it with an empty environment and `/` as working directory.
* **Loop.** Read a frame from stdin (`Worker.readFrame`, cap `Protocol.requestCap`), decode it
  (`Protocol.decodeBody`), answer with one frame on stdout (`Protocol.frameResponse`, cap
  `Protocol.responseCap`). A payload that does not decode gets an `error .malformed` answer
  and the loop goes on (the frame boundary is intact). A header above the cap gets an
  `error .tooLong` answer and the worker exits with status 2 (the stream cannot be
  resynchronised without reading the oversized payload). End of input or `quit` ends it.
* **The same calls as the viewer.** Rendering is `Core.Raster.Glyph.renderDocPage` with the
  substitute fonts (as `App.Viewer.renderPage` and `Shell.Ffi.render`); text is
  `SafePdf.Api.pageText` (with or without annotation text); page info, outline and links are
  `SafePdf.Api.pageInfo`, `outline`, `pageLinks`. Limits are the startup configuration's
  (`Protocol.StartConfig`, flag `--limits=`; task 12.2d), `Limits.default` without the flag.
* **The viewer's text and links** (task 12.2d). `pageIndex` answers with exactly what the
  viewer's selection, copy and search index (`App.Select.PageIndex.ofText` of
  `Core.Annot.extractDocPageAnnots`: page and annotation text, glyphs outside the CropBox and
  clipped glyphs left out) holds, computed here with the same calls under the requested layers
  state; `viewLinks` answers with `App.Links.pageLinks`. Renders take a layers state too.
* **One decode budget per request** (task 12.3b). `answer` makes the request's
  `Filter.Budget` once (`requestBudget`, the full `Limits.maxDecodedTotalBytes`) and threads it
  through everything the request decodes (`answerDocB`: the render, the text, the selection
  index); no request covers more than one page, so no page gets a budget of its own beside the
  request's. The budget is not carried **across** requests (a search's pages, a session):
  that would make a page's answer depend on the requests before it, so a worker's answer would
  no longer equal the in-process call (`Api.renderPage`, `Api.pageText`, which start from a
  fresh budget; the `worker` suite checks byte equality), and the protocol would have to carry
  the remainder. Work across requests is bounded by the viewer instead: a search's shared
  allowance (`App.Budget.Allowance`, pages), the work pool (memory) and the worker's fences
  (deadline, `RLIMIT_CPU`, memory ceiling).

Nothing but frames is written to stdout. The executable's `main` is in
`SafePdf.Shell.Worker.Main`; this module holds everything else, so tests can import it.
-/

namespace SafePdf.Shell.Worker.Serve

open SafePdf SafePdf.Core
open SafePdf.Shell.Worker
open SafePdf.Shell.Worker.Protocol (Request Response ErrorKind)

/-- The worker's state: the open document and the substitute fonts (loaded at startup). -/
structure State where
  /-- The open document. -/
  doc : Option Api.Document := none
  /-- Substitute fonts for non-embedded standard-14 faces. -/
  subst : Raster.Subst.SubstFonts := {}

/-- The protocol's target of an API target. -/
def target : Api.Target → Protocol.Target
  | .none => .none
  | .page i f => .page i f
  | .danglingDest f => .danglingDest f
  | .unresolved n => .unresolved n
  | .uri u => .uri u
  | .action k => .action k

/-- The protocol's glyph of an API glyph. -/
def glyph (g : Api.Glyph) : Protocol.Glyph :=
  { text := g.text, origin := g.origin, box := g.box, fontSize := g.fontSize, dir := g.dir
    visible := g.visible, item := g.item, seq := g.seq }

/-- A failed per-page call. -/
def pageError (e : Api.Error) : Response := .error .pageFailed e.message

/-- The protocol's cell of a selection cell. -/
def cell (c : App.Select.Cell) : Protocol.Cell :=
  { text := c.text, sep := c.sep, box := c.box, line := c.line }

/-- The protocol's action of a viewer link action. -/
def action : App.Links.Action → Protocol.Action
  | .goto j => .goto j.page j.left j.top
  | .uri s => .uri s
  | .badPage => .badPage
  | .unresolved n => .unresolved n
  | .other k => .other k
  | .none => .none

/-- **The selection index of page `p`** as the viewer builds it in process (task 12.2d):
`Select.PageIndex.ofText` of `Annot.extractDocPageAnnots` with a fresh budget under `oc`. An
error is the viewer's text for it (`Shell.renderError`). -/
def pageIndexOf (limits : Limits) (doc : Doc.Doc) (page : Doc.Page)
    (oc : Option Doc.OptionalContent.State) : Except String App.Select.PageIndex :=
  match (Annot.extractDocPageAnnots limits doc page (Filter.Budget.init limits) (oc := oc)).1 with
  | .ok pt => .ok (App.Select.PageIndex.ofText pt)
  | .error e => .error (Shell.renderError e)

/-- **The request's decode budget** (task 12.3b): one per request, the full document budget. -/
def requestBudget (limits : Limits) : Filter.Budget := Filter.Budget.init limits

/-- `Api.pageTextCore` with the request's budget `b` instead of a fresh one (task 12.3b);
equal to it from `requestBudget` (`pageTextB_init`). -/
def pageTextB (d : Api.Document) (i : Nat) (o : Api.TextOptions) (b : Filter.Budget) :
    Except Api.Error Text.PageText := do
  let p ← d.page i
  let r := if o.withAnnots then (Annot.extractDocPageAnnots d.limits d.doc p b o.layout o.oc).1
    else (Text.extractDocPage d.limits d.doc p b o.layout o.oc).1
  match r with
  | .ok pt => .ok pt
  | .error e => .error (.pdf e)

/-- From the request's budget the worker's text is the API's. -/
theorem pageTextB_init (d : Api.Document) (i : Nat) (o : Api.TextOptions) :
    pageTextB d i o (requestBudget d.limits) = Api.pageTextCore d i o := rfl

/-- The selection index of page `page` with the request's budget `b` (`pageIndexOf`). -/
def pageIndexB (limits : Limits) (doc : Doc.Doc) (page : Doc.Page)
    (oc : Option Doc.OptionalContent.State) (b : Filter.Budget) :
    Except String App.Select.PageIndex :=
  match (Annot.extractDocPageAnnots limits doc page b (oc := oc)).1 with
  | .ok pt => .ok (App.Select.PageIndex.ofText pt)
  | .error e => .error (Shell.renderError e)

/-- From the request's budget the worker's index is the viewer's in-process one. -/
theorem pageIndexB_init (limits : Limits) (doc : Doc.Doc) (page : Doc.Page)
    (oc : Option Doc.OptionalContent.State) :
    pageIndexB limits doc page oc (requestBudget limits) = pageIndexOf limits doc page oc := rfl

/-- **Answer one request on the open document `d`** with the request's decode budget `b`
(pure; `subst` are the fonts): every decode of the request draws on `b`. -/
def answerDocB (d : Api.Document) (subst : Raster.Subst.SubstFonts) (b : Filter.Budget) :
    Request → Response
  | .info => .docInfo d.pageCount d.repaired d.encrypted
  | .pageInfo i =>
    match Api.pageInfo d i with
    | .ok pi => .pageInfo pi.label pi.size.1 pi.size.2 (rotationToNat pi.rotation)
    | .error e => pageError e
  | .render i zoom rot oc =>
    match rotationOfNat? rot with
    | none => .error .pageFailed s!"rotation must be 0–3 quarter turns (got {rot})"
    | some r =>
      match d.page i with
      | .error e => pageError e
      | .ok p =>
        if zoom ≤ 0 then pageError (.badZoom zoom)
        else
          match (Raster.Glyph.renderDocPage d.limits d.doc p zoom r b (subst := subst)
              (oc := oc)).1 with
          | .ok img => .image img.w img.h img.data
          | .error e => pageError (.pdf e)
  | .text i withAnnots =>
    match (pageTextB d i { withAnnots } b).map (Api.PageText.ofCore {}) with
    | .ok t => .text t.text (t.glyphs.toList.map glyph)
    | .error e => pageError e
  | .outline => .outline ((Api.outline d).map fun it =>
      { title := it.title, depth := it.depth, target := target it.target, count := it.count })
  | .links i =>
    match Api.pageLinks d i with
    | .ok ls => .links (ls.map fun l => { rect := l.rect, target := target l.target })
    | .error e => pageError e
  | .pageIndex i oc =>
    match d.page i with
    | .error e => pageError e
    | .ok p =>
      match pageIndexB d.limits d.doc p oc b with
      | .ok ix => .pageIndex (ix.cells.toList.map cell) ix.lineDirs.toList ix.hidden.toList
      | .error m => .error .pageFailed m
  | .viewLinks i =>
    match d.page i with
    | .error e => pageError e
    | .ok _ => .viewLinks ((App.Links.pageLinks d.doc d.limits i).toList.map fun l =>
        { box := l.box, action := action l.action })
  | .openDoc .. | .quit => .error .malformed "unreachable"

/-- Answer one request on the open document `d` (pure; `subst` are the fonts). Before task
12.3b; kept as the reference `answerDocB_init` compares with. -/
def answerDoc (d : Api.Document) (subst : Raster.Subst.SubstFonts) : Request → Response
  | .info => .docInfo d.pageCount d.repaired d.encrypted
  | .pageInfo i =>
    match Api.pageInfo d i with
    | .ok pi => .pageInfo pi.label pi.size.1 pi.size.2 (rotationToNat pi.rotation)
    | .error e => pageError e
  | .render i zoom rot oc =>
    match rotationOfNat? rot with
    | none => .error .pageFailed s!"rotation must be 0–3 quarter turns (got {rot})"
    | some r =>
      match d.page i with
      | .error e => pageError e
      | .ok p =>
        if zoom ≤ 0 then pageError (.badZoom zoom)
        else
          match (Raster.Glyph.renderDocPage d.limits d.doc p zoom r
              (Filter.Budget.init d.limits) (subst := subst) (oc := oc)).1 with
          | .ok img => .image img.w img.h img.data
          | .error e => pageError (.pdf e)
  | .text i withAnnots =>
    match Api.pageText d i { withAnnots } with
    | .ok t => .text t.text (t.glyphs.toList.map glyph)
    | .error e => pageError e
  | .outline => .outline ((Api.outline d).map fun it =>
      { title := it.title, depth := it.depth, target := target it.target, count := it.count })
  | .links i =>
    match Api.pageLinks d i with
    | .ok ls => .links (ls.map fun l => { rect := l.rect, target := target l.target })
    | .error e => pageError e
  | .pageIndex i oc =>
    match d.page i with
    | .error e => pageError e
    | .ok p =>
      match pageIndexOf d.limits d.doc p oc with
      | .ok ix => .pageIndex (ix.cells.toList.map cell) ix.lineDirs.toList ix.hidden.toList
      | .error m => .error .pageFailed m
  | .viewLinks i =>
    match d.page i with
    | .error e => pageError e
    | .ok _ => .viewLinks ((App.Links.pageLinks d.doc d.limits i).toList.map fun l =>
        { box := l.box, action := action l.action })
  | .openDoc .. | .quit => .error .malformed "unreachable"

/-- **Threading the request's budget changes no answer**: from `requestBudget` the worker
answers exactly as before task 12.3b (a fresh budget per call), so the `worker` suite's byte
equality with the in-process calls still holds. -/
theorem answerDocB_init (d : Api.Document) (subst : Raster.Subst.SubstFonts) (req : Request) :
    answerDocB d subst (requestBudget d.limits) req = answerDoc d subst req := by
  cases req <;> rfl

/-- Answer one request, updating the state (pure: no file, network or environment access).
Documents open under `limits` (the startup configuration's). Task 12.3b: the request's one
decode budget (`requestBudget`) is made here and threaded through it (`answerDocB`). -/
def answer (st : State) (req : Request) (limits : Limits := {}) : State × Response :=
  match req with
  | .openDoc bytes allowRepair =>
    match Api.openBytes bytes { allowRepair, limits } with
    | .error e => ({ st with doc := none }, .error .openFailed e.message)
    | .ok d => ({ st with doc := some d }, .docInfo d.pageCount d.repaired d.encrypted)
  | .quit => (st, .bye)
  | _ =>
    match st.doc with
    | none => (st, .error .noDocument "no document is open")
    | some d => (st, answerDocB d st.subst (requestBudget d.limits) req)

/-- The request loop, starting with the substitute fonts `subst`. Its only effects are reading
stdin and writing stdout, and `beforeEach`, run before every decoded request (task 12.3: the
worker re-arms its CPU-time fence there, `Sandbox.armCpu`). Returns the exit status. -/
def loop (limits : Limits) (subst : Raster.Subst.SubstFonts) (stallMs : Nat := 0)
    (beforeEach : IO Unit := pure ()) (spinMs : Nat := 0) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut st : State := { subst }
  repeat
    match ← readFrame stdin (Protocol.requestCap limits) with
    | .eof => return 0
    | .truncated _ => return 1
    | .tooLong len =>
      writeAll stdout (Protocol.frameResponse limits (.error .tooLong
        s!"request of {len} bytes exceeds the cap of {Protocol.requestCap limits} bytes"))
      return 2
    | .frame payload =>
      match Protocol.decodeBody Protocol.request payload with
      | .error e =>
        writeAll stdout (Protocol.frameResponse limits (.error .malformed (reprStr e)))
      | .ok req =>
        beforeEach
        TestHooks.beforeRequest stallMs req spinMs
        let (st', resp) := answer st req limits
        st := st'
        writeAll stdout (Protocol.frameResponse limits resp)
        if let .quit := req then return 0
  return 0

end SafePdf.Shell.Worker.Serve
