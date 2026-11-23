import SafePdf.Api
import SafePdf.Shell.Worker.Wire

/-!
# The document worker: request handling and loop (task 12.2a)

Plan.md §6 Phase 12, "Restricted, stoppable document worker": a separate process that holds
the open document and does the work on untrusted bytes (parsing, rendering, text extraction),
so that the GUI can stop it (kill) at any time and, in task 12.2b, run it in a sandbox.

* **Input is bytes, never a path.** The worker opens no document file: the client sends the
  document in a `Request.openDoc` frame (`SafePdf.Api.openBytes`, strict mode available). The
  only files it reads are the substitute fonts in the fixed system font directories
  (`Worker.workerFonts`, loaded once, on the first `openDoc`) — a known gap for 12.2b, which
  decides whether the GUI sends font bytes instead.
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
  `SafePdf.Api.pageInfo`, `outline`, `pageLinks`. Limits are `Limits.default`.

Nothing but frames is written to stdout. The executable's `main` is in
`SafePdf.Shell.Worker.Main`; this module holds everything else, so tests can import it.
-/

namespace SafePdf.Shell.Worker.Serve

open SafePdf SafePdf.Core
open SafePdf.Shell.Worker
open SafePdf.Shell.Worker.Protocol (Request Response ErrorKind)

/-- The worker's state: the open document and the substitute fonts (loaded on first open). -/
structure State where
  /-- The open document. -/
  doc : Option Api.Document := none
  /-- Substitute fonts for non-embedded standard-14 faces. -/
  subst : Option Raster.Subst.SubstFonts := none

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

/-- Answer one request on the open document `d` (pure; `subst` are the fonts). -/
def answerDoc (d : Api.Document) (subst : Raster.Subst.SubstFonts) : Request → Response
  | .info => .docInfo d.pageCount d.repaired d.encrypted
  | .pageInfo i =>
    match Api.pageInfo d i with
    | .ok pi => .pageInfo pi.label pi.size.1 pi.size.2 (rotationToNat pi.rotation)
    | .error e => pageError e
  | .render i zoom rot =>
    match rotationOfNat? rot with
    | none => .error .pageFailed s!"rotation must be 0–3 quarter turns (got {rot})"
    | some r =>
      match d.page i with
      | .error e => pageError e
      | .ok p =>
        if zoom ≤ 0 then pageError (.badZoom zoom)
        else
          match (Raster.Glyph.renderDocPage d.limits d.doc p zoom r
              (Filter.Budget.init d.limits) (subst := subst)).1 with
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
  | .openDoc .. | .quit => .error .malformed "unreachable"

/-- Answer one request, updating the state. -/
def answer (st : State) (req : Request) : IO (State × Response) := do
  match req with
  | .openDoc bytes allowRepair =>
    match Api.openBytes bytes { allowRepair } with
    | .error e => return ({ st with doc := none }, .error .openFailed e.message)
    | .ok d =>
      let subst ← match st.subst with
        | some s => pure s
        | none => workerFonts d.limits
      return ({ doc := some d, subst := some subst },
        .docInfo d.pageCount d.repaired d.encrypted)
  | .quit => return (st, .bye)
  | _ =>
    match st.doc with
    | none => return (st, .error .noDocument "no document is open")
    | some d => return (st, answerDoc d (st.subst.getD {}) req)

/-- The request loop. Returns the exit status. -/
def loop (limits : Limits) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut st : State := {}
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
        let (st', resp) ← answer st req
        st := st'
        writeAll stdout (Protocol.frameResponse limits resp)
        if let .quit := req then return 0
  return 0

end SafePdf.Shell.Worker.Serve
