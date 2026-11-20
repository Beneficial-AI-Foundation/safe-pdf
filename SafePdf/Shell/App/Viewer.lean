import SafePdf.Shell.App.Shim
import SafePdf.Shell.App.Tcl
import SafePdf.Shell.Inspect
import SafePdf.Shell.Views.Pages

/-!
# Native viewer skeleton (task 8.2a; Plan.md §6 Phase 8, §8 native app, §10 `SafePdf/Shell/`)

The unverified, replaceable shell of the viewer (Plan.md §8): one Tk window with a toolbar
(Open…, Prev, Next, page k/n), a canvas showing the current page as a Tk photo image, and a
status line. Ledger Decisions 8.1 chose Tcl/Tk through the C shim `c/tk_shim.c`.

* **Opening.** A file named on the command line, else `tk_getOpenFile` (also Ctrl+O and the
  Open… button). The file is read and parsed exactly as the inspector does
  (`Inspect.load`: size check against `Limits.maxInputBytes`, `SafePdf.parseWith`), then
  `Views.Pages.docOf` builds the page tree.
* **Rendering.** The verified full-page renderer `Core.Raster.Glyph.renderDocPage` with a
  fresh decoded-bytes budget per page (as the inspector's `raster` view), user rotation 0, at
  the zoom that fits the page (CropBox, page `/Rotate`) into the canvas (`fitZoom`). The RGBA
  buffer goes to the photo through `Shim.photoPut` (`Tk_PhotoPutBlock`). A page is re-rendered
  when the page, the document or the fitting zoom changes (window resizes are debounced by
  100 ms in Tcl).
* **Navigation.** Next: `Next`/`Right`/`Down`/`space` keys or the Next button; previous:
  `Prior`/`Left`/`Up`/`BackSpace` or Prev; `Home`/`End` first/last page; Ctrl+Q quits.
* **Errors** (unreadable file, parse error, render error, Tcl error) are shown in the status
  line; the window stays usable. Every event handler catches its own exceptions.
* **No data in script text.** Every Tcl command that carries data (file names, error messages,
  numbers) is built with `Tcl.cmd`/`Script.render`, whose literal words go through the proved
  `Tcl.quote` (`Tcl.parseScript_render`); the only raw script text is the constant UI setup.
* **Smoke mode** (`SAFEPDF_VIEWER_SMOKE=DIR`, used by `scripts/viewer-smoke.sh`): after the first
  page is shown the viewer writes the photo to `DIR/page-1.ppm`, sends itself a `Next` key
  event through Tk (`event generate`), writes `DIR/page-2.ppm` when the document has a second
  page, writes `DIR/state.txt` (window title and status line) and exits.

`docs/viewer.md` describes building and running it.
-/

namespace SafePdf.Shell.App.Viewer

open SafePdf.Shell
open SafePdf.Core.Doc (Doc)
open SafePdf.Core.Raster (Clip.Image)

/-! ## State -/

/-- The viewer's state, kept in one `IO.Ref`. -/
structure State where
  /-- Path of the open file, if any. -/
  path : Option String := none
  /-- The opened document (`none`: no file, or it failed to open). -/
  doc : Option Doc := none
  /-- Current page, 0-based. -/
  page : Nat := 0
  /-- Canvas width in pixels (last `<Configure>`). -/
  canvasW : Nat := 800
  /-- Canvas height in pixels (last `<Configure>`). -/
  canvasH : Nat := 1000
  /-- What is on screen: (path, page, zoom) of the last successful or failed render. -/
  shown : Option (String × Nat × Rat) := none
  /-- Smoke-test output directory (`SAFEPDF_VIEWER_SMOKE`). -/
  smokeDir : Option String := none
  /-- Smoke-test step counter. -/
  smokeStep : Nat := 0

/-- The limits the viewer parses and renders with. -/
def limits : Limits := Limits.default

/-- Name of the Tk photo image that shows the page. -/
def photoName : String := "::safepdf::page"

/-! ## Pure helpers -/

/-- Number of pages of the open document (0 when none). -/
def State.pageCount (s : State) : Nat :=
  match s.doc with
  | some d => d.pages.size
  | none => 0

/-- Margin in pixels around the page inside the canvas (each side). -/
def margin : Nat := 8

/-- The zoom (pixels per page unit) that fits a page box `pw × ph` (in page units, after
rotation) into a `cw × ch` canvas less `margin` on every side, rounded down to a multiple of
1/64 (small denominators keep the renderer's rational arithmetic cheap) and kept in
`[1/16, 8]`. A degenerate box gets zoom 1. -/
def fitZoom (cw ch : Nat) (pw ph : Rat) : Rat :=
  if pw ≤ 0 || ph ≤ 0 then 1
  else
    let aw : Rat := ((cw - 2 * margin : Nat) : Rat)
    let ah : Rat := ((ch - 2 * margin : Nat) : Rat)
    let z := min (aw / pw) (ah / ph)
    let q : Rat := ((z * 64).floor : Rat) / 64
    max (1 / 16) (min 8 q)

#guard fitZoom 1000 1000 0 100 = 1
#guard fitZoom 100 100 10000 10000 = 1 / 16
#guard fitZoom 2000 2000 100 100 = 8
#guard fitZoom 216 216 100 200 = 1

/-- The zoom that fits page `p` of `doc` into the canvas of `s`. -/
def pageZoom (s : State) (doc : Doc) (p : Nat) : Rat :=
  match doc.pages[p]? with
  | some page =>
    let r := SafePdf.Core.Raster.Geom.rotAdd page.rotate .r0
    let bx := SafePdf.Core.Raster.Geom.Box.ofRect page.cropBox
    let sz := SafePdf.Core.Raster.Geom.screenSize 1 r bx
    fitZoom s.canvasW s.canvasH sz.1 sz.2
  | none => 1

/-- Last path component of a file name (for the window title). -/
def baseName (path : String) : String :=
  (System.FilePath.mk path).fileName.getD path

/-- Window title: `safe-pdf`, or `NAME — page k/n — safe-pdf`. -/
def State.title (s : State) : String :=
  match s.path, s.doc with
  | some p, some _ => s!"{baseName p} - page {s.page + 1}/{s.pageCount} - safe-pdf"
  | some p, none => s!"{baseName p} - safe-pdf"
  | none, _ => "safe-pdf"

/-! ## Tcl -/

/-- Evaluates a command built from literal words (every word quoted by `Tcl.quote`). -/
def run (words : List String) : IO String :=
  Shim.eval (Tcl.Script.render ⟨[Tcl.cmd words]⟩)

/-- Shows `msg` in the status line. -/
def setStatus (msg : String) : IO Unit := do
  discard <| run [".status", "configure", "-text", msg]

/-- The constant UI setup script (no data in it). Widgets: toolbar `.bar` (Open…, Prev,
Next, page label `.bar.page`), canvas `.c` with the photo image `::safepdf::page` on item
tag `page`, status line `.status`. Key bindings on the toplevel's bind tag `.`; canvas resizes
are debounced and reported as `emit resize W H`. -/
def setupScript : String := "
namespace eval ::safepdf { variable resizeId {} }
wm title . safe-pdf
wm geometry . 820x1040
wm minsize . 240 200
ttk::frame .bar
ttk::button .bar.open -text {Open...} -command {::safepdf::emit open}
ttk::button .bar.prev -text {< Prev} -command {::safepdf::emit prev}
ttk::button .bar.next -text {Next >} -command {::safepdf::emit next}
ttk::label .bar.page -text {} -anchor w
pack .bar.open .bar.prev .bar.next -side left -padx 2 -pady 2
pack .bar.page -side left -padx 8
canvas .c -background gray60 -highlightthickness 0 -takefocus 1
image create photo ::safepdf::page
.c create image 8 8 -anchor nw -image ::safepdf::page -tags page
ttk::label .status -text {} -anchor w -relief sunken -padding {4 2}
pack .bar -side top -fill x
pack .status -side bottom -fill x
pack .c -side top -fill both -expand 1
foreach k {Next Right Down space} { bind . <Key-$k> {::safepdf::emit next} }
foreach k {Prior Left Up BackSpace} { bind . <Key-$k> {::safepdf::emit prev} }
bind . <Key-Home> {::safepdf::emit first}
bind . <Key-End> {::safepdf::emit last}
bind . <Control-o> {::safepdf::emit open}
bind . <Control-q> {destroy .}
bind .c <Configure> {
  after cancel $::safepdf::resizeId
  set ::safepdf::resizeId [after 100 {::safepdf::emit resize [winfo width .c] [winfo height .c]}]
}
focus .c
"

/-! ## Rendering -/

/-- Renders page `p` of `doc` at `zoom` with a fresh budget (the inspector's `raster` view
does the same). -/
def renderPage (doc : Doc) (p : Nat) (zoom : Rat) : IO (Except Error Clip.Image) := do
  match doc.pages[p]? with
  | some page =>
    IO.lazyPure fun _ =>
      (SafePdf.Core.Raster.Glyph.renderDocPage limits doc page zoom .r0
        (SafePdf.Core.Filter.Budget.init limits)).1
  | none => return .error (.malformed 0 "page index out of range")

/-- Updates title, page label and (when page, document or zoom changed) the page image. -/
def refresh (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  discard <| run ["wm", "title", ".", s.title]
  match s.path, s.doc with
  | some path, some doc =>
    discard <| run [".bar.page", "configure", "-text", s!"page {s.page + 1} of {s.pageCount}"]
    let zoom := pageZoom s doc s.page
    if s.shown == some (path, s.page, zoom) then return
    st.modify ({ · with shown := some (path, s.page, zoom) })
    let t0 ← IO.monoNanosNow
    match ← renderPage doc s.page zoom with
    | .ok img =>
      let t1 ← IO.monoNanosNow
      Shim.photoPut photoName img.w.toUInt32 img.h.toUInt32 img.data
      -- Centre the page horizontally when it is narrower than the canvas.
      let x := max margin ((s.canvasW - img.w) / 2)
      discard <| run [".c", "coords", "page", toString x, toString margin]
      setStatus s!"{path}: page {s.page + 1}/{s.pageCount}, {img.w}x{img.h} px, \
        rendered in {formatMs (t1 - t0)} ms"
    | .error e =>
      discard <| run [photoName, "blank"]
      setStatus s!"{path}: page {s.page + 1}: cannot render: {renderError e}"
  | _, _ =>
    discard <| run [".bar.page", "configure", "-text", ""]
    discard <| run [photoName, "blank"]

/-- Opens `path`: reads and parses it, builds the page tree, shows page 1. Every failure
ends up in the status line with an empty page. -/
def openFile (st : IO.Ref State) (path : String) : IO Unit := do
  st.modify ({ · with path := some path, doc := none, page := 0, shown := none })
  match ← Inspect.load {} path with
  | .error msg =>
    discard <| run [photoName, "blank"]
    refresh st
    setStatus s!"{path}: cannot read: {msg}"
  | .ok input =>
    match Views.Pages.docOf limits input.result with
    | .error e =>
      discard <| run [photoName, "blank"]
      refresh st
      setStatus s!"{path}: cannot open: {renderError e}"
    | .ok doc =>
      st.modify ({ · with doc := some doc })
      if doc.pages.size == 0 then
        refresh st
        setStatus s!"{path}: the document has no pages"
      else refresh st

/-- Moves to page `p` (clamped to the document) and refreshes. -/
def goTo (st : IO.Ref State) (p : Nat) : IO Unit := do
  let s ← st.get
  if s.pageCount == 0 then return
  let p := min p (s.pageCount - 1)
  if p != s.page then
    st.modify ({ · with page := p })
    refresh st

/-- The `tk_getOpenFile` dialog; opens the chosen file (nothing when cancelled). -/
def openDialog (st : IO.Ref State) : IO Unit := do
  let path ← run ["tk_getOpenFile", "-parent", ".", "-title", "Open PDF", "-filetypes",
    "{{PDF files} {.pdf .PDF}} {{All files} *}"]
  if !path.isEmpty then openFile st path

/-! ## Smoke mode -/

/-- One step of the smoke test (see the module doc). -/
def smoke (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some dir := s.smokeDir | return
  st.modify ({ · with smokeStep := s.smokeStep + 1 })
  -- Writing an empty photo fails in Tk; that only means there is nothing to write.
  let write (name : String) : IO Unit :=
    try discard <| run [photoName, "write", ((dir : System.FilePath) / name).toString,
      "-format", "ppm"]
    catch _ => pure ()
  match s.smokeStep with
  | 0 =>
    write "page-1.ppm"
    if s.pageCount ≥ 2 then
      try
        discard <| run ["focus", "-force", ".c"]
        discard <| run ["event", "generate", ".c", "<Key-Next>"]
      catch _ => pure ()
    discard <| run ["after", "200", "::safepdf::emit smoke"]
  | _ =>
    if s.pageCount ≥ 2 then write "page-2.ppm"
    let title ← run ["wm", "title", "."]
    let status ← run [".status", "cget", "-text"]
    IO.FS.writeFile ((dir : System.FilePath) / "state.txt")
      s!"title: {title}\nstatus: {status}\npage: {(← st.get).page + 1}/{s.pageCount}\n"
    discard <| run ["destroy", "."]

/-! ## Events -/

/-- Handles one `::safepdf::emit` call. -/
def handle (st : IO.Ref State) (args : Array String) : IO Unit := do
  let s ← st.get
  match args.toList with
  | ["next"] => goTo st (s.page + 1)
  | ["prev"] => goTo st (s.page - 1)
  | ["first"] => goTo st 0
  | ["last"] => goTo st (s.pageCount - 1)
  | ["open"] => openDialog st
  | ["smoke"] => smoke st
  | ["resize", w, h] =>
    match w.toNat?, h.toNat? with
    | some w, some h =>
      if w ≥ 2 && h ≥ 2 && (w, h) != (s.canvasW, s.canvasH) then
        st.modify ({ · with canvasW := w, canvasH := h })
        refresh st
    | _, _ => pure ()
  | _ => setStatus s!"internal: unknown event {args}"

/-- Runs `act`, showing an exception in the status line instead of letting it escape into
Tk (stderr when even the status line fails). -/
def guarded (act : IO Unit) : IO Unit := do
  try act
  catch e =>
    try setStatus s!"error: {e}" catch _ => IO.eprintln s!"viewer: {e}"

/-- `handle`, with every exception shown in the status line instead of escaping into Tk. -/
def safeHandle (st : IO.Ref State) (args : Array String) : IO Unit :=
  guarded (handle st args)

/-- Usage text. -/
def usage : String :=
  "usage: viewer [FILE.pdf]
Opens FILE (or asks for one) in a window. Keys: Next/Right/Down/space next page,
Prior/Left/Up/BackSpace previous page, Home/End first/last, Ctrl+O open, Ctrl+Q quit.
SAFEPDF_VIEWER_SMOKE=DIR: render, write DIR/page-1.ppm (and page-2.ppm), DIR/state.txt, exit."

/-- Runs the viewer. Exit codes: 0 after the window closes; 2 usage error; 3 Tk failed to
start (no display, missing Tk). -/
def main (args : List String) : IO UInt32 := do
  let file ← match args with
    | [] => pure none
    | ["--help"] | ["-h"] => IO.println usage; return 0
    | [f] => pure (some f)
    | _ => IO.eprintln usage; return 2
  try Shim.init
  catch e =>
    IO.eprintln s!"viewer: cannot start Tk: {e}"
    return 3
  let smokeDir ← IO.getEnv "SAFEPDF_VIEWER_SMOKE"
  let st ← IO.mkRef ({ smokeDir } : State)
  Shim.setEmitHandler (safeHandle st)
  try
    discard <| Shim.eval setupScript
    -- Lay the window out so that the first render uses the real canvas size.
    discard <| Shim.eval "update"
    let w ← Shim.eval "winfo width .c"
    let h ← Shim.eval "winfo height .c"
    if let (some w, some h) := (w.toNat?, h.toNat?) then
      if w ≥ 2 && h ≥ 2 then st.modify ({ · with canvasW := w, canvasH := h })
  catch e =>
    IO.eprintln s!"viewer: cannot build the window: {e}"
    return 3
  match file with
  | some f => guarded (openFile st f)
  | none =>
    setStatus "No file. Press Ctrl+O or Open... to choose a PDF."
    if smokeDir.isNone then discard <| run ["after", "idle", "::safepdf::emit open"]
  if smokeDir.isSome then discard <| run ["after", "300", "::safepdf::emit smoke"]
  Shim.mainLoop
  return 0

end SafePdf.Shell.App.Viewer
