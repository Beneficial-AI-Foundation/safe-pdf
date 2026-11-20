import SafePdf.Shell.App.Viewer
import SafePdf.Shell.App.BibLean.Launch
import SafePdf.Shell.App.BibLean.Annots
import SafePdf.Shell.App.BibLean.SelfTest

/-!
# Entry point of the `viewer` executable (tasks 8.2a, 10.1, 10.1b, 10.2, 10.3, 10.4; Plan.md §6 Phases 8 and 10, §8, §10)

The native viewer shell (unverified). See `SafePdf.Shell.App.Viewer` and `docs/viewer.md`.

`viewer --biblean [--page N] [--probe [--annots echo|demo] | --self-test]` is bib-lean's reader mode (Plan.md §6 Phase 10,
`bib-lean/docs/READER-CONTRACT.md`): `BibLean.Launch.openFromBibLean` reads the token from
file descriptor 3 and `BIBLEAN_SERVER` / `BIBLEAN_ATTACHMENT` / `BIBLEAN_PAGE` from the
environment and fetches the PDF and its title over loopback HTTP. Exit codes (contract §5):
0 the window closed (or the probe finished), 1 the server refused or the file did not open,
2 usage error, 3 no valid token on file descriptor 3.

* `--probe`: headless; prints `key`, `title`, `pages`, `requested`, `page`, `bytes` (one
  `name: value` line each, never the token), then runs `BibLean.Launch.afterOpen` (task 10.3:
  identifiers on pages 1–2 to `/detected`, the full text to `/fulltext`) and prints `doi`,
  `arxiv` (every distinct one found, with its one-based page), `detected`, `fulltext` (the
  outcomes) and exits 0 — also when those posts fail: they are optional (contract §3) and
  never make a launch fail. Used by `Tests/biblean/launch-test.sh` and `text-test.sh`.
* `--self-test` (task 10.4, `BibLean.SelfTest.run`): headless; the contract's sequence (GET
  the file, POST two annotations, POST a detection, PUT the re-saved file), one
  `name: value` line per step and the verdict `viewer self-test: ok|FAILED (…)`; exit 0 when
  every step passed, 1 otherwise (2 usage, 3 no token, as above). Not combinable with
  `--probe`. Used by `scripts/biblean-contract.sh` and `Tests/biblean/selftest-test.sh`.
* Otherwise the window (task 10.1b, `windowInit`): the document is opened **from memory**
  (`Viewer.openBytes`; nothing is written to disk), titled with the library's title, at the
  requested page. Annotations (task 10.2, `BibLean.Annots.Sync`, attached as
  `Viewer.Library`): the stored set is merged into the marks read back from the file
  (`Sync.load`); every change of the marks is posted (debounced); Save (labelled "Save to
  library") sends `Save.build`'s bytes with `PUT` instead of writing a file, then the marks;
  Save As… still writes a local copy. When the window closes, `Sync.flush` gets at most
  `annotsGraceMs`; when something is still pending the process exits at once
  (`IO.Process.exit`). With `--probe`, the stored set is loaded and summarised (`annotations:`
  line); `--annots echo` posts it back unchanged, `--annots demo` runs `annotsDemo`; the
  outcomes are printed as `sync:` lines and `sync-done:` tells whether everything was sent in
  time.

  File descriptor 3 is closed right after the token was read (`Launch.closeTokenFd`, set to
  `Shim.closeFd3` here; every path).

  The text posts (task 10.3) run on a **dedicated thread** (`IO.asTask (prio := .dedicated)`)
  started before the window, so the window never waits for them. When the window closes,
  they get at most `textGraceMs` more to finish, then the task is cancelled (it stops at the
  next page); if it is still inside a post, the process exits without waiting for it (after
  the annotations were flushed). A failed post only prints its outcome on stderr
  (status or connection error, nothing from the library).

  The window run always ends with `exitNow` (task 8.9): once the annotations were flushed (or
  their grace expired) and the text posts had theirs, the process exits through
  `IO.Process.exit` with the window's code, so a page render still running on a worker thread
  (task 8.8) never holds it.
-/

open SafePdf.Shell.App

/-- Arguments of `viewer --biblean`. -/
structure BibleanArgs where
  /-- `--probe`: no window. -/
  probe : Bool := false
  /-- `--page N` / `--page=N` (the contract's `{page}`), used when `BIBLEAN_PAGE` is absent. -/
  page : Option Nat := none
  /-- `--annots echo|demo` (with `--probe`, task 10.2): post the loaded set back unchanged, or
  run the scripted change/save sequence `annotsDemo`. -/
  annots : Option String := none
  /-- `--self-test` (task 10.4): the contract's sequence without a window. -/
  selfTest : Bool := false

/-- Parses the arguments after `--biblean`. -/
def parseBibleanArgs : List String → BibleanArgs → Option BibleanArgs
  | [], a => some a
  | "--probe" :: rest, a => parseBibleanArgs rest { a with probe := true }
  | "--self-test" :: rest, a => parseBibleanArgs rest { a with selfTest := true }
  | "--annots" :: m :: rest, a =>
    if m == "echo" || m == "demo" then parseBibleanArgs rest { a with annots := some m } else none
  | "--page" :: n :: rest, a =>
    (BibLean.Launch.pageOf? (some n)).bind fun p => parseBibleanArgs rest { a with page := some p }
  | w :: rest, a =>
    if w.startsWith "--page=" then
      (BibLean.Launch.pageOf? (some (w.drop 7).toString)).bind fun p =>
        parseBibleanArgs rest { a with page := some p }
    else none

/-- How long the text posts may still run after the window closed: three seconds. -/
def textGraceMs : UInt32 := 3000

/-- How long annotation requests may still run when the viewer exits: three seconds in the
window, five in the probe. -/
def annotsGraceMs : Nat := 3000

/-- The probe's scripted annotation session (`--annots demo`, task 10.2; the window calls the
same hooks since 10.1b): a highlight over the first word of page 1, recoloured three times
30 ms apart (each change reported with `onMarksChanged`, so the debounce must fold them into
one post), a note near the CropBox's upper-left corner, then Save (`Save.build`'s bytes go to
`onSaved`, i.e. the `PUT`; the marks become saved, which changes nothing in the posted set).
Returns a line for the probe output. -/
def annotsDemo (y : BibLean.Annots.Sync) (s : Marks.Store) : IO String := do
  let pi ← y.pageInfo 0
  if pi.cells.isEmpty then return "no text on page 1"
  let (a, b) := Select.wordAt pi.cells 0
  let some (s1, hid) := s.addHighlight 0 .yellow (Select.rangeBoxes pi.cells a b)
    | return "no quads on page 1"
  let mut s := s1
  y.onMarksChanged s
  for c in [Marks.Color.green, .blue, .pink] do
    IO.sleep 30
    s := s.recolor hid c
    y.onMarksChanged s
  s := (s.addNote 0 .yellow "demo note" (.point ⟨pi.box.llx + 20, pi.box.ury - 20⟩)).1
  y.onMarksChanged s
  let d := y.document
  match Save.build d.limits d.doc s (← Save.nowDate) with
  | .error e => return s!"save failed: {e}"
  | .ok (bytes, _) =>
    y.onSaved bytes
    y.onMarksChanged { s with saved := (s.marks.map (·.id)).toList }
    return s!"highlight {hid} on {(Select.rangeText pi.cells a b).length} characters, a note, \
      saved {bytes.size} bytes"

/-- The window's start in bib-lean's reader mode (task 10.1b): the document is opened from
memory (`Viewer.openBytes`, named `Launch.fileNameOf` for Save As…'s proposal, titled with
the library's title), the library's annotation sync attached as `Viewer.Library` (Save goes to
the library, every change of the marks is reported), the stored set merged into the marks read
back from the file (`Sync.load`) and the requested page shown. -/
def windowInit (o : BibLean.Launch.Opened) (sync : BibLean.Annots.Sync)
    (st : IO.Ref Viewer.State) : IO Unit := do
  st.modify ({ · with titleOverride := some o.title,
                      library := some { onMarksChanged := sync.onMarksChanged,
                                        onSaved := sync.onSaved,
                                        flush := sync.flush annotsGraceMs } })
  Viewer.setSaveLabels true
  Viewer.openBytes st (BibLean.Launch.fileNameOf o.session.key o.title) o.bytes
  let s ← st.get
  if s.doc.isNone then return
  -- `s.marks` is the file's store (`Store.load (Save.readMarks …)`, read by `openBytes`).
  let marks ← sync.load s.marks
  st.modify ({ · with marks })
  if marks.marks.size != s.marks.marks.size then
    Viewer.repaint st
    Viewer.setStatus s!"{marks.marks.size - s.marks.marks.size} mark(s) loaded from the library"
  if let some p := o.page then Viewer.goTo st p

/-- Ends the window run of `viewer --biblean` (task 8.9): flushes stdout and stderr, then exits
the process with `code` (0 after the window closed; anything above 255 becomes 1) through
`IO.Process.exit`. Returning from `main` instead would make the Lean runtime wait for every
dedicated task — a page render still running on a worker thread (task 8.8) cannot be
interrupted and could hold the process for seconds after the window closed. Called only after
`Sync.flush` returned (everything sent, or its grace expired) and the text posts finished or
had their grace; nothing else needs to run: the document lives in memory (no temporary file)
and the token pipe is already closed. -/
def exitNow {α : Type} (code : UInt32) : IO α := do
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()
  IO.Process.exit (if code > 255 then 1 else code.toUInt8)

/-- `viewer --biblean …` (see the module documentation). -/
def bibleanMain (args : List String) : IO UInt32 := do
  -- Contract §2: close the token pipe (fd 3) once the token is read (task 10.1b).
  BibLean.Launch.closeTokenFd.set Shim.closeFd3
  let usage := "usage: viewer --biblean [--page N] [--probe [--annots echo|demo] | --self-test]   \
    (token: one line on fd 3)"
  let some a := (parseBibleanArgs args {}).filter fun a => !(a.selfTest && (a.probe || a.annots.isSome))
    | IO.eprintln usage
      return 2
  if a.selfTest then return ← BibLean.SelfTest.run a.page
  match ← BibLean.Launch.openFromBibLean (argPage := a.page) with
  | .error f =>
    IO.eprintln s!"viewer --biblean: {f.message}"
    return f.exitCode
  | .ok o =>
    if a.probe then
      let fmt (o : Option Nat) : String := (o.map toString).getD "none"
      IO.println s!"key: {o.session.key}\ntitle: {o.title}\npages: {o.document.pageCount}\n\
        requested: {fmt o.requested}\npage: {fmt o.page}\nbytes: {o.bytes.size}"
      let r ← BibLean.Launch.afterOpen o
      IO.println s!"doi: {BibLean.Text.foundLine r.detection.dois}\n\
        arxiv: {BibLean.Text.foundLine r.detection.arxivs}\ndetected: {r.detected}\n\
        fulltext: {r.fulltext} ({r.fulltextPages} pages, {r.fulltextBytes} bytes)"
      let y ← BibLean.Annots.Sync.create o
      let fileStore := Marks.Store.load (Save.readMarks o.document.doc o.document.limits)
      let s ← y.load fileStore
      IO.println s!"annotations: {y.stored.size} stored, {s.marks.size} marks \
        ({fileStore.marks.size} from the file), {(← y.state.get).passthrough.size} kept as they are"
      match a.annots with
      | none => return 0
      | some m =>
        if m == "demo" then IO.println s!"demo: {← annotsDemo y s}"
        else y.onMarksChanged s
        let done ← y.flush (annotsGraceMs + 2000)
        for l in ← y.outcomes do IO.println s!"sync: {l}"
        IO.println s!"sync-done: {done}"
        -- A request stuck in a server that never answers must not hold the process.
        unless done do IO.Process.exit 0
        return 0
    let text ← IO.asTask (prio := .dedicated) do
      let r ← BibLean.Launch.afterOpen o
      unless r.ok do
        IO.eprintln s!"viewer --biblean: detected: {r.detected}; fulltext: {r.fulltext}"
    let sync ← BibLean.Annots.Sync.create o
    let code ← Viewer.mainWith [] (windowInit o sync)
    -- Close/quit: send what is pending; a server that never answers must not hold the process.
    if ← sync.flush annotsGraceMs then
      let grace ← IO.asTask (IO.sleep textGraceMs)
      let _ ← IO.waitAny [text, grace]
      IO.cancel text
    exitNow code

/-- Entry point of the `viewer` executable. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "--biblean" :: rest => bibleanMain rest
  | _ => Viewer.main args
