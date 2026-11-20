import SafePdf.Shell.App.Viewer
import SafePdf.Shell.App.BibLean.Launch
import SafePdf.Shell.App.BibLean.Annots

/-!
# Entry point of the `viewer` executable (tasks 8.2a, 10.1, 10.2, 10.3; Plan.md §6 Phases 8 and 10, §8, §10)

The native viewer shell (unverified). See `SafePdf.Shell.App.Viewer` and `docs/viewer.md`.

`viewer --biblean [--page N] [--probe [--annots echo|demo]]` is bib-lean's reader mode (Plan.md §6 Phase 10,
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
* Otherwise the window. **Interim** until `Viewer.lean` has an entry point taking bytes (task
  10.1 report): the bytes go into a private temporary directory (`IO.FS.createTempDir`, mode
  0700; the file made 0600 before it is written), named after the title (`fileNameOf`, so
  the window title shows it), opened with `Viewer.main`, and the directory is removed when
  the window closes (contract §2: only private temporary files that are removed). The
  requested page is not applied yet on this path.

  Annotations (task 10.2, `BibLean.Annots`): until the viewer calls the sync's hooks (task
  10.1b), the window path only handles a Save: when the window wrote
  `Save.defaultTarget` of the private copy, that file is sent with `PUT` and its marks,
  merged with the stored set, are posted (`Annots.afterWindow`, at most `annotsGraceMs`).
  With `--probe`, the stored set is loaded and summarised (`annotations:` line);
  `--annots echo` posts it back unchanged, `--annots demo` runs `annotsDemo`; the outcomes are
  printed as `sync:` lines and `sync-done:` tells whether everything was sent in time.

  The text posts (task 10.3) run on a **dedicated thread** (`IO.asTask (prio := .dedicated)`)
  started before the window, so the window never waits for them. When the window closes,
  they get at most `textGraceMs` more to finish, then the task is cancelled (it stops at the
  next page); if it is still inside a post, the process exits without waiting for it (after
  the temporary directory is removed). A failed post only prints its outcome on stderr
  (status or connection error, nothing from the library).
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

/-- Parses the arguments after `--biblean`. -/
def parseBibleanArgs : List String → BibleanArgs → Option BibleanArgs
  | [], a => some a
  | "--probe" :: rest, a => parseBibleanArgs rest { a with probe := true }
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

/-- The probe's scripted annotation session (`--annots demo`, task 10.2), standing in for the
viewer's hooks until 10.1b: a highlight over the first word of page 1, recoloured three times
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

/-- `viewer --biblean …` (see the module documentation). -/
def bibleanMain (args : List String) : IO UInt32 := do
  let some a := parseBibleanArgs args {}
    | IO.eprintln "usage: viewer --biblean [--page N] [--probe [--annots echo|demo]]   (token: one line on fd 3)"
      return 2
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
    let dir ← IO.FS.createTempDir
    let code ← try
      let p := dir / BibLean.Launch.fileNameOf o.session.key o.title
      IO.FS.writeFile p ""
      IO.setAccessRights p { user := { read := true, write := true } }
      IO.FS.writeBinFile p o.bytes
      let code ← Viewer.main [p.toString]
      -- Interim (task 10.1b adds the viewer hooks): a Save in the window wrote
      -- `Save.defaultTarget p`; it goes to bib-lean as the new file and its marks as the set.
      let target : System.FilePath := Save.defaultTarget p.toString
      try
        let r ← BibLean.Annots.afterWindow sync target annotsGraceMs
        unless r == "sent" || r == "nothing saved" do
          IO.eprintln s!"viewer --biblean: annotations: {r}"
      catch e => IO.eprintln s!"viewer --biblean: annotations: {e}"
      pure code
    finally
      try IO.FS.removeDirAll dir catch _ => pure ()
    -- A request stuck in a server that never answers must not hold the process.
    if (← sync.state.get).running then
      IO.Process.exit (if code > 255 then 1 else code.toUInt8)
    let grace ← IO.asTask (IO.sleep textGraceMs)
    let _ ← IO.waitAny [text, grace]
    IO.cancel text
    unless ← IO.hasFinished text do
      IO.Process.exit (if code > 255 then 1 else code.toUInt8)
    return code

/-- Entry point of the `viewer` executable. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "--biblean" :: rest => bibleanMain rest
  | _ => Viewer.main args
