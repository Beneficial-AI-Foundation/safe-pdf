import SafePdf.Shell.App.Viewer
import SafePdf.Shell.App.BibLean.Launch

/-!
# Entry point of the `viewer` executable (tasks 8.2a, 10.1; Plan.md §6 Phases 8 and 10, §8, §10)

The native viewer shell (unverified). See `SafePdf.Shell.App.Viewer` and `docs/viewer.md`.

`viewer --biblean [--page N] [--probe]` is bib-lean's reader mode (Plan.md §6 Phase 10,
`bib-lean/docs/READER-CONTRACT.md`): `BibLean.Launch.openFromBibLean` reads the token from
file descriptor 3 and `BIBLEAN_SERVER` / `BIBLEAN_ATTACHMENT` / `BIBLEAN_PAGE` from the
environment and fetches the PDF and its title over loopback HTTP. Exit codes (contract §5):
0 the window closed (or the probe finished), 1 the server refused or the file did not open,
2 usage error, 3 no valid token on file descriptor 3.

* `--probe`: headless; prints `key`, `title`, `pages`, `requested`, `page`, `bytes` (one
  `name: value` line each, never the token) and exits 0. Used by `Tests/biblean/launch-test.sh`.
* Otherwise the window. **Interim** until `Viewer.lean` has an entry point taking bytes (task
  10.1 report): the bytes go into a private temporary directory (`IO.FS.createTempDir`, mode
  0700; the file made 0600 before it is written), named after the title (`fileNameOf`, so
  the window title shows it), opened with `Viewer.main`, and the directory is removed when
  the window closes (contract §2: only private temporary files that are removed). The
  requested page is not applied yet on this path.
-/

open SafePdf.Shell.App

/-- Arguments of `viewer --biblean`. -/
structure BibleanArgs where
  /-- `--probe`: no window. -/
  probe : Bool := false
  /-- `--page N` / `--page=N` (the contract's `{page}`), used when `BIBLEAN_PAGE` is absent. -/
  page : Option Nat := none

/-- Parses the arguments after `--biblean`. -/
def parseBibleanArgs : List String → BibleanArgs → Option BibleanArgs
  | [], a => some a
  | "--probe" :: rest, a => parseBibleanArgs rest { a with probe := true }
  | "--page" :: n :: rest, a =>
    (BibLean.Launch.pageOf? (some n)).bind fun p => parseBibleanArgs rest { a with page := some p }
  | w :: rest, a =>
    if w.startsWith "--page=" then
      (BibLean.Launch.pageOf? (some (w.drop 7).toString)).bind fun p =>
        parseBibleanArgs rest { a with page := some p }
    else none

/-- `viewer --biblean …` (see the module documentation). -/
def bibleanMain (args : List String) : IO UInt32 := do
  let some a := parseBibleanArgs args {}
    | IO.eprintln "usage: viewer --biblean [--page N] [--probe]   (token: one line on fd 3)"
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
      return 0
    let dir ← IO.FS.createTempDir
    try
      let p := dir / BibLean.Launch.fileNameOf o.session.key o.title
      IO.FS.writeFile p ""
      IO.setAccessRights p { user := { read := true, write := true } }
      IO.FS.writeBinFile p o.bytes
      Viewer.main [p.toString]
    finally
      try IO.FS.removeDirAll dir catch _ => pure ()

/-- Entry point of the `viewer` executable. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "--biblean" :: rest => bibleanMain rest
  | _ => Viewer.main args
