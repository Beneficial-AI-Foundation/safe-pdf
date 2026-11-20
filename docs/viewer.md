# The native viewer (`viewer`)

Task 8.2a (Plan.md §6 Phase 8, §8 native app, §10 `SafePdf/Shell/`; toolkit decision in the
ledger's Decisions, 8.1: Tcl/Tk through a small C shim). The shell is unverified and
replaceable; everything it shows comes from the verified core.

## Build and run

    lake build viewer                 # needs Tcl/Tk development files (pkg-config tk)
    .lake/build/bin/viewer FILE.pdf   # or `lake exe viewer FILE.pdf`
    .lake/build/bin/viewer            # asks for a file (tk_getOpenFile)

Dependencies: Debian/Ubuntu `tk-dev` (Tk 8.6 or 9.0; the lean-tools sandbox has Debian's Tk
9.0), macOS `brew install tcl-tk` (the lakefile adds Homebrew's keg `pkgconfig` directories
to `PKG_CONFIG_PATH`). The Tk link flags are computed when Lake elaborates `lakefile.lean`;
after installing or moving Tk run `lake -R build viewer` once to reconfigure.

`viewer` is **not** a default target: `lake build`, `lake build tests fuzz` and `lake exe tests`
never compile the shim or link Tk (the shim is a custom `target` attached only to the
`viewer` executable, not an `extern_lib`, which Lake would link into every executable).

## What it does today (8.2a skeleton)

* Window: toolbar (Open…, `< Prev`, `Next >`, "page k of n"), a canvas with the current page,
  a status line (file, page, pixel size, render time, or the error).
* Title: `NAME - page k/n - safe-pdf`.
* Pages are rendered by `Core.Raster.Glyph.renderDocPage` (fresh budget per page, user
  rotation 0, CropBox and `/Rotate` honoured) at the zoom that fits the page into the canvas
  (`Viewer.fitZoom`, multiples of 1/64 in [1/16, 8]); window resizes re-render (debounced
  100 ms).
* Keys: `Next`/`Right`/`Down`/`space` next page; `Prior`/`Left`/`Up`/`BackSpace` previous;
  `Home`/`End` first/last; `Ctrl+O` open; `Ctrl+Q` quit.
* Errors never crash the viewer: unreadable files, parse errors (e.g. a `/Kids` cycle), render
  errors and Tcl errors go to the status line.

Later tasks: 8.2b scrolling/zoom/rotation/page cache, 8.2c selection/copy/search, 8.2d
outline/links/page labels.

## Structure

| File | Role |
|---|---|
| `c/tk_shim.c` | Tcl interpreter, Tk init, `::safepdf::emit` → Lean callback, `Tk_PhotoPutBlock` from an RGBA `ByteArray`, event loop. Adapted from bib-lean's `c/tk_shim.c`. |
| `SafePdf/Shell/App/Shim.lean` | `@[extern]` bindings and the exported dispatcher `safepdf_gui_dispatch`. Only the `viewer` executable may import it. |
| `SafePdf/Shell/App/Tcl.lean`, `TclLemmas.lean` | Tcl scripts as data and the proof that `Tcl.quote` is injection-free (`parseWordStr_quote`, `parseScript_render`, …). Copied from bib-lean `BibLean/Gui/Tcl.lean` + `Tcl/Lemmas.lean`. Built by default (lib `SafePdfApp`). |
| `SafePdf/Shell/App/Viewer.lean` | State, rendering, event handlers, smoke mode. |
| `SafePdf/Shell/App/Main.lean` | `main` of the `viewer` executable. |

**No data in script text.** Every Tcl command that carries data (file names, error text,
numbers) is a `Tcl.cmd` of literal words rendered through the proved `Tcl.quote`; pixels go
through `Tk_PhotoPutBlock`; event arguments come back as separate words. The only raw script
is the constant UI setup (`Viewer.setupScript`). The smoke test opens a file named
`odd [exit 7] $HOME {x" \.pdf` and checks that the title shows it verbatim.

**Threads.** The shim's interpreter is used only from the thread running Lean's `main`. On
macOS (Cocoa must run on the main thread) the shim sets `LEAN_MAIN_USE_THREAD=0` from a
constructor, as bib-lean does; on Linux Lean's `main` keeps its large-stack thread.

**Linux linking.** Lean links with its own clang/ld.lld and sysroot; the lakefile appends the
system library directories as `-Wl,-L…` (searched after the toolchain's) plus
`-Wl,--allow-shlib-undefined` so the system Tk links (pattern from bib-lean's lakefile).

## Smoke test

    scripts/viewer-smoke.sh [--no-build]

Builds `viewer`, then runs it with `SAFEPDF_VIEWER_SMOKE=DIR` (uses `$DISPLAY` when an X
server answers, else `xvfb-run -a`). In smoke mode the viewer writes the page photo to
`DIR/page-1.ppm`, sends itself a `Next` key event through Tk, writes `DIR/page-2.ppm` and
`DIR/state.txt` (title, status, page) and exits. The script checks, on a generated two-page
vector PDF (`scripts/viewer-smoke-pdf.py`): page 1 ≥ 10% non-white pixels, page 2 drawn and
landscape (`/Rotate 90`), the key event reached page 2, the title; the odd file name above;
and that a non-PDF, `Tests/adversarial/pages-kids-cycle.pdf` and a missing file each end
normally with the error in the status line.

CI: the workflow cannot be pushed from the sandbox; the job that installs `tk-dev`/`xvfb`,
builds `viewer` and runs the smoke test is in `docs/ci-viewer-step.patch` (it also points the
cache keys at `lakefile.lean`).
