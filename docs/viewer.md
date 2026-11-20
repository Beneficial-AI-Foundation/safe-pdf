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

## What it does (8.2a skeleton, 8.2b viewing)

* Window: toolbar (Open…, `< Prev`, `Next >`, `-`, `+`, `100%`, `Fit page`, `Fit width`,
  `Rotate left`, `Rotate right`, "page k of n", zoom %), a scrollable canvas (scroll bars)
  with the current page, a status line (file, page, zoom, rotation, pixel size, render time
  or "from cache", notes, or the error).
* Title: `NAME - page k/n - safe-pdf`.
* Pages are rendered by `Core.Raster.Glyph.renderDocPage` (fresh budget per page, CropBox and
  `/Rotate` honoured, the user rotation added with `rotAdd`).
* **Zoom** (`View.Mode`): fit page (default), fit width, or a fixed percentage of actual size,
  where 100 % = 72 dpi × the screen scale factor (`tk scaling`, pixels per point). Steps
  25, 33, 50, 67, 75, 100, 125, 150, 200, 300, 400, 600, 800 %. Effective zooms are multiples
  of 1/64 pixel per point. Zooming keeps a point fixed: the page point under the mouse
  (Ctrl+wheel) or at the window centre (keys, toolbar) is computed with `Geom.toPage` before
  the change and put back under the same window position with `Geom.toScreen` after it
  (C2; `View.reanchor`). Window resizes re-render in the fit modes (debounced 100 ms).
* **Huge zooms are bounded**: a page image above `View.maxViewPixels` (2²⁶ px = 256 MiB RGBA)
  gets a smaller zoom ("zoom limited" in the status line); a side above `Limits.maxPageSide`
  (16384) is cropped by the renderer ("cropped" in the status line).
* **Rotation**: view rotation in 90° steps, combined with each page's `/Rotate`; the window
  centre's page point stays at the centre.
* **Scrolling** is page-at-a-time: the canvas holds one page image. Scrolling past the bottom
  (or right) edge with the keys moves to the top of the next page; past the top, to the bottom
  of the previous page. The mouse wheel only scrolls within the page.
* **Page cache** (`View.Cache`): render results keyed by (document, page, zoom, rotation), LRU,
  at most `View.cacheBytes` = 256 MiB of images and `View.cacheEntries` = 64 entries; results
  above half the budget are not cached. 100 ms after a page is shown, the next page is
  rendered into the cache when it is at most `Viewer.prefetchPixels` (2²² px); no threads.
* Errors never crash the viewer: unreadable files, parse errors (e.g. a `/Kids` cycle), render
  errors and Tcl errors go to the status line.

### Keys

| Key | Action |
|---|---|
| `Next` (PageDown), `space` | scroll down a window; at the bottom: next page (top) |
| `Prior` (PageUp), `BackSpace`, `Shift+space` | scroll up a window; at the top: previous page (bottom) |
| `Down` / `Up` | scroll a tenth of the window; past the edge: next / previous page |
| `Right` / `Left` | scroll horizontally; past the edge: next / previous page (top) |
| `Home` / `End` | first / last page |
| `+` (`=`, keypad `+`, also with Ctrl) | zoom in one step (about the window centre) |
| `-` (keypad `-`, also with Ctrl) | zoom out one step |
| `0`, `Ctrl+0` | actual size (100 %) |
| `f` / `w` | fit page / fit width |
| `r` / `R` | rotate the view 90° clockwise / counter-clockwise |
| mouse wheel, `Shift`+wheel | scroll vertically / horizontally |
| `Ctrl`+wheel | zoom in/out about the mouse pointer |
| `Ctrl+O` / `Ctrl+Q` | open / quit |

Later tasks: 8.2c selection/copy/search, 8.2d outline/links/page labels; continuous scrolling
(several pages on one canvas) is optional and not done.

## Structure

| File | Role |
|---|---|
| `c/tk_shim.c` | Tcl interpreter, Tk init, `::safepdf::emit` → Lean callback, `Tk_PhotoPutBlock` from an RGBA `ByteArray`, event loop. Adapted from bib-lean's `c/tk_shim.c`. |
| `SafePdf/Shell/App/Shim.lean` | `@[extern]` bindings and the exported dispatcher `safepdf_gui_dispatch`. Only the `viewer` executable may import it. |
| `SafePdf/Shell/App/Tcl.lean`, `TclLemmas.lean` | Tcl scripts as data and the proof that `Tcl.quote` is injection-free (`parseWordStr_quote`, `parseScript_render`, …). Copied from bib-lean `BibLean/Gui/Tcl.lean` + `Tcl/Lemmas.lean`. Built by default (lib `SafePdfApp`). |
| `SafePdf/Shell/App/View.lean` | Tk-free viewing logic with `#guard` checks: zoom modes/steps/cap, C2 re-anchoring (`reanchor`, `reanchor_self`), Tcl number parsing, the LRU page cache. |
| `SafePdf/Shell/App/Viewer.lean` | State, rendering, scrolling/zoom/rotation handlers, prefetch, smoke mode. |
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
server answers, else `xvfb-run -a`). In smoke mode the viewer drives itself with Tk key
events (`event generate`) and writes photos and state files (`Viewer.smoke`): `page-1.ppm`,
`Next`, `page-2.ppm` + `state.txt` (title, status, page), `Home` `0` → `zoom-100.ppm`, `+` →
`zoom-in.ppm`, `-` `-` → `zoom-out.ppm`, `r` → `rot.ppm`, then `R` and `+`×4 (200 %) and a
scroll sequence recorded in `view.txt`. The script checks, on a generated two-page vector PDF
(`scripts/viewer-smoke-pdf.py`): page 1 ≥ 10% non-white pixels, page 2 drawn and landscape
(`/Rotate 90`), the key event reached page 2 and page 2 came from the prefetch cache, the
title; zoom in/out give 125 %/75 % of the 100 % size with ink (non-white pixels) scaling by the
area; rotation swaps the sides with the same ink; at 200 % the window centre shows the page
centre (C2 anchoring, both axes within 1 %); `Down` and `Next` scroll within page 1, repeated
`Next` reaches the top of page 2, `Prior` there the bottom of page 1; the odd file name above;
and that a non-PDF, `Tests/adversarial/pages-kids-cycle.pdf` and a missing file each end
normally with the error in the status line.

CI: the workflow cannot be pushed from the sandbox; the job that installs `tk-dev`/`xvfb`,
builds `viewer` and runs the smoke test is in `docs/ci-viewer-step.patch` (it also points the
cache keys at `lakefile.lean`).
