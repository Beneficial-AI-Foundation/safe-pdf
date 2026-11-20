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

## What it does (8.2a skeleton, 8.2b viewing, 8.2c selection and search, 8.2d navigation, 9.1 menubar, 9.2 wheel)

* Window: menubar (File, Edit, View, Go; see *Menubar* below), toolbar (Open…, Outline, Back, Forward, `< Prev`, `Next >`, Go to…, `-`, `+`, `100%`, `Fit page`, `Fit width`,
  `Rotate left`, `Rotate right`, "page k of n", zoom %), a scrollable canvas (scroll bars)
  with the current page, a status line (file, page, zoom, rotation, pixel size, render time
  or "from cache", notes, or the error).
* Title: `NAME - page k/n - safe-pdf`, with page labels `NAME - page iii (3/120) - safe-pdf`.
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
  of the previous page. The mouse wheel does the same (9.2, below).
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
| mouse wheel | scroll vertically; past the edge: next page (top) / previous page (bottom) |
| `Shift`+wheel | scroll horizontally (stops at the edge) |
| `Ctrl`+wheel | zoom in/out about the mouse pointer |
| `Ctrl+O` / `Ctrl+W` / `Ctrl+Q` | open / close the document / quit |

## Menubar (9.1)

A native Tk menubar (`.menubar`, attached with `. configure -menu`; on X11 Tk draws it at the
top of the window, on macOS it is the system menu bar) duplicates the toolbar and the keys.
The model is Tk-free: `SafePdf/Shell/App/Menu.lean` lists the commands (`Menu.Cmd`: label,
accelerator text, the constant Tcl script that runs it, an enabled rule) and the menus; the
viewer builds the Tk menus from it (`Viewer.buildMenus`) and after every event sets the
`-state` of each entry and of the toolbar buttons Prev/Next/Back/Forward/Outline whose rule
changed (`Viewer.syncMenus`). Task 9.7 rebuilds the toolbar after PDF.js on the same commands.

| Menu | Entries (accelerator) |
|---|---|
| File | Open… (Ctrl+O), Close (Ctrl+W), Quit (Ctrl+Q) |
| Edit | Copy (Ctrl+C), Select all (Ctrl+A), Find… (Ctrl+F) |
| View | Outline (F9, a check entry showing whether the panel is open), Zoom in (`+`), Zoom out (`-`), Actual size (`0`), Fit page (`f`), Fit width (`w`), Rotate right (`r`), Rotate left (`R`) |
| Go | Previous page (PageUp), Next page (PageDown), First page (Home), Last page (End), Go to page… (Ctrl+G), Back (Alt+Left), Forward (Alt+Right) |

Disabled: everything but Open… and Quit without a document; Copy without a selection;
Outline when the document has none; Previous/First on the first page, Next/Last on the last;
Back/Forward with an empty history. The keys stay; a menu accelerator is only a label. The
Outline button stays on the toolbar (it becomes the PDF.js sidebar button in 9.7). *Close*
empties the window (as when started without a file).

## Wheel scrolling across pages (9.2)

The wheel continues into the next / previous page as the keys do. Pure logic in
`View.wheelStep` (`#guard` checks), driven by `::safepdf::emit wheel AXIS KIND D`:

* **Deltas.** `<MouseWheel>` `%D` is in 1/120 notches on Tk ≥ 8.7 (Tk 9 turns X11 wheel
  buttons into `<MouseWheel>`) and on Windows; `<Button-4>`/`<Button-5>` (Tk 8.6 on X11) are
  sent as ±120; Tk 8.6 on macOS gives lines (`KIND line`); Tk 9 trackpads (`<TouchpadScroll>`,
  unpacked with `tk::PreciseScrollDeltas`) give pixels. One notch scrolls a tenth of the view
  (as Tk's `scroll 1 units`); smaller deltas (high-resolution wheels, trackpads) accumulate
  their fractions (`View.Wheel.acc`) instead of being rounded to a notch or lost.
* **Edges.** Within the page the view scrolls and stops exactly at the edge (the rest of that
  event is dropped). Only further events at the edge push past it; when the push reaches one
  notch (a quarter of the view for trackpads) the page turns: down → top of the next page,
  up → bottom of the previous page. A tiny overscroll never turns a page; a pause of 400 ms or
  a change of direction forgets the push. A page that fits the window (fit page) turns with
  every notch.
* **Momentum.** After a trackpad turns the page, trackpad events are ignored until a 400 ms
  pause, so inertial scrolling does not run through several pages. Wheel notches are not
  latched.
* **Horizontal** (`Shift`+wheel, trackpad sideways): scrolls and stops at the edge; it never
  turns pages (the `Left`/`Right` keys still do).
* Not tested here: real macOS trackpad deltas (the smoke test generates Tk 9 `<MouseWheel>`
  and `<Button-4/5>` events on X11; the `line` and `pixel` kinds are covered by the `#guard`s
  only).

## Selection, copy and search (8.2c)

All text comes from the verified extraction: a page's text is extracted on first use
(`Annot.extractDocPageAnnots` with a fresh budget, the same pass and reading order as
`inspect --view text`) and cached for the open document as a `Select.PageIndex`: the glyphs
in reading order (`Text.layout` lines, `Text.lineOrder` within a line) with their page-space
boxes (C3: glyph origin, advance and size; 0.2 em below to 0.8 em above the baseline, in the
glyph's direction) and the separators the layout puts between them, so selecting the whole
page copies exactly the page text of the text view.

* **Drag** on the page: the press and the current mouse position are mapped to page space
  with `Geom.toPage`; the glyphs from the one nearest to the press to the one nearest to the
  pointer, in reading order, are selected (`Select.dragRange`). A click without moving clears
  the selection. **Double-click** selects a word (letters, digits, non-ASCII characters
  without a separator in between, `Select.wordAt`). **Ctrl+A** selects the page.
* The selection is drawn as canvas rectangles over the page image (one per line run,
  `Select.rangeBoxes`, mapped back with `Geom.toScreen`), stippled 50 % blue; the page is not
  re-rendered. On macOS (Aqua has no stipples) highlights are outlines instead.
* **Ctrl+C** (or the right-button menu: Copy, Select all, Find…) copies the selected text
  (`Select.rangeText`) with `clipboard clear; clipboard append -- TEXT`, the text one word
  quoted by `Tcl.quote`. The selection is per page and cleared when the page changes.
* **Search**: **Ctrl+F** opens a find bar under the toolbar (the entry does not carry the
  window's key bindings, so typing does not zoom or scroll). **Enter**/**F3** finds the next
  hit, **Shift+Enter**/**Shift+F3** the previous one, **Escape** closes the bar and removes
  the highlights. Matching is case-insensitive (ASCII and Latin-1 letters) on the page text
  with every whitespace run (spaces, line breaks) collapsed to one space
  (`Select.normChars`, `Select.normQuery`); a match maps back to the glyphs of its first and
  last character (`Select.hitRange`; `Select.findAll_sound` proves every reported position is
  a match). The search runs from the current hit through the current page, then the
  following (or preceding) pages, wrapping around; pages are extracted lazily as it goes.
  All hits of the shown page are highlighted in yellow, the current one in orange, and the
  current hit is scrolled into view. The status line says `"q": hit k/n on page p` (k of the
  n hits on that page, `(wrapped)` after wrapping around) or `"q": not found`.
* Not done: selection across pages, hits counted over the whole document (the count is per
  page, so that a search never has to extract every page first), full Unicode case folding.

| Key / mouse | Action |
|---|---|
| drag (button 1) | select text |
| double-click | select a word |
| `Ctrl+A` / `Ctrl+C` | select the page / copy |
| right button | menu: Copy, Select all, Find… |
| `Ctrl+F` | open the find bar |
| `Enter`, `F3` / `Shift+Enter`, `Shift+F3` | next / previous hit |
| `Escape` (in the find bar) | close the find bar |

## Outline, links, history, page labels (8.2d)

Pure logic in `SafePdf/Shell/App/Links.lean` (Tk-free, `#guard` checks and theorems); all
data comes from the verified navigation layer `Core.Doc.Nav` (task 4.2: visited sets cut
outline and name-tree cycles, every walk is bounded by the object count).

* **Outline panel**: a `ttk::treeview` in the left pane of a paned window (drag the sash to
  resize). It opens automatically when the document has an outline; **F9**, the *Outline*
  button or the right-button menu toggle it. Items come from `Nav.outline` (flat preorder list
  with depths; a depth more than one below the previous item is clamped so that every item has
  a parent), titles decoded as PDF text strings (`Links.textString`: UTF-16BE, UTF-8 or
  PDFDocEncoding; control and bidi-override characters become spaces; at most 500
  characters), items with a positive `/Count` start open. Clicking an item (not its
  expand arrow) or Enter on it activates its destination.
* **Destinations**: the page of an explicit destination (also reached through a named
  destination: catalog `/Dests` or the `/Names /Dests` tree, `Nav.resolveDest`) and, when
  the fit spec gives them, the left/top coordinates (`/XYZ`, `/FitH`, `/FitV`, `/FitR`,
  `/FitBH`, `/FitBV`): that page point is mapped with `Geom.toScreen` (C2) and scrolled to
  the window's top-left corner (a missing coordinate is the page's left or top edge). The
  viewer keeps its own zoom: the `/XYZ` zoom and the `/Fit*` zoom modes are not applied.
* **Links** (`Links.pageLinks`: the page's `/Annots` `/Link` annotations as `Nav.pageLinks`
  reads them, plus the `/URI` string of a URI action, which `Nav` does not keep). Moving the
  pointer over a link turns the cursor into a hand and shows the target in the status line:
  `go to page N` (with the label: `go to page iii (3/120)`), the full address of a URI, an
  unknown named destination, or another action type (`/Launch`, `/GoToR`, `/JavaScript`, …:
  `not followed`); leaving the link restores the status line. Overlapping links: the last
  one in `/Annots` order wins (it is painted on top). A **click** (press and release at the
  same point; a drag still selects text) on an internal link jumps.
* **URI links are never opened.** A click opens a modal *External link* dialog that shows the
  exact address in a read-only text widget (the address enters Tk as one `Tcl.quote`d word
  and is inserted by variable substitution, never evaluated) with *Copy address* and *Cancel*
  (default; Escape and closing the window cancel). Only *Copy address* puts it on the
  clipboard. No browser is launched in this task. The address is shown as `Links.uriText`:
  printable ASCII as written, every other byte (space, control characters, non-ASCII)
  percent-encoded (`%20`, `%E2%80%AE`), so nothing in it can be invisible or reorder the
  text (`Links.uriText_ascii` proves the result is printable ASCII; a URI is 7-bit ASCII by
  §12.6.4.8, so a conforming address is shown unchanged).
* **History**: every jump (link, outline item, Ctrl+G) records where the view was (page and
  scroll fractions) on a back stack and clears the forward stack, browser-style; **Alt+Left**
  / **Alt+Right** (and the *Back* / *Forward* buttons) move through it (at most 100 entries
  each way; `Links.History.back_push`: Back right after a jump returns to where it started,
  Forward then returns). Ordinary paging and scrolling are not recorded.
* **Page labels** (`Nav.labelTable`, one number-tree walk at open): the title, the toolbar
  and the status line say `page iii (3/120)`, or `page 3/120` when the label is the page
  number. **Ctrl+G** (or *Go to…*) opens a go-to bar: an exact label first, then a page
  number `1..n`, then a label ignoring ASCII case (`Links.gotoPage`); so with labels
  `i, ii, 1, 2` the input `1` goes to the third page. Unknown input leaves the bar open
  with an error in the status line; Escape closes it.

| Key / mouse | Action |
|---|---|
| `F9` | show / hide the outline panel |
| click on an outline item | go to its destination |
| pointer over a link | hand cursor, target in the status line |
| click on a link | internal: jump; URI: confirmation dialog (copy the address) |
| `Alt+Left` / `Alt+Right` | back / forward |
| `Ctrl+G` | go to a page label or number |

Not done: launching a browser (the address can only be copied), remote destinations
(`/GoToR`), the `/XYZ` zoom, link borders/highlighting (`/H`), keyboard focus traversal of
links. Continuous scrolling (several pages on one canvas) is optional and not done.

## Structure

| File | Role |
|---|---|
| `c/tk_shim.c` | Tcl interpreter, Tk init, `::safepdf::emit` → Lean callback, `Tk_PhotoPutBlock` from an RGBA `ByteArray`, event loop. Adapted from bib-lean's `c/tk_shim.c`. |
| `SafePdf/Shell/App/Shim.lean` | `@[extern]` bindings and the exported dispatcher `safepdf_gui_dispatch`. Only the `viewer` executable may import it. |
| `SafePdf/Shell/App/Tcl.lean`, `TclLemmas.lean` | Tcl scripts as data and the proof that `Tcl.quote` is injection-free (`parseWordStr_quote`, `parseScript_render`, …). Copied from bib-lean `BibLean/Gui/Tcl.lean` + `Tcl/Lemmas.lean`. Built by default (lib `SafePdfApp`). |
| `SafePdf/Shell/App/View.lean` | Tk-free viewing logic with `#guard` checks: zoom modes/steps/cap, C2 re-anchoring (`reanchor`, `reanchor_self`), Tcl number parsing, wheel scrolling across pages (`wheelStep`, 9.2), the LRU page cache. |
| `SafePdf/Shell/App/Select.lean` | Tk-free selection and search logic with `#guard` checks: glyph cells in reading order (`cellsOf`, text equal to `Text.layout`'s), boxes, nearest glyph, drag range, word, copy text, highlight boxes, normalised search with hits mapped back to glyphs (`findAll_sound`). Lib `SafePdfApp`. |
| `SafePdf/Shell/App/Links.lean` | Tk-free navigation logic with `#guard` checks: PDF text strings, URI display (`uriText_ascii`), destinations and their positions, page links with URIs, topmost link at a point, outline entries and treeview parents, page-label display and Ctrl+G lookup, back/forward history (`History.back_push`). |
| `SafePdf/Shell/App/Menu.lean` | Tk-free command and menubar model with `#guard` checks: commands (label, accelerator, script, enabled rule), menus, toolbar buttons that follow the rules, entry indices (task 9.1). |
| `SafePdf/Shell/App/Viewer.lean` | State, menubar, rendering, scrolling/zoom/rotation handlers, prefetch, selection/copy/search handlers and highlights, outline panel, link hover/activation, history, go-to bar, smoke mode. |
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

Selection and search (8.2c) run in a second smoke variant
(`SAFEPDF_VIEWER_SMOKE_MODE=text`, `Viewer.smokeText`) on a generated two-page Helvetica PDF:
Ctrl+A + Ctrl+C must put exactly the page text of `inspect --view text` (page 1) on the
clipboard (`clipboard get`), with one highlight rectangle per line; a double click (two
generated button presses) on `safe` copies `safe`; a drag (press, button-1 motion, release)
from the first glyph to the end of `world` copies `Hello safe world`; the highlight of `safe`
must cover a black marker rectangle drawn under the word in the PDF (an independent check of
the page ↔ device mapping, since standard fonts without an embedded program are not painted);
Ctrl+F with `ZEBRA  crossing` + Enter must move to page 2 and report `hit 1/1 on page 2` with
a highlight; F3 and Shift+F3 wrap to the same hit; an absent phrase reports `not found`;
Escape removes the highlights.

Navigation (8.2d) runs in a third variant (`SAFEPDF_VIEWER_SMOKE_MODE=nav`,
`Viewer.smokeNav`) on a generated three-page PDF labelled `i`, `ii`, `1` with an outline
(`Intro`; `Chapter`, a UTF-16 title, `/XYZ 0 400` on page 3; its child `Section`, page 2
through a named destination in the `/Names` tree), an internal link (to page 3) and a URI
link on page 1 whose address is full of Tcl metacharacters
(`https://example.org/p?q=[exit_7]&v=$HOME{x}\`). Driven by generated pointer and key events,
it checks: the outline panel opens with the three titles and depths; the title says
`page i (1/3)`; hovering the internal link gives the hand cursor and `go to page 1 (3/3)`; a
click jumps to page 3; Alt+Left, Alt+Right, Alt+Left go to pages 1, 3, 1; hovering the URI
link shows the exact address; a click opens the dialog, whose text widget holds exactly the
address (read just before the dialog confirms itself), and the clipboard then holds exactly
the address; clicking `Section` goes to page 2; at 200 % clicking `Chapter` goes to page 3
with the window top at y = 400 (yview within 0.45–0.53); Ctrl+G `ii` → page 2, `1` → page 3
(label before number), `nope` → error; F9 hides the panel.

The menubar (9.1) runs in a fourth variant (`SAFEPDF_VIEWER_SMOKE_MODE=menu`,
`Viewer.smokeMenu`) on the same three-page PDF: the window's `-menu` is `.menubar` with
File / Edit / View / Go and the expected entries; each action is invoked as
`.menubar.go invoke {Next page}` and so on: Go → Next, Last, Next at the end (disabled: stays),
First, Previous at the start (stays), Go to page… (`ii` → page 2), Back, Forward (with the
entry states checked on pages 1 and 3 and after the jump); View → Outline twice (panel and
check variable follow), Actual size, Zoom in (125 %), Zoom out, Fit width, Fit page, Rotate
right/left; Edit → Find… (bar mapped), Select all (no text on that page); File → Close (title
`safe-pdf`, document entries disabled) and File → Quit, which ends the run. Before closing, the
same run checks the wheel (9.2) with generated Tk 9 `<MouseWheel>` events: in fit page one
notch down turns to page 2 and one up back to page 1; at 200 % notches scroll page 1 down,
the view reaches the bottom and exactly one notch more turns to the top of page 2; eleven
1/12-notch deltas up leave page 2, the twelfth turns to the bottom of page 1; twelve 1/12
notches scroll as far as one notch (within 1.5 px); `<Button-5>`/`<Button-4>` scroll down and
back; Shift+wheel scrolls horizontally to the right edge and the page stays.

CI: the workflow cannot be pushed from the sandbox; the job that installs `tk-dev`/`xvfb`,
builds `viewer` and runs the smoke test is in `docs/ci-viewer-step.patch` (it also points the
cache keys at `lakefile.lean`).
