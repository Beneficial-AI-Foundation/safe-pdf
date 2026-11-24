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

## What it does (8.2a skeleton, 8.2b viewing, 8.2c selection and search, 8.2d navigation, 9.1 menubar, 9.2 wheel, 9.3 view modes, 9.4 highlights and notes, 9.5c saving marks into the PDF, 9.5g editing saved marks, 9.7 PDF.js look, 9.8 selection bubble and Highlight pop-over, 9.9 Add text and Draw, 9.11 XFDF import/export, 9.r8 document open settings, 9.r10 attachments panel, 9.r11b layers panel)

* Window (1200×960 by default; `SAFEPDF_VIEWER_GEOMETRY=WxH` sets another size): menubar
  (File, Edit, View, Go; see *Menubar* below), a toolbar and an outline sidebar modelled on
  PDF.js (see *Toolbar and sidebar* below), a scrollable canvas (scroll bars) with the current
  pages — a file opens as its own open settings say (see *Document open settings* below),
  otherwise in continuous vertical scrolling (View → Vertical Scrolling, No Spreads, as PDF.js;
  task 9.r1) at Automatic Zoom on page 1, or, in the other view modes, one page or two side by side
  (see *View modes* below; `SAFEPDF_VIEWER_VIEW=single|continuous|facing|continuous-facing`
  sets the one for files without `/PageLayout`) —, a status line (file, page, zoom, rotation, pixel size, render time
  or "from cache", notes, the view mode when it is not the default, notes about open settings
  that were not honoured, or the error). Every open starts afresh (task 9.r8): a mode or zoom
  chosen for one file does not carry over to the next; only the reopen after Save keeps them.
* Title: `NAME - page k/n - SafePDF`, with page labels `NAME - page iii (3/120) - SafePDF`.
* About (task 10.5): the app presents as **SafePDF** (the executable stays `viewer`). Help → About SafePDF (all platforms; on macOS also the application menu's About, `tkAboutDialog`) opens a message box. The macOS application menu's own name comes from the process (`viewer`) until a bundle exists (task 11.x).
* Pages are rendered by `Core.Raster.Glyph.renderDocPage` (fresh budget per page, CropBox and
  `/Rotate` honoured, the user rotation added with `rotAdd`).
* **Zoom** (`Toolbar.ZoomChoice` over `View.Mode`): Automatic Zoom (default, as in PDF.js:
  the page width for a portrait page, the whole page for a landscape one, at most 125 %), fit
  page, fit width, or a fixed percentage of actual size,
  where 100 % = 72 dpi × the screen scale factor (`tk scaling`, pixels per point). Steps
  25, 33, 50, 67, 75, 100, 125, 150, 200, 300, 400, 600, 800 %. Effective zooms are multiples
  of 1/64 pixel per point. Zoom in/out step on the effective zoom (task 10.12,
  `View.stepInZ`/`stepOutZ`): to the first step whose quantised zoom is strictly larger, or the
  last one strictly smaller, and nothing at the end of the range; from a fit mode `+` then `-`
  ends on the largest step at most the starting zoom (`View.stepOutZ_stepInZ_le`). Zooming keeps a point fixed: the page point under the mouse
  (Ctrl+wheel) or at the window centre (keys, toolbar) is computed with `Geom.toPage` before
  the change and put back under the same window position with `Geom.toScreen` after it
  (C2; `View.reanchor`). Window resizes re-render in the fit modes (debounced 100 ms).
* **Huge zooms are bounded**: a page image above `View.maxViewPixels` (2²⁶ px = 256 MiB RGBA)
  gets a smaller zoom ("zoom limited" in the status line); a side above `Limits.maxPageSide`
  (16384) is cropped by the renderer ("cropped" in the status line).
* **Rotation**: view rotation in 90° steps, combined with each page's `/Rotate`; the window
  centre's page point stays at the centre.
* **Scrolling** in the single-page view (and the facing view; not the default since 9.r1) is page-at-a-time: the canvas
  holds one page (spread). Scrolling past the bottom (or right) edge with the keys moves to the
  top of the next page; past the top, to the bottom of the previous page. The mouse wheel does
  the same (9.2, below). In the continuous modes the canvas holds the whole document (9.3).
* **Page cache** (`View.Cache`): render results keyed by (document, page, zoom, rotation), LRU,
  at most `View.cacheBytes` = 256 MiB of images and `View.cacheEntries` = 64 entries; results
  above half the budget are not cached. 100 ms after a page is shown, the next page (in the
  facing view: the next spread) is rendered into the cache when it is at most
  `Viewer.prefetchPixels` (2²² px), on a worker thread (8.8). Each page on the canvas has its own Tk photo
  (`::safepdf::pgN`), kept only while the page is in view or next to it (9.3).
* Errors never crash the viewer: unreadable files, parse errors (e.g. a `/Kids` cycle), render
  errors and Tcl errors go to the status line.

### Keys

One row per action; the Linux/X11 column is also Windows. On macOS (aqua) **every X11 key
keeps working** (the Ctrl bindings stay); the macOS column lists the keys added there and the
one the menus show (first). Where macOS has its own convention (Preview, the HIG) it is used
instead of a plain Command twin of the Ctrl key (task 10.9). "10.7" marks keys owned by task
10.7 (undo/redo, deleting marks), listed here but not bound by 10.9.

| Action | Linux / X11 | macOS (aqua) |
|---|---|---|
| scroll down a window; at the bottom: next page (top) | `Next` (PageDown), `space` | same (fn+↓ is PageDown) |
| scroll up a window; at the top: previous page (bottom) | `Prior` (PageUp), `BackSpace`, `Shift+space` | same (fn+↑) |
| scroll a tenth of the window; past the edge: next / previous page | `Down` / `Up` | same |
| scroll horizontally; past the edge: next / previous page (top) | `Right` / `Left` | same |
| first / last page | `Home` / `End` | **⌘↑ / ⌘↓**; `Home` / `End` (fn+← / fn+→) |
| zoom in one step (about the window centre) | `+`, `=`, keypad `+`, each also with Ctrl | **⌘+**, ⌘=, ⌘ keypad `+`; the plain keys |
| zoom out one step | `-`, keypad `-`, each also with Ctrl | **⌘−**, ⌘ keypad `-`; the plain keys |
| actual size (100 %) | `0`, `Ctrl+0` | **⌘0**, `0` |
| fit page / fit width | `f` / `w` | **⌘9** (Preview's Zoom to Fit), `f` / `w` |
| rotate the view 90° clockwise / counter-clockwise | `r` / `R` | **⌘R / ⌘L** (Preview); `r` / `R` |
| mouse wheel | scroll vertically; past the edge: next page (top) / previous page (bottom) | same; trackpad two-finger scroll in both axes |
| horizontal wheel | `Shift`+wheel | same |
| zoom about the pointer | `Ctrl`+wheel | **⌘**+wheel, `Ctrl`+wheel |
| open a PDF | `Ctrl+O` | **⌘O** |
| close the document / quit (asks Save / Don't Save / Cancel about unsaved marks, 9.r2) | `Ctrl+W` / `Ctrl+Q` (Ctrl+Q also in the page field, find and go-to bars, text-box editor) | **⌘W** / **⌘Q** (also there; the application menu's Quit and a quit from the Dock run the same command, `::tk::mac::Quit`) |
| save the marks into the opened file (asks before the first overwrite, 9.r2) / into a new file (9.5c) | `Ctrl+S` / `Ctrl+Shift+S` | **⌘S** / **⇧⌘S** |
| copy the selection / select all text of the page | `Ctrl+C` / `Ctrl+A` | **⌘C** / **⌘A** |
| open the find bar | `Ctrl+F` | **⌘F** |
| find next / previous | `F3` / `Shift+F3`; in the find bar also `Return` / `Shift+Return` | **⌘G / ⇧⌘G** (also in the find bar); `F3` / `Shift+F3`, `Return` / `Shift+Return` |
| close the find bar, go-to bar, page field (reverts) | `Escape` | same |
| go to page (number or label) | `Ctrl+G` | **⌥⌘G** (Preview; ⌘G is Find next); `Ctrl+G` |
| back / forward in the jump history | `Alt+Left` / `Alt+Right` | **⌘[ / ⌘]** (Preview, Safari); `Option+←` / `Option+→` |
| show / hide the sidebar | `F9` | **⌃⌘S** (the HIG's Show Sidebar); `F9` (fn+F9) |
| sidebar thumbnails: previous / next / go | `Up` / `Down` / `Return` (focused thumbnails) | same |
| highlight the selection | `h` | **⌃⌘H** (Preview); `h` |
| delete the selected mark | `Delete`; more keys: 10.7 | `Delete` (fn+⌫); ⌫: 10.7 |
| undo / redo a mark change | 10.7: `Ctrl+Z` / `Ctrl+Shift+Z` | 10.7: ⌘Z / ⇧⌘Z |
| save / cancel the note popup | `Ctrl+Return` / `Escape` | **⌘Return** / `Escape`, **⌘.** |
| finish the text-box editor | `Escape` (or a click elsewhere) | same |
| dialogs (external link, Save / Don't Save / Cancel): press the focused button / cancel | `Return` / `Escape` | `Return` / `Escape`, **⌘.** |
| selection bubble, Highlight pop-over, tools | mouse; `Escape` (its rules: task 10.6) | same |
| text fields (find, go-to, page field): select all, copy, paste, cut | Tk's entry keys (`Ctrl+/`, `Ctrl+C`, `Ctrl+V`, `Ctrl+X`) | Tk's aqua entry keys (⌘A, ⌘C, ⌘V, ⌘X) |

**How it is built.** The X11 keys are bound by `Viewer.setupScript` (plain keys) and
`Menu.platformScript` (Ctrl keys); on aqua (`tk windowingsystem` = `aqua`) `platformScript`
adds the macOS keys and sets the menus' accelerators to the macOS form (`Command-S`,
`Command-Option-G`, `Control-Command-S`, `Command-[`, which Tk's aqua menus draw as ⌘S, ⌥⌘G,
⌃⌘S, ⌘[); the Save tooltip, the sidebar tooltip and the status hints follow
(`Menu.Platform.keyText`: `Ctrl+S` → ⌘S, `F9` → ⌃⌘S). The table is pure Lean in `Menu.lean`:
`Menu.Key` (with the macOS-only `ctrl` modifier), `Cmd.key` / `Cmd.primaryKeys` (X11),
`Cmd.macKeys` (macOS; by default the Command twins of the Ctrl keys), `Menu.Action` (find
next / previous, not menu commands), `Menu.keyTable` (every sequence bound on the main window
with its script, per platform). Its `#guard`s check that every command with a Ctrl key has
Command keys on macOS, that every command with a key on X11 shows one on macOS, that the
macOS table extends the X11 one only by Command sequences, that no sequence runs two
different scripts on either platform (Tk picks the binding with the most modifiers, so ⌃⌘S
and ⌘S, ⌥⌘G and ⌘G do not overlap), and that no Command binding reaches X11 (where Tk reads
`Command` as Meta). ⌘. is bound by `::safepdf::cancelBind W SCRIPT`, which the dialogs and
the note popup call beside their Escape binding (a no-op off aqua).

Deliberate differences: on X11 `Ctrl+G` stays Go to page and find next is `F3` (as in Okular
and Firefox); on macOS ⌘G is Find next as everywhere on the Mac, so Go to
page moves to ⌥⌘G. Back / Forward and first / last page take the Mac's document keys (⌘[ ⌘],
⌘↑ ⌘↓) because PageUp/Home/End need fn on Mac keyboards. ⌘H is the system's Hide, so
Highlight is ⌃⌘H as in Preview; ⌘, (Preferences) and ⌘? (Help) are not bound — the viewer
has neither. Not verified on a real Mac: whether Tk 9 reports the keysym `g` for ⌥⌘G (with
Option held some layouts change the character; `Ctrl+G` still works there).

**Icon (9.r3).** The application/window icon is the logo's document mark
(`docs/branding/icon-{16,32,64,128,256,512}.png`, generated once from
`docs/branding/safe-pdf.png` by `docs/branding/make-icons.sh`, which also writes
`SafePdf/Shell/App/Icons.lean`). The PNGs are embedded as base64 (≈ 160 KB) so that an
installed `viewer` does not need the source tree; `Viewer.setIcon` loads them with
`image create photo -format png -data` and calls `wm iconphoto . -default` largest first
(X11: `_NET_WM_ICON` with all six sizes; macOS: the first image becomes the Dock icon of the
unbundled app).

## Menubar (9.1)

A native Tk menubar (`.menubar`, attached with `. configure -menu`; on X11 Tk draws it at the
top of the window, on macOS it is the system menu bar) duplicates the toolbar and the keys.
The model is Tk-free: `SafePdf/Shell/App/Menu.lean` lists the commands (`Menu.Cmd`: label,
accelerator text, the constant Tcl script that runs it, an enabled rule) and the menus; the
viewer builds the Tk menus from it (`Viewer.buildMenus`) and after every event sets the
`-state` of each entry and of the toolbar buttons Prev/Next/Back/Forward/Sidebar whose rule
changed (`Viewer.syncMenus`, over `Toolbar.targets`/`Toolbar.states`: menubar entries, the
toolbar's overflow menu and its buttons). The toolbar (9.7, below) reuses the same commands.

| Menu | Entries (accelerator) |
|---|---|
| File | Open… (Ctrl+O), Save (Ctrl+S), Save As… (Ctrl+Shift+S), Import annotations…, Export annotations… (XFDF, 9.11), Close (Ctrl+W), Quit (Ctrl+Q) |
| Edit | Copy (Ctrl+C), Select all (Ctrl+A), Highlight selection (H), Highlight colour ▸ (five colours), Add note…, Delete mark (Delete), Highlight tool (check, 9.8), Show all highlights (check, 9.8), Find… (Ctrl+F) |
| View | Sidebar (F9, a check entry showing whether the sidebar is open; *Outline* before 9.r9), Zoom in (`+`), Zoom out (`-`), Actual size (`0`), Fit page (`f`), Fit width (`w`), Rotate right (`r`), Rotate left (`R`), then two radio groups (9.3): Page Scrolling / Vertical Scrolling, No Spreads / Odd Spreads / Even Spreads |
| Go | Previous page (PageUp), Next page (PageDown), First page (Home), Last page (End), Go to page… (Ctrl+G), Back (Alt+Left), Forward (Alt+Right) |

Disabled: everything but Open… and Quit without a document; Save without unsaved marks; Copy and Highlight selection
without a selection; Delete mark without a selected mark;
Previous/First on the first page (spread), Next/Last on the
last (spread);
Back/Forward with an empty history. The keys stay; a menu accelerator is only a label (also
on macOS, where the accelerators read ⌘O, ⌘S, … — see Keys). The
Sidebar command is also the toolbar's sidebar button (9.7). *Close* empties the window (as
when started without a file).

## Toolbar and sidebar (9.7)

**Design reference: PDF.js**, the PDF viewer built into Firefox (Mozilla, Apache License 2.0,
<https://github.com/mozilla/pdf.js>, files `web/viewer.html`, `web/viewer.css`,
`web/toolbar.js`, `web/sidebar.js`), and the screenshot `docs/viewer-reference/pdfjs-firefox.png`.
Layout, sizes, spacing, colours and behaviour are re-created in Tk; **no PDF.js code and no
icon file is copied** — the icons are drawn with Tk canvas lines and polygons
(`::safepdf::icon::*` in `Viewer.setupScript`). The Tk-free model is in
`SafePdf/Shell/App/Toolbar.lean` and `SafePdf/Shell/App/Sidebar.lean` (`#guard` checks).

* **Toolbar** (`.bar`, 40 px, background `#f9f9fa`, a 1 px line below; `Toolbar.layout`):
  * *left*: the sidebar toggle (shown with a document — since 9.r9 every document has
    thumbnails; drawn pressed while the sidebar is open), ∧ / ∨ previous / next page (disabled on the first / last page),
    the page field and its label. The field shows the page number and `of N`, or, when the
    document has page labels, the label and `(k of N)` (as PDF.js). **Enter** jumps to an exact
    label, else a page number `1..N`, else a label ignoring case (`Toolbar.pageEntry`; the jump
    is recorded in the back/forward history as PDF.js does); an out-of-range number or other
    text reverts the field to the current page (and says so in the status line); Escape or
    leaving the field reverts it too. The field follows every page change (arrows, keys, wheel,
    links, outline). The entry has its own bind tags, so typing does not trigger viewer keys.
    Right after `of N`, the **view-mode drop-down** (9.r4, `Toolbar.ViewChoice`): a small
    rounded button (`.bar.vmode`, 56 × 32 px, the zoom box's border and radius) with an icon
    of the current mode drawn with canvas items — one page, two stacked pages, two pages side
    by side, four pages in a grid — and a chevron; its tooltip names the mode. Clicking it
    opens a menu (`.viewmenu`) with **Single Page**, **Vertical Scrolling** (the start-up
    default since 9.r1), **Two Pages** and **Two Pages Scrolling** as radio entries: each is a
    pair of the 9.3 modes (`ViewChoice.modes`: Page / Vertical Scrolling with No Spreads or
    spreads; a two-page choice keeps Even Spreads when they are on, else takes Odd Spreads)
    and runs `emit viewMode view KEY`. Whatever changes the mode — this menu, View → Page /
    Vertical Scrolling and No / Odd / Even Spreads, the same entries of the `»` menu,
    `SAFEPDF_VIEWER_VIEW` — goes through `Viewer.setViewMode`, which sets the View and `»`
    menus' variables (`::safepdf::scrollMode`, `::safepdf::spreadMode`) and the drop-down's
    checked entry and icon (`::safepdf::viewSel` = `ViewChoice.ofModes` of the two), so all
    three always agree (`ViewChoice.ofModes_modes`, `modes_ofModes`). Disabled (dimmed) with no
    document.
  * *centre* (centred in the window): − / + (zoom out / in one step, as the keys) and the zoom
    drop-down, a rounded button showing the current choice; clicking it opens a menu with
    Automatic Zoom, Actual Size, Page Fit, Page Width, 50 %, 75 %, 100 %, 125 %, 150 %, 200 %,
    300 %, 400 % (`Toolbar.ZoomChoice.presets`, radio entries). A zoom reached with − / +, the
    keys or Ctrl+wheel that is not in the list (33 %, 67 %, 600 %, …) shows as its percentage
    with no entry checked (PDF.js's custom option).
  * *right*: **Select text** (10.8, an I-beam icon; the default tool, see *Select-text tool
    and cursors* below), Highlight (works since 9.4: highlights the selection in the current colour;
    without a selection it turns the Highlight tool on and opens its pop-over, or off (9.8);
    see *Selection bubble and Highlight pop-over*), Add comment (9.9: Add note… on the
    selection, else at the window centre), Add text and Draw (9.9, see *Add text and Draw*),
    Add image, then Print and Save — Save (PDF.js's download icon) is the command File →
    Save since 9.5c, enabled while there are unsaved marks; Add image and Print are
    **disabled placeholders** (after M9) — and the `»` overflow menu: Open…, Import annotations…, Export annotations… (9.11), Find…, Go to page…, First page, Last
    page, Rotate right, Rotate left (`Toolbar.overflow`; the commands that lost their toolbar
    buttons), then, as in PDF.js's secondary toolbar, the scroll modes (Page Scrolling, Vertical
    Scrolling) and the spread modes (No Spreads, Odd Spreads, Even Spreads) as radio entries on
    the same variables as the View menu (9.3). Document properties are not available yet.
  * Buttons are 32 px canvases with round hover (`#e4e4e9`), pressed and toggled backgrounds,
    16 px icons in `#3b3b44`, dimmed when disabled (PDF.js: opacity 0.5); a tooltip appears
    after 600 ms; separators are 1 px × 20 px.
* **Select-text tool and cursors** (10.8, Plan.md §6 Phase 10; `Toolbar.Mode`,
  `Toolbar.cursorFor`). Exactly one of Select text, Highlight, Add text, Draw is the active
  tool, and its button shows toggled (`Toolbar.pressed_unique`). The active tool is read off
  the tool state (`Bubble.Ui`), never stored apart: Add text / Draw when that mode is on, else
  Highlight when its tool is on, else Select text — the default at start-up and after a
  document closes (`Mode.of_default`). PDF.js has no Select button: its editor-mode buttons
  toggle and "no editor" is the default; here that state has a button. Picking another tool
  unpresses Select text; turning that tool off with its own button gives it back
  (`Mode.of_selectEditor_twice`, `Mode.of_toolClick_twice`); the Select text button turns the
  others off with their pop-overs (`Toolbar.selectTool`, `Mode.of_selectTool`; an open text
  box is committed). Escape still only closes a pop-over and keeps the tool (10.6). The page
  canvas cursor telegraphs what a press does there, from what lies under the pointer
  (`Toolbar.hitOf`, in the click's order: a mark, else a link, else a glyph box of the page
  text `Select.Cell.box`, else nothing):

  | tool | text | link | mark | elsewhere |
  |---|---|---|---|---|
  | Select text, Highlight | `xterm` (I-beam) | `hand2` | `hand2` | default arrow |
  | Add text | `xterm` | `xterm` | `hand2` | `xterm` |
  | Draw | `crosshair` | `crosshair` | `crosshair` | `crosshair` |

  Tk's portable names, which Tk Aqua maps to the native I-beam, pointing hand and crosshair.
  Choices: a mark shows the hand because a click selects it (as a link click follows the link;
  a drag from a highlight still selects the text under it); Add text shows the I-beam
  everywhere, as PDF.js (`--editorFreeText-editing-cursor: text`), since a click places a
  text box even over a link; Draw shows a crosshair where PDF.js shows a pen. PDF.js's free
  highlight (drawing a highlight over non-text in Highlight mode) is not implemented, so
  Highlight keeps the arrow off the text. The cursor is updated on `<Motion>` (`Viewer.hover`:
  `Links.linkAt` and `Marks.Store.hitAt`, and the per-page cached text index only for Select
  text / Highlight over nothing else) and after every tool change at the last pointer position
  (`Viewer.refreshCursor`); Tk is called only when the cursor changes.
* **Opening and closing the sidebar** (9.r4): the canvas changes width with it. Window
  resizes are reported to Lean 100 ms after the last `<Configure>` (a window drag sends many),
  so before 9.r4 the canvas showed the old layout in the new width for that time — the page,
  centred for the old width, sat at the old offset from the canvas's new left edge (on closing
  it jumped left by the sidebar's width, then back to the centre; "the page flickers to the
  side", most visible at Page Fit). Now `Viewer.showOutline` calls `::safepdf::resizeSoon`
  first: for 300 ms the canvas's `<Configure>` binding reports a change of its width at once
(height-only changes, such as the find bar's, stay debounced). Tk runs
  that binding while it lays out the panes, before it paints the canvas at its new size, so
  Lean lays the pages out for the new width (and at a fit zoom renders or takes from the cache
  the new zoom) before anything is drawn: the page goes straight to its final place, in
  every view mode. Smoke case 1q samples the page frame's canvas and screen x at every
  `<Configure>` and every 2 ms and requires just the start and the end value (before the fix:
  screen x 403 → 117 → 260 on closing, 260 → 531 → 396 on opening).
* **Sidebar** (`.ol`, the left pane of the paned window, `Sidebar`; panels since 9.r9): a row
  of small **view buttons** (`.ol.sw`, PDF.js's sidebar view buttons *Show Thumbnails*, *Show
  Document Outline*, *Show Attachments*, *Show Layers*; the shown panel's button drawn
  pressed) above a white panel with its heading (*Thumbnails*, *Document outline*) on the
  `#f0f0f4` background. A button shows only when the document has that content
  (`Sidebar.buttons`: thumbnails always, the outline when there is one; attachments since 9.r10 (see
  *Attachments panel* below) when the document has some; layers since 9.r11b (see *Layers
  panel* below) when it has optional content). The sidebar **opens on load as the document's
  `/PageMode` says** (`Sidebar.onLoad`): `/UseThumbs` → thumbnails, `/UseOutlines` → the
  outline, `/UseAttachments` → attachments, `/UseOC` → layers (each when the document has
  that content), `/UseNone` and `/FullScreen` → closed; without a page mode the outline when there is
  one, else closed. The toggle (F9, View → Sidebar, the toolbar button) works for every
  document and reopens the last panel chosen while the document has it, else the outline, else
  the thumbnails (`Sidebar.pick`). The panels are a list in `Sidebar.panels` (key, button path,
  icon, tooltip, heading); in Tk each panel grids its widgets into row 1 of `.ol.p`
  (`::safepdf::panelWidgets(KEY)`), `::safepdf::showPanel KEY TITLE` shows one and runs
  `::safepdf::panelShown::KEY` when it exists — a new panel adds its `Sidebar.panels` entry,
  its `Sidebar.Content` flag (set in `Viewer.contentOf`) and these two Tcl pieces.
* **Outline panel**: a text widget drawn as a tree: one row per entry, indented
  20 px per level, long titles wrapped; entries with children have a disclosure triangle (▼
  open, ▶ closed; entries with a positive `/Count` start open); clicking a triangle collapses
  or expands the subtree (`Sidebar.toggle`: the rows of a closed entry's subtree are elided
  through one tag per ancestor), clicking a title jumps to its destination and marks the row;
  rows highlight under the pointer. The scroll bar appears only when the tree does not fit.
* **Thumbnails panel** (9.r9, after PDF.js's `pdf_thumbnail_viewer.js` / `.thumbnail`; drawn
  with a Tk canvas `.ol.th`, nothing copied): one image per page, 98 px wide
  (`Sidebar.thumbW`, PDF.js's `THUMBNAIL_WIDTH`), the height from the page's crop box with
  its `/Rotate` and the user rotation (`Sidebar.thumbSize`, kept between 8 and 392 px), on a
  white frame with the page number (or page label) below, in a vertical list
  (`Sidebar.thumbLayout`). The current page's thumbnail has a rounded grey background and
  follows the main view (scrolled into view when the page changes, PDF.js's
  `scrollThumbnailIntoView`). **Click** a thumbnail to go to its page (recorded in the
  history, as a link); in the focused panel **Up / Down** move a blue focus ring, **Return**
  goes there. Wheel, Button-4/5 and Tk 9 `<TouchpadScroll>` scroll the panel.
  **Rendering is lazy and off the critical path**: only the visible thumbnails and 3 more on
  each side (`Sidebar.thumbsWanted`) are rendered, by the same renderer at the thumbnail's
  zoom (98 px / page width) on worker threads (`thumbSubmit`, at most 2 at once and only while
  the page renders leave a slot of `maxJobs` free, so the main view goes first); results come
  in through the same 15 ms `poll` as the pages. At most 40 thumbnail images are kept
  (`Sidebar.thumbBudget`, ≈ 50 KB each); beyond that the ones farthest from the view are
  dropped (`Sidebar.thumbEvict`) and rendered again when scrolled back to. Nothing is rendered
  while the panel is hidden; a new document or rotation lays them out again. Thumbnails show
  the page as the file has it (and saved marks being edited, `State.view`); unsaved
  highlights are not composited into them.
* **Page area**: background `#f0f0f4`, the page with a 1 px grey border.

Not done (visible differences from the reference): no "find current outline item" button;
the menubar stays above the
toolbar; the status line stays at the bottom; fonts are Tk's default (DejaVu Sans on Linux)
instead of the system UI font; canvas drawing on X11 is not antialiased, so icons and rounded
corners are slightly jagged; the zoom menu is a plain Tk menu, not a native select pop-up;
Add image (stamp) and Print come after M9.

## Document open settings (9.r8)

ISO 32000-2 §7.7.2, §12.2, §12.3.2; ledger Decision 2026-11-23 "The viewer honours every
document open setting". `Core.Doc.OpenSettings.read` (pure, total, never fails the document;
rules O1–O7 in its module doc; suite `open-settings`) reads them, `Viewer.applyOpenSettings`
applies them on **every open** (start-up, File → Open, Close + Open, bib-lean's reader). A
file opened later starts again from the defaults (`resetOpenView`: the start-up view mode,
Automatic Zoom, page 1, outline when there is one, the whole window UI, the file name as title)
— nothing carries over from the previous file. Changes the user makes (View menu, zoom,
F9, Escape) win until the next open. **The reopen after Save / Save to library keeps the
user's current view** (view mode, zoom, outline, page; the document's settings are not
applied again: they have not changed and the user is mid-work) — `openWith … (keepView :=
true)`. The window's size and position are the user's and are never reset.

| Setting | What the viewer does |
|---|---|
| `/PageLayout /SinglePage` | Single Page (Page Scrolling, No Spreads) |
| `/OneColumn` | Vertical Scrolling, No Spreads |
| `/TwoColumnLeft` / `/TwoColumnRight` | Two Pages Scrolling with Odd / Even Spreads |
| `/TwoPageLeft` / `/TwoPageRight` | Two Pages with Odd / Even Spreads |
| `/PageMode /UseNone` | sidebar closed |
| `/UseOutlines` | sidebar open on the outline (when the file has one, else closed) |
| `/UseThumbs` | sidebar open on the thumbnails (9.r9; every document has them) |
| `/UseAttachments` | sidebar open on the attachments (9.r10) when the file has attachments; else the outline rule (open with an outline), no note |
| `/UseOC` | sidebar open on the layers (9.r11b) when the file has optional content; else the outline rule (open with an outline), no note |
| `/FullScreen` | `wm attributes . -fullscreen 1`, sidebar closed, note "full screen (Escape leaves)"; Escape leaves and applies `/NonFullScreenPageMode` to the sidebar |
| `/OpenAction` destination or `/S /GoTo` | page, position (`/XYZ` left/top, `/FitH` top, …: the page point at the window's top-left, as links) and zoom: `/XYZ` zoom > 0 → that percentage (clamped to 25–800 %), `null`/0 → Automatic Zoom stays; `/Fit`, `/FitB` → Page Fit; `/FitH`, `/FitBH` → Page Width; `/FitV`, `/FitBV` → Page Fit (best effort: no fit-height zoom; the same for portrait pages in a wide window); `/FitR` → Page Fit with the rectangle's left/top at the top-left (best effort). Named destinations through `/Dests` and `/Names /Dests`. |
| `/OpenAction` JavaScript, URI, Launch, Named, GoToR, … | **never executed**; note "open action /KIND ignored (not executed)". `/Next` chains are not followed. |
| `/HideToolbar`, `/HideMenubar`, `/HideWindowUI` | toolbar (`pack forget .bar`), menubar (`. configure -menu {}`), scroll bars (`grid remove .ys .xs`) hidden; note "the document hides parts of the window (Escape shows them)"; **Escape** shows them again (so a document can never lock the user out of the UI; the keys keep working meanwhile) |
| `/FitWindow` | window sized for the first page at the open zoom (100 % for the fit choices), both pages of a spread, at most 90 % of the screen |
| `/CenterWindow` | window centred on the screen |
| `/DisplayDocTitle` | window title from `/Info /Title` (text string, control and bidi characters as spaces, ≤ 500 characters; XMP `dc:title` not read: no XMP parser) |
| `/Direction /R2L` | spreads mirrored: the first page of a spread on the right (`View.mirrorPlace`); status "…, right to left"; keys and wheel unchanged |
| `/NonFullScreenPageMode` | the page-mode rule above on leaving full screen |
| print keys (`PrintScaling`, `Duplex`, `ViewArea`, …) | ignored |

Invalid values (wrong type, unknown name, a destination outside the document or not found)
leave the default and add a note ("invalid /PageLayout ignored", "open destination … not
found"); notes stay at the end of the status line until the next open (Escape drops the
full-screen and hidden-UI ones). Hyperref writes `/PageMode /UseOutlines /OpenAction [p1 /Fit]`
by default, so most LaTeX papers now open at Page Fit with the outline (checked on
`arxiv-0704.0001`, `arxiv-1301.3781`, `arxiv-1904.00001`, `arxiv-2006.00001`: page 1 whole at
73–78 % in the 1200×960 window, outline open; `arxiv-0905.0002` (`/UseNone` + Fit): Page Fit,
outline closed; `arxiv-2111.00001` (`/DisplayDocTitle true`, no `/Title` in `/Info`): the file
name stays the title; `arxiv-2209.00001` (`/OneColumn`): Vertical Scrolling, Automatic Zoom).

Unverified: on aqua `. configure -menu {}` leaves Tk's default application menu (the menubar
cannot disappear on macOS); full screen on aqua uses the native full-screen space; without a
window manager (Xvfb) `wm attributes . -fullscreen` reads back 0, so the smoke test checks the
viewer's state only.

## Honest UI for hidden content (12.5)

* **Trusted identity line.** While a document has the window in full screen (`/PageMode
  /FullScreen`) or hides parts of it (`/HideToolbar`, `/HideMenubar`, `/HideWindowUI`), a dark
  strip `.ident` above the status line, outside the page canvas, reads `SafePDF is showing
  NAME (PATH) - this line is drawn by SafePDF, never by the document` (`identityLine`: file
  name and path with controls and bidi overrides blanked, never the document's `/Title`; a
  bib-lean document says "opened from the library"). It is packed before the window enters
  full screen and removed when Escape leaves it / shows the chrome (`syncIdentity`); the
  10.13 rule (the full-screen note is stored before entering full screen) is unchanged.
* **Invisible text in copies.** Copy keeps text drawn with text rendering mode 3/7 (an OCR
  layer is the page's text) but says so: `copied N characters; the copied text includes K
  characters that are not visible on the page (invisible text, e.g. an OCR layer)`
  (`copyStatus`, `Select.PageIndex.hiddenChars`, from `Core.Text`'s per-glyph `visible`).
  Text outside the CropBox and text the clip hides is never in the selection. The inspector's
  `text` view lists hidden runs (`"hidden": [{…, "invisible": true, …}]`, `reason`
  `render-mode` or `outside-cropbox`). White-on-white and transparent text are not detected.
* **Revision-retention notice.** A Save that deletes saved marks appends `; note: the N
  deleted mark(s) are still in the file's earlier revision (Save only appends an update) and
  can be recovered from it` to its status (`retentionNote`; Save, Save As…, the library).

## Attachments panel (9.r10)

Files embedded in the PDF (ISO 32000-2 §7.11.4) are listed in a sidebar panel after PDF.js's
attachments view (`web/pdf_attachment_viewer.js`; nothing copied). The data is read by the
verified core module `SafePdf/Core/Doc/Attachments.lean` (pure, total, bounded; rules A1–A6
in its module doc), the panel's Tk-free model is `SafePdf/Shell/App/Attach.lean`.

* **What is listed**: the `/Names /EmbeddedFiles` name tree (walked by `Nav.treeEntries`:
  visited set, `/Kids` cycles cut) in its order, then the `/FileAttachment` annotations of
  every page (`/FS`); an annotation whose file specification is already listed adds no row
  (its page is noted). At most 1024 rows.
* **A row**: the name — `/UF`, else `/F`, else the name-tree key; decoded as a text string,
  control characters, bidi overrides/isolates, LRM/RLM and line separators removed, at most
  200 characters — and the size **known without decoding** (`Attachments.listedSize`:
  `/Params /Size`, else the stream's `/DL`, else the stored length of an unfiltered stream);
  `?` for a compressed file of unknown size until it is decoded, `—` for an external file
  reference (no `/EF`), `error` once decoding failed. **Listing decodes nothing**, so a large
  attachment never stalls the window. A file is decoded only on demand: when it is saved
  (the filter chain under the viewer's limits: a decompression bomb is a limit error in the
  status line and its row), and when its **tooltip** opens (600 ms over a row; a probe under
  the viewer's limits with the per-stream cap lowered to 16 MB, `Attach.probeLimit`: a larger
  file shows `> 16 MB` and is decoded only when saved). The tooltip shows the description
  (`/Desc`), the MIME type (`/Subtype`), creation and modification dates (`/Params`), the page
  of its annotation, the stored size of a compressed file not decoded yet, and any problem or
  decoding error. Selecting a row describes it in the status line.
* **Save attachment as…**: double-click a row, press Return, or right-click (on aqua also
  Control-click / Button-2) → *Save attachment as…*. The bytes are decoded first (an error is
  reported, no dialog), then `tk_getSaveFile` (title *Save attachment as*, no `-filetypes`:
  any type; on aqua the Format pop-up would overflow, 9.r6) starts in the opened file's
  folder with the **sanitized** name proposed (`Attachments.fileNameOf`: the last path
  component only, `:*?"<>|` → `_`, no leading dots, ≤ 200 bytes; `../../etc/evil:name.txt` →
  `evil_name.txt`). Refused with a status message: a folder, **the opened PDF**, a read-only
  file, a folder that is not writable (`Attach.targetProblem`, the rules of 9.r6). The file is
  written atomically (`Save.writeAtomic`: temporary file in the same folder, then rename;
  permissions of a replaced file kept) with exactly the decoded bytes.
* **Never run**: the viewer has no "open" or "open with" action for attachments; nothing
  launches, opens or interprets an attachment's bytes.
* **Icons on the page**: a click inside a file attachment annotation's `/Rect` (drawn by the
  renderer from its appearance stream when it has one) opens the sidebar on the attachments
  panel and selects that row; it never opens the file.
* **Panel switcher** (9.r9's): the *Show Attachments* button shows only when the document
  has attachments (`Sidebar.Content.hasAttachments`, set in `Viewer.contentOf`); the panel's
  widgets are `.ol.at` / `.ol.as` (`::safepdf::panelWidgets(attachments)`,
  `::safepdf::panelShown::attachments` for its scroll bar). `/PageMode /UseAttachments`
  opens it (`Sidebar.onLoad`); without attachments the outline rule applies, with no note.

Unverified (no Mac here): the secondary click on aqua (Button-2/3, Control-click), the
`ttk::treeview` look under the aqua theme, and `tk_getSaveFile` on aqua with an
attachment name.

## Layers panel (9.r11b)

The document's optional content groups (ISO 32000-2 §8.11; read by
`SafePdf/Core/Doc/OptionalContent.lean`, task 9.r11a) are listed in a sidebar panel after
PDF.js's layers view (`web/pdf_layer_viewer.js`; drawn with Tk, nothing copied). The panel's
Tk-free model is in `SafePdf/Shell/App/Sidebar.lean` (`layerRows`, `layerToggle`).

* **The tree** follows the default configuration's `/D /Order`: a group is a row with a
  **checkbox** showing whether it is ON and its `/Name`; a nested array whose first element is
  a string is a **heading** (bold, no checkbox) over its items; a nested array without a label
  nests its items under the row before it (the spec's sub-groups; PDF.js drops such arrays);
  a labelled array with nothing left in it is dropped (PDF.js). Rows with children have a
  disclosure triangle (open at first; a click on the triangle or the heading closes/opens it).
  **Groups not listed in `/Order`** follow under an italic heading **"Additional Layers"**,
  in `/OCGs` order, each with its checkbox (radio and locked rules as usual), and that heading
  starts collapsed — as PDF.js (`src/core/catalog.js` `parseOrder`, `web/pdf_layer_viewer.js`).
  (PDF.js also puts there the groups of an unlabelled array, since it drops those arrays; here
  they are nested in place, so they are not repeated.)
  Without `/Order` every group of `/OCGs` is listed by name. Names and labels are text
  strings with control and bidi characters removed, at most 200 characters
  (`Attachments.displayText`); an empty name shows `(no name)`.
* **Toggling** a checkbox (or clicking its name, as PDF.js's `<label>`) is
  `Config.setGroup`: a group of a radio-button set (`/RBGroups`) turned ON turns the others
  OFF; a **locked** group (`/Locked`) has a disabled checkbox and a grey name and never
  changes (the event alone says "layer NAME is locked"). Every checkbox is then set from the
  new state, and the document is shown again under it (`Viewer.applyLayers`): a new render
  generation (the render cache and running renders are stale), the **thumbnails** laid out and
  rendered again when their panel shows (9.r9's cache keyed by the generation), and the
  **text indexes** dropped — hidden text is neither selectable nor found by search; the
  selection and the search hit are cleared. The state is passed to the renderer
  (`renderDocPage … (oc := …)`) and to text extraction (`extractDocPageAnnots … (oc := …)`).
* **When**: the state is the document's default (`/D`: BaseState, ON, OFF, `/Usage /View
  /ViewState`) at **every open** (9.r8's rule: nothing carries over); the reopen after Save /
  Save to library (`keepView`) keeps the state the user set (when the groups are the same).
  `/PageMode /UseOC` opens the sidebar on the layers (`Sidebar.onLoad`); the *Show Layers*
  button shows only when the document has optional content with something to list
  (`Sidebar.Content.hasLayers`).
* **Saving never writes the layer state**: the panel changes only the viewer's state; Save
  writes the marks' incremental update and leaves `/OCProperties` (and the catalog) as they
  are (checked by the smoke test).
* **Inspector**: the `svg` and `ops` views run under the document's default state too
  (`Views.Svg.defaultOC`): content in an OFF layer is not drawn in the SVG and its items are
  not counted (its operators are, in the histogram). There is no way to choose another state
  there.
* Tk: a text widget `.ol.ly` (scroll bar `.ol.ls`, `::safepdf::panelWidgets(layers)`) drawn
  as a tree like the outline; row `K` is either a heading (tag `hK`) or an embedded
  `ttk::checkbutton .ol.ly.cK` (style `Ly.TCheckbutton`, variable `::safepdf::ly(K)`, event
  `layer K`) followed by its name (tag `gK`, wraps in the panel); `tK` is the triangle
  (`lyToggle K`), `uA` every ancestor (a closed ancestor elides the row with its checkbox).

Unverified (no Mac here): the `ttk::checkbutton` look under the aqua theme (its `-background`
style options are ignored there), and `<TouchpadScroll>` over the panel on aqua (bound like the
thumbnails', scrolling `.ol.ly` by pixels).

## Wheel scrolling across pages (9.2, 9.r1)

The wheel continues into the next / previous page as the keys do. Pure logic in
`View.wheelStep` (`#guard` checks, including `View.wheelPages`, a simulated document), driven by
`::safepdf::emit wheel AXIS KIND D`. Each axis keeps its own state (`View.Wheels`, 9.r1). In the
continuous modes (the default) the wheel simply scrolls the document; the rules below on page
edges are for the page scroll modes (single page, facing).

* **Deltas.** `<MouseWheel>` `%D` is in 1/120 notches on Tk ≥ 8.7 (Tk 9 turns X11 wheel
  buttons into `<MouseWheel>`) and on Windows; `<Button-4>`/`<Button-5>` (Tk 8.6 on X11) are
  sent as ±120; Tk 8.6 on macOS gives lines (`KIND line`); Tk 9 trackpads (`<TouchpadScroll>`,
  unpacked with `tk::PreciseScrollDeltas`) give pixels. One notch scrolls a tenth of the view
  (as Tk's `scroll 1 units`); smaller deltas (high-resolution wheels, trackpads) accumulate
  their fractions (`View.Wheel.acc`) instead of being rounded to a notch or lost.
* **Edges.** Within the page the view scrolls and stops exactly at the edge (the rest of that
  event is dropped, so no part of a page is skipped). Further events at the edge push past it;
  when the push reaches the threshold (`View.wheelThreshold`) the page turns: down → top of the
  next page, up → bottom of the previous page. Threshold: one notch for wheels (a tenth of the
  view); for trackpads a twentieth of the view (the gap between pages), but at least a quarter
  of the view less what the page scrolls, so a page that fits the window (Page Fit) costs a
  quarter of a view of finger travel. A tiny overscroll never turns a page; a pause of 400 ms
  or a change of direction forgets the push.
* **Flow (9.r1).** No event is ever swallowed: the push beyond the threshold is carried onto
  the page just turned to, so a swipe, a fast wheel or trackpad momentum flows on into the new
  page with its next event. 9.2 ignored every trackpad event after a turn until a 400 ms pause
  (the gesture and its momentum stopped dead on the new page — the human's "when it scrolls to
  the next page then it stops scrolling"), and shared one state between the axes, so the ±1 px
  sideways jitter of a vertical swipe (`<TouchpadScroll>` carries both deltas) reset the push
  and the page never turned at all (reproduced on X11: 3000 generated events stuck on page 1).
* **Precision.** The wheel's `moveto` uses twelve digits (`Viewer.fmtFracFine`); with six, a
  one-pixel step in a document taller than 500 000 pixels (vertical modes) rounded back to
  where it started.
* **Horizontal** (`Shift`+wheel, trackpad sideways): scrolls and stops at the edge; it never
  turns pages (the `Left`/`Right` keys still do).
* **Smoke** (`SAFEPDF_VIEWER_SMOKE_MODE=wheelflow`, case 1o): bursts of 12 px
  `<TouchpadScroll>` events with sideways jitter and of third-notch `<MouseWheel>` events, 8 ms
  apart, through five pages in every view mode at Page Width and in the single page at Page
  Fit; trace of (event, ms, page, top) in `wheelflow-trace.txt`. On `arxiv-1706.03762.pdf`
  (882 px view) before 9.r1 the trackpad bursts never left page 1 in the page modes; after,
  the longest run of events that moved nothing is 3 (single, Page Width), 18 (Page Fit and
  facing: the quarter-view push), 0 in the continuous modes.
* **Not verified here (aqua only):** real macOS trackpad and Magic Mouse events. The smoke test
  generates Tk 9 `<TouchpadScroll>` and `<MouseWheel>` events on X11 (and `xdotool` wheel
  buttons); whether Tk 9 on macOS delivers momentum as further `<TouchpadScroll>` events, the
  size of its deltas, the scale of `<MouseWheel>` `%D` for a mouse there, and the feel of the
  thresholds are not tested; the `line` kind (Tk 8.6 on macOS) is covered by the `#guard`s
  only.

## View modes (9.3)

PDF.js's *Scroll mode* and *Spread mode* (`web/pdf_viewer.js`, `ScrollMode`, `SpreadMode`), in
the View menu and the `»` overflow menu as two radio groups. Pure layout logic in `View.lean`
(`#guard` checks; theorems `mem_spreadPages` — page `p` is in spread `k` exactly when
`spreadOf p = k`, so every page is in exactly one spread —, `spreadOf_lt_count`,
`spreadOf_spreadFirst`, `nextPage_spread` — Next moves exactly one spread —, `stack_pairwise` —
stacked rows and the pages of a row never overlap, each ends at least the gap before the next
starts).

| Mode | Scroll | Spread | Shows |
|---|---|---|---|
| single page | Page Scrolling | No Spreads | one page at a time |
| continuous (default, 9.r1) | Vertical Scrolling | No Spreads | all pages stacked, 10 px apart (`View.pageGap`) |
| facing | Page Scrolling | Odd / Even Spreads | one spread at a time: two pages side by side |
| continuous facing | Vertical Scrolling | Odd / Even Spreads | all spreads stacked |

* **Spreads** (`View.spreads`): Odd = pages 1|2, 3|4, …; Even = page 1 alone, then 2|3, 4|5, …
  (the last spread may hold one page). The pages of a row are 10 px apart, centred together,
  each centred vertically in the row (PDF.js `vertical-align: middle`).
* **Layout** (`View.layoutRows`): the rows are stacked from the top margin (in the page scroll
  mode the one row is centred when it fits, as the single page always was), each centred
  horizontally; the scroll region is at least the window. Every page on the canvas has a white
  frame with a 1 px border (the placeholder until its image arrives), its own photo
  `::safepdf::pgN` and canvas image item (tags `pageframe fN`, `pimg pN`; a page that fails to
  render shows the error as text in its frame, tag `perr eN`).
* **Zoom**: one zoom for the layout, chosen for the current page. The fit modes (Automatic
  Zoom, Page Fit, Page Width) use the page's size in the single and continuous modes and twice
  its width (and the window less the 10 px gap) in the facing modes, as PDF.js does
  (`View.fitBox`, `#pageWidthScaleFactor` 2), so every spread of a paper shows at the same zoom;
  Automatic Zoom still asks whether the page itself is portrait. Each page is capped at
  `View.maxViewPixels` separately. A new layout is computed when the document, mode, zoom,
  rotation, window size or (page scroll mode) the spread shown changes — never by scrolling in
  the continuous modes; there it keeps the view's place in the current page.
* **Current page**: in the continuous modes the page under the window centre
  (`View.pageAt`; the nearest page when the centre falls in a gap), updated as the view moves
  (wheel, keys, scroll bar: the canvas's `-yscrollcommand` reports `viewChanged` once per idle
  moment) — the page field, title and Previous/Next follow it. After a jump (Next/Previous,
  Home/End, Ctrl+G, a link, the outline, a search hit) the page jumped to stays current while
  the view stays where the jump put it, even if another page is under the centre.
* **Paging**: Next/Previous (toolbar arrows, Go menu, PageDown/PageUp at the edge, wheel at the
  edge in the facing view) move a whole spread (`View.nextPage`, `View.prevPage`): two pages in
  the facing modes; Previous/First are disabled in the first spread, Next/Last in the last. In
  the continuous modes a jump scrolls the page's top (with the 8 px margin) to the window top;
  the keys PageDown/Space/arrows scroll the whole document, Home/End go to the first/last page.
* **Wheel**: in the page scroll modes as in 9.2/9.r1 (a spread turns after a push past the
  edge, and the gesture flows on); in the continuous modes the wheel simply scrolls the
  document (`View.wheelStep` without page crossing).
* **Rendering and memory**: the current page — in the facing view its whole spread — is
  shown first; the other pages in view and one more place before and after them
  (`View.wantedPages`) follow (`renderMore`, nearest to the current page first). Since 8.8 all
  rendering runs on worker threads (next section), so no page blocks the window; a page not
  rendered yet shows its white frame with "Rendering…". Photos of pages that leave that set
  are deleted (`image delete`), so Tk holds at most the pages in view plus two; the rendered
  images stay in the LRU cache (256 MiB, 64 entries) at the current zoom.
* **Everything per page works in every mode**: positions are mapped through the slot of the
  page under the pointer (`Viewer.pagePointAt`; a drag stays on the page where it started),
  so selection, double click, links and their hover, highlights and notes (drawn on every page
  on screen, marks multiplied into each page's photo), saved marks, the selection bubble and
  the edit bubble, search hits (all pages on screen; the current hit is scrolled into view),
  the outline, Ctrl+G, history (page and scroll fractions) and the page field work as in the
  single-page view.
* **Render time** (`SAFEPDF_VIEWER_SMOKE_MODE=scroll`, the 15-page `arxiv-1706.03762.pdf` at
  Automatic Zoom 125 % in a 1900×940 window, outline open, Xvfb, scrolled top to bottom with
  wheel notches, every page in view rendered before the next notch): continuous 15 renders,
  3.88 s rendering (≈ 259 ms per page), 3.81 s wall time for 231 notches, at most 4 photos
  alive, peak RSS 236 MiB; the single-page view over the same paper: 15 renders, 3.89 s, 119
  notches, 1 photo, peak RSS 209 MiB. The per-page render cost does not change; the continuous
  modes hold up to three more page photos (≈ 5.8 MB each at this size).

Not done (PDF.js has them): Wrapped and Horizontal scrolling, the per-document memory of the
mode, an animated spinner (the placeholder is a static "Rendering…").

## Rendering on worker threads (8.8)

* `Viewer.submit` starts a page render with `IO.asTask (prio := .dedicated)`: the task runs
  only the pure renderer (`renderDocPage` on the document, or the 9.5g preview, with the
  substitute fonts) and returns the image and its render time. **Tk stays on the main thread**:
  the workers never call Tcl; a `poll` event (`after 15`, `Viewer.pollMs`, scheduled only while
  renders run) takes finished renders (`IO.hasFinished`), puts them into the page cache and
  shows them.
* **Bounded**: at most `Viewer.maxJobs` = 4 renders at once; neighbours and the prefetch leave
  one slot for the current page. A render of a key already running is not started twice (the
  prefetch of the next page and the Next key share it).
* **Short wait, then placeholder**: an event that must show the current page (open, page
  keys, zoom, rotation, view mode, resize) waits for its render at most
  `State.syncWaitMs` = 100 ms, so a typical page (median 64 ms) appears without a flash;
  a slower one shows its white frame with a small grey "Rendering…" (canvas text, tag
  `pwait wN`, after PDF.js's loading state) and the event returns. The status line says
  `rendering...` until the page arrives, then `rendered in N ms`.
* **Stale results**: a result is shown only when the open document (generation), the page's
  zoom and rotation still match its cache key (`Viewer.keyOf`) and the page is still in view;
  otherwise it is dropped (`State.staleDropped`; a result for the open document still goes
  into the cache, e.g. a page that scrolled away). A pure render cannot be interrupted, so a
  stale render keeps its slot until it ends; `Viewer.main` therefore exits the process as soon
  as the window is closed instead of letting the runtime wait for it (the `--biblean` path
  in `Main.lean` still returns normally after its flush).
* Everything per page is unchanged: selection, highlights (multiplied in when the photo
  arrives), search hits, links, bubbles and the overlays work on pages with a photo; the
  overlays are redrawn whenever a page arrives.
* Smoke mode waits for every render (`syncWaitMs = none`, `settle` waits for all running
  renders), so its steps see the pages at once; the `async` case runs with no wait at all.

## The document worker (12.2c, 12.2d)

Since task 12.2c the viewer renders pages and thumbnails, and reads the outline, in a separate
process: the `worker` executable (`SafePdf/Shell/Worker/`, task 12.2a; OS confinement task
12.2b), found next to the viewer (`.lake/build/bin/worker`; `lake build` builds it,
`scripts/viewer-smoke.sh` builds `viewer worker`). The client side is
`Worker.Session` (`SafePdf/Shell/Worker/Client.lean`).

* **One process per open document.** The viewer still reads the file itself (capped at
  `maxInputBytes`, task 12.1) and parses it for the page layout, labels, open settings,
  attachments, layers and Save; the worker gets **the same bytes** in an `openDoc` request, never
  a path. A new file, Close, or a preview of edited saved marks (9.5g, the preview's bytes)
  gives the session a new document id (`State.srcSerial`): the old worker is killed and the next
  request spawns a new one. Save keeps using the bytes the viewer read.
* **Asynchronous, queued.** `Viewer.renderTask` queues a `render` request and returns a task (a
  promise the session resolves), so `poll`, `showNow` and `settle` work exactly as with the
  8.8 render threads and no event waits on the worker's pipes. The worker answers one request
  at a time; the session's dispatcher thread picks the most urgent: priority 0 for the
  current page or spread (and the outline), 1 for other pages in view and the prefetch, 2 for
  thumbnails; a queued neighbour that becomes the current page is raised to 0
  (`Viewer.raiseJob`).
* **Cancellation.** Renders whose result would be dropped (another document generation, or a
  page now laid out at another zoom or rotation; thumbnails of another rotation) are cancelled
  (`Viewer.cancelStale`, at every `poll`, `renderMore`, `showNow`, `settle`): dropped while
  queued; a running one is killed (and the worker restarted for the next request) once it ran
  `preemptMs` = 250 ms. A render that blocks a more urgent one (lower priority, or a current
  page asked for at least 100 ms later) is preempted the same way and queued again. Unlike the
  8.8 threads, a superseded render no longer keeps a CPU busy until it ends.
* **Deadline.** A request (or a spawned worker's `openDoc`) without an answer within
  `Viewer.workerDeadlineMs` = 20 s kills the worker. The page shows, and for the current page
  the status line says, `rendering stopped: the document took too long (no answer within 20 s;
  its worker was stopped)` (cached for that zoom, so it is not retried in a loop); the next
  request spawns a fresh worker and sends the bytes again, and another file opens normally.
  20 s is far above the slowest corpus page (about 3 s) and the slowest decompression bomb
  under the default limits (about 3.3 s).
* **Images are checked** before Tk sees them: `4·w·h` bytes or the page shows an error
  (`Viewer.outOfReply`). Worker errors show their own text (`Viewer.workerErr`, `pageErr`).
* **Outline**: asked for right after the `openDoc` and waited for during the open (after
  labels, attachments and layers are read here); items become `Links.Entry`s with the same
  display rules (`safeText`: controls and bidi overrides as spaces, 500 characters; URIs
  percent-encoded by `Links.uriText`). A worker without an outline answer falls back to the
  in-process outline with a status note.
* **Text, links, layers, fonts and limits (12.2d).** The protocol gained `pageIndex PAGE OC`
  (answered with the viewer's selection/search index: `Select.PageIndex.ofText` of
  `Annot.extractDocPageAnnots` — cells in reading order with text, separator, page-space box
  and line, line directions, hidden flags; CropBox and clip filtering and the layers state
  applied in the worker), `viewLinks PAGE` (`Links.pageLinks`, actions included) and a layers
  state on `render`; all with round-trip and framing proofs (`Protocol.lean`). The viewer
  rebuilds the index (`Viewer.indexOfReply`: search text by `Select.normChars` here) and
  re-checks link strings (`linkOfWire`: URIs and action names must be printable ASCII, else
  percent-encoded again; names through `safeText`; a jump outside the document is `badPage`).
  `submit` asks for the links of every page in view and the text index of the current page
  right after its render (priority 1); pointer motion uses `linksOf`/`pageIndex` with
  `wait := false` and never waits (no link or I-beam until the reply is there); selection,
  copy, search and clicks wait for the reply (raised to priority 0; bounded by the deadline).
  A failed request is cached as an error / no links: the page is then not parsed in this
  process. Startup data are **flags** parsed before `Sandbox.prepare` (the fonts are read
  before confinement and the worker reads no environment; `Protocol.StartConfig`,
  `Viewer.workerStart`): `--limits=HEX` (the viewer's `Limits`, `limitsC` in hex,
  `limitsOfHex_limitsHex`), `--no-subst` (`SAFEPDF_SUBST_FONTS=0`), `--home=DIR` (`$HOME`, for
  `~/Library/Fonts`), `--font-dir=DIR` per `$SAFEPDF_FONT_DIR` entry, `--test-stall-ms=N`,
  and since 12.3 `--mem-limit-mib=N` / `--cpu-limit-s=N` (the resource fences, "Budgets and
  ceilings" below) and `--test-spin-ms=N`; an unknown argument ends the worker with status 5. So the worker searches exactly the fonts the
  viewer would, and no render stays in-process for its layers state or font configuration.
* **Still in this process:**
  * the parse the GUI keeps for layout, page sizes and labels, open settings, attachments, the
    layers panel, the 9.5c marks read from the file and Save;
  * the text index and links while edited saved marks are previewed (`State.view`: the worker
    then holds the preview's bytes, while text and links are read from the opened document);
  * everything, when the worker executable is missing (a build of only `viewer`; the status
    line says `no document worker at …: pages render in this process`) or with
    `SAFEPDF_VIEWER_WORKER=0` (for comparisons). This fallback keeps development builds
    usable; a release should ship the worker and could refuse instead.
  * The macOS FFI shell (`SafePdf/Shell/Ffi`, task 11.x) keeps rendering in-process until 11.2
    decides.
* **Measurements** (macOS, the smoke case 12.2c, medians of 3): page 1 of the two-page fixture
  at 124 % (1014×1312 px) 8.2 ms in-process, 9.1 ms through the worker; page 1 of the
  Transformer paper at 82 % (670×867 px) 64.6 ms in-process, 58.1 ms through the worker. The
  1m `async` case's slow page at 150 % finished after 4.1 s through the worker, 4.3 s on the
  8.8 threads. While a render runs the Tk event loop keeps going: the smoke's 10 ms heartbeat
  never missed more than 16 ms.
* **Test hook** (`SafePdf/Shell/Worker/TestHooks.lean`): `SAFEPDF_WORKER_TEST_STALL_MS=N` in a
  session's test environment (`Worker.Session.setEnv`, only the smoke step) becomes the
  worker's `--test-stall-ms=N` flag: it sleeps `N` ms before every render. The worker's own
  environment stays empty (Lean 4.36's `IO.Process.spawn` crashes the child when
  `inheritEnv := false` comes with a non-empty `env`, and the confined worker refuses one).

## Budgets and ceilings (12.3)

**Published ceilings** (the source is `Budget.ceilings` in `SafePdf/Shell/App/Budget.lean`;
`scripts/interleave.sh` reads its two scenario numbers from there):

| What | Ceiling | Enforced by |
|---|---|---|
| Reserved for work in flight (page renders, thumbnails, text and links requests) | **512 MiB** (`poolBytes`), of which images leave **32 MiB** to text (`textReserve`) | `Budget.Pool`: the invariant `used ≤ ceiling` is a field of the structure (`Pool.used_le_ceiling`) |
| Estimate of one image | `4·w·h` bytes (`imageBytes`; the largest page, 2²⁶ px, is 256 MiB and always fits: `page_fits_pool`) | `Pool.admit` |
| Estimate of one text or links request | **2 MiB** (`textBytes`) | `Pool.admit` |
| Render cache (unchanged, 8.2b) | 256 MiB / 64 entries | `View.Cache` |
| One search (Find Next/Previous) | **400 pages** indexed and **60 s**, shared by all pages it visits (`searchPages`, `searchMs`) | `Budget.Allowance` (`spendAll_le`) |
| Document worker memory | **2048 MiB** (`workerMemMiB`, flag `--mem-limit-mib=`) | Linux: `RLIMIT_DATA` 2048 MiB + `RLIMIT_AS` 4096 MiB; macOS: `phys_footprint` watchdog (see below) |
| Document worker CPU time per request | **60 s** (`workerCpuS`, flag `--cpu-limit-s=`), next to the 20 s wall-clock deadline | `RLIMIT_CPU`, re-armed before every request |
| Interleave scenario, viewer peak RSS | **1024 MiB** (`viewerRssMiB`) | `scripts/interleave.sh` (CI) |
| Interleave scenario, each worker's peak RSS | **512 MiB** (`workerRssMiB`) | `scripts/interleave.sh` (CI) |

* **Reservation before dispatch.** `Viewer.submit` (pages), `thumbView` (thumbnails) and
  `sideJob` (text index, links) ask `Viewer.admit` → `Budget.Pool.admit` before a request
  goes to the worker (or to an in-process render thread). The answer is *reserved* (the
  ticket is kept in the `Job`/`SideJob`), *wait* (a page: `State.budgetWait`, `poll` runs
  `renderMore` again; a thumbnail: later, from `thumbView`; a prefetch text/links request:
  skipped; a text request the user waits for: the GUI waits for the text requests in flight,
  which release theirs), *lowered quality* (a thumbnail rendered at ½, ¼ or ⅛ of its zoom) or
  *refused* (an image larger than the pool: cached as `limitExceeded imagePixels`; cannot
  happen for the viewer's capped pages).
* **Release exactly once.** A render's ticket is released where its job leaves `jobs`
  (`finish`) or `thJobs` (`thumbPoll`) — each job leaves its list once; a text/links ticket
  when its reply is there (`sweepSide`, every `poll` and before every admission), when it is
  answered (`dropSideJob`) or dropped with an old document generation. `Pool.release_reserve`
  (a release gives back the pool before the reservation) and `Pool.release_release` (a second
  release changes nothing) are proven; the interleave scenario checks that the idle viewer
  holds no reservation at the end.
* **One work allowance per search.** `Viewer.nextHit` starts one `Budget.Allowance` per Find
  and spends a page for every page whose text index is not cached; when it is used up the
  status line says `"…": not found in the N pages searched so far (this search's work
  allowance is used up); search again to go on` — the next Find continues past the pages
  indexed (cached) so far. Each page request remains bounded by the worker's deadline and its
  own `Filter.Budget` (the decode budget still starts fresh per page inside the worker).
* **Not in the pool (yet):** the Tk photos of the pages in view and the open document's bytes
  and parse (bounded by `maxInputBytes` and the view's pixel cap, not by the pool), and Save /
  XFDF export (synchronous, outside the pool; follow-up). Measured: with 600 % zoom on every
  page of the 15-page Transformer paper the viewer's RSS reached 4.9 GiB on macOS while the
  pool never exceeded 447 MiB — the photos and the cache, not the work in flight, dominate.
* **Worker fences outside Lean's cost model** (`c/worker_sandbox.c`, `Sandbox.fence`, applied
  before confinement): Linux `RLIMIT_DATA`/`RLIMIT_AS` with soft = hard (an allocation beyond
  them fails and Lean's runtime ends the process); **macOS 26 rejects `setrlimit(RLIMIT_AS)`
  and `RLIMIT_DATA` with `EINVAL` for every finite value and refuses `memorystatus_control` to
  an unprivileged process**, so a watchdog thread reads the task's `phys_footprint` every
  10 ms and ends the worker with status 6 above the ceiling (a fence against runaway inputs,
  not against a compromised worker, for which the client's deadline kill remains).
  `RLIMIT_CPU` works on both (`SIGXCPU`, measured on macOS); its soft limit is re-armed before
  every request to the CPU used so far + 60 s + 1, so a long session is never ended by earlier
  requests. The `worker` test suite checks both fences: a 64 MiB worker asked for a 124 MB
  render ends (exit 6 on macOS) while a 2048 MiB one renders it; a 1 s CPU fence ends a 4 s
  busy request after 2 s (`SIGXCPU`, exit 152) while four 0.6 s requests pass.
* **The interleave scenario** (`scripts/interleave.sh`, smoke mode `interleave`,
  `Viewer.smokeInterleave`; CI job `interleave`): on the Transformer paper (15 pages), 8 rounds
  of zoom in ×4 (75 % → 200 %), a search for `the` and for a word that is nowhere (every page
  indexed under one allowance), the thumbnails panel scrolled, two page changes and zoom
  out ×4, with 250 ms of event loop after each step; the sampler reads `ps` RSS (and VmHWM on
  Linux) of the viewer and of every worker every 0.2 s. macOS 26 (arm64), 2026-11-23: viewer
  peak 703 MiB, 10 workers (preemption kills and respawns them), worker peak 129 MiB, pool
  peak 22 MiB, nothing waited, lowered or refused, pool empty at the end; 34 s.

## Highlights and notes (9.4)

Pure model in `SafePdf/Shell/App/Marks.lean` (Tk-free, `#guard` checks, `Store.add_id` /
`Store.add_next`: ids are never reused). Marks are kept **in memory** per open document in
this task (closing or opening a file drops them); saving them into the PDF as annotations by
incremental update is tasks 9.5b/9.5c, and the model is shaped for it: every mark has a
stable id (`/NM` = `Mark.nm` = `safepdf-mark-ID`), a page, a colour (`Color.unit` = `/C`)
and page-space geometry (`Mark.quadPoints` in the upper-left, upper-right, lower-left,
lower-right order PDF.js and Acrobat use; `Mark.rect`; `Store.restore` re-inserts a mark read
back from a file with its own id).

* **Colours**: PDF.js's highlight palette (`web/app_options.js`, `highlightEditorColors`):
  yellow `#FFFF98` (default), green `#53FFBC`, blue `#80EBFF`, pink `#FFCBE6`, red `#FF4F5F`.
  The colour menus (Edit → Highlight colour, the context menu's Highlight cascade) show a
  swatch per colour and share one radio variable (`::safepdf::hlColor`): the checked colour is
  the current one (the Highlight pop-over's swatches set it too, 9.8).
* **Highlight**: select text (drag, double-click, Ctrl+A), then the toolbar's Highlight
  button, `h`, Edit → Highlight selection, or a colour in a colour menu (which also makes it
  the current colour). The quads are the selection's C3 glyph boxes, one per line run
  (`Select.rangeBoxes`), in page space. The new highlight is selected and the text selection
  cleared, as in PDF.js.
* **Drawing**: highlights are **multiplied into the page image** (`Marks.composite`; the
  cached render stays clean, the composite is put into the photo on every show), because
  PDF.js draws highlights with `mix-blend-mode: multiply` at fill opacity 1
  (`web/draw_layer_builder.css`, `src/display/editor/highlight.js`): white paper takes the
  colour and the glyphs stay black. A Tk canvas has no alpha; a stipple (as the selection
  uses) would be a 50 % dot pattern that lightens the text and looks nothing like PDF.js, so
  blending into the pixels is the closest match. Notes, the dashed outline of a note's
  anchor text and the selected mark's outline (`#0060df`, PDF.js's selected-editor blue) are
  canvas items (tag `mark`) drawn below the selection and search highlights.
* **Notes**: Add note… (Edit menu, no click position: a comment on the selection if there is
  one, else on the selected highlight's comment, else a point note at the window centre;
  context menu: a note at the right-clicked point, unless the click is inside the selection's
  highlight boxes, which makes it a comment on the selection — a click on an empty spot far
  from the selection never turns the selection into a comment, task 10.17,
  `Marks.noteAnchor`; the selection bubble's Add comment has no click position, so it
  comments on the selection) adds a yellow note and opens its
  popup (a small window: text, Delete, Save (Ctrl+Return), Cancel/Escape; closing it is
  described below). A note shows as a
  speech-bubble icon of 20 × 20 page units (the size of a `/Text` annotation icon; it scales
  with the zoom as in PDF.js), its upper-left corner at the point, or right of the first
  quad for a note on text (whose quads get a dashed outline); the icon is kept inside the page.
  The text enters Tk by variable substitution and comes back as one event word, never parsed
  as script.
* **Closing a note popup without Save** (9.r12) — Escape (also while the cursor is in the
  text), Cancel or the window's close button — follows one rule (`Marks.Store.onUnsavedClose`):
  a note that already has a text keeps it and the popup's edits are discarded, even when the
  popup was cleared; a note without a stored text (new, or saved empty) gets the popup's text
  when that has more than white space (as Save), and is otherwise **deleted**, through the
  same path as the popup's Delete: a saved note's removal is an unsaved change (`*` in the
  title), an empty highlight comment goes and its highlight stays, no icon is left. The same
  holds for every way the popup opens (Edit → Add note…, the context menu, the bubble's Add
  comment, a click on a note). Opening another note's popup closes the open one by this rule
  (reopening the same note keeps its popup and edits); deleting a note (or its highlight)
  while its popup is open closes the popup.
* **Selecting, recolouring, deleting**: a click (press and release in place) on a mark selects
  it (icons before highlights, the newest first, except that a highlight wins over its comment
  on its quads (9.8); marks before links) and a note's click
  opens its popup; a right click on a mark selects it, on empty paper deselects. A colour
  entry recolours the selected highlight; **Delete**, Edit → Delete mark or the context menu's
  Delete mark removes it (the note popup's Delete removes its note).
* Marks are stored in page space, so they follow zoom, rotation and page changes; a page's
  marks are drawn whenever it is shown.

Not done here: free (drawn) highlights, undo. Saving: next section (9.5c). The selected-mark outline
is drawn per quad (PDF.js outlines the union shape).

| Key / mouse | Action |
|---|---|
| `h`, toolbar Highlight | highlight the selection in the current colour (toolbar without a selection: Highlight tool on/off, 9.8) |
| click on a mark | select it (a note opens its popup) |
| `Delete` | delete the selected mark |
| right button | menu: … Highlight ▸ colours, Add note…, Delete mark |

## Saving marks into the PDF (9.5c, 9.5g, 9.r2, 9.r6)

Tk-free flow and decisions in `SafePdf/Shell/App/Save.lean` (`#guard` checks), driven by
`Viewer.save`, `overwriteInto`, `saveAs`, `saveTo` and `confirmDiscard`. Plan.md S8/C7 (S8
amended by the Decision of 2026-11-23): the marks become annotation objects appended to the
file as an **incremental update**; the original bytes stay unchanged at the start of the file
(its first revision).

* **Save** (Ctrl+S, File → Save, the toolbar's Save) writes the marks **into the opened file**
  (9.r2; `Save.route`). Before the first overwrite of a session it asks **Overwrite / Save
  As… / Cancel** (`Save.overwriteQuestion`: the marks are added to the file itself, its present
  content is kept unchanged inside it as the first revision; Save As… writes a new file
  instead); after that (and for a file this session wrote with Save As…) Save is silent. Save
  is enabled only while there are unsaved changes (new marks, saved marks changed or
  deleted); with none, Ctrl+S says "nothing to save". A document opened from memory without a
  library goes to Save As…; a library's document to the library (below).
* **Overwriting, step by step** (`Viewer.overwriteInto`): (1) the bytes are built and checked
  (`Save.build`, below) — an encrypted or repaired document is refused here, before any
  question; (2) a read-only file or a folder we cannot write into is refused with a status
  message (`Save.writeProblem`; the rename would otherwise replace a read-only file); (3) the
  file on disk must still hold exactly the bytes the document was opened from (`Save.diskState`:
  size, then a full comparison) — if another program changed, moved or deleted it, nothing is
  written and the dialog **File changed on disk** offers Save As… / Cancel; (4) the
  first-overwrite question; (5) the disk check once more, then `Save.writeAtomic` on the
  resolved path (a symbolic link stays a link to the updated file): a fresh temporary file
  `.NAME.safepdf-N.tmp` next to it, read back and compared, given the original's permissions
  (Tcl `file attributes -permissions`; owner and group are those of the writing user), renamed
  over the file — a crash leaves the old or the new file, never a partial one; (6) the file is
  reopened in place on the same page, so the viewer works on the new bytes and a second Save
  is a further revision.
* **Save As…** (Ctrl+Shift+S) asks for a file (`tk_getSaveFile`, which confirms replacing an
  existing file), proposing `STEM-annotated.pdf` in the opened file's folder (its home folder
  when that folder is gone or not writable, and for a document from memory — 9.r6,
  `Save.dialogDir`), writes a new file (a file it replaces keeps its permissions) and opens
  it; choosing the **opened file** needs an explicit yes (after the dialog's own replace
  question) and then goes through the overwrite steps above. With no unsaved marks it writes
  a plain copy.
* **The chosen file is checked** (9.r6, `Viewer.checkTarget`): a name not ending in `.pdf`
  (any case) gets `.pdf` (`Save.withExt` — Tk's X11 dialog appends `-defaultextension` only
  to names without a dot, so `3453483.3454032-final` came back bare); if that names an
  existing file the dialog did not confirm, **Replace it?** is asked. A folder, an existing
  read-only file (a rename would replace it) and a folder we cannot write into are refused
  with `cannot save: …` (`Save.targetProblem`); nothing is written, the marks stay unsaved.
  The temporary file's name cuts `NAME` to 100 bytes (`Save.tmpName`), so a name near the
  255-byte limit saves. Write errors (disk full, the folder removed meanwhile) appear on one
  line (`Save.oneLine`) and leave no temporary file.
* **Dialog options** (`Save.saveDialogOptions`): `-defaultextension .pdf -confirmoverwrite 1`
  and, on X11/Windows, `-filetypes {{PDF files} {.pdf .PDF}} {{All files} *}`. **On aqua no
  `-filetypes`**: Tk 9's `tk_getSaveFile` builds its **Format:** accessory view from them with
  a pop-up 340 pt wide at x = 50 inside a 300 pt view (`macosx/tkMacOSXDialog.c`,
  `Tk_GetSaveFileObjCmd`, the same in 9.0.x and on Tk's main branch of 2026-11-21), so the
  pop-up always ran past the panel's right edge (the human's screenshots
  `docs/viewer-reference/macos-save-as.png`, `macos-export-annotations.png` — even the short
  `XFDF (.xfdf)` overflows: the labels are not the cause). Without `-filetypes` Tk shows no
  accessory view and still restricts the panel to the `-defaultextension` type (other types
  allowed on request). Open… and Import keep their filters (Tk's open panel uses a 240 pt
  pop-up inside its 300 pt view); they start in the opened file's folder (9.r6; Open… with
  no document open keeps Tk's choice) and a cancelled Open… says `open cancelled`.
* **Dialogs**: the three-way questions are `::safepdf::choose` (a modal Tk dialog; the default
  button has the focus first; Return or keypad Enter presses the **focused** button — 9.r6:
  it used to run the default even after Tab to Cancel —, Space too, Escape and the close
  button Cancel; the focus goes back where it was). Button order (`Save.unsavedButtons`,
  `Save.overwriteButtons`, `Save.changedButtons`): Save / Don't Save / Cancel and Overwrite /
  Save As… / Cancel left to right on X11 and Windows; on aqua the macOS order — Don't Save
  (Save As…) leftmost, Cancel, the default rightmost.
* **What is written** (9.5g: one update with additions, supersessions and removals,
  `Save.edits` → `Annots.writeEdits` → `Incremental.writeUpdate`, writer rule W11): the file's
  own marks are scanned (`Save.scan`: object reference, popup, comment, `/CreationDate`) and
  compared with the store. Marks not in the file are **added**; marks whose colour, text or
  comment changed are **superseded** — their annotation object is written again under its own
  number and generation (ISO 32000-2 §7.5.6) with a fresh appearance stream and the original
  `/CreationDate`; annotations of deleted marks are **removed** from their page's `/Annots`
  (a highlight's popup with it). The old objects stay in the earlier revision. Marks are
  converted by `Save.toCore` (quads, a note's icon box as `/Rect`, `/C`, `/Contents`,
  `/NM safepdf-mark-ID`, `/M` = the current UTC time `D:YYYYMMDDHHmmSSZ`; **no author** `/T`,
  so the login name never ends up in the file). A highlight's comment (the note on its quads
  with a text, `Store.commentOf`, 9.8) is written **into the highlight** as pdf.js does:
  `/Contents` + a `/Popup` annotation whose `/NM` is `safepdf-mark-ID-popup-CID` (CID = the
  comment note's id, so it comes back with the same id). Files saved by 9.5c builds, with the
  comment as a separate `/Text`, are still read; that `/Text` is removed and the comment moved
  into the highlight on the next save that touches the highlight or the note.
* **Checked before anything is written**: the result must start with the original bytes, must
  reopen through the **strict** parser (`Api.openBytes`, repair refused), and reading our
  marks back must give every mark of the store (page, kind, colour, text, geometry within
  1/500; a comment takes its highlight's colour), each written one exactly once, and no
  deleted one. Then the bytes go to a fresh temporary file in the same
  directory, which is renamed over the target (never truncated in place; on failure the
  temporary file is removed). The written file is then opened in place of the old one, on the
  same page (selection, search and history are reset as on any open).
* **Reopening**: on open, the annotations with `/NM safepdf-mark-ID` are read back
  (`Save.readMarks`): `/Highlight` → highlight over its `/QuadPoints` (with a non-empty
  `/Contents` also its comment: a note on the same quads, id from the popup's `/NM` or, for a
  popup without one, a fresh id after all others), `/Text` → note with
  `/Contents` anchored to its `/QuadPoints` or its `/Rect`'s upper-left corner, colour =
  nearest palette colour to `/C`; they are restored with their ids (`Store.load`) and count as
  saved. Saved marks are **drawn by the renderer** from their appearance streams (so they are
  not multiplied in again and their note icons are not canvas items); they can be selected and
  a note's popup shows its text. Other annotations are only rendered.
* **Saved marks are editable** (9.5g): recolour (Highlight menu, pop-over swatch, edit
  bubble), Delete (deleting a highlight also deletes its comment) and note text edits work
  on them as on new marks and make the document dirty (`Store.changedSaved`,
  `Store.deletedSaved`, compared with `Store.base`, the marks as in the file). Since saved
  marks are drawn by the renderer, the pages are then rendered from a **preview**
  (`State.view`, `Viewer.updatePreview`, `Save.preview`): the opened document with only the
  edits of saved marks applied by the same writer in memory and reopened strictly; the next
  Save writes from the opened document, not from the preview. A comment written into its
  highlight has no appearance of its own, so its icon is a canvas item. "Show all" off hides
  only unsaved highlights.
* **Unsaved changes** (9.r2): the title starts with `* `; every way a document goes away asks
  **Save / Don't Save / Cancel** (`Viewer.confirmDiscard`, `Save.unsavedQuestion`): Close
  (Ctrl+W, File → Close), Quit (File → Quit, Ctrl+Q, the window's close button
  `wm protocol . WM_DELETE_WINDOW`, and on macOS the application menu's Quit / Cmd+Q through
  `proc ::tk::mac::Quit`) — all quitting goes through the one Tcl proc `::safepdf::quit` —,
  and Open… (another file). Save saves (into the opened file without a second question, since
  the prompt says so; to the library in bib-lean mode; through Save As… for a document from
  memory) and then goes on; Don't Save discards the marks and leaves the file untouched;
  Cancel, or a Save that fails or is cancelled, keeps the document open (`Save.closeGoesOn`).
  Nothing is ever saved without this answer.
* **Errors** (an encrypted document, refused by the writer until 9.5f; a document opened
  through the repair path; a failed check; a write error) appear in the status line as
  `cannot save to NAME: …` (a read-only file or folder: `cannot save: NAME is read-only…`; a
  file changed on disk: `not saved: NAME changed on disk…`); nothing is written and the marks
  stay unsaved.

## Add text and Draw (9.9)

PDF.js's FreeText and Ink editors (`src/display/editor/freetext.js`, `ink.js`, the parameter
toolbar of `web/viewer.css` `.editorParamsToolbar`; nothing copied). Pure state in
`Bubble.lean` (`Ui.editor`, `Ui.selectEditor`, `EdPop` layout and `Slider`s; theorem
`Ui.selectEditor_exclusive`: one tool at a time), marks in `Marks.lean` (`Kind.freeText`,
`Kind.ink`, `Store.translate`, `setRgb`, `setSize`, `setOpacity`, `addStroke`), writing in
`Core/Write/Annots.lean` (rules A12–A15).

* **Modes.** The toolbar's Add text and Draw buttons turn their mode on (button toggled, the
  Highlight tool off) with a parameter pop-over `.edbar` under the button: *Font color* +
  *Font size* (5–100, default 10) for text; *Color*, *Thickness* (1–20, default 1) and
  *Opacity* (5–100 %, step 5, default 100 %) for drawing. PDF.js shows a native colour input;
  here the colour is a row of six swatches (black — PDF.js's default —, red, blue, green,
  orange, purple), so it can be driven and tested deterministically. A second click on the
  button ends the mode; Escape closes the pop-over and ends a drawing session.
* **Add text.** A click on the page opens a text box: a Tk text widget in a canvas window
  (tag `ftedit`) with its upper-left corner at the click, Helvetica at font size × zoom in
  the chosen colour; typed keys stay in it (own bind tags). A click elsewhere, Escape, a tool
  change, Save, Close or Quit commit it: a free-text mark (an empty box is dropped). A double
  click on a text box opens it again with its text (emptying it deletes it). Unsaved text is
  drawn as canvas text items with the first baseline where the appearance stream puts it.
* **Draw.** Each press–drag–release draws a stroke (canvas line `inkcur`, points at least one
  pixel apart, in page space). The strokes of one session — until Escape, the end of the
  mode, or a stroke on another page — form one ink mark (PDF.js groups them in one editor).
  Unsaved drawings are canvas lines with round caps (opacity shown with a stipple).
* **Select, move, edit, delete.** A press on a text box or drawing selects it (blue outline,
  the editor bubble with Delete) and dragging moves it (canvas items follow; on release
  `Store.translate`); the pop-over's colour and sliders apply to the selected mark of the
  mode's kind (as PDF.js applies parameters to the selected editor); Delete or the bubble's
  Delete removes it. Saved ones are drawn by the renderer from their appearance streams, so
  an edit of a saved one goes through the preview (9.5g) and Save supersedes its annotation
  (W11). **Exception (task 9.r5):** a saved free text's appearance uses the non-embedded
  standard-14 Helvetica, which the renderer paints only with a substitute font program (7.7,
  `Shell/Fonts.lean`: URW base-35 or TeX Gyre files). Where none is found — macOS without
  those fonts, the human's setup in the 2026-11-23 review — the reopened text box was
  invisible until a double click opened its editor; now `drawMarks` draws saved free text on
  the canvas like unsaved free text whenever `State.paintsHelvetica` is false (turned with the
  page rotation via Tk's `-angle`). Smoke: `m9-reopen` reports `screen-text` (red pixels in
  the text box on an X screenshot of the canvas, before any click) and `screen-after` (after
  Page Width, a page change, rotation 90° and back, vertical and single page mode); the script
  runs it with and without substitute fonts. Since task 9.r7 a stock Mac has a substitute
  Helvetica too (`/System/Library/Fonts/Helvetica.ttc`, `docs/raster.md`), so there the
  renderer paints saved free text and this canvas fallback is not used.
* **In the PDF** (rules A12–A15 of `Core/Write/Annots.lean`, as pdf.js
  `FreeTextAnnotation`/`InkAnnotation.createNewDict`): `/FreeText` with `/Contents`, `/DA
  (/Helv SIZE Tf R G B rg)`, `/Rect` = the text box (`freeTextBox`: Helvetica AFM widths,
  line height 1.35 × size, 2 pt padding), `/F 4`, `/Border [0 0 0]`, an appearance stream
  with a `/Helv` standard-14 resource (Helvetica, WinAnsiEncoding, nothing embedded);
  `/Ink` with `/InkList` (one array per stroke), `/BS /W`, `/C`, `/CA` below 1, an appearance
  stream with round caps and joins. **Characters outside WinAnsi** (e.g. ✓, CJK) are kept
  exactly in `/Contents` (UTF-16BE) — what readers extract and what we read back and edit —
  while the appearance stream draws `·` in their place (the gap is visible; MuPDF's
  replacement character). pdf.js writes no appearance at all in that case and relies on the
  reader's fonts; we keep one so viewers that do not synthesise FreeText still show the text.
  Our renderer paints the non-embedded Helvetica with the substitute fonts (7.7).
* **Reopen**: our `/FreeText` and `/Ink` annotations (`/NM safepdf-mark-ID`) come back as
  marks (`Save.markOf`: text from `/Contents`, size and colour from `/DA`, position from
  `/Rect`'s upper-left corner; strokes from `/InkList`, width `/BS /W`, colour `/C`, opacity
  `/CA`).
* **XFDF**: `<freetext>` with `<contents>` and `<defaultappearance>`, `<ink>` with
  `<inklist><gesture>x,y;x,y;…</gesture></inklist>` and `width`/`opacity` (export and import;
  the samples' pdf.js- and Okular-style elements now import).
* **bib-lean**: the reader contract has the kinds `text` and `ink` (§4.1), so they are posted
  (`text`: the box, the text, `extra {"fontSize"}`; `ink`: the box, `extra {"inkList",
  "width", "opacity"}`) and restored.

Not done: the text box is upright in page space (no `/Rotate` for rotated views, which PDF.js
writes); no rich text; strokes are straight segments (PDF.js smooths them into Béziers); no
resize handles; the colour is a fixed palette.

## XFDF import and export (9.11)

XFDF (ISO 19444-1) is interchange only — the marks live in the PDF (9.5c). The Tk-free reader
and writer are `SafePdf/Shell/App/Xfdf.lean` (9.5d; `#guard`s and the suite `xfdf`).

* **File → Export annotations…** (also in the toolbar's `»` menu) asks for a file
  (`tk_getSaveFile`, `Save.saveDialogOptions`: filtered to `{{XFDF} {.xfdf .XFDF}} {{All
  files} *}` except on aqua, proposing `STEM.xfdf` next to the PDF, `Viewer.xfdfTarget`), checks
  it like Save As… (9.r6: `.xfdf` added when missing — so choosing the opened `NAME.pdf`
  writes `NAME.pdf.xfdf` instead of replacing the PDF with XML, as it did before; never onto
  the opened document, a folder or a read-only file) and writes every mark of the document — saved or not —
  through `Save.writeAtomic` (temporary file + rename): `<highlight>` with `coords`,
  `<text>` for notes, page boxes from the document, `date` now, `<f href="NAME.pdf"/>`.
  **A highlight's comment** is written in the standard form, as `<contents>` of the
  `<highlight>` followed by `<popup … name="safepdf-mark-H-popup-C" open="no"/>` (the popup
  name carries the comment note's id, like the popup's `/NM` in the PDF since 9.5g); like in
  the PDF, the comment has no colour of its own (its highlight's). Other notes — anchored to a
  point, empty, or older notes on the same quads — stay `<text>` elements (ours carry a
  non-standard `coords` attribute with their quads, ignored by other readers). Status:
  `exported N mark(s) to FILE`; a write error: `cannot export to FILE: …`.
* **File → Import annotations…** (also in `»`) asks for a file (`tk_getOpenFile`, same
  filter) and reads it with `Xfdf.readFile` (size checked before reading; no DTD, only the
  five predefined entities, depth/attribute/length/node limits; pages checked against the
  document). Highlights (with a `<contents>`/`<contents-richtext>` comment → a comment note on
  the same quads), and text notes (9.5d's separate comment `<text coords>` included) become
  **unsaved** marks (`Xfdf.importItems`: a mark equal to one already present is not added
  again; our ids are kept when never used in this document; the added marks follow in id
  order), drawn at once; the title gets its `* `. Status: `FILE: N imported, D already
  present, S skipped` (plus the first skipped element and why: other annotation types,
  replies, pages not in the document). A refused or unreadable file — billion laughs, XXE, an
  unknown entity, a non-XFDF root, a missing file — shows `cannot import FILE: <reason>` and
  changes nothing.

## Selection bubble and Highlight pop-over (9.8)

Pure logic in `SafePdf/Shell/App/Bubble.lean` (Tk-free, `#guard` checks; theorems
`place_inside`: a placed bubble stays inside its area, `Ui.escape_closes`). Reference: PDF.js
`src/display/editor/toolbar.js` (`FloatingToolbar`, `EditorToolbar`), `color_picker.js`,
`highlight.js` and `web/annotation_editor_layer_builder.css` (`.editToolbar`, `.colorPicker`,
`#highlightParamsToolbarContainer`), fetched read-only; nothing is copied, everything is drawn
with Tk canvas items; colours sampled from the Firefox screenshot
`docs/viewer-reference/pdfjs-firefox.png` (icons `#6a5b92`, borders `#d0cfd5`, accent
`#6b45d3`).

* **Float bubble**: after a text selection (mouse-up of a drag, a double click, Ctrl+A) a
  small rounded bubble with the Highlight icon and, after a divider, **Add comment** (9.r4:
  the toolbar's note icon); its right edge is at the end of the lowest
  selected line and its top 6 px below it (PDF.js `#getLastPoint`,
  `--editor-toolbar-vert-offset`), above the selection when it would leave the scroll region
  at the bottom, and clamped into it (`Bubble.place`). Clicking it highlights in the current
  colour (Edit → Highlight selection's script, `Bubble.Btn.cmd?`). Add comment runs Add
  note… (the toolbar's Add comment, Edit → Add note…): a note anchored to the selection's
  quads, its popup opened for typing; the selection and with it the bubble go away. Both
  buttons show a tooltip (Highlight, Add comment) after 600 ms over them, as toolbar buttons
  do (each button has a white hit area under its icon, tag `b:NAME`; `Bubble.Btn.tip`). The
  wider bubble (67 px) is placed and clamped as before (`place_inside` holds for any size).
* **Edit bubble**: on a selected highlight (after creating it, or a click on it): the colour
  swatch with a chevron, Comment and Delete, separated by dividers. The chevron opens the
  colour picker (five swatches in a column under the button, the highlight's colour ringed;
  above the bubble when it does not fit below); a row recolours the highlight. Comment opens
  the highlight's note (the note anchored to exactly its quads, `Marks.Store.noteOn`) or adds
  one in its colour (`Viewer.addNote`; Edit → Add note… on a selected highlight does the
  same); Delete removes the highlight (Edit → Delete mark's script). On its quads a commented
  highlight is selected before its note; the note is reached through its icon.
* Bubbles are canvas items (tag `bub`) in canvas coordinates, so they scroll with the page;
  every redraw (zoom, rotation, page change, mark change) places them again. They go away on
  Escape, on a click elsewhere (which clears the selection and the selected mark) and on a page
  change. A press on a bubble is not a text selection; nor is the second click of a double
  click on it.
* **Highlight tool and pop-over**: the toolbar's Highlight button without a selection (or Edit
  → Highlight tool) turns the tool on — the button looks toggled — and opens the pop-over under
  the button, right-aligned with it (a canvas `.hlbar` placed over the window): "Highlight
  color" with the five 24 px swatches (the current one ringed; a click makes it current and
  recolours a selected highlight, as PDF.js applies parameters to the selected editor),
  "Thickness" with the small and large example dots and a slider 8–24 (default 12; press or
  drag; the value is kept in `Bubble.Ui.thickness` for free highlights, a later task), a
  divider, and the "Show all" switch, which hides all highlights of the page view (the page
  image is composited without them; notes stay; a hidden highlight cannot be selected) and
  shows them again (also Edit → Show all highlights). While the tool is on, a mouse-up that
  leaves a selection (drag or double click) highlights it at once, as PDF.js does. Escape
  closes the pop-over (the tool stays on); the button turns the tool off. With a selection the
  button highlights it instead (as in 9.4), without toggling the tool — PDF.js also switches
  to the highlight mode there.

Not done (visible differences from the reference): Tk on X11 draws no antialiasing and no
real shadow (a 2 px offset grey shape stands in), so the pill-shaped bubble and the round
swatches have jagged edges; the bubble buttons have no hover background (tooltips since
9.r4); the
pop-over is a rectangle window, so its rounded corners show the canvas colour behind them
(`#f0f0f4`); the toolbar's toggled Highlight button is grey, not PDF.js's lavender; fonts are
Tk's default; a comment is a separate note mark anchored to the highlight's quads (PDF.js
keeps the comment in the highlight annotation), so deleting the highlight leaves its note.

| Key / mouse | Action |
|---|---|
| mouse-up after selecting | float bubble (with the Highlight tool on: highlight at once) |
| bubble buttons | after a selection: Highlight, Add comment (9.r4); on a highlight: colour ▾ (picker), Comment, Delete |
| toolbar Highlight without a selection | Highlight tool and pop-over on / off |
| `Escape` | close the pop-over and the picker, dismiss the bubble (clears the selection and the selected mark) |

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
* The selection is drawn over the page image (mapped back with `Geom.toScreen`; the page is
  not re-rendered) as a **continuous light-blue fill** as in PDF.js and Preview (task 10.18,
  `Select.selBands`): one band per selected line, spanning the line's full height (lowest to
  highest glyph box of the whole line); the first line from the selection start to the line's
  end, interior lines from the line's start to its end, the last line from its start to the
  selection end (a single line from the start glyph to the end glyph). Consecutive bands are
  joined, both edges moved to the middle of the gap, when both lines are left-to-right
  horizontal, the layout puts a plain line break (`"\n"`) between them (never across a
  paragraph break `"\n\n"` or a column change) and the gap is at most the smaller band's
  height. Bands only grow, so tightly set lines whose bands overlap stay as they are; rotated
  and vertical lines keep their selected glyphs' run box (`Select.rangeBoxes`) and are not
  joined. Band edges are rounded to the nearest pixel, so joined bands share a pixel edge. The
  bands are translucent photo items (`::safepdf::tint`, `#3874f2` at 35 %) on **both**
  platforms; copy and search ranges are unchanged. Checked by `#guard`s in `Select` and the
  theorems `shape_covers`, `bandAt_covers` (bands cover every selected glyph box) and
  `bandAt_meet` (joined bands meet), and by smoke case 10.10 (`sel-bands`). **Highlight
  rendering** (task 10.10): on X11 the search hits are canvas rectangles stippled 50 %
  (`-stipple gray50`; hits yellow, the current hit orange). Tk Aqua has no
  stipples (they used to be outlines there), so on macOS each box is a canvas **image item
  showing a translucent photo** (`::safepdf::tint`): the colour at alpha 35 % for the
  selection (`#3874f2`, over white ≈ `#b9cefa`) and 50 % for hits (`#ffff00`, current
  `#ffa500`), `Viewer.Tint`. Tk composites the photo's alpha over the page image, so glyph ink
  stays visible and paper is tinted. One photo per colour, alpha and pixel size is shared by
  every box of that size (smoke case 10.10 allows at most 12 photos for 561 hits of one word); after each overlay
  redraw `::safepdf::tintGc` deletes the photos no item shows (`image inuse`). A single
  page-sized overlay image composited in Lean was rejected: it costs O(page pixels) per redraw
  (≈ 150 ns/px for Lean compositing, ~130 ms on a 612 × 792 pt page at 133 %, on every drag
  motion), the per-box photos O(boxes). X11 keeps the stipples for search hits (Tk's X11 alpha
  blending reads the window back per redraw, and a page can have hundreds of hits; the
  selection is one band per line); switching it is the `State.stipple` flag. User
  highlight marks are not affected (multiplied into the page image, below); unsaved drawings
  with an opacity below 88 % are stippled on X11 and opaque on Aqua.
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
| right button | menu: Copy, Select all, Find…, Highlight ▸, Add note…, Delete mark, … |
| `Ctrl+F` | open the find bar |
| `Enter`, `F3` / `Shift+Enter`, `Shift+F3` | next / previous hit |
| `Escape` (in the find bar) | close the find bar |

## Outline, links, history, page labels (8.2d)

Pure logic in `SafePdf/Shell/App/Links.lean` (Tk-free, `#guard` checks and theorems); all
data comes from the verified navigation layer `Core.Doc.Nav` (task 4.2: visited sets cut
outline and name-tree cycles, every walk is bounded by the object count).

* **Outline panel**: a tree in the left pane of a paned window (restyled after PDF.js in 9.7, see above; drag the sash to
  resize). It opens automatically when the document has an outline (and no page mode says
  otherwise); **F9**, the sidebar button or the right-button menu toggle the sidebar. Items come from `Nav.outline` (flat preorder list
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
| `F9` | show / hide the sidebar (outline, thumbnails) |
| click on a thumbnail; Up / Down + Return in the thumbnails | go to that page |
| click on an outline item | go to its destination |
| pointer over a link | hand cursor, target in the status line |
| click on a link | internal: jump; URI: confirmation dialog (copy the address) |
| `Alt+Left` / `Alt+Right` | back / forward |
| `Ctrl+G` | go to a page label or number |

Not done: launching a browser (the address can only be copied), remote destinations
(`/GoToR`), the `/XYZ` zoom, link borders/highlighting (`/H`), keyboard focus traversal of
links. Continuous scrolling: see *View modes (9.3)*.

## Structure

| File | Role |
|---|---|
| `c/tk_shim.c` | Tcl interpreter, Tk init, `::safepdf::emit` → Lean callback, `Tk_PhotoPutBlock` from an RGBA `ByteArray`, event loop. Adapted from bib-lean's `c/tk_shim.c`. |
| `SafePdf/Shell/App/Shim.lean` | `@[extern]` bindings and the exported dispatcher `safepdf_gui_dispatch`. Only the `viewer` executable may import it. |
| `SafePdf/Shell/App/Tcl.lean`, `TclLemmas.lean` | Tcl scripts as data and the proof that `Tcl.quote` is injection-free (`parseWordStr_quote`, `parseScript_render`, …). Copied from bib-lean `BibLean/Gui/Tcl.lean` + `Tcl/Lemmas.lean`. Built by default (lib `SafePdfApp`). |
| `SafePdf/Shell/App/View.lean` | Tk-free viewing logic with `#guard` checks: zoom modes/steps/cap, C2 re-anchoring (`reanchor`, `reanchor_self`), Tcl number parsing, wheel scrolling across pages (`wheelStep`, `wheelPages`, 9.2, 9.r1), view modes (9.3: spreads, paging by spread, page layout, visible and wanted pages, page at a point, scroll positions, fit box; theorems `mem_spreadPages`, `nextPage_spread`, `stack_pairwise`), the LRU page cache. |
| `SafePdf/Shell/App/Select.lean` | Tk-free selection and search logic with `#guard` checks: glyph cells in reading order (`cellsOf`, text equal to `Text.layout`'s), boxes, nearest glyph, drag range, word, copy text, highlight boxes, normalised search with hits mapped back to glyphs (`findAll_sound`). Lib `SafePdfApp`. |
| `SafePdf/Shell/App/Links.lean` | Tk-free navigation logic with `#guard` checks: PDF text strings, URI display (`uriText_ascii`), destinations and their positions, page links with URIs, topmost link at a point, outline entries and treeview parents, page-label display and Ctrl+G lookup, back/forward history (`History.back_push`). |
| `SafePdf/Shell/App/Menu.lean` | Tk-free command and menubar model with `#guard` checks: commands (label, accelerator, script, enabled rule), menus, entry indices (task 9.1); mark commands, colour cascades and the context menu's mark entries (task 9.4). |
| `SafePdf/Shell/App/Marks.lean` | Tk-free model of highlights and notes with `#guard` checks: PDF.js colours, marks with stable ids and `/NM` names, quads and `/QuadPoints`, note icon boxes, the store (add, remove, recolour, edit, restore), hit-testing, the multiply blend into the page image (task 9.4). |
| `SafePdf/Shell/App/Save.lean` | Tk-free save flow (task 9.5c) with `#guard` checks: marks → `Core.Write.Annots.Mark`, PDF dates, reading our marks back from a document, the read-back check, default target, atomic write. |
| `SafePdf/Shell/App/Bubble.lean` | Tk-free selection bubble and Highlight pop-over logic with `#guard` checks: bubble kinds and button layout after PDF.js (float bubble: Highlight and Add comment since 9.r4), placement at the selection's last point with clamping (`place_inside`), hit-testing, the colour picker, the pop-over layout and hits, thickness slider mapping, tool state (task 9.8). |
| `SafePdf/Shell/App/Toolbar.lean` | Tk-free toolbar model after PDF.js with `#guard` checks: layout of the three groups, buttons and their enabled/visible rules, tools, overflow menu, all enabled-state targets, page-field text and parsing, zoom choices (labels, keys, Automatic Zoom rule) (task 9.7), the view-mode drop-down's choices (`ViewChoice`, theorems `ofModes_modes`, `modes_ofModes`; task 9.r4). |
| `SafePdf/Core/Doc/OpenSettings.lean` | The document's open settings (task 9.r8; pure, total, verified-core rules): `/PageLayout`, `/PageMode`, `/OpenAction` as a destination or GoTo only, `/ViewerPreferences`, `/Info /Title`; the zoom of a fit, the outline rule; theorems `read_dest_page`, `titleOf_le`, `zoomOf_percent_bounds`; | `SafePdf/Core/Doc/Attachments.lean` | Embedded files (task 9.r10; pure, total, bounded): the `/EmbeddedFiles` tree and `/FileAttachment` annotations, sanitized names and default file names, sizes, MIME types, dates, decoding under the limits; theorems `list_entries_le`, `clean_safe`, `clean_length_le`, `fileNameOf_noSlash`, `decode_size_le`; tests `Tests/Attachments.lean`. |
| `SafePdf/Shell/App/Attach.lean` | Tk-free attachments-panel model with `#guard` checks: size column, tooltip, status text, refused save targets, the icon under a click (task 9.r10). |
| `SafePdf/Shell/App/Sidebar.lean` | Tk-free sidebar model with `#guard` checks: the panel list and switcher buttons per content, the panel opened by page mode and by the toggle (9.r8, 9.r9), thumbnail sizes, layout, lazy band, eviction and keyboard steps (9.r9), the layers tree from `/Order`, checkbox states, locked rows and toggling (9.r11b), tree rows (parents, ancestors, children), open/closed state, visible rows, triangles, indentation (task 9.7). |
| `SafePdf/Shell/App/Viewer.lean` | State, menubar, toolbar and sidebar (built from the models), page layout on the canvas (9.3: slots, per-page photos, deferred rendering), scrolling/zoom/rotation/view-mode handlers, prefetch, selection/copy/search handlers and highlights, outline panel, link hover/activation, history, go-to bar, smoke mode. |
| `SafePdf/Shell/App/Main.lean` | `main` of the `viewer` executable. |

**No data in script text.** Every Tcl command that carries data (file names, error text,
numbers) is a `Tcl.cmd` of literal words rendered through the proved `Tcl.quote`; pixels go
through `Tk_PhotoPutBlock`; event arguments come back as separate words. The only raw script
is the constant UI setup (`Viewer.setupScript`). The smoke test opens a file named
`odd [exit 7] $HOME {x" \.pdf` and checks that the title shows it verbatim.

**No Tcl from other X clients** (task 8.7, defence in depth). A PDF never reaches Tcl as
script (above), but two Tk mechanisms let *other clients of the X display* do it, and the
viewer closes both:

* **Tk `send`.** A Tk application registers its name on the display, and any client the X
  server admits can `send` it a script, evaluated at global level (`exec` included). Right
  after Tk starts, before the event loop ever runs, `Viewer.mainWith` evaluates
  `Viewer.sendOffScript` (`rename ::send {}`); Tk's delete callback of `send` also removes the
  application from the display's registry, so `winfo interps` elsewhere no longer lists it and
  `send tk …` fails with "no application named". (Setting `tk appname` would register it again;
  the viewer never does.) The **test hook** `SAFEPDF_VIEWER_DRIVE=1` keeps `send`:
  `scripts/viewer-corpus.sh` sets it because its driver works through `send`; nothing else
  should.
* **The X resource database.** Tk fills every widget option not given at creation from the
  option database, loaded from the display's `RESOURCE_MANAGER` property (which any client can
  set, e.g. with `xrdb`) or `~/.Xdefaults`. Several options are scripts: `-command`,
  `-validatecommand` (with `-validate`), `-invalidcommand`, `-postcommand`, `-tearoffcommand`,
  `-x/yscrollcommand`, `-takefocus` (evaluated by keyboard traversal); others link variables
  (`-textvariable`, `-listvariable`) or re-parent a toplevel (`-use`, `-screen`,
  `-container`). Verified before the fix: `*Entry.validateCommand: exec touch …` ran in the
  viewer. `Viewer.resourceGuardScript`, the first lines of `setupScript`, adds `*NAME {}` (and
  `*validate none`, `*container 0`) at priority `interactive` (80); Tk ranks option entries by
  priority before specificity and loads resources at `userDefault` (60), so they no longer reach
  any widget (the main window's `-takefocus` is reset explicitly; it existed before). `option
  clear` does not help: Tk reloads the resources on the next lookup.

Reviewed and found safe (all data reaches Tcl as quoted words of `Tcl.cmd` via `Viewer.run`,
or as variables inside constant procs, never as script): document and outline titles
(`wm title`, `.ol.t insert` in `fillOutline`), link URIs (`::safepdf::askUri` inserts them into
a text widget by variable; `clipboard append --`), file names (title, status line, dialogs'
`-initialdir`/`-initialfile` through `::safepdf::askSavePath`/`askXfdf*` arguments), note and
comment text (`::safepdf::noteEdit` inserts it by variable; it comes back as one `emit` word),
XFDF content (parsed in Lean, `Xfdf.readFile`; only marks reach Tk, as above), search and
go-to text (`emit … $::safepdf::query` is one word), render errors (`-text` of a canvas item).
Every `after`/`-command`/`bind` script is a constant (`Menu.Cmd.script`, `Toolbar` tool
scripts name constant icons), Tcl-side `expr` calls are braced, and the toolbar's
`uplevel #0` runs only the constant command stored when the button was built. Other X-level
inputs only trigger UI actions (`WM_DELETE_WINDOW` → Quit, which asks about unsaved marks;
synthetic key events), and clipboard/selection requests from other clients only read data.
The smoke test's `lockdown` case checks all of this from a second interpreter on the display.

**Threads.** The shim's interpreter is used only from the thread running Lean's `main`. On
macOS (Cocoa must run on the main thread) the shim sets `LEAN_MAIN_USE_THREAD=0` from a
constructor, as bib-lean does; on Linux Lean's `main` keeps its large-stack thread.

**Linux linking.** Lean links with its own clang/ld.lld and sysroot; the lakefile appends the
system library directories as `-Wl,-L…` (searched after the toolchain's) plus
`-Wl,--allow-shlib-undefined` so the system Tk links (pattern from bib-lean's lakefile).

## Smoke test

    scripts/viewer-smoke.sh [--no-build]

Builds `viewer`, then runs it with `SAFEPDF_VIEWER_SMOKE=DIR` (on Linux: uses `$DISPLAY` when
an X server answers, else `xvfb-run -a`; on macOS see below). It ends with a summary: cases
passed, skipped (with the reason) and failed on this platform (`case_begin NAME` starts a case;
a new case appended to the script starts with it too). `SAFEPDF_SMOKE_KEEP=1` keeps the work
directory (printed at the start) for inspection. In smoke mode the viewer drives itself with Tk key
events (`event generate`) and writes photos and state files (`Viewer.smoke`): `f` (fit page;
the viewer opens in Automatic Zoom), `page-1.ppm`,
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
`SafePDF`, document entries disabled) and File → Quit, which ends the run. Before closing, the
same run checks the wheel (9.2) with generated Tk 9 `<MouseWheel>` events: in fit page one
notch down turns to page 2 and one up back to page 1; at 200 % notches scroll page 1 down,
the view reaches the bottom and exactly one notch more turns to the top of page 2; eleven
1/12-notch deltas up leave page 2, the twelfth turns to the bottom of page 1; twelve 1/12
notches scroll as far as one notch (within 1.5 px); `<Button-5>`/`<Button-4>` scroll down and
back; Shift+wheel scrolls horizontally to the right edge and the page stays.

The toolbar and sidebar (9.7) run in a fifth variant (`SAFEPDF_VIEWER_SMOKE_MODE=toolbar`,
`Viewer.smokeToolbar`), once on the three-page labelled PDF with an outline and once on the
two-page PDF without one. It checks: the packed widgets of the three toolbar groups (the
sidebar toggle with any document since 9.r9); the sidebar open with an outline (panes `.ol .v`, toggle
drawn pressed) and closed without (`.v`, the toggle opens it on the thumbnails); the page field `i` / `(1 of 3)`
(labels) and `1` / `of 2`; generated clicks on ∨ and ∧ page and stop at the ends (∧ disabled on
page 1); Enter in the field with the last page number jumps, `999` and `abc` revert to the
current page, the first page's label jumps back, both jumps are in the history, leaving the
field reverts typed text; End/Home update the field; the zoom menu lists the twelve PDF.js
choices; choosing Page Width, Page Fit, Actual Size (≈ 100 %), 150 % shows those labels and
radio values, + gives `200%`, − − gives `125%`, 50 % then − gives the custom `33%` with no
radio value, Automatic Zoom returns; the overflow menu lists Open… … Rotate left and its Last /
First page entries page; all seven tool buttons are disabled and a click on Highlight changes
nothing; clicking the disclosure triangle of `Chapter` hides `Section` and a second click
shows it again; the toggle button hides the sidebar and shows it again. Since 9.4 Highlight is
enabled with a document (the disabled-click check uses Comment).

Highlights and notes (9.4) run in a sixth variant (`SAFEPDF_VIEWER_SMOKE_MODE=marks`,
`Viewer.smokeMarks`) on the text PDF of the selection test (substitute fonts off, so page 1 is
white except the black marker under `safe`), reading the photo's pixels with `photo get`: a
double click on `world` and the toolbar's Highlight turn its pixels `255 255 152` (yellow);
Edit → Highlight colour → Green recolours the selected highlight (`83 255 188`); `safe` +
Edit → Highlight selection gives a green highlight in which the marker stays `0 0 0` and the
paper above it is green (multiply); a click selects the `world` highlight and Delete makes it
white again; a right click at a blank point (Delete mark disabled there) + Add note… opens the
popup, a text full of Tcl metacharacters is saved verbatim and the icon's canvas bounding box
matches the model's icon box; a click on the icon reopens the popup with that text, which is
then edited (non-ASCII); after zooming in twice, rotating, going to page 2 (no mark items) and
back, the pixels and the icon are still right; Edit → Delete mark removes the selected note;
ids are never reused. (In smoke mode the context menu and the toolbar's colour menu are not
posted — their entries are invoked directly — so that no menu grab blocks the generated
events.)

The selection bubble and the Highlight pop-over (9.8) run in a seventh variant
(`SAFEPDF_VIEWER_SMOKE_MODE=bubble`, `Viewer.smokeBubble`) on the same text PDF: a drag over
`world` shows the float bubble with its right edge and top at the selection's last point; its
Highlight button turns the pixels yellow and the edit bubble replaces it; a click on blank
paper dismisses it; a click on the highlight brings it back and it follows a zoom; its colour
button opens the picker, whose blue row turns the pixels `128 235 255`; Delete makes them
white again. The toolbar's Highlight button without a selection opens the pop-over
(right-aligned with the button), the tool's check variable and the toggled look follow; its
pink swatch makes pink current; a drag over `safe` then highlights at once in pink; a press
on the slider sets thickness 20 and a drag to the right 24; the "Show all" switch makes the
paper white (and the highlight unselectable) and pink again; the edit bubble's Comment opens a
note anchored to the highlight's quads, which a second Comment reopens with its text; Escape
closes the pop-over and dismisses the bubble with the tool still on; Edit → Highlight tool
turns it off; a new selection's bubble goes on Escape and on End (page 2). Generated clicks
carry `-time` and are spaced past Tk's double-click time where two land close together.

Saving (9.5c) runs in the variants `save`, `reopen` and `encrypted` (`Viewer.smokeSave`,
`smokeReopen`, `smokeEncrypted`; questions and the Save As dialog are answered through
`::safepdf::autoAnswer` / `::safepdf::autoPath`, the last question is kept in
`::safepdf::lastAsk`). On a copy of the text PDF (mode 640): a highlight on `world` and a
note make the title start with `* ` and enable Save (menu entry and toolbar button); Quit,
Ctrl+W and the window's close button (its `WM_DELETE_WINDOW` script, `::safepdf::quit`)
answered Cancel keep everything and each asked the unsaved-changes question; Ctrl+S asks the
first-overwrite question — Cancel writes nothing, Overwrite writes into `text.pdf` itself (its
original bytes a prefix) and reopens it (2 saved marks, no `*`, Save disabled; the highlight
pixels are yellow from the renderer, no canvas note icon, the note text restored); a second
Ctrl+S writes nothing; the saved highlight can be selected; a new highlight on `safe` + Ctrl+S
appends to the same file without a question (3 marks with distinct ids, read back strictly);
Save As writes `saveas.pdf`; with a new note, Ctrl+S on a read-only `saveas.pdf` is refused
and on a `saveas.pdf` changed on disk refused with the changed-on-disk question (file
unchanged both times); Ctrl+W answered Don't Save closes and leaves `saveas.pdf` byte for byte
as it was. The `reopen` run on `text.pdf` restores the 3 marks (pixels, a click on the note's
place opens its popup with the saved text), Save As onto the opened file answered No writes
nothing and Yes appends, and with one more note Quit answered Cancel keeps the window (the
question asked) and Quit answered Save saves it before quitting. (Up to 9.5c the smoke's
"quit did not save" check meant the same: the reopen run's Quit was answered Yes in the
prompt; there was never a save on quit without the prompt, and 9.r2 keeps it that way.) The
script then checks `qpdf --check` on the written files, that the original (and each saved
revision) is a byte-for-byte prefix of the later file (`cmp -n`), that the overwritten file
kept its mode 640 and no temporary file was left, that the final file has 5 revisions and
each of its 5 mark annotations once, and that `mutool draw` shows the highlight (yellow
pixels in the box of `world`). The `edit` run (9.5g, `Viewer.smokeEdit`) on
a copy of that file deletes the whole-page highlight and the `safe` highlight, recolours the
`world` highlight green (pixels follow at once from the preview) and gives it a comment, edits
a note's text, saves into the opened file (answered Overwrite; 4 marks, comment restored with its id, its icon
drawn), then a third revision on top (blue, comment deleted: 3 marks); the script checks
`qpdf --check`, the byte prefixes, no duplicate ids, and that `mutool draw` shows `world`
green (then blue) and no tint in the box of `safe`. The `encrypted` run (RC4 fixture) saves a
note: until 9.5f the status line shows the writer's refusal before any question and the file
stays byte for byte unchanged.

Add text and Draw (9.9) run in the variant `editors` (`Viewer.smokeEditors`) on a copy of the
text PDF with substitute fonts on: the Add text mode and pop-over; a click places a text box,
typed text + Escape make a free-text mark; a double click edits it and a click elsewhere
commits; the pop-over's red swatch and size slider (20) restyle it; Draw in blue at thickness
4: two strokes form one drawing; Ctrl+S (Overwrite) writes into and reopens `text.pdf` (both read
back exactly; text pixels and a blue stroke pixel from the renderer); the text box dragged 50
units right and saved; Delete and the drawing's bubble Delete remove both, saved (none left,
white paper). The script checks `qpdf --check`, the byte prefixes, and that `mutool draw`
shows the red text and the blue strokes. The variant `editors-shot` sets up a text box, a
drawing and the open Draw pop-over and stays up 20 s for a screenshot.

XFDF (9.11) runs in the variant `xfdf` (`Viewer.smokeXfdf`) on a copy of the text PDF: a
highlight on `world` with a comment and a note at (300, 400); File → Export annotations…
(answered by `::safepdf::autoPath`) writes `marks.xfdf`, which the script checks for
`<highlight … name="safepdf-mark-1" …><contents>Comment ✓ &lt;&amp;&gt;</contents><popup …
name="safepdf-mark-1-popup-2" …/></highlight>` and a single `<text>` (the note); every mark is
deleted (white pixels), `importXfdf` with the file's path brings the three marks back (yellow
pixels, the comment still the highlight's, the note text equal, unsaved, `* ` title) with
`marks.xfdf: 3 imported, 0 already present, 0 skipped`; a second import gives `0 imported, 3
already present`; `billion-laughs.xfdf`, `xxe.xfdf`, `undeclared-entity.xfdf` (from
`Tests/xfdf/`), a missing file and a `<fdf>` file each give `cannot import NAME: …` with the
reader's message, the marks unchanged and the window alive; Acrobat's sample imports 3 marks
and skips 2.

The view modes (9.3) run in a variant `SAFEPDF_VIEWER_SMOKE_MODE=modes` (`Viewer.smokeModes`)
on a generated three-page text PDF (substitute fonts off, so the pages are white): `Alpha` on
page 1, `Bravo` on page 2, `zebra` on page 3; each mode is chosen by invoking its View menu
entry. Continuous: three page frames, a scroll region over three pages; generated wheel notches
scroll the document monotonically to its end while the page field shows 1, 2, 3 (no page
turns), at most three photos alive; Home goes back to the top; Go → Next page shows page 2;
`+` keeps the page point at the window centre (C2 on its slot); a double click on `Bravo`
(page 2) selects on page 2 and `h` highlights it (the pixel of page 2's photo is `255 255 152`);
Ctrl+F `zebra` from page 1 reports `hit 1/1 on page 3`, makes page 3 current and the hit lies
in the view. Continuous facing (Odd Spreads): pages 1 and 2 in one row, page 3 below, the
highlight still drawn. Facing (Page Scrolling): two frames (pages 1, 2), the highlight drawn;
Next → page 3 alone (Next disabled), Previous → 1|2; at fit page one wheel notch down turns to
page 3, one up back to 1|2. Even Spreads: page 1 alone, Next → 2|3 (Next disabled), the
highlight drawn. No Spreads: back to one frame. `SAFEPDF_VIEWER_SMOKE_MODE=scroll` is the
benchmark above (not run by the script).

The consolidated Phase 9 run (9.6, the M9 clause "a paper reads end-to-end with the wheel in
every view mode; a highlight and a note survive close/reopen inside the PDF" as an automated
check) is the variant `m9` (`Viewer.smokeM9`) followed by `m9-reopen` (`Viewer.smokeM9Reopen`,
a fresh process). It needs no particular words, so the script runs it on two generated fixtures
(three and four Helvetica pages, so that the last facing spread is once single and once a pair)
and on real papers: `SAFEPDF_SMOKE_PAPERS` (space-separated paths; empty skips), by default the
git-ignored `corpus/files/arxiv-1706.03762.pdf` when it exists (copy it from the corpus). The
run checks: the menubar is attached with File / Edit / View / Go and every command of
`Menu.Cmd.all` sits at its `Menu.locate` index with its label; the toolbar page box (Enter on
the last page jumps, `abc` reverts, the first page's label goes back), ∨/∧ and the zoom
drop-down (Page Width, Page Fit, Automatic Zoom); then, in each of the four view modes chosen
through the View menu (Page Scrolling + No Spreads, Vertical Scrolling, Page Scrolling + Odd
Spreads, Vertical Scrolling + Odd Spreads), from Home the wheel alone (`<MouseWheel>` −120 per
notch, `m9WheelThrough`) until the view shows the bottom of the last spread: every spread is
passed in order, (spread, view top) never goes back, the page box ends on a page of the last
spread with its own label, the `yview` ends at 1. At Page Fit on page 1: a drag over the first
word of five or more letters shows the float bubble, its Highlight makes the highlight (edit
bubble shown); a note (context menu, top right); Add text with the pop-over's red swatch and
size 16 (bottom left); Draw with blue, thickness 4, two strokes (bottom right). Ctrl+S (Overwrite) writes
into the opened copy `FILE.pdf` (4 marks read back strictly), File → Close empties the window, `openFile`
reopens it from disk: the four marks are restored with equal descriptions (`m9Desc`: kind,
colour, text, rounded geometry), no canvas items (the renderer draws them all) and coloured
pixels in the photo for each (yellow highlight and note icon, red text, blue strokes); File →
Export annotations… writes `m9.xfdf`, every mark is deleted (no coloured pixel left), File →
Import annotations… brings the same four back (`4 imported`). The fresh process on the saved
file restores the same four with pixels. The script then checks `qpdf --check`, that the
original is unchanged and a byte prefix of the saved file, and that `mutool draw` (72 dpi)
shows each mark in its colour inside its box. On arxiv-1706.03762 (15 pages) the wheel passes
pages 1…15 in 72 notches (single page, Automatic Zoom), 186 (continuous), spreads 1…8 in 7
(facing) and 42 (continuous facing); the whole M9 pair runs in about 4 s.

The `wheelflow` case (9.r1, `Viewer.smokeWheelFlow`, script case 1o) runs on the four-page M9
fixture and the M9 papers, opened **without** `SAFEPDF_VIEWER_VIEW` (every other case of the
script runs with `SAFEPDF_VIEWER_VIEW=single`, the view it was written for): the file must
open in Vertical Scrolling, No Spreads (state and both radio variables); then the bursts
described under *Wheel scrolling across pages* must reach page 5 (or the last page) in every
view mode without going back, without a run of motionless events longer than the page-turn
push (none in the continuous modes), and without a step longer than one event plus the
carried push. About 12 s per file.

A 9.4 screenshot (`arxiv-1706.03762.pdf`, two abstract lines highlighted in yellow, a note
with its popup) was taken this way, with `xdotool` driving drag, `h`, right click and the
popup.

Screenshots for comparison with the reference can be taken under Xvfb at the reference size,
e.g. `Xvfb :97 -screen 0 1900x940x24 &`, then
`DISPLAY=:97 SAFEPDF_VIEWER_GEOMETRY=1900x940 .lake/build/bin/viewer FILE.pdf &` and
`DISPLAY=:97 import -window root shot.png` (ImageMagick).

The `async` case (8.8, `Viewer.smokeAsync`) opens `viewer-smoke-pdf.py --slow 3000` (page 1:
3000 stroked curves, about 2 s per render at 125–150 %; page 2 light) with `syncWaitMs = 0`:
page 1 shows the placeholder while it renders; a Tcl timer every 20 ms keeps firing; `+`,
`End` and `Home` return within 250 ms (measured ~0–3 ms); after the zoom change two renders
run (old and new zoom); `End` shows page 2 (page field 2) while page 1 still renders; at the
end the old zoom's result was dropped (`stale ≥ 1`) and page 1's photo has the size of its
slot at the new zoom.

The `lockdown` case (8.7, `Viewer.smokeLockdown`) runs the viewer with `HOME` holding a
hostile `~/.Xdefaults` (`*Entry.validateCommand`, `*TEntry.validateCommand`,
`*Menu.postCommand`, `*Menu.tearOffCommand`, `*takeFocus` that would `exec touch pwned`,
`*Entry.textVariable` pointing at a toolbar command, `*Toplevel.container: 1`) together with a
second `wish` on the same display: the viewer records that `send` is gone and that the page
field, the overflow menu, `.` and fresh probe widgets carry none of the resources, types into
the entries, posts the menu and runs keyboard traversal; the `wish` checks that it got the
resources itself (control), lists `winfo interps` (only itself) and tries `send` to every
interpreter and to `tk`/`viewer`/`safe-pdf` (all fail); no `pwned` file. A second run with
`SAFEPDF_VIEWER_DRIVE=1` must reach the viewer through `send`: the viewer then renames itself
`safepdf-lock-PID` and records it (`appname` in `lockdown.txt`), the `wish` sends to exactly that
name with `send -async` and the script creates a file `sent` (10.19). On Aqua the lockdown half
tries only `tk`/`viewer`/`safe-pdf` (`winfo interps` lists every Tk interpreter of the user,
also other runs'), and when the control fails while a baseline `send` between two plain `wish`
processes fails too (Tk Aqua delivers no AppleEvents in this session, seen with a locked
screen), the control is skipped, not failed.

The `keys` case (9.r3, `Viewer.smokeKeys`, case 1o) runs on the text PDF twice: as installed
(X11: `Ctrl+…` menu and context-menu accelerators, the Control bindings, no `<Command-…>`
binding, no `::tk::mac::Quit`, Save tooltip `Save (Ctrl+S)`, Ctrl+A selects) and with
`SAFEPDF_VIEWER_PLATFORM=aqua` (honoured only in smoke mode; it installs the macOS mapping
on X11, where Tk's `Command` modifier is Meta): `Command-O`/`Command-S`/`Command-Shift-S`/
`Command-Q`/`Command-+`/`Command-[` labels (`Option-Left` before 10.9), `<Command-Key-s>`, `<Command-Key-S>` and
`<Shift-Command-Key-s>` bound to Save / Save As, `<Command-Key-q>` on `.` and in the find bar,
`::tk::mac::Quit` = `::safepdf::emit quit`, tooltip `Save (⌘S)`, and a generated
`<Command-Key-a>` selects all (status `… (⌘C copies)`); task 10.9 adds the labels
`Command-Option-G` (Go to page), `Command-Up`, `Command-]`, `Control-Command-S`, `Command-L`, the
bindings `<Command-Key-g>` / `<Command-Key-G>` (find next / previous, also in the find bar),
`<Option-Command-Key-g>` and `<Control-Key-g>` (Go to page), `<Command-Key-bracketleft>`,
`<Command-Key-Up>`, `<Control-Command-Key-s>`, `<Command-Key-l>`, `<Command-Key-9>` and the
⌘. body of `::safepdf::cancelBind` — and on X11 their absence, `Ctrl+G`/`Home`/`Alt+Right`/
`F9`/`Shift+R` labels and an empty `cancelBind`. Both runs check the six icon images
(16–512 px) and, when `xprop`/`xwininfo` are installed, that the toplevel's wrapper carries
`_NET_WM_ICON` starting with `512, 512`.

The `r4` case (9.r4, `Viewer.smokeR4`, script case 1q) runs in the default view on the text
PDF, the outline PDF and the M9 papers. The view-mode drop-down: it starts on Vertical
Scrolling, lists the four modes, sits right after `of N`; each entry, invoked, sets the
scroll and spread variables of the View and `»` menus and redraws its icon (1, 2, 2 or 4
page shapes); View → Even Spreads and `»` → Vertical Scrolling move its checked entry; Two
Pages keeps even spreads. On the text PDF a drag over `world` shows the float bubble with
`[highlight, comment]` inside the scroll region, its Add comment tooltip shows, and Add
comment adds exactly one note anchored to the selection's quads with its popup open and the
bubble gone. With an outline, in Single Page and Vertical Scrolling at Page Fit, the outline
is closed and opened while `r4Probe` samples the first page frame's canvas and screen x at
every `<Configure>` of the canvas and every 2 ms for 700 ms; the run of distinct values must
be just start → end (an intermediate value fails: the flicker). It writes `toolbar.png`,
`viewmenu.png`, `bubble.png` and `bubble-tip.png` when `import` is installed.

The `opensettings` case (9.r8, `Viewer.smokeOpenSettings`, script case 1s) runs in the
default view on generated five-page files with an outline, opened one after another with
`openFile` (File → Open after its dialog), one line per file in `opensettings.txt`: every
`/PageLayout` (state and View-menu variables; Even Spreads put page 1 alone on the right),
`/PageMode` UseOutlines / UseNone / UseThumbs (outline open / closed / thumbnails open, no
note since 9.r9),
`/OpenAction [p3 /XYZ 0 792 1.5]` (page 3 at 150 %, its top at the window top), then Two Pages
+ Actual Size chosen and the file reopened with `keepView` (both kept), `[p1 /Fit]` + UseOutlines
(Page Fit, outline), a GoTo to a named destination in a `/Names /Dests` tree (page 4, Page
Width), JavaScript and URI open actions (page 1, Automatic Zoom, the "ignored (not executed)"
note), HideToolbar + HideMenubar + HideWindowUI + DisplayDocTitle (toolbar, menubar and
scroll bars gone, title from `/Info /Title`; Escape brings them back), TwoPageLeft + R2L
(page 1 right of page 2), FullScreen + `/NonFullScreenPageMode /UseOutlines` (outline closed;
Escape leaves full screen and opens it), FitWindow + CenterWindow at zoom 0.5 (window
resized and centred), and last a file without settings: Vertical Scrolling, Automatic Zoom,
page 1, outline, toolbar, its file name as title.

The `thumbs` case (9.r9, `Viewer.smokeThumbs`, case 1u) runs on generated files, one line
per step in `thumbs.txt` (`Viewer.thumbRow`: sidebar shown, panel, mapped view buttons,
toggle, heading, thumbnails laid out / rendered / kept, visible, highlighted, selected, page,
`::safepdf::thN` photos): `th-outline.pdf` (60 pages, an outline, page 5 `/Rotate 90`) opens
on the outline with the Thumbnails and Document outline buttons and no thumbnail rendered; the
Thumbnails button shows 60 frames with only the visible thumbnails plus the 3-page margin
rendered (9 of 60 in the 1200×960 window); page 5's slot is 98×76 (rotated), page 1's
98×127; a generated click on thumbnail 3 goes to page 3; Go to page 40 highlights thumbnail
40 and scrolls it into view; Down, Down move the selection to 42 (the page stays 40), Return
goes to 42; the panel scrolled to the end in ten steps never keeps more than 40 images (photos
= kept); Rotate right lays the 60 thumbnails out rotated (page 1 98×76, page 5 98×127);
`th-thumbs.pdf` (`/PageMode /UseThumbs`, no outline) opens on the thumbnails with only that
button and no "not available" note; `th-plain.pdf` (3 pages, nothing) opens with the sidebar
closed but the toggle shown, the toggle opens the thumbnails (3 rendered) and closes them.
The `thumbperf` case (reported, not checked) reopens the corpus paper
`arxiv-1706.03762.pdf` when present with the thumbnails panel through the event loop and
prints the times to open, to the first thumbnail and to every visible one, the slowest Next
while thumbnails render, a scroll through the whole panel, the most images kept and the
memory (VmRSS / VmHWM). Measured (Xvfb, this sandbox): 15 pages — open 58 ms, first
thumbnail 125 ms, all visible 295 ms, whole panel 286 ms, 15 kept, VmHWM 116 MiB (page renders included);
a 384-page file (`qpdf` concatenation of the corpus's
two NTSB reports and `arxiv-astro-ph_0603449`; the corpus's largest file has 173 pages) —
open with the 768 thumbnail items 162 ms, first thumbnail 319 ms, all visible 495 ms, the
slowest Next while thumbnails render 92 ms, the whole panel scrolled in 72 steps 11.5 s (384
rendered, never more than 40 kept), VmHWM 154 MiB; `www.ntsb.gov-AAR0701.pdf` (173 pages) —
first thumbnail 192 ms, all visible 360 ms, VmHWM 82 MiB.

The `noteclose` case (9.r12, `Viewer.smokeNoteClose`, case 1t) runs on the text PDF and
closes note popups without Save: a new note + Escape generated on the text widget (which has
the focus) leaves no note and no canvas icon; typed text + Escape keeps the note with that
text; the same note made saved, reopened by a click, cleared + Escape keeps its text and the
document clean; an empty saved note reopened + Escape is removed and the title gets `* `; an
empty comment on a highlight (Edit → Add note… with the highlight selected) is removed, the
highlight stays; white space only on a selection is removed; the Cancel button and the
`WM_DELETE_WINDOW` script behave as Escape (empty → removed, typed → saved); Add note… while
an empty note's popup is open removes that note; Edit → Delete mark with the popup open
closes it and a stale `noteClose` is ignored.

The `attach` case (9.r10, `Viewer.smokeAttach`, case 1v) generates `att.pdf`
(`/PageMode /UseAttachments`, an outline, an `/EmbeddedFiles` tree with kids holding a plain
`hello.txt` with `/Desc` and `/Params`, a FlateDecode `data.bin` without `/Size` and an
external file specification, and a file attachment annotation on page 2 named
`../../etc/evil:name.txt` plus a right-to-left override), `outline.pdf` and `noatt.pdf`.
It checks: the sidebar opens on the attachments panel with its Show Attachments and Show
Document Outline buttons; the rows before any decoding (`data.bin ?`, `hello.txt 26 B`,
`external.pdf —`, the hostile name without the override, `16 B`) and the tooltips (data.bin's
stored size; hello.txt's description, type and dates); the tooltip probe (`attProbe`) turns
`data.bin` into `10 KB`; Save attachment as… on every row writes exactly the generator's bytes
(also compared with `pdfdetach -saveall` when installed), proposes `evil_name.txt`, and
refuses the external file; the opened PDF, a read-only file, a read-only folder and a folder
are refused and stay unchanged; the switcher and the toggle; a click on the annotation's icon
(sidebar closed on the outline panel) opens the attachments panel on its row; `outline.pdf`
has no Attachments button, nor has `noatt.pdf` (its sidebar has the thumbnails only).

The `layers` case (9.r11b, `Viewer.smokeLayers`, case 1w) generates `oc.pdf` (`/PageMode
/UseOC`, one page whose coloured squares and words belong to the groups Base ON, Extra OFF,
Notes ON, the radio pair English ON / French OFF under the UTF-16 heading "Languages" with a
right-to-left override, Locked (locked, nested under Notes by an unlabelled array), Orphan
(ON, not in `/Order`), and an OCMD `AllOn` of Base and Extra), `oc-nomode.pdf`,
`oc-noorder.pdf` and `plain.pdf` (`/UseOC` without `/OCProperties`), and runs on a copy
(`saved.pdf`). It checks: the sidebar opens on the layers with the tree
`Base ✓, Extra ☐, [Languages], English ✓, French ☐, Notes ✓, Locked ✓ (disabled),
[Additional Layers], Orphan ✓` with Orphan hidden under its collapsed heading, no "not
available" note; the page's pixel at each square and the search hits of each
word; a thumbnail pixel; Extra on → its blue square, the OCMD's green one and `bravo`
findable; French on → English off (pixels, hits); the locked checkbox and the `layer K` event
change nothing; opening Additional Layers shows Orphan, which toggles off (its square white)
and on again; collapsing the heading unmaps its checkboxes; the thumbnail shows the blue
square; a note saved with Ctrl+S (Overwrite) — the reopen keeps the toggled state; opening the
file again restores the defaults; `oc-nomode.pdf` has the Layers button with the sidebar
closed, `oc-noorder.pdf` lists all seven groups by name (no Additional Layers heading), `plain.pdf` has no Layers button.
The shell then checks that the saved file is an incremental update of `oc.pdf` whose appended
bytes contain no `OCProperties`, `/OCGs`, `/ON`, `/OFF`, catalog or `/OCProperties` object,
and runs `qpdf --check` on it.

The `savedlg` case (9.r6, `Viewer.smokeSaveDialogs`, case 1r) runs on a copy of the text PDF
alone in a folder, as installed and with `SAFEPDF_VIEWER_PLATFORM=aqua`: the real
`::safepdf::choose` dialog driven by generated keys (Return on the default, Tab-focus on
Cancel + Return → Cancel, Escape, Space on Save As…; focus back on `.c`); Save As… dialog
options (`-filetypes` only off aqua, `-defaultextension .pdf`, the file's folder, the
proposed name); a 240-character name; `3453483.3454032-final` → `.pdf` added; `exists` with
an `exists.pdf` present → Replace? answered No keeps it; a read-only file, a folder and a
file in a read-only folder refused (the document still unsaved, Save enabled); a name with
spaces, `$`, brackets, braces, quotes and non-ASCII saved and shown in the title; Export
onto the opened PDF writes `NAME.pdf.xfdf` (the PDF unchanged), `notes` → `notes.xfdf`; the
opened file deleted behind the viewer's back → Save asks the "no longer there" question and
creates nothing. The shell then checks that no `*.tmp` file is left. Disk full was checked
by hand (a 16 KiB tmpfs: `cannot save to f.pdf: resource exhausted (… no space left on
device)`, the title keeps `* `, Quit → Save stays open with `quitting cancelled`, no
temporary file); `ulimit -f` cannot simulate it (SIGXFSZ kills the process).

### Smoke test on macOS (10.11)

On macOS (`uname -s` = Darwin) the script runs the viewer natively on Tk Aqua (Homebrew
`tcl-tk` 9.x): no X server, no `xvfb-run`; the whole script takes 2–3 minutes.

**Background mode (the default).** You can keep working while it runs: in smoke mode on
macOS the shim (`c/tk_shim.c`, `safepdf_prohibit_activation`) sets the application's
activation policy to *Prohibited* before and after `Tk_Init` (no Dock icon, no menu bar, never
the active app) and makes every toplevel transparent (`-alpha 0`) and `.` off screen
(`+-30000+-30000`). Rendering, photos and `event generate` key/mouse events still work (case 1
gives the same `state.txt` and `view.txt` as a foreground run), but with no active application
Tk has no keyboard focus, so: the focus part of 1r's prompt answers, of 1t's `menu-open` and of
the 10.6 `dismiss` rows is dropped; 1s expects no full screen (`true,0`, as without a window
manager); 1q is skipped (it times out without an active app). Normal (non-smoke) launches are
unchanged.

**Leak-proofing (10.16).** Setting the policy was not enough: during `Tk_Init` Tk itself calls
`[NSApp setActivationPolicy:Regular]` and `[NSApp activateIgnoringOtherApps:YES]` (the viewer
was briefly a Foreground app and sometimes became the front app about a second after launch,
seen in the `tint` and `edit` cases), every smoke `sendKey`/`sendEvent` (`focus -force`) asks
for activation again (~1,900 times per run), and with the screen unlocked
`wm attributes . -fullscreen 1` (1s) put the hidden window into native full screen (a new
Space). So in background mode the shim (`safepdf_block_activation`, installed before
`Tk_Init`) overrides, on Tk's `TKApplication`, `setActivationPolicy:` (always Prohibited),
`activateIgnoringOtherApps:`, `activate` and `unhide:` (no-ops), and on `NSWindow`/`TKWindow`
`toggleFullScreen:` (no-op). `SAFEPDF_SMOKE_TRACE_ACTIVATION=1` logs every blocked call to
stderr with a millisecond timestamp. To check a run, sample the front application and the
viewer's application type (`lsappinfo list`: `type="BackgroundOnly"` expected, never
`Foreground`) every ~0.2 s while the script runs; a viewer from your checkout that is ever in
front must be killed by pid (never `pkill -f viewer`: the user may have their own open).

**Foreground mode** (`SAFEPDF_SMOKE_FOREGROUND=1`, for when nobody uses the machine): the
windows show on screen and the app is activated, and every check runs with the full aqua
expectations below. macOS does not let a background process take the keyboard focus from the
app you are using, so the focus-dependent cases (1q, 1r, 1s, 1t) fail or time out if you work
meanwhile or the screen is locked (the script warns when the front app is `loginwindow`).

GNU `stat -c` and `cmp -n` are replaced by BSD equivalents on macOS (`file_size`, `file_mode`,
`cmp_prefix`).

What differs on Aqua, and how the script handles it:

* **1l lockdown** runs (Tk Aqua has `send` and reads `~/.Xdefaults`). `winfo interps` lists
  every Tk interpreter of the user, not of one display, so other Tk programs may appear; the
  check instead requires every `send` to fail with "no application named" or inside an
  interpreter without `::safepdf` (not a viewer).
* **1p keys** and **1r savedlg**: only the aqua variant runs (natively); the X11 variant is
  skipped — Tk Aqua cannot install the X11 mapping or dialog options.
* **1s opensettings**: page 1 alone in an even spread is checked against the midpoint of
  TwoColumnLeft's columns (the canvas width, hence the pixel x, differs); with a window manager
  `wm attributes . -fullscreen` reads back 1 while in full screen; `smokeOpenSettings` waits
  1 s before Escape on Aqua, which ignores leaving full screen while the window is still
  entering it.
* Everything else runs with the Linux expectations (pixel checks read the page photos, so
  translucent highlights and Retina scaling do not matter; `tk scaling` here is 1.334).
* `qpdf`, `xprop`/`xwininfo` and ImageMagick `import` checks skip themselves when missing, as
  on Linux.

Known macOS failures (real viewer bugs, left failing and named in the summary as
`KNOWN-MAC-BUG`): **1i bubble** and **1m async** — at `tk scaling` 1.334 Automatic Zoom capped
at 125 % quantises to 106/64 and shows 124 %; Zoom In goes to 125 %, the same quantised zoom,
so `+` does nothing visible and `+` `-` ends at 100 % (1i's later clicks miss; 1m sees no
second render). **1s opensettings** — a `/PageMode /FullScreen` file's status line lacks
"full screen (Escape leaves)" until the next status update.

CI: the workflow cannot be pushed from the sandbox; the job that installs `tk-dev`/`xvfb`,
builds `viewer` and runs the smoke test is in `docs/ci-pending.patch` (task 12.6 merged the
earlier `ci-viewer-step.patch` into it; it also points the cache keys at `lakefile.lean` and
runs the viewer on the pinned corpus subset).

## M9 evidence (9.6, 9.10)

Recorded 2026-11-20 on the worktree of tasks 9.6/9.10 (base c368bc9), Linux arm64, Xvfb.
M9 reads: *a paper reads end-to-end with the wheel in every view mode; a highlight and a note
survive close/reopen inside the PDF (C7 proved; the annotated file opens in
Acrobat/Okular/pdf.js with the highlights visible, and in our strict parser unchanged);
side-by-side screenshots of the same paper in our viewer and in Firefox's PDF.js show the same
toolbar layout (sidebar only with an outline, page box with arrows, centred zoom, tools on the
right) and the same selection bubble.*

### Wheel end to end, close/reopen (automated: `scripts/viewer-smoke.sh`, case 1n)

The `m9` / `m9-reopen` smoke runs (see "Smoke test" above) on the two fixtures and on
`arxiv-1706.03762.pdf` (15 pages, an outline) pass:

    wheel-single: seen=1,2,…,15 spreads=15 notches=72 monotone=true field=15 last=true bottom=true
    wheel-continuous: seen=1,2,…,15 spreads=15 notches=186 monotone=true field=15 last=true bottom=true
    wheel-facing: seen=1,2,3,4,5,6,7,8 spreads=8 notches=7 monotone=true field=15 last=true bottom=true
    wheel-cfacing: seen=1,2,3,4,5,6,7,8 spreads=8 notches=42 monotone=true field=15 last=true bottom=true
    saved: true false 4 4
    closed: true 0 SafePDF
    reopened: true 4 4 false false
    marks-reopened: highlight 0 yellow 1 | ink 0 2 [5, 5] 4 100 #0060DF | note 0 yellow M9 note ✓ [x] | text 0 M9 text 59 60 16 #D70022
    pixels-reopened: hl=55 note=30 text=14 ink=10
    export: exported 4 mark(s) to m9.xfdf
    removed: 0 hl=0 note=0 text=0 ink=0
    import: m9.xfdf: 4 imported, 0 already present, 0 skipped
    (fresh process) restored: 4 4 false; pixels: hl=55 note=30 text=14 ink=10
    mutool: coloured pixels per mark: {'hl': 371, 'note': 85, 'text': 152, 'ink': 628}

(In facing mode at Automatic Zoom a whole spread fits the window, so one notch per spread.)

### The annotated file in other readers

The file is the `arxiv-1706.03762-annotated.pdf` the `m9` run wrote before 9.r2 (since 9.r2
Save writes into the opened file: the run's copy `m9-arxiv…/arxiv….pdf` in the smoke's work
directory, the original being the corpus file) (a highlight on
`Provided`, a note, the free text `M9 text` in red, a blue two-stroke drawing; 3,533 bytes
appended to the 2,215,272-byte original).

* **Byte prefix, qpdf**: `cmp -n $(stat -c %s paper.pdf) paper.pdf paper-annotated.pdf` →
  equal; `qpdf --check paper-annotated.pdf` → "No syntax or stream encoding errors found".
* **Our strict parser, "unchanged"**: `inspect paper-annotated.pdf` → `open: strict`,
  `revisions: 2`; `inspect --view resolve` → `5965 ok, 0 error(s)` (original: `5957 ok`).
  `diff <(inspect --view objects paper.pdf) <(inspect --view objects paper-annotated.pdf)`
  removes only the old definition of page 1 (`91 0 obj`, superseded by the update: the same
  dictionary plus `/Annots [5958 0 R 5959 0 R 5960 0 R 5961 0 R]`) and adds the new objects
  5958–5965; every other object's pretty-printed tree is identical. The general statement is
  proved (`Spec.Write.c7`, `c7Update`, value level `c7Value'`/`c7ValueAnnots'`) and tested on
  fixtures, encrypted fixtures and the corpus by `Tests/WriteIncremental.lean` ("every original
  object … fetches identically", checks `original objects unchanged` / `objects not written
  unchanged`) and `Tests/WriteAnnots.lean`.
* **MuPDF**: `mutool draw -r 72 -o p1.png paper-annotated.pdf 1` draws all four marks (yellow
  highlight, the yellow note icon, the red text, the blue strokes); the smoke script counts
  their coloured pixels in each mark's box (above).
* **Poppler** (Okular's PDF backend; Okular itself is not installed — 382 packages): `pdftoppm
  -r 72 -f 1 -l 1 -png paper-annotated.pdf p` (poppler 25.03.0) draws all four marks the same
  way.
* **pdf.js**: Node 20.19.2 and npm from Debian (`sudo apt-get install nodejs npm`, system
  tools of the sandbox, not project dependencies) and `pdfjs-dist@4.10.38` (published
  2025-01-01) with its optional `@napi-rs/canvas` 0.1.100, installed with
  `npm install --ignore-scripts pdfjs-dist@4.10.38` in a scratch directory outside the
  repository. `node scripts/pdfjs-annots.mjs SCRATCH/node_modules/pdfjs-dist
  paper-annotated.pdf p1.png` (`getDocument` + `page.getAnnotations()` on every page):

      pdfjs 4.10.38: 15 pages
      page 1: Highlight id=5958R color=255,255,152 rect=124.7,707.6,167.7,719.6 hasAppearance=true contents="" quads=1
      page 1: Text id=5959R color=255,255,152 rect=566.7,727.5,586.7,747.5 hasAppearance=true contents="M9 note ✓ [x]"
      page 1: FreeText id=5960R color=font:215,0,34 size:16 rect=59.4,34.6,115.8,60.2 hasAppearance=true contents="M9 text" textContent=["M9 text"]
      page 1: Ink id=5961R color=0,96,223 rect=437.5,46.9,525.3,84.6 hasAppearance=true contents="" inkLists=2

  Subtypes, colours (PDF.js yellow `#FFFF98`, red `#D70022`, blue `#0060DF`), contents and
  geometry are ours; the sorted listing differs from the original file's only by these four
  lines (the original's 113 `/Link` annotations are listed unchanged). pdf.js does not expose
  `/NM`. Rendering page 1 through pdf.js (`AnnotationMode.ENABLE`, `standardFontDataUrl` set
  to pdfjs-dist's `standard_fonts/`) shows all four marks; without `standardFontDataUrl` the
  free text (non-embedded `/Helv` in its appearance) is not drawn in Node.
* **Acrobat, Okular (GUI), Firefox's built-in PDF.js**: not available here. **Check for the
  human**: open `arxiv-1706.03762-annotated.pdf` (re-create it with
  `scripts/viewer-smoke.sh`, or by hand: highlight, note, Add text, Draw, Save) in Acrobat
  Reader, Okular and Firefox and confirm the four marks are drawn, the note opens with its
  text, and the highlight can be selected/edited.

### Side by side with PDF.js (look check)

`docs/viewer-reference/m9-side-by-side.png`: left the human's reference
(`pdfjs-firefox.png`, 1915 × 938, Firefox PDF.js on Perceus, PLDI '21), right our viewer at
1900 × 940 on `arxiv-1706.03762.pdf` (the Perceus PDF has no clear licence for the corpus, so
the paper differs; layout only). Ours was taken with the smoke variant `m9-shot`
(`Viewer.smokeM9Shot`: Highlight pop-over open, the abstract's first sentence dragged over in
the tool mode → yellow highlight with its edit bubble; `ready.txt` reports `marks: 1`,
`bubble: edit`, `popover: 1`, `field: 1 of 15`, `zoom: Automatic Zoom`, `sidebar: true`):

    Xvfb :97 -screen 0 1900x940x24 -nolisten tcp &
    DISPLAY=:97 SAFEPDF_VIEWER_SMOKE=out SAFEPDF_VIEWER_SMOKE_MODE=m9-shot \
      SAFEPDF_VIEWER_GEOMETRY=1900x940 .lake/build/bin/viewer corpus/files/arxiv-1706.03762.pdf &
    # when out/ready.txt exists:
    DISPLAY=:97 import -window root ours.png
    convert ref.png ours.png … +append m9-side-by-side.png   # ImageMagick, labels spliced on top

What matches:

* Toolbar layout: sidebar toggle at the far left (shown because there is an outline), ∧ / ∨
  arrows, the editable page box `1` and `of N`; centred − | + and the `Automatic Zoom`
  drop-down with its chevron; the tool buttons at the right, then Print, Save and `»`; the
  active Highlight tool drawn on a round grey-lavender background.
* Sidebar rule: the outline sidebar is open on load because the document has an outline, with
  a "Document outline" title and indented, collapsible entries.
* Highlight pop-over: right-aligned under the Highlight button, "Highlight color" with the same
  five swatches (yellow selected with a ring, green, blue, pink, red), "Thickness" with a small
  dot, a slider and a large dot, a divider, "Show all" with an on switch.
* The highlight: PDF.js yellow multiplied over the text (glyphs stay black), outlined in blue
  while selected; the edit bubble below it near the end of the selection with colour swatch +
  chevron, comment and delete icons separated by dividers.
* Page on a grey background, white paper, the same zoom choice.

What differs:

* We have a native menubar row (File / Edit / View / Go, 31 px) above the toolbar (Plan
  Phase 9 asks for it); Firefox's own chrome is cropped from the reference.
* Tool order and set: PDF.js (this Firefox build) shows Comment, Signature, Highlight, Add
  text, Draw, Add image; we show Highlight, Comment, Add text, Draw, Add image (no Signature
  tool). Our Print and Add image are disabled (greyed, post-M9); PDF.js's are enabled.
* Spacing: PDF.js leaves a wider gap between the sidebar toggle and the arrows (arrows at
  x ≈ 120 vs ours ≈ 63); the toolbars are about as tall (41 vs 40 px) but ours is lighter
  (`#f9f9fa` vs Firefox's `#ebebef`).
* Shapes: PDF.js uses rounded corners almost everywhere (page box, zoom pill, pop-over card
  with a shadow, sidebar card, round slider thumb, pill-shaped edit bubble with a shadow); ours
  has square or slightly rounded corners, a flat pop-over with a thin border, a square slider
  thumb and a smaller, flatter bubble.
* Sidebar: PDF.js's header has a view-switch button (thumbnails/outline, with chevron) and an
  outline-options button; ours is a plain title. PDF.js expands nested entries (▼) here, ours
  shows top-level entries with ▸ collapsed; PDF.js's sidebar is ≈ 230 px wide, ours ≈ 270 px.
* Selection outline: PDF.js traces one dark-indigo outline around the union of the line
  boxes; ours draws one brighter blue rectangle per line (they overlap at the line join).
* Fonts and colours: PDF.js uses the system UI font (the reference is from macOS) at a
  slightly larger size, icons in a purple-grey; ours DejaVu Sans via Tk/Xft, the zoom label
  bold, icons near-black.
* Anti-aliasing: the reference is a (HiDPI) browser screenshot with smooth text; our page is
  drawn by our own rasterizer at 1× with greyscale anti-aliasing (slightly heavier glyph
  edges), UI text by Xft.
* The paper differs (Perceus vs Attention Is All You Need), so page content, positions and
  the page count ("of 16" vs "of 15") are not comparable.
