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

## What it does (8.2a skeleton, 8.2b viewing, 8.2c selection and search, 8.2d navigation, 9.1 menubar, 9.2 wheel, 9.3 view modes, 9.4 highlights and notes, 9.5c saving marks into the PDF, 9.5g editing saved marks, 9.7 PDF.js look, 9.8 selection bubble and Highlight pop-over)

* Window (1200×960 by default; `SAFEPDF_VIEWER_GEOMETRY=WxH` sets another size): menubar
  (File, Edit, View, Go; see *Menubar* below), a toolbar and an outline sidebar modelled on
  PDF.js (see *Toolbar and sidebar* below), a scrollable canvas (scroll bars) with the current
  page — or, in the other view modes, all pages or two side by side (see *View modes* below;
  `SAFEPDF_VIEWER_VIEW=single|continuous|facing|continuous-facing` sets the initial one) —,
  a status line (file, page, zoom, rotation, pixel size, render time or "from cache",
  notes, the view mode when it is not the single page, or the error).
* Title: `NAME - page k/n - safe-pdf`, with page labels `NAME - page iii (3/120) - safe-pdf`.
* Pages are rendered by `Core.Raster.Glyph.renderDocPage` (fresh budget per page, CropBox and
  `/Rotate` honoured, the user rotation added with `rotAdd`).
* **Zoom** (`Toolbar.ZoomChoice` over `View.Mode`): Automatic Zoom (default, as in PDF.js:
  the page width for a portrait page, the whole page for a landscape one, at most 125 %), fit
  page, fit width, or a fixed percentage of actual size,
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
* **Scrolling** in the single-page view (and the facing view) is page-at-a-time: the canvas
  holds one page (spread). Scrolling past the bottom (or right) edge with the keys moves to the
  top of the next page; past the top, to the bottom of the previous page. The mouse wheel does
  the same (9.2, below). In the continuous modes the canvas holds the whole document (9.3).
* **Page cache** (`View.Cache`): render results keyed by (document, page, zoom, rotation), LRU,
  at most `View.cacheBytes` = 256 MiB of images and `View.cacheEntries` = 64 entries; results
  above half the budget are not cached. 100 ms after a page is shown, the next page (in the
  facing view: the next spread) is rendered into the cache when it is at most
  `Viewer.prefetchPixels` (2²² px); no threads. Each page on the canvas has its own Tk photo
  (`::safepdf::pgN`), kept only while the page is in view or next to it (9.3).
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
| `Ctrl+O` / `Ctrl+W` / `Ctrl+Q` | open / close the document / quit (asks about unsaved marks) |
| `Ctrl+S` / `Ctrl+Shift+S` | save the marks into `FILE-annotated.pdf` / into a chosen file (9.5c) |

## Menubar (9.1)

A native Tk menubar (`.menubar`, attached with `. configure -menu`; on X11 Tk draws it at the
top of the window, on macOS it is the system menu bar) duplicates the toolbar and the keys.
The model is Tk-free: `SafePdf/Shell/App/Menu.lean` lists the commands (`Menu.Cmd`: label,
accelerator text, the constant Tcl script that runs it, an enabled rule) and the menus; the
viewer builds the Tk menus from it (`Viewer.buildMenus`) and after every event sets the
`-state` of each entry and of the toolbar buttons Prev/Next/Back/Forward/Outline whose rule
changed (`Viewer.syncMenus`, over `Toolbar.targets`/`Toolbar.states`: menubar entries, the
toolbar's overflow menu and its buttons). The toolbar (9.7, below) reuses the same commands.

| Menu | Entries (accelerator) |
|---|---|
| File | Open… (Ctrl+O), Save (Ctrl+S), Save As… (Ctrl+Shift+S), Close (Ctrl+W), Quit (Ctrl+Q) |
| Edit | Copy (Ctrl+C), Select all (Ctrl+A), Highlight selection (H), Highlight colour ▸ (five colours), Add note…, Delete mark (Delete), Highlight tool (check, 9.8), Show all highlights (check, 9.8), Find… (Ctrl+F) |
| View | Outline (F9, a check entry showing whether the panel is open), Zoom in (`+`), Zoom out (`-`), Actual size (`0`), Fit page (`f`), Fit width (`w`), Rotate right (`r`), Rotate left (`R`), then two radio groups (9.3): Page Scrolling / Vertical Scrolling, No Spreads / Odd Spreads / Even Spreads |
| Go | Previous page (PageUp), Next page (PageDown), First page (Home), Last page (End), Go to page… (Ctrl+G), Back (Alt+Left), Forward (Alt+Right) |

Disabled: everything but Open… and Quit without a document; Save without unsaved marks; Copy and Highlight selection
without a selection; Delete mark without a selected mark;
Outline when the document has none; Previous/First on the first page (spread), Next/Last on the
last (spread);
Back/Forward with an empty history. The keys stay; a menu accelerator is only a label. The
Outline command is also the toolbar's sidebar button (9.7). *Close* empties the window (as
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
  * *left*: the sidebar toggle (shown only when the document has an outline; drawn pressed
    while the sidebar is open), ∧ / ∨ previous / next page (disabled on the first / last page),
    the page field and its label. The field shows the page number and `of N`, or, when the
    document has page labels, the label and `(k of N)` (as PDF.js). **Enter** jumps to an exact
    label, else a page number `1..N`, else a label ignoring case (`Toolbar.pageEntry`; the jump
    is recorded in the back/forward history as PDF.js does); an out-of-range number or other
    text reverts the field to the current page (and says so in the status line); Escape or
    leaving the field reverts it too. The field follows every page change (arrows, keys, wheel,
    links, outline). The entry has its own bind tags, so typing does not trigger viewer keys.
  * *centre* (centred in the window): − / + (zoom out / in one step, as the keys) and the zoom
    drop-down, a rounded button showing the current choice; clicking it opens a menu with
    Automatic Zoom, Actual Size, Page Fit, Page Width, 50 %, 75 %, 100 %, 125 %, 150 %, 200 %,
    300 %, 400 % (`Toolbar.ZoomChoice.presets`, radio entries). A zoom reached with − / +, the
    keys or Ctrl+wheel that is not in the list (33 %, 67 %, 600 %, …) shows as its percentage
    with no entry checked (PDF.js's custom option).
  * *right*: Highlight (works since 9.4: highlights the selection in the current colour;
    without a selection it turns the Highlight tool on and opens its pop-over, or off (9.8);
    see *Selection bubble and Highlight pop-over*), Comment, Text,
    Draw, Image, then Print and Save — Save (PDF.js's download icon) is the command File →
    Save since 9.5c, enabled while there are unsaved marks; the others are **disabled
    placeholders** until their tasks land (Comment, Text, Draw 9.9; Print and Image after
    M9) — and the `»` overflow menu: Open…, Find…, Go to page…, First page, Last
    page, Rotate right, Rotate left (`Toolbar.overflow`; the commands that lost their toolbar
    buttons), then, as in PDF.js's secondary toolbar, the scroll modes (Page Scrolling, Vertical
    Scrolling) and the spread modes (No Spreads, Odd Spreads, Even Spreads) as radio entries on
    the same variables as the View menu (9.3). Document properties are not available yet.
  * Buttons are 32 px canvases with round hover (`#e4e4e9`), pressed and toggled backgrounds,
    16 px icons in `#3b3b44`, dimmed when disabled (PDF.js: opacity 0.5); a tooltip appears
    after 600 ms; separators are 1 px × 20 px.
* **Sidebar** (`.ol`, the left pane of the paned window, `Sidebar`): a white panel titled
  *Document outline* on the `#f0f0f4` background. It **opens on load only when the document
  has an outline**; without one it stays closed and the toggle is hidden (F9 and View → Outline
  do nothing then). The outline is a text widget drawn as a tree: one row per entry, indented
  20 px per level, long titles wrapped; entries with children have a disclosure triangle (▼
  open, ▶ closed; entries with a positive `/Count` start open); clicking a triangle collapses
  or expands the subtree (`Sidebar.toggle`: the rows of a closed entry's subtree are elided
  through one tag per ancestor), clicking a title jumps to its destination and marks the row;
  rows highlight under the pointer. The scroll bar appears only when the tree does not fit.
* **Page area**: background `#f0f0f4`, the page with a 1 px grey border.

Not done (visible differences from the reference): no outline header buttons (thumbnail /
attachment views, "find current outline item"), no thumbnails; the menubar stays above the
toolbar; the status line stays at the bottom; fonts are Tk's default (DejaVu Sans on Linux)
instead of the system UI font; canvas drawing on X11 is not antialiased, so icons and rounded
corners are slightly jagged; the zoom menu is a plain Tk menu, not a native select pop-up;
the other annotation tools are later tasks (9.9).

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
| single page (default) | Page Scrolling | No Spreads | one page at a time |
| continuous | Vertical Scrolling | No Spreads | all pages stacked, 10 px apart (`View.pageGap`) |
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
* **Wheel**: in the page scroll modes as in 9.2 (a spread turns after a push past the edge); in
  the continuous modes the wheel simply scrolls the document (`View.wheelStep` without page
  crossing).
* **Rendering and memory**: the current page — in the facing view its whole spread — is
  rendered at once, as before; the other pages in view and one more place before and after
  them (`View.wantedPages`) are rendered one per event-loop turn (`after 1 … renderMore`,
  nearest to the current page first), so scrolling never waits for a slow page: a page not
  rendered yet shows as its white frame. Photos of pages that leave that set are deleted
  (`image delete`), so Tk holds at most the pages in view plus two; the rendered images stay in
  the LRU cache (256 MiB, 64 entries) at the current zoom. Rendering stays synchronous (no
  threads): one slow page still blocks the event loop while it renders.
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
mode, a spinner in pages being rendered, rendering in a background thread.

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
* **Notes**: Add note… (Edit menu: on the selection, else at the window centre; context
  menu: on the selection, else at the right-clicked point) adds a yellow note and opens its
  popup (a small window: text, Delete, Save (Ctrl+Return), Cancel/Escape). A note shows as a
  speech-bubble icon of 20 × 20 page units (the size of a `/Text` annotation icon; it scales
  with the zoom as in PDF.js), its upper-left corner at the point, or right of the first
  quad for a note on text (whose quads get a dashed outline); the icon is kept inside the page.
  The text enters Tk by variable substitution and comes back as one event word, never parsed
  as script.
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

## Saving marks into the PDF (9.5c, 9.5g)

Tk-free flow in `SafePdf/Shell/App/Save.lean` (`#guard` checks), driven by `Viewer.save`,
`saveAs`, `saveTo` and `confirmDiscard`. Plan.md S8/C7: the marks become annotation objects
appended to the file as an **incremental update**; the original bytes are never modified.

* **Save** (Ctrl+S, File → Save, the toolbar's Save) writes `DIR/STEM-annotated.pdf` next to
  the opened file (for an opened `…-annotated.pdf`: that file itself, a further revision).
  It asks first when that means writing into the opened file, or replacing another existing
  file — unless this session wrote the file (so repeated saves are silent). Save is enabled
  only while there are unsaved changes (new marks, saved marks changed or deleted); with none,
  Ctrl+S says "nothing to save".
* **Save As…** (Ctrl+Shift+S) asks for a file (`tk_getSaveFile`, which confirms replacing an
  existing file), proposing `STEM-annotated.pdf`; writing over the **opened file** needs an
  explicit yes (its bytes still stay a prefix of the new file). With no unsaved marks it
  writes a plain copy.
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
* **Unsaved changes**: the title starts with `* `; Close (Ctrl+W), Quit (Ctrl+Q, File → Quit,
  the window's close button: `wm protocol WM_DELETE_WINDOW`) and Open… ask Save / Discard /
  Cancel (a Tk message box: Yes / No / Cancel).
* **Errors** (an encrypted document, refused by the writer until 9.5f; a document opened
  through the repair path; a failed check; a write error) appear in the status line as
  `cannot save to NAME: …`; nothing is written and the marks stay unsaved.

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
  small rounded bubble with the Highlight icon; its right edge is at the end of the lowest
  selected line and its top 6 px below it (PDF.js `#getLastPoint`,
  `--editor-toolbar-vert-offset`), above the selection when it would leave the scroll region
  at the bottom, and clamped into it (`Bubble.place`). Clicking it highlights in the current
  colour (Edit → Highlight selection's script, `Bubble.Btn.cmd?`).
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
swatches have jagged edges; the bubble buttons have no hover background or tooltips; the
pop-over is a rectangle window, so its rounded corners show the canvas colour behind them
(`#f0f0f4`); the toolbar's toggled Highlight button is grey, not PDF.js's lavender; fonts are
Tk's default; a comment is a separate note mark anchored to the highlight's quads (PDF.js
keeps the comment in the highlight annotation), so deleting the highlight leaves its note.

| Key / mouse | Action |
|---|---|
| mouse-up after selecting | float bubble (with the Highlight tool on: highlight at once) |
| bubble buttons | Highlight; colour ▾ (picker), Comment, Delete |
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
| right button | menu: Copy, Select all, Find…, Highlight ▸, Add note…, Delete mark, … |
| `Ctrl+F` | open the find bar |
| `Enter`, `F3` / `Shift+Enter`, `Shift+F3` | next / previous hit |
| `Escape` (in the find bar) | close the find bar |

## Outline, links, history, page labels (8.2d)

Pure logic in `SafePdf/Shell/App/Links.lean` (Tk-free, `#guard` checks and theorems); all
data comes from the verified navigation layer `Core.Doc.Nav` (task 4.2: visited sets cut
outline and name-tree cycles, every walk is bounded by the object count).

* **Outline panel**: a tree in the left pane of a paned window (restyled after PDF.js in 9.7, see above; drag the sash to
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
links. Continuous scrolling: see *View modes (9.3)*.

## Structure

| File | Role |
|---|---|
| `c/tk_shim.c` | Tcl interpreter, Tk init, `::safepdf::emit` → Lean callback, `Tk_PhotoPutBlock` from an RGBA `ByteArray`, event loop. Adapted from bib-lean's `c/tk_shim.c`. |
| `SafePdf/Shell/App/Shim.lean` | `@[extern]` bindings and the exported dispatcher `safepdf_gui_dispatch`. Only the `viewer` executable may import it. |
| `SafePdf/Shell/App/Tcl.lean`, `TclLemmas.lean` | Tcl scripts as data and the proof that `Tcl.quote` is injection-free (`parseWordStr_quote`, `parseScript_render`, …). Copied from bib-lean `BibLean/Gui/Tcl.lean` + `Tcl/Lemmas.lean`. Built by default (lib `SafePdfApp`). |
| `SafePdf/Shell/App/View.lean` | Tk-free viewing logic with `#guard` checks: zoom modes/steps/cap, C2 re-anchoring (`reanchor`, `reanchor_self`), Tcl number parsing, wheel scrolling across pages (`wheelStep`, 9.2), view modes (9.3: spreads, paging by spread, page layout, visible and wanted pages, page at a point, scroll positions, fit box; theorems `mem_spreadPages`, `nextPage_spread`, `stack_pairwise`), the LRU page cache. |
| `SafePdf/Shell/App/Select.lean` | Tk-free selection and search logic with `#guard` checks: glyph cells in reading order (`cellsOf`, text equal to `Text.layout`'s), boxes, nearest glyph, drag range, word, copy text, highlight boxes, normalised search with hits mapped back to glyphs (`findAll_sound`). Lib `SafePdfApp`. |
| `SafePdf/Shell/App/Links.lean` | Tk-free navigation logic with `#guard` checks: PDF text strings, URI display (`uriText_ascii`), destinations and their positions, page links with URIs, topmost link at a point, outline entries and treeview parents, page-label display and Ctrl+G lookup, back/forward history (`History.back_push`). |
| `SafePdf/Shell/App/Menu.lean` | Tk-free command and menubar model with `#guard` checks: commands (label, accelerator, script, enabled rule), menus, entry indices (task 9.1); mark commands, colour cascades and the context menu's mark entries (task 9.4). |
| `SafePdf/Shell/App/Marks.lean` | Tk-free model of highlights and notes with `#guard` checks: PDF.js colours, marks with stable ids and `/NM` names, quads and `/QuadPoints`, note icon boxes, the store (add, remove, recolour, edit, restore), hit-testing, the multiply blend into the page image (task 9.4). |
| `SafePdf/Shell/App/Save.lean` | Tk-free save flow (task 9.5c) with `#guard` checks: marks → `Core.Write.Annots.Mark`, PDF dates, reading our marks back from a document, the read-back check, default target, atomic write. |
| `SafePdf/Shell/App/Bubble.lean` | Tk-free selection bubble and Highlight pop-over logic with `#guard` checks: bubble kinds and button layout after PDF.js, placement at the selection's last point with clamping (`place_inside`), hit-testing, the colour picker, the pop-over layout and hits, thickness slider mapping, tool state (task 9.8). |
| `SafePdf/Shell/App/Toolbar.lean` | Tk-free toolbar model after PDF.js with `#guard` checks: layout of the three groups, buttons and their enabled/visible rules, tools, overflow menu, all enabled-state targets, page-field text and parsing, zoom choices (labels, keys, Automatic Zoom rule) (task 9.7). |
| `SafePdf/Shell/App/Sidebar.lean` | Tk-free outline-sidebar model with `#guard` checks: when it shows, tree rows (parents, ancestors, children), open/closed state, visible rows, triangles, indentation (task 9.7). |
| `SafePdf/Shell/App/Viewer.lean` | State, menubar, toolbar and sidebar (built from the models), page layout on the canvas (9.3: slots, per-page photos, deferred rendering), scrolling/zoom/rotation/view-mode handlers, prefetch, selection/copy/search handlers and highlights, outline panel, link hover/activation, history, go-to bar, smoke mode. |
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
`safe-pdf`, document entries disabled) and File → Quit, which ends the run. Before closing, the
same run checks the wheel (9.2) with generated Tk 9 `<MouseWheel>` events: in fit page one
notch down turns to page 2 and one up back to page 1; at 200 % notches scroll page 1 down,
the view reaches the bottom and exactly one notch more turns to the top of page 2; eleven
1/12-notch deltas up leave page 2, the twelfth turns to the bottom of page 1; twelve 1/12
notches scroll as far as one notch (within 1.5 px); `<Button-5>`/`<Button-4>` scroll down and
back; Shift+wheel scrolls horizontally to the right edge and the page stays.

The toolbar and sidebar (9.7) run in a fifth variant (`SAFEPDF_VIEWER_SMOKE_MODE=toolbar`,
`Viewer.smokeToolbar`), once on the three-page labelled PDF with an outline and once on the
two-page PDF without one. It checks: the packed widgets of the three toolbar groups (the
sidebar toggle only with an outline); the sidebar open with an outline (panes `.ol .v`, toggle
drawn pressed) and absent without (`.v`, toggle unmapped); the page field `i` / `(1 of 3)`
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
`::safepdf::lastAsk`). On a copy of the text PDF: a highlight on `world` and a note make the
title start with `* ` and enable Save (menu entry and toolbar button); Quit and Ctrl+W
answered Cancel keep everything; Ctrl+S writes `text-annotated.pdf` without a question and
opens it (2 saved marks, no `*`, Save disabled; the highlight pixels are yellow from the
renderer, no canvas note icon, the note text restored); a second Ctrl+S writes nothing; the
saved highlight can be selected; a new highlight on `safe` + Ctrl+S appends
to the same file (3 marks with distinct ids, read back strictly); Save As writes
`saveas.pdf`; a new note and Ctrl+W answered No discards it. The `reopen` run on
`text-annotated.pdf` restores the 3 marks (pixels, a click on the note's place opens its popup
with the saved text), Save As onto the opened file answered No writes nothing and Yes
appends, and Quit answered Yes saves one more note before quitting. The script then checks
`qpdf --check` on the written files, that the original (and each saved revision) is a
byte-for-byte prefix of the later file (`cmp -n`) and the original unchanged, that the final
file has 5 revisions and each of its 5 mark annotations once, and that `mutool draw` shows the
highlight (yellow pixels in the box of `world`). The `edit` run (9.5g, `Viewer.smokeEdit`) on
a copy of that file deletes the whole-page highlight and the `safe` highlight, recolours the
`world` highlight green (pixels follow at once from the preview) and gives it a comment, edits
a note's text, saves into the opened file (4 marks, comment restored with its id, its icon
drawn), then a third revision on top (blue, comment deleted: 3 marks); the script checks
`qpdf --check`, the byte prefixes, no duplicate ids, and that `mutool draw` shows `world`
green (then blue) and no tint in the box of `safe`. The `encrypted` run (RC4 fixture) saves a
note: until 9.5f the status line shows the writer's refusal and nothing is written.

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

A 9.4 screenshot (`arxiv-1706.03762.pdf`, two abstract lines highlighted in yellow, a note
with its popup) was taken this way, with `xdotool` driving drag, `h`, right click and the
popup.

Screenshots for comparison with the reference can be taken under Xvfb at the reference size,
e.g. `Xvfb :97 -screen 0 1900x940x24 &`, then
`DISPLAY=:97 SAFEPDF_VIEWER_GEOMETRY=1900x940 .lake/build/bin/viewer FILE.pdf &` and
`DISPLAY=:97 import -window root shot.png` (ImageMagick).

CI: the workflow cannot be pushed from the sandbox; the job that installs `tk-dev`/`xvfb`,
builds `viewer` and runs the smoke test is in `docs/ci-viewer-step.patch` (it also points the
cache keys at `lakefile.lean`).
