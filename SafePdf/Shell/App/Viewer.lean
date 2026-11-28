import SafePdf.Shell.App.Shim
import SafePdf.Shell.App.Tcl
import SafePdf.Shell.App.View
import SafePdf.Shell.App.Select
import SafePdf.Shell.App.Links
import SafePdf.Shell.App.Menu
import SafePdf.Shell.App.Toolbar
import SafePdf.Shell.App.Sidebar
import SafePdf.Shell.App.Attach
import SafePdf.Shell.App.Marks
import SafePdf.Shell.App.Bubble
import SafePdf.Shell.App.Save
import SafePdf.Shell.App.Xfdf
import SafePdf.Shell.App.Icons
import SafePdf.Shell.App.Budget
import SafePdf.Core.Annot
import SafePdf.Shell.Inspect
import SafePdf.Shell.Views.Pages
import SafePdf.Shell.Fonts
import SafePdf.Shell.Worker.Client

/-!
# Native viewer (tasks 8.2a–8.2d, 9.1–9.4, 9.5c, 9.7, 9.8; Plan.md §6 Phases 8–9, §8 native app, §10 `SafePdf/Shell/`)

The unverified, replaceable shell of the viewer (Plan.md §8): one Tk window with a menubar
(File / Edit / View / Go, built from the Tk-free model `Menu.menubar`, entries enabled by
`Menu.Cmd.enabled` and kept in step after every event by `syncMenus`; task 9.1), a toolbar and
a sidebar imitating PDF.js, Firefox's viewer (task 9.7; built from the Tk-free models
`Toolbar.layout` and `Sidebar.rows`; since task 9.r9 with view buttons for its panels
(`Sidebar.panels`): the outline, lazily rendered page thumbnails (`thumbView`), attachments
(task 9.r10) and layers (task 9.r11b, `fillLayers`, `layerClick`)): sidebar toggle, page arrows, page field, zoom −/+ and
drop-down, the Highlight tool (task 9.4) and disabled placeholders for the other annotation
tools, `»` overflow menu; the design reference is
cited in `docs/viewer.md`, nothing of PDF.js is copied), a scrollable canvas showing the
current page as a Tk photo image, and a status line.
Ledger Decisions 8.1 chose Tcl/Tk through the C shim `c/tk_shim.c`.

* **Opening.** A file named on the command line, else `tk_getOpenFile` (also Ctrl+O and the
  Open… button). The file is read and parsed exactly as the inspector does
  (`Inspect.load`: size check against `Limits.maxInputBytes`, `SafePdf.parseWith`), then
  `Views.Pages.docOf` builds the page tree.
* **Rendering.** The verified full-page renderer `Core.Raster.Glyph.renderDocPage` with a
  fresh decoded-bytes budget per page (as the inspector's `raster` view), at the zoom of the
  current `View.Mode` (fit page, fit width, or a percentage of actual size: 100 % = 72 dpi ×
  `tk scaling`) and the user rotation (added to the page's `/Rotate` by the renderer through
  `rotAdd`). Zoom is capped at `Budget.Ceilings.pagePixels` (task 12.3b) pixels per page image (status line says
  so); a side above `Limits.maxPageSide` is cropped by the renderer (status line says so).
  Non-embedded fonts are painted with the substitute programs `Shell.Fonts.loadSubstFonts`
  finds at start-up (task 7.7, `docs/raster.md`; `State.subst`).
* **Page cache** (`View.Cache`): render results keyed by (document generation, page, zoom,
  rotation), LRU, at most `Budget.Ceilings.cacheBytes` (96 MiB) of images. After a page is shown the
  next page is prefetched 100 ms later (on a worker, below) when it is at most
  `prefetchPixels` pixels.
* **Rendering on worker threads** (task 8.8). Every render runs on a dedicated thread
  (`submit`: `IO.asTask` around the pure renderer; at most `maxJobs` at once, one kept free for
  the current page); Tk is only touched on the main thread. An event that must show the
  current page (its spread) waits for its render at most `State.syncWaitMs` (100 ms; smoke
  mode: until done), so fast pages appear at once; otherwise the page shows its white frame
  with a small "Rendering…" (`showWaiting`) and a `poll` event every `pollMs` while renders
  run takes the finished ones (`finish`, into the cache) and shows those still wanted
  (`place`): the same document, zoom and rotation (the cache key, which carries the document
  generation), page in view. Results for an old zoom, rotation or document are dropped
  (`staleDropped`); a render cannot be interrupted (the renderer is pure), so it keeps its
  slot until it ends. `main` exits the process when the window closes instead of waiting for
  a running render.
* **Scrolling.** The canvas has scroll bars; its scroll region is the page image plus a margin.
  Keys (Tcl proc `::safepdf::step`): `Down`/`Up` and `Right`/`Left` scroll by a tenth of the window,
  `Next`/`space` and `Prior`/`BackSpace`/`Shift+space` by a window. Past the bottom (right) edge
  they move to the top of the next page; past the top they move to the bottom of the previous
  page (page-at-a-time). The mouse wheel does the same (task 9.2, `wheel`, logic in
  `View.wheelStep`: small deltas accumulate, the page turns only after the view reached the
  edge and the wheel pushes on past it; task 9.r1: each axis has its own state, nothing is
  swallowed after a turn and the push beyond the threshold flows on into the new page);
  Shift+wheel scrolls horizontally without turning pages; Ctrl+wheel zooms about the mouse
  pointer.
* **View modes** (task 9.3, pure layout in `View`): the View menu and the overflow menu choose
  the scroll mode (Page / Vertical Scrolling) and the spread mode (No / Odd / Even Spreads):
  single page, continuous, facing, continuous facing. Files open in continuous (Vertical
  Scrolling, No Spreads; task 9.r1). `computeLayout` places the pages
  (`View.layoutRows`) as `Slot`s; every page on the canvas has a white frame and its own photo
  `::safepdf::pgN`; the current page (its spread in the facing view) is shown first, the
  other pages in view and their neighbours follow (`viewChanged`, `renderMore`, workers and
  `poll`), and photos of pages out of view are deleted. In the continuous modes the
  current page is the page under the window centre, the wheel just scrolls, and paging moves by
  spreads. Pointer positions map through the slot of the page under them (`pagePointAt`), so
  selection, links, marks, bubbles and search work on every page shown.
* **Anchoring (C2).** Before a zoom or rotation change the viewer reads the canvas point under
  the mouse (Ctrl+wheel) or at the window centre, maps it to page space with `Geom.toPage`;
  after the new image is shown it maps that page point back with `Geom.toScreen`
  (`View.reanchor`) and scrolls so it lies under the same window position.
* **Selection and copy** (task 8.2c, pure logic in `Select`). A page's text is extracted on
  first use (`Annot.extractDocPageAnnots`, fresh budget, as the text view) and cached per page
  as a `Select.PageIndex` (glyph cells in reading order with page-space boxes, plus the
  normalised search text). A mouse press/drag/release maps the window positions to page space
  with `Geom.toPage` and selects the glyphs between the nearest glyphs in reading order;
  double-click selects a word; Ctrl+A the page. The selection is drawn over the page image
  (tag `sel`; the image is not re-rendered) as one translucent light-blue band per line on
  both platforms (task 10.18, `Select.selBands`: full line height, consecutive lines of a
  paragraph touching; photo image items, `Tint`, `::safepdf::tint` of task 10.10). Ctrl+C or the
  context menu (right button) copies `Select.rangeText` to the clipboard (`clipboard append`,
  the text passed as one quoted word).
* **Search** (Ctrl+F opens the find bar; Enter/F3 next, Shift+Enter/Shift+F3 previous, Escape
  closes): case-insensitive, whitespace-normalised (`Select.normQuery`), page by page from the
  current hit, wrapping around the document; pages are extracted lazily. All hits of the
  current page are highlighted (tag `hit`, the current one in orange) and the current hit is
  scrolled into view; the status line says `"q": hit k/n on page p` (k of the n hits of that
  page) or `"q": not found`.
* **Navigation** (task 8.2d, pure logic in `Links`). The outline (`Nav.outline`) fills a
  tree (a text widget, task 9.7) in the left pane of a paned window (the sidebar, opened as the
  page mode says, `Sidebar.onLoad`; F9, the sidebar button or the context menu toggle it); clicking an item jumps to its
  destination page, scrolled to the destination's position (`/XYZ`, `/FitH`, `/FitR`, … left/top
  mapped with `Geom.toScreen`, C2). Links (`Links.pageLinks`, read per page on first use):
  over a link the cursor is a hand and the status line shows the target (`go to page …`, or
  the full address of a URI as `Links.uriText`); a click in place on an internal link (also
  through a named destination) jumps; a click on a URI link opens the `::safepdf::askUri`
  dialog showing the exact address and, only when confirmed, copies it to the clipboard —
  nothing is ever opened or launched. Jumps (links, outline, Ctrl+G) record the previous place
  (page and scroll fractions) in a back/forward history (Alt+Left/Alt+Right, toolbar). Page
  labels (`Nav.labelTable`) appear in the title, toolbar and status line (`page iii (3/120)`);
  Ctrl+G opens a go-to bar accepting a label or a page number (`Links.gotoPage`).
* **Attachments** (task 9.r10, data from the verified `Core.Doc.Attachments`, model in
  `Attach`): the sidebar's attachments panel (`.ol.at`, plugged into 9.r9's switcher) lists
  the embedded files (name, size known without decoding; description and details as a
  tooltip). Files are decoded only on demand: Save attachment as… (double-click, Return, the
  context menu; `saveAttachment` writes the decoded bytes to a file chosen with
  `tk_getSaveFile`, the opened PDF, read-only files and folders refused, `Save.writeAtomic`)
  and the tooltip's probe (at most 16 MB, `attProbe`). An attachment is never opened or run.
  A click on a file attachment annotation's icon selects its row.
* **Marks** (task 9.4, pure model in `Marks`): highlights of the selection in PDF.js's five
  colours (toolbar Highlight button, `h`, Edit menu, context-menu colour cascade) and notes
  (Add note… on the selection or at the right-clicked point; a popup edits the text), kept in
  memory per document in page space (`Marks.Store`, stable ids). Highlights are multiplied
  into the shown page image (`Marks.composite`, PDF.js's `mix-blend-mode: multiply`); note
  icons, note anchors and the selected-mark outline are canvas items (tag `mark`). A click on
  a mark selects it (a note also opens its popup); Delete or Edit → Delete mark removes it,
  a colour entry recolours it.
* **Selection bubble and Highlight pop-over** (task 9.8, pure logic in `Bubble`): after a
  text selection a floating bubble at the selection's end with Highlight and Add comment (task
  9.r4: a note anchored to the selection; tooltips on both); on a selected highlight
  the edit bubble (colour swatch with a picker, Comment, Delete), canvas items placed again on
  every redraw (`drawBubble`); the toolbar's Highlight button without a selection toggles the
  Highlight tool and its pop-over `.hlbar` (swatches, thickness slider, "Show all"; `syncTool`,
  `drawPopover`); with the tool on a mouse-up that selects text highlights it at once; Escape
  closes the pop-over and dismisses the bubble.
* **Dismissal** (task 10.6, rule in `Toolbar.Transient`): the note popup, the colour picker,
  the Highlight and Add text / Draw pop-overs and the go-to / find bars all close on Escape
  (the topmost one; only with none open does Escape leave full screen) and on a mouse press
  elsewhere in the main window (`::safepdf::clickAway` on the tag `all`, `clickAway`; the
  press is not consumed). A press on the page keeps the tool pop-overs (their tool is in use
  there) and is the picker's own (`press`); the note closes through `noteDone … close`
  (9.r12); opening the find or go-to bar closes the other (`opening`).
* **Review 2026-11-23** (task 9.r4): the toolbar's view-mode drop-down `.bar.vmode` after the
  page count (`Toolbar.ViewChoice`, kept in sync with the View and `»` menus by
  `setViewMode` / `showViewChoice`); opening or closing the outline sidebar lays the pages out
  for the canvas's new width from inside its `<Configure>` binding (`showOutline`,
  `::safepdf::resizeSoon`), so the page never shows at the old offset (the Page Fit flicker).
* **Add text and Draw** (task 9.9, PDF.js's FreeText and Ink editors; pure state in
  `Bubble.Ui`/`Bubble.EdPop`, marks in `Marks`): the toolbar's Add text and Draw buttons turn
  their mode on with a parameter pop-over `.edbar` (`drawEdPop`: colour swatches, Font size /
  Thickness / Opacity sliders), exclusive with the Highlight tool. Add text: a click on the
  page opens a text box (a Tk text widget in a canvas window, tag `ftedit`, Helvetica at the
  font size × zoom in the chosen colour); a click elsewhere or Escape commits it as a free-text
  mark (an empty box is dropped); a double click on a text box edits it again. Draw: each
  press–drag–release draws a stroke (canvas line `inkcur`); the strokes of one session (until
  the mode is left, Escape, or the drawing is on another page) form one ink mark. Free text
  and drawings are selected by a click, moved by dragging them (`Marks.Store.translate`),
  deleted with Delete or their bubble's Delete; the pop-over's colour and sliders apply to the
  selected one of the mode's kind. Unsaved ones are canvas items (`drawMarks`), saved ones are
  drawn by the renderer from their appearance streams (edits through the preview). Add
  comment adds a note (`addNote`).
* **Delete, undo and redo** (task 10.7): Delete or Backspace removes the selected mark
  (Backspace without one scrolls back, as before); Ctrl+Z / Edit → Undo and Ctrl+Shift+Z /
  Edit → Redo (Command+Z / Command+Shift+Z on macOS) step through `Marks.History`: every edit
  is recorded by `marksChanged` (one slider drag is one step), at most 100 steps, cleared
  when a document is opened (also the reopen after Save: the file's marks are read back
  rounded, so the steps before it would not line up). Only the marks are restored, so the
  title's `*` and Save follow `Marks.Store.dirty`: undoing back to the opened state is clean.
  The text fields (note popup, find and go-to bars, page field, text box) have their own bind
  tags, so their Backspace, Delete and Ctrl+Z stay theirs.
* **macOS keys and the icon** (task 9.r3): after the window is built, `Menu.platformScript`
  gives every Ctrl binding its Command twin on aqua (menu labels `Command-S`, ⌘ in the Save
  tooltip and status hints via `keyText`, `::tk::mac::Quit` → Quit); `setIcon` sets the
  embedded `Icons` PNGs with `wm iconphoto . -default`. Task 10.9 adds the macOS
  conventions (`Menu.Cmd.macKeys`, `Menu.Action`: ⌘G / ⇧⌘G find, ⌥⌘G go to page, ⌘[ / ⌘],
  ⌘↑ / ⌘↓, ⌃⌘S, ⌃⌘H, ⌘R / ⌘L, ⌘9) and ⌘. in the dialogs (`::safepdf::cancelBind`).
* **Saving** (tasks 9.5c, 9.r2; Tk-free flow and decisions in `Save`): Ctrl+S / File → Save /
  the toolbar's Save writes the unsaved marks **into the opened file** as an incremental
  update (Plan S8/C7, Decision 2026-11-23), checked by a strict reopen and read-back, refused
  when the file changed on disk since it was opened (then Save As… is offered) or is
  read-only, written to a temporary file next to it and renamed over it (permissions kept),
  then reopened in place; the first overwrite of a session asks Overwrite / Save As… / Cancel
  (`overwriteInto`). Save As… (Ctrl+Shift+S) writes a chosen new file, proposing
  `STEM-annotated.pdf`. On open our marks (`/NM safepdf-mark-ID`) are restored as saved marks, drawn by the
  renderer. Saved marks can be recoloured, deleted and their text edited (task 9.5g): Save
  writes one update with additions, supersessions and removals (writer rule W11); until then
  the pages are rendered from a **preview** (`State.view`, `updatePreview`: the same writer's
  output with only the edits of saved marks, built in memory and reopened strictly), so an
  edit shows at once. A highlight's comment is written into it (`/Contents` + `/Popup`, as
  pdf.js); its icon is drawn by the viewer. The title starts with `* ` while there are
  unsaved changes; Close, Quit (menu, Ctrl+Q, `::safepdf::quit`, `::tk::mac::Quit` on aqua),
  the window's close button and Open… ask Save / Don't Save / Cancel (`confirmDiscard`; a
  failed save or Cancel keeps the document). Writer errors go to the status line.
* **XFDF** (task 9.11, Tk-free reader/writer in `Xfdf`): File → Import annotations… /
  Export annotations… (also in the `»` menu) with Tk file dialogs filtered to `.xfdf`. Import
  reads the file bounded and total (`Xfdf.readFile`, pages checked against the document),
  adds the marks not already present as unsaved marks (`Xfdf.importItems`) and reports
  "N imported, D already present, S skipped"; a refused file (DTD, unknown entity, limits,
  not XFDF, unreadable) only puts `Xfdf.Error.message` into the status line and changes
  nothing. Export writes every mark (`Xfdf.toXfdf`, a highlight's comment as `<contents>` of
  the `<highlight>`) atomically (`Save.writeAtomic`) to the chosen file, `STEM.xfdf` next to
  the PDF by default.
* **Errors** (unreadable file, parse error, render error, Tcl error) are shown in the status
  line; the window stays usable. Every event handler catches its own exceptions.
* **No data in script text.** Every Tcl command that carries data (file names, error messages,
  numbers) is built with `Tcl.cmd`/`Script.render`, whose literal words go through the proved
  `Tcl.quote` (`Tcl.parseScript_render`); the only raw script text is the constant UI setup.
* **No Tcl from other X clients** (task 8.7, defence in depth): Tk's `send` would let any
  client of the display evaluate Tcl (`exec` included) in the viewer, so `mainWith` deletes
  the `send` command right after Tk starts (`sendOffScript`), which also withdraws the
  application from the display's registry (`winfo interps`), unless the test hook
  `SAFEPDF_VIEWER_DRIVE=1` keeps it for `scripts/viewer-corpus.sh`. The X resource database
  (also writable by any client of the display) could give widgets script-valued options
  (`*Entry.validateCommand`, `*Menu.postCommand`, `*takeFocus`, …); `setupScript` first
  overrides every such option name (`resourceGuardScript`).
* **Library documents** (task 10.1b, `viewer --biblean`): `mainWith` runs an `init` after the
  window is built; bib-lean's reader mode opens its bytes there from memory (`openBytes`,
  nothing on disk; `State.inMemory`), titled with `State.titleOverride`, with a `Library`
  attached: every change of the marks is reported (`marksChanged`), Save is "Save to library"
  (`saveToLibrary`: `Save.build`'s bytes to the library, then reopened from memory), Save As…
  writes a local copy and stays on the library's document, Close flushes the library.
* **Document worker** (task 12.2c, Plan.md §6 Phase 12; `Worker.Session` in
  `SafePdf/Shell/Worker/Client.lean`). Pages and thumbnails are rendered, and the outline is
  read, by the `worker` executable found next to the viewer's (`workerExe`): one process per
  open document, sent the bytes the viewer read (capped, task 12.1; Save keeps using them).
  `submit`/`thumbSubmit` queue a render (`renderTask`: priority 0 for the current page or
  spread, 1 for other pages and the prefetch, 2 for thumbnails) and get a task, so `poll` and
  `showNow` work as with the render threads of task 8.8 and no event waits on the worker's
  pipes (except where it did before: `showNow`'s 100 ms and smoke mode). Superseded renders
  (an old zoom, rotation or document) are cancelled (`cancelStale`): dropped while queued,
  the worker killed and restarted when one runs longer than `preemptMs`; a page that blocks
  the current page is preempted the same way and rendered again later. A render without an
  answer within `workerDeadlineMs` (20 s) kills the worker: the page shows "rendering stopped:
  the document took too long", and the next request starts a fresh worker with the bytes
  again. Task 12.2d: renders carry the layers state (`State.oc`); the worker is started with
  the viewer's limits and font search as flags (`workerStart`: `SAFEPDF_SUBST_FONTS=0`,
  `$HOME`, `$SAFEPDF_FONT_DIR`); the selection/search text index (`pageIndex`) and the links
  (`linksOf`) come from the worker while the pages are rendered from the opened document
  itself (`workerForText`), asked for when a page is rendered so that pointer motion never
  waits (`wait := false`). In-process (as in task 8.8) remain: the whole viewer when the worker
  executable is missing (status note) or `SAFEPDF_VIEWER_WORKER=0`; the text index and links
  while edited saved marks are previewed (`State.view`); the parse the GUI keeps for layout,
  page labels, open settings, attachments, the layers panel and Save (`docs/viewer.md`).
* **Smoke mode** (`SAFEPDF_VIEWER_SMOKE=DIR`, used by `scripts/viewer-smoke.sh`): drives the
  viewer with Tk key events (`event generate`) and writes photos and state files into `DIR`
  (see `smoke`), then exits.

`docs/viewer.md` describes building and running it.
-/

namespace SafePdf.Shell.App.Viewer

open SafePdf.Shell
open SafePdf.Core.Doc (Doc)
open SafePdf.Core.Raster (Clip.Image)
open SafePdf.Core.Raster.Geom (Pt Box rotAdd toPage toScreen)

/-! ## State -/

/-- Where to scroll after the next page image is shown. -/
inductive ScrollTo where
  /-- Top of the page (left edge kept). -/
  | top
  /-- Bottom of the page. -/
  | bottom
  /-- Keep the point `p` of page `page` under the window position `(wx, wy)` (C2 anchoring). -/
  | anchor (page wx wy : Nat) (p : Pt)
  /-- Show the page point (`left`, `top`) at the window's top-left corner (a destination's
  position; a missing coordinate is the page's left or top edge). -/
  | dest (left top : Option Rat)
  /-- Restore the scroll fractions `(x, y)` (history). -/
  | frac (x y : Rat)
  /-- Put the view's top `f` page heights below the top of page `page` (task 9.3: a new
  layout of the vertical modes keeps the place in the current page). -/
  | within (page : Nat) (f : Rat)

/-- How page `p` is displayed: zoom, total rotation (`/Rotate` + user rotation), page box,
whether the zoom was capped and whether the image is cropped. -/
structure ViewParams where
  /-- Zoom in pixels per page unit. -/
  zoom : Rat
  /-- Total rotation. -/
  rot : SafePdf.Core.Doc.Rotation
  /-- CropBox. -/
  box : Box
  /-- The zoom was lowered to `Budget.Ceilings.pagePixels`. -/
  capped : Bool
  /-- The image is cropped to `Limits.maxPageSide`. -/
  cropped : Bool

/-- A page laid out in the scroll region (task 9.3): its place (`View.layoutRows`) and how it
is displayed. -/
structure Slot where
  /-- Canvas position and pixel size of the page image. -/
  place : View.Place
  /-- Zoom, rotation and box it is drawn with. -/
  vp : ViewParams

/-- What a layout depends on (task 9.3): a change means a new layout. In the page scroll mode
the spread shown is part of it; in the vertical modes the current page is not (scrolling never
lays the pages out again). -/
structure LayoutKey where
  /-- Document generation. -/
  gen : Nat
  /-- Scroll mode. -/
  scroll : View.ScrollMode
  /-- Spread mode. -/
  spread : View.SpreadMode
  /-- Zoom choice. -/
  zoomSel : Toolbar.ZoomChoice
  /-- User rotation. -/
  rot : SafePdf.Core.Doc.Rotation
  /-- Canvas width. -/
  canvasW : Nat
  /-- Canvas height. -/
  canvasH : Nat
  /-- The spread shown (page scroll mode), else 0. -/
  spreadIx : Nat
  deriving DecidableEq

/-- The library the open document belongs to (task 10.1b, bib-lean's reader mode): hooks into
`BibLean.Annots.Sync`, kept Tk- and HTTP-free here so the viewer does not depend on the
bib-lean modules. Each hook returns at once (the sync works on its own thread), except
`flush`. -/
structure Library where
  /-- The marks after every change of `State.marks` (add, remove, recolour, text, import, a
  save): posted as the library's annotation set after the debounce. -/
  onMarksChanged : Marks.Store → IO Unit
  /-- The document's bytes with the marks written in (`Save.build`), on Save: the library's
  new file (`PUT`). -/
  onSaved : ByteArray → IO Unit
  /-- Sends what is pending without the debounce, waiting at most a grace period; `true` when
  everything was sent (Close; `Main.lean` calls it again after the window closed). -/
  flush : IO Bool

/-- How many partial pages `State.partialKeys` remembers (task 13.4d). -/
def partialKeysMax : Nat := 256

/-- What a render job gives: the result and the render time (ns), or `none` when it was
cancelled (task 12.2c: superseded before the worker answered; nothing is shown or cached). -/
abbrev RenderOut := Option (Except Error Clip.Image × Nat)

/-- A page render running on a worker thread (task 8.8) or queued for the document worker
(task 12.2c): what it renders, when it was asked for (`IO.monoNanosNow`), the task, which
returns the result and the render time in nanoseconds, and the worker request id. -/
structure Job where
  /-- Document generation, page, zoom and rotation rendered. -/
  key : View.Key
  /-- Submission time (ns). -/
  start : Nat
  /-- The render (`IO.asTask` on a dedicated thread, or the worker's reply). -/
  task : Task RenderOut
  /-- The worker request (`Worker.Session.cancel`); `none` for an in-process render. -/
  id : Option Nat := none
  /-- Its reservation in `State.pool` (task 12.3), released when the job leaves its list. -/
  ticket : Option Budget.Ticket := none
  /-- Task 13.4d: finishes with `task`; `true` when the image is a **partial page** (the
  render work allowance was spent: the document worker answered `image … (complete := false)`,
  or the in-process render's `PageRender.exceeded`). -/
  incomplete : Task Bool := .pure false

/-- A text-index or links request queued for the document worker (task 12.2d): the page, the
document generation it was asked for, the worker request id and the reply. -/
structure SideJob where
  /-- Page index. -/
  page : Nat
  /-- `State.gen` when it was asked for (a reply for another generation is not cached). -/
  gen : Nat
  /-- The worker request (`Worker.Session.cancel`, `raise`). -/
  id : Nat
  /-- The worker's reply. -/
  task : Task Worker.Reply
  /-- Its reservation in `State.pool` (task 12.3), released when the reply is there or the
  request is dropped (`sweepSide`, `dropSideJob`). -/
  ticket : Option Budget.Ticket := none

/-- The free-text editor open on the canvas (task 9.9). -/
structure FtEdit where
  /-- The mark it edits (`none`: a new one). -/
  id : Option Nat
  /-- Page index. -/
  page : Nat
  /-- Upper-left corner of the box (page space). -/
  pos : Pt
  /-- Font size. -/
  size : Nat
  /-- Text colour. -/
  rgb : Marks.Rgb

/-- The viewer's state, kept in one `IO.Ref`. -/
structure State where
  /-- Path of the open file, if any (`inMemory`: only a display name). -/
  path : Option String := none
  /-- The document was opened from memory (`openBytes`, task 10.1b): there is no file at
  `path`, which only names the document (dialogs propose files next to it). -/
  inMemory : Bool := false
  /-- Shown in the window title instead of the file name (task 10.1b: bib-lean's item title). -/
  titleOverride : Option String := none
  /-- The library the document comes from (task 10.1b, `viewer --biblean`): marks are synced
  to it after every change and Save sends the annotated file to it instead of writing a local
  file (`saveToLibrary`); `none` for a local file. -/
  library : Option Library := none
  /-- The opened document (`none`: no file, or it failed to open). -/
  doc : Option Doc := none
  /-- The document the pages are rendered from while saved marks are edited (task 9.5g:
  `doc` with those edits applied in memory, `Save.preview`); `none`: `doc` itself. -/
  view : Option Doc := none
  /-- Document generation, bumped on every open (part of the cache key). -/
  gen : Nat := 0
  /-- Current page, 0-based. -/
  page : Nat := 0
  /-- Canvas width in pixels (last `<Configure>`). -/
  canvasW : Nat := 800
  /-- Canvas height in pixels (last `<Configure>`). -/
  canvasH : Nat := 1000
  /-- Zoom choice (task 9.7: the zoom drop-down's value; Automatic Zoom by default, as PDF.js). -/
  zoomSel : Toolbar.ZoomChoice := .auto
  /-- User rotation (added to each page's `/Rotate`). -/
  rot : SafePdf.Core.Doc.Rotation := .r0
  /-- Screen scale: pixels per point (`tk scaling`). -/
  scaling : Rat := 4 / 3
  /-- Rendered pages (task 12.3b: at most `Budget.ceilings.cacheBytes`). -/
  cache : View.Cache := { budget := Budget.ceilings.cacheBytes }
  /-- Task 13.4d: the keys of the cached pages that are **partial** (the render work allowance
  was spent; the image holds the pixels painted until then). They are shown with the
  stopped-page message and never rendered again for the same key. The newest
  `partialKeysMax` are kept (a lost entry only loses the message). -/
  partialKeys : Array View.Key := #[]
  /-- Substitute programs for non-embedded fonts (task 7.7, `Shell.Fonts`), found at start-up
  and parsed on first use. -/
  subst : SafePdf.Core.Raster.Subst.SubstFonts := {}
  /-- Key of what is on screen (successful or failed render). -/
  shown : Option View.Key := none
  /-- Canvas position of the current page's image, zoom and total rotation it is drawn with
  (the current page's `Slot`, mirrored for anchoring and the smoke tests). -/
  imgX : Nat := View.margin
  /-- See `imgX`. -/
  imgY : Nat := View.margin
  /-- See `imgX`. -/
  shownZoom : Rat := 1
  /-- See `imgX`. -/
  shownRot : SafePdf.Core.Doc.Rotation := .r0
  /-- Scroll to apply after the next image is shown. -/
  pending : Option ScrollTo := none
  /-- Scroll region size (pixels; the whole document in the vertical modes). -/
  regionW : Nat := 1
  /-- See `regionW`. -/
  regionH : Nat := 1
  /-- Text index per page of the open document (`none`: not extracted yet; an error message
  when extraction failed). -/
  texts : Array (Option (Except String Select.PageIndex)) := #[]
  /-- The selection: page, first and last cell (reading order). -/
  sel : Option (Nat × Nat × Nat) := none
  /-- Page point of the mouse press that starts a drag selection. -/
  pressPt : Option Pt := none
  /-- The normalised search query (`Select.normQuery`; empty: no search). -/
  query : Array Char := #[]
  /-- The current search hit: page and index among that page's hits. -/
  hit : Option (Nat × Nat) := none
  /-- Search hits are stippled fills (X11); `false` on Aqua, which has no stipples:
  translucent photo fills (`::safepdf::tint`, task 10.10). The selection is a photo fill on
  both (task 10.18). -/
  stipple : Bool := true
  /-- Smoke-test output directory (`SAFEPDF_VIEWER_SMOKE`). -/
  smokeDir : Option String := none
  /-- Smoke-test variant: `text` runs the selection/search steps (`smokeText`). -/
  smokeMode : String := ""
  /-- Smoke-test step counter. -/
  smokeStep : Nat := 0
  /-- Page labels of the open document as text (task 8.2d). -/
  labels : Array String := #[]
  /-- Outline entries of the open document (outline row `oK` is entry `K`). -/
  outline : Array Links.Entry := #[]
  /-- Whether the sidebar is shown (task 9.r9: with the panel `panel`; the name is from the
  time it only held the outline). -/
  outlineShown : Bool := false
  /-- The sidebar panel shown, or the last one shown while the sidebar is closed (task 9.r9). -/
  panel : Sidebar.Panel := .outline
  /-- The panel buttons last shown (`Sidebar.buttons` keys; `none`: not applied yet). -/
  panelButtons : Option (List String) := none
  /-- Thumbnail layout (task 9.r9, `Sidebar.thumbLayout`) and its height. -/
  thSlots : Array Sidebar.ThumbSlot := #[]
  /-- See `thSlots`. -/
  thHeight : Nat := 0
  /-- Document generation and user rotation the thumbnails are laid out for (`none`: not
  laid out). -/
  thKey : Option (Nat × SafePdf.Core.Doc.Rotation) := none
  /-- Pages with a thumbnail image (photo `::safepdf::thN`), at most `Sidebar.thumbBudget`. -/
  thHave : List Nat := []
  /-- Thumbnail renders running on worker threads (at most `thumbJobs`). -/
  thJobs : Array Job := #[]
  /-- The page whose thumbnail is highlighted as the current one. -/
  thMarked : Option Nat := none
  /-- The keyboard selection in the thumbnails (Up/Down; Return goes there). -/
  thSel : Option Nat := none
  /-- Thumbnails rendered for the open document (smoke tests: lazy rendering). -/
  thRendered : Nat := 0
  /-- When the document was opened (`IO.monoNanosNow`) and how long after that the first
  thumbnail was shown (ns; the `thumbperf` measurement). -/
  thOpenNs : Nat := 0
  /-- See `thOpenNs`. -/
  thFirstNs : Option Nat := none
  /-- Links per page (`none`: not read yet). -/
  links : Array (Option (Array Links.Link)) := #[]
  /-- The link under the mouse pointer: its page and index on that page. -/
  hover : Option (Nat × Nat) := none
  /-- The status line text from before the pointer entered a link (restored on leaving). -/
  savedStatus : String := ""
  /-- The last pointer position over the page canvas (window coordinates; `none` after it
  left), to update the cursor when the tool changes (task 10.8). -/
  pointer : Option (Int × Int) := none
  /-- Back/forward history of jumps. -/
  history : Links.History := {}
  /-- Enabled states last applied to the menubar entries and toolbar buttons
  (`Menu.entryStates` order; empty: not applied yet). -/
  menuStates : List Bool := []
  /-- Wheel state of each axis: movement owed and push past the page edge (tasks 9.2, 9.r1). -/
  wheel : View.Wheels := {}
  /-- Rows of the outline tree (task 9.7, `Sidebar.rows`). -/
  olRows : List Sidebar.Row := []
  /-- Which outline rows are open (`Sidebar.toggle`). -/
  olOpen : Array Bool := #[]
  /-- The document's attachments (task 9.r10, `Core.Doc.Attachments.list`). -/
  attList : Array Core.Doc.Attachments.Attachment := #[]
  /-- The file attachment annotations' icons (task 9.r10): page, rectangle, row. -/
  attIcons : List Core.Doc.Attachments.Icon := []
  /-- What decoding each attachment gave, once it was decoded (saved or probed). -/
  attStatus : Array (Option Attach.Probe) := #[]
  /-- The document's optional content (task 9.r11b, `Core.Doc.OptionalContent.read`); `none`
  without `/OCProperties` (no Layers panel). -/
  ocCfg : Option Core.Doc.OptionalContent.Config := none
  /-- The visibility state the pages, thumbnails and text are made with (task 9.r11b): the
  document's default (`Config.initial`) at every open, changed by the layers panel; `none`
  without optional content (the renderer then uses the document's default itself). -/
  oc : Option Core.Doc.OptionalContent.State := none
  /-- Rows of the layers panel (`Sidebar.layerRows`; row `K` is `.ol.ly`'s row `K`). -/
  lyRows : List Sidebar.LayerRow := []
  /-- The layers tree (`Sidebar.rows` of `Sidebar.layerEntries lyRows`). -/
  lyTree : List Sidebar.Row := []
  /-- Which layers tree rows are open (`Sidebar.toggle`). -/
  lyOpen : Array Bool := #[]
  /-- Whether the sidebar toggle is shown (`none`: not applied yet). -/
  toggleShown : Option Bool := none
  /-- The user's highlights and notes of the open document (task 9.4). -/
  marks : Marks.Store := {}
  /-- The selected mark (its id). -/
  markSel : Option Nat := none
  /-- Undo/redo history of the marks (task 10.7; `marksChanged` records every edit). -/
  markHist : Marks.History := {}
  /-- The current highlight colour (`::safepdf::hlColor`). -/
  hlColor : Marks.Color := .yellow
  /-- The pages with a photo on the canvas (task 9.3: `::safepdf::pgN`, the visible pages and
  one more on each side) and their render result before the highlights are multiplied in
  (`Marks.composite`), or the render error. -/
  photos : Array (Nat × Except String Clip.Image) := #[]
  /-- Scroll mode (task 9.3, PDF.js "Page Scrolling" / "Vertical Scrolling"); files open in
  vertical scrolling (task 9.r1, as in PDF.js). -/
  scroll : View.ScrollMode := .vertical
  /-- Spread mode (task 9.3, PDF.js "No / Odd / Even Spreads"). -/
  spread : View.SpreadMode := .none
  /-- The view a file without `/PageLayout` opens in (task 9.r8): Vertical Scrolling without
  spreads, or what `SAFEPDF_VIEWER_VIEW` asks for at start-up. -/
  defaultView : View.ScrollMode × View.SpreadMode := (.vertical, .none)
  /-- Spreads run right to left (task 9.r8, `/ViewerPreferences /Direction /R2L`): the first
  page of a spread is on the right. -/
  rtl : Bool := false
  /-- The window is in full screen (task 9.r8, `/PageMode /FullScreen`); Escape leaves. -/
  fullScreen : Bool := false
  /-- The page mode applied on leaving full screen (`/NonFullScreenPageMode`). -/
  afterFullScreen : Core.Doc.OpenSettings.PageMode := .useNone
  /-- The document's `/Title` as display text, when `/DisplayDocTitle` asks for it in the
  window title (task 9.r8). -/
  docTitle : Option String := none
  /-- What the document's viewer preferences hide (task 9.r8): toolbar, menubar, scroll bars
  (`/HideToolbar`, `/HideMenubar`, `/HideWindowUI`); Escape shows them again. -/
  hidden : Bool × Bool × Bool := (false, false, false)
  /-- Notes about open settings that were not honoured (task 9.r8), added to the status line
  until the next open. -/
  openNote : String := ""
  /-- The laid-out pages (one spread in the page scroll mode, all pages in the vertical ones),
  in page order. -/
  slots : Array Slot := #[]
  /-- What `slots` was computed for (`none`: no layout). -/
  layoutKey : Option LayoutKey := none
  /-- A `renderMore` event is scheduled. -/
  renderQueued : Bool := false
  /-- Renders running on worker threads (task 8.8), at most `maxJobs`. -/
  jobs : Array Job := #[]
  /-- Task 12.3: the reservations of the work in flight (`Budget.Pool`, ceiling
  `Budget.ceilings.poolBytes`): every render, thumbnail and text or links request reserves its
  bytes before it is dispatched and releases them where its job leaves its list. -/
  pool : Budget.Pool := Budget.Pool.empty Budget.ceilings.poolBytes
  /-- A page render waits for the pool (`renderMore` runs again from `poll`). -/
  budgetWait : Bool := false
  /-- Most bytes ever reserved at once (the interleave scenario's measurement). -/
  poolPeak : Nat := 0
  /-- Operations that waited for the pool, thumbnails rendered smaller for it, operations
  refused by it, text requests dispatched without a reservation (expected 0), searches stopped
  by their work allowance. -/
  budgetWaits : Nat := 0
  /-- See `budgetWaits`. -/
  budgetDegraded : Nat := 0
  /-- See `budgetWaits`. -/
  budgetRefused : Nat := 0
  /-- See `budgetWaits`. -/
  budgetUnreserved : Nat := 0
  /-- See `budgetWaits`. -/
  searchStops : Nat := 0
  /-- Task 12.3b: the reservations of the live Tk photos (`Budget.Pool`, ceiling
  `Budget.ceilings.photoPoolBytes`): every page photo and thumbnail holds one
  (`Budget.photoBytes`) from its `put` until its `image delete`. -/
  photoPool : Budget.Pool := Budget.Pool.empty Budget.ceilings.photoPoolBytes
  /-- The photo each ticket of `photoPool` belongs to (its Tk image name). -/
  photoTix : Array (String × Budget.Ticket) := #[]
  /-- Most bytes the live photos ever held at once (the interleave scenario's measurement). -/
  photoPeak : Nat := 0
  /-- Page photos evicted to make room for a page in view, and page photos refused for lack of
  room (pages in view: a message in the page frame; neighbours: deferred). -/
  photoEvicted : Nat := 0
  /-- See `photoEvicted`. -/
  photoRefused : Nat := 0
  /-- Neighbouring pages (not in view) whose photo did not fit: not rendered or shown again
  until a photo is released (`missingPages` leaves them out). -/
  photoDeferred : List Nat := []
  /-- A `poll` event is scheduled (`ensurePoll`). -/
  pollQueued : Bool := false
  /-- How long (ms) an event that must show pages now (`showNow`) waits for their renders
  before it shows placeholders and leaves them to the workers; `none`: until they are done
  (smoke mode, so its steps see the pages at once). -/
  syncWaitMs : Option Nat := some 100
  /-- Render results not shown because the document, zoom or rotation changed while they ran
  (task 8.8; the smoke test checks it). -/
  staleDropped : Nat := 0
  /-- The view top (scroll-region pixel) the viewer itself scrolled to (a jump, a page key):
  while the view stays there the current page is the one it went to, not the one under the
  window centre (vertical modes). -/
  ownTop : Option Nat := none
  /-- The page of the last mouse press (the drag selects on it). -/
  pressPage : Nat := 0
  /-- Pages rendered so far and the time spent rendering them (ns; the `scroll` benchmark). -/
  renders : Nat := 0
  /-- See `renders`. -/
  renderNs : Nat := 0
  /-- Highlight tool, pop-over, colour picker, thickness and "Show all" (task 9.8). -/
  ui : Bubble.Ui := {}
  /-- The bubble on screen: its kind and canvas rectangle (task 9.8). -/
  bubble : Option (Bubble.Kind × Bubble.Rect) := none
  /-- The edit bubble's colour picker on screen (canvas rectangle). -/
  pickerAt : Option Bubble.Rect := none
  /-- The last mouse press hit a bubble or the picker: the drag, release and double click that
  follow it are not text selection. -/
  bubblePress : Bool := false
  /-- The last press in the pop-over was on the thickness slider (drags move it). -/
  popSlide : Bool := false
  /-- Files this session wrote (task 9.5c): saving into one of them again asks nothing. -/
  ownFiles : List String := []
  /-- The window title last applied (`syncMenus` keeps it in step with `State.title`). -/
  titleShown : String := ""
  /-- The free-text editor on the canvas (task 9.9). -/
  ftEdit : Option FtEdit := none
  /-- The ink mark of the current drawing session (task 9.9): further strokes join it. -/
  inkSession : Option Nat := none
  /-- The stroke being drawn: its page and points (page space). -/
  inkStroke : Option (Nat × Array Pt) := none
  /-- A free text or drawing being dragged: its id, the press point and the last point. -/
  moveFrom : Option (Nat × Pt × Pt) := none
  /-- The pop-over slider row being dragged (task 9.9). -/
  edSlide : Option Nat := none
  /-- The document worker session (task 12.2c); `none`: everything renders in this process. -/
  worker : Option Worker.Session := none
  /-- Why there is no worker session (shown in the status line after every open). -/
  workerNote : String := ""
  /-- Bumped whenever the document the pages are rendered from changes (an open, a preview of
  edited saved marks, Close): the worker's document id. -/
  srcSerial : Nat := 0
  /-- The `srcSerial` whose bytes the worker session has (`Worker.Session.setDoc`). -/
  workerSrc : Option Nat := none
  /-- Renders the worker answered and their total time (ns, request to answer; smoke
  measurements). -/
  workerRenders : Nat := 0
  /-- See `workerRenders`. -/
  workerNs : Nat := 0
  /-- Worker renders cancelled (superseded) before they were answered. -/
  cancelledRenders : Nat := 0
  /-- Text-index requests queued for the document worker (task 12.2d, `pageIndex`). -/
  textJobs : Array SideJob := #[]
  /-- Links requests queued for the document worker (task 12.2d, `linksOf`). -/
  linkJobs : Array SideJob := #[]
  /-- Text indexes and link lists the worker answered (smoke measurements, task 12.2d). -/
  workerTexts : Nat := 0
  /-- See `workerTexts`. -/
  workerLinks : Nat := 0

/-- The limits the viewer parses and renders with. -/
def limits : Limits := Limits.default

/-- Name of the Tk photo image that shows page `p` (task 9.3: one per page on the canvas). -/
def photoOf (p : Nat) : String := s!"::safepdf::pg{p}"

/-- Pages up to this many pixels are prefetched (2²² ≈ 4 Mpx, e.g. Letter at 250 %). -/
def prefetchPixels : Nat := 1 <<< 22

/-- Most renders running at once (task 8.8). The pages that must be shown now may use every
slot; neighbours and the prefetch leave one free for them. A render cannot be interrupted
(the renderer is pure), so renders whose page scrolled away or whose zoom changed keep their
slot until they finish (their result goes to the cache when it is still for the open
document). -/
def maxJobs : Nat := 4

/-- Interval (ms) of the `poll` event while renders are running. -/
def pollMs : Nat := 15

/-! ## Pure helpers -/

/-- Number of pages of the open document (0 when none). -/
def State.pageCount (s : State) : Nat :=
  match s.doc with
  | some d => d.pages.size
  | none => 0

/-- View parameters of page `p` of `doc` at the layout zoom `z0` (capped per page at
`Budget.Ceilings.pagePixels`, task 12.3b). -/
def viewParamsAt (s : State) (doc : Doc) (p : Nat) (z0 : Rat) : Option ViewParams :=
  doc.pages[p]?.map fun page =>
    let r := rotAdd page.rotate s.rot
    let bx := Box.ofRect page.cropBox
    let (z, capped) := View.capZoom Budget.ceilings.pagePixels z0 r bx
    ⟨z, r, bx, capped, View.cropped limits.maxPageSide z r bx⟩

/-- The zoom of a layout, chosen (`Toolbar.ZoomChoice.zoomWith`) for page `basis`: its size,
or twice its width in the facing modes (`View.fitBox`, PDF.js), in the canvas less the gap
between the pages of a spread (task 9.3). In the single-page view this is the zoom of the page
itself, as before. -/
def baseZoom (s : State) (doc : Doc) (basis : Nat) : Rat :=
  match doc.pages[basis]? with
  | some page =>
    let r := rotAdd page.rotate s.rot
    let (pw, ph) := View.boxSize r (Box.ofRect page.cropBox)
    let (fw, fh) := View.fitBox s.spread pw ph
    s.zoomSel.zoomWith (View.fitCanvasW s.spread s.canvasW) s.canvasH s.scaling fw fh
      (decide (pw ≤ ph))
  | none => 1

/-- The rows of the layout (task 9.3): the current spread in the page scroll mode, every
spread in the vertical ones (`View.spreads`). -/
def layoutRowsOf (s : State) (n : Nat) : List (List Nat) :=
  match s.scroll with
  | .page => [View.spreadPages s.spread n (View.spreadOf s.spread s.page)]
  | .vertical => View.spreads s.spread n

/-- Lays out the pages of `doc` (task 9.3): zoom from the current page (`baseZoom`), page
images of `Clip.pageSize` pixels placed by `View.layoutRows` (centred vertically in the page
scroll mode). Returns the slots in page order and the scroll region's size. -/
def computeLayout (s : State) (doc : Doc) : Array Slot × Nat × Nat :=
  let n := doc.pages.size
  let rows := layoutRowsOf s n
  let z0 := baseZoom s doc s.page
  let vps : Array (Option ViewParams) := (Array.range n).map fun p =>
    if s.scroll == .vertical || rows.any (·.contains p) then viewParamsAt s doc p z0 else none
  let sizes := vps.map fun o => match o with
    | some vp => SafePdf.Core.Raster.Clip.pageSize limits.maxPageSide vp.zoom vp.rot vp.box
    | none => (0, 0)
  let (ps, rw, rh) := View.layoutRows sizes rows s.canvasW s.canvasH (s.scroll == .page)
  -- Task 9.r8, `/Direction /R2L`: spreads mirrored, the first page of each on the right (rows
  -- are centred in the region, so mirroring the region keeps them centred).
  let ps := if s.rtl && s.spread != .none then ps.map (View.mirrorPlace rw) else ps
  (ps.filterMap fun pl => (vps[pl.page]?.join).map (⟨pl, ·⟩), rw, rh)

/-- The layout key of the state (task 9.3). -/
def layoutKeyOf (s : State) : LayoutKey :=
  ⟨s.gen, s.scroll, s.spread, s.zoomSel, s.rot, s.canvasW, s.canvasH,
   if s.scroll == .page then View.spreadOf s.spread s.page else 0⟩

/-- The slot of page `p`, when it is laid out. -/
def slotOf (s : State) (p : Nat) : Option Slot :=
  s.slots.find? (·.place.page == p)

/-- The places of the layout. -/
def State.places (s : State) : Array View.Place :=
  s.slots.map (·.place)

/-- Canvas rectangle `(x0, y0, x1, y1)` of a page-space box on the page of slot `sl`. -/
def Slot.rect (sl : Slot) (b : Box) : Rat × Rat × Rat × Rat :=
  let p0 := toScreen sl.vp.zoom sl.vp.rot sl.vp.box ⟨b.llx, b.lly⟩
  let p1 := toScreen sl.vp.zoom sl.vp.rot sl.vp.box ⟨b.urx, b.ury⟩
  let x : Rat := sl.place.x
  let y : Rat := sl.place.y
  (min p0.x p1.x + x, min p0.y p1.y + y, max p0.x p1.x + x, max p0.y p1.y + y)

/-- The page point (of slot `sl`'s page) at canvas point `(cx, cy)` (`Geom.toPage`, C2). -/
def Slot.toPage (sl : Slot) (cx cy : Rat) : Pt :=
  SafePdf.Core.Raster.Geom.toPage sl.vp.zoom sl.vp.rot sl.vp.box
    ⟨cx - (sl.place.x : Rat), cy - (sl.place.y : Rat)⟩

/-- Whether page `p` has a photo (or a render error) on the canvas. -/
def State.hasPhoto (s : State) (p : Nat) : Bool :=
  s.photos.any (·.1 == p)

/-- What the status line adds for the view mode (nothing in the default view, vertical
scrolling without spreads, task 9.r1). -/
def modeNote (s : State) : String :=
  let sc := match s.scroll with
    | .page => "page scrolling"
    | .vertical => ""
  let sp := match s.spread with
    | .none => ""
    | .odd => "odd spreads"
    | .even => "even spreads"
  let sp := if s.rtl && s.spread != .none then s!"{sp}, right to left" else sp
  match sc, sp with
  | "", "" => ""
  | a, "" => s!"; {a}"
  | "", b => s!"; {b}"
  | a, b => s!"; {a}, {b}"

#guard modeNote {} == "" && modeNote { scroll := .page, spread := .odd } ==
  "; page scrolling, odd spreads" && modeNote { spread := .even } == "; even spreads" &&
  modeNote { spread := .odd, rtl := true } == "; odd spreads, right to left" &&
  modeNote { rtl := true } == ""

/-- Last path component of a file name (for the window title). -/
def baseName (path : String) : String :=
  (System.FilePath.mk path).fileName.getD path

/-- Window title: `SafePDF`, or `NAME - page k/n - SafePDF`, with `* ` in front while there
are unsaved marks (task 9.5c); `NAME` is `titleOverride` when set (task 10.1b), else the
file name, or the document's `/Title` when its `/DisplayDocTitle` asks for it (task 9.r8,
`docTitle`). -/
def State.title (s : State) : String :=
  match s.path, s.doc with
  | some p, some _ =>
    let star := if s.marks.dirty then "* " else ""
    s!"{star}{s.titleOverride.getD (s.docTitle.getD (baseName p))} - {Links.pageText s.labels s.page s.pageCount} - {Menu.appName}"
  | some p, none => s!"{s.titleOverride.getD (baseName p)} - {Menu.appName}"
  | none, _ => Menu.appName

#guard ({} : State).title == "SafePDF"
#guard ({ path := some "/a/b.pdf" } : State).title == "b.pdf - SafePDF"

/-- A fraction in `[0, 1]` as a decimal with six digits (for `xview`/`yview moveto`). -/
def fmtFrac (r : Rat) : String :=
  let r := max 0 (min 1 r)
  let n := (r * 1000000).floor.toNat
  s!"{n / 1000000}.{padLeft 6 '0' (toString (n % 1000000))}"

/-- A canvas coordinate with two decimals (truncated toward −∞), for Tk. -/
def num (r : Rat) : String :=
  let c := (r * 100).floor
  let a := c.natAbs
  s!"{if c < 0 then "-" else ""}{a / 100}.{padLeft 2 '0' (toString (a % 100))}"

#guard num 12 = "12.00" && num (3 / 2) = "1.50" && num (-1 / 4) = "-0.25"
#guard fmtFrac (1 / 4) = "0.250000"

/-- A fraction in `[0, 1]` with twelve digits, for the wheel's `moveto` (task 9.r1): Tk rounds
`moveto` to the nearest pixel, and six digits are off by up to `region / 10⁶` pixels, over
half a pixel in the vertical modes of a document taller than 500 000 pixels (some 450 pages
at Page Width), where a one-pixel trackpad step would round back to where it started and the
wheel would stall. -/
def fmtFracFine (r : Rat) : String :=
  let r := max 0 (min 1 r)
  let n := (r * 1000000000000).floor.toNat
  s!"{n / 1000000000000}.{padLeft 12 '0' (toString (n % 1000000000000))}"

-- Pixel 400 001 of a 900 000-pixel region: six digits land 0.6 px short (Tk rounds that to
-- 400 000), twelve digits within 10⁻⁶ px.
#guard fmtFracFine (1 / 4) = "0.250000000000" && fmtFracFine 1 = "1.000000000000"
#guard fmtFrac ((400001 : Rat) / 900000) = "0.444445" &&
  fmtFracFine ((400001 : Rat) / 900000) = "0.444445555555"
#guard fmtFrac 2 = "1.000000"
#guard fmtFrac (-1) = "0.000000"

/-- Name of a zoom choice for the status line. -/
def modeName (c : Toolbar.ZoomChoice) : String := c.statusName

/-! ## Tcl -/

/-- Evaluates a command built from literal words (every word quoted by `Tcl.quote`). -/
def run (words : List String) : IO String :=
  Shim.eval (Tcl.Script.render ⟨[Tcl.cmd words]⟩)

/-- The platform the keys are bound and labelled for (task 9.r3; set once at start-up from
`tk windowingsystem`, `Menu.Platform`). -/
initialize platformRef : IO.Ref Menu.Platform ← IO.mkRef .other

/-- A constant UI text naming keys the X11 way (`Ctrl+O`) in the platform's form (`⌘O` on
macOS, `Menu.Platform.keyText`). Only for the viewer's own texts, never document data. -/
def keyText (s : String) : IO String :=
  return (← platformRef.get).keyText s

/-- Shows `msg` in the status line. -/
def setStatus (msg : String) : IO Unit := do
  discard <| run [".status", "configure", "-text", msg]

/-- After a change of `State.marks`: records it in the undo history (task 10.7,
`Marks.History.record`; `merge`: a further step of a slider drag) and reports the marks to the
library (task 10.1b; nothing for a local file). -/
def marksChanged (st : IO.Ref State) (merge : Bool := false) : IO Unit := do
  st.modify fun s => { s with markHist := s.markHist.record s.marks.marks merge }
  let s ← st.get
  if let some l := s.library then l.onMarksChanged s.marks

/-- Deletes Tk's `send` command (task 8.7). Tk's delete callback for `send` also removes the
application from the display's interpreter registry, so other X clients no longer find it
(`winfo interps`) and a `send` to its name fails with "no application named …". Tk on
Windows has no `send`; then nothing happens. -/
def sendOffScript : String :=
  "if {[llength [info commands ::send]]} { rename ::send {} }"

/-- The X resource database guard (task 8.7, run first in `setupScript`). Tk fills widget
options not given at creation from the option database, which Tk loads from the display's
`RESOURCE_MANAGER` property (any client of the display can set it) or `~/.Xdefaults`, at
priority `userDefault` (60). Several options are scripts or redirect a window: `-command`,
`-validatecommand` (with `-validate`), `-invalidcommand`, `-postcommand`,
`-tearoffcommand`, `-xscrollcommand`/`-yscrollcommand`, `-takefocus` (a script for keyboard
traversal), `-textvariable`/`-listvariable`, and a toplevel's `-use`, `-screen`,
`-container`. Entries for them at priority `interactive` (80) win over every resource loaded
from the display (Tk ranks by priority before specificity), so a widget created without such
an option gets the harmless default; options the viewer passes explicitly are unaffected.
The main window `.` existed before this ran, so its `-takefocus` is reset explicitly. -/
def resourceGuardScript : String := "
foreach o {command validateCommand invalidCommand postCommand tearOffCommand xScrollCommand
           yScrollCommand takeFocus textVariable listVariable use screen} {
  option add *$o {} interactive
}
option add *validate none interactive
option add *container 0 interactive
. configure -takefocus {}
"

/-- The constant UI setup script (no data in it). It starts with `resourceGuardScript`
(task 8.7). Widgets: the toolbar `.bar` after PDF.js
(task 9.7: groups `.bar.l`, `.bar.m` (centred), `.bar.r`, filled from `Toolbar.layout` by
`buildToolbar` with the procs defined here: canvas icon buttons `::safepdf::iconButton`, the
page field `.bar.pg` + `.bar.of`, the zoom drop-down `.bar.zoom` + menu `.zoommenu`, the
overflow menu `.more`), the outline sidebar `.ol` (a text widget `.ol.t` drawn as a tree),
canvas `.c` with scroll bars `.xs`/`.ys` gridded in frame `.v`, the photo image
`::safepdf::page` on canvas item tag `page`, status line `.status`. Key bindings on the
toplevel's bind tag `.`; canvas resizes are debounced and reported as `emit resize W H`.
Colours and sizes follow PDF.js's light theme (`web/viewer.css`: toolbar `#f9f9fa`, 40 px
high with 32 px round buttons and 16 px icons, separators, field and drop-down borders). -/
def setupScript : String := "
namespace eval ::safepdf { variable resizeId {}; variable query {}; variable outlineOn 0; variable panel outline }
namespace eval ::safepdf::icon {}
" ++ resourceGuardScript ++ "
wm title . SafePDF
wm geometry . 1200x960
wm minsize . 480 240
array set ::safepdf::col {
  bar #f9f9fa line #d7d7db ink #3b3b44 inkOff #b6b6bd hover #e4e4e9 press #d2d2d9
  toggled #dddde3 sep #d0d0d7 field #ffffff fieldLine #8f8f9d focus #0a84ff text #15141a
  body #f0f0f4 panel #ffffff tri #5b5b66 olHover #ededf1 olCur #e0e0e6 dim #5b5b66
}
set ::safepdf::family [font actual TkDefaultFont -family]
font create ::safepdf::fBar -family $::safepdf::family -size -13
font create ::safepdf::fZoom -family $::safepdf::family -size -14 -weight bold
font create ::safepdf::fOl -family $::safepdf::family -size -13
font create ::safepdf::fOlHead -family $::safepdf::family -size -15
font create ::safepdf::fTri -family $::safepdf::family -size -9
# A rounded rectangle (a smoothed polygon with doubled corner points).
proc ::safepdf::rrect {c x0 y0 x1 y1 r args} {
  set a [expr {$x0 + $r}]; set b [expr {$x1 - $r}]; set u [expr {$y0 + $r}]; set v [expr {$y1 - $r}]
  $c create polygon $a $y0 $a $y0 $b $y0 $b $y0 $x1 $y0 $x1 $u $x1 $u $x1 $v $x1 $v $x1 $y1 \\
    $b $y1 $b $y1 $a $y1 $a $y1 $x0 $y1 $x0 $v $x0 $v $x0 $u $x0 $u $x0 $y0 -smooth 1 {*}$args
}
# Translucent highlight fills (task 10.10; Tk Aqua has no stipples): a canvas image item showing
# a photo filled with colour rgb (6 hex digits) at alpha a (2 hex digits), one photo per colour,
# alpha and size, shared by every item of that size (search hits of one word, full lines).
# Task 10.c1: Tk 9 takes `#RRGGBBAA` in `photo put`; Tk 8.6 (Ubuntu's tk-dev) does not (\"can't
# parse color\") and has no `get -withalpha`. There the fill tiles a one-pixel RGBA PNG (built
# here; Tk 8.6 reads PNG alpha and blends partly transparent photos on X11) with `copy -to`,
# and `::safepdf::pixel` reads a pixel back as a one-pixel PNG. Decided once, at start;
# SAFEPDF_TINT_PNG=1 forces the Tk 8.6 paths (the smoke test runs them on Aqua).
set ::safepdf::tintRgba [expr {![catch {
  image create photo ::safepdf::tintProbe -width 1 -height 1
  ::safepdf::tintProbe put {{#3874f25a}}
}]}]
catch {image delete ::safepdf::tintProbe}
set ::safepdf::getAlpha [expr {![catch {
  image create photo ::safepdf::tintProbe -width 1 -height 1
  ::safepdf::tintProbe get 0 0 -withalpha
}]}]
catch {image delete ::safepdf::tintProbe}
if {[info exists ::env(SAFEPDF_TINT_PNG)] && $::env(SAFEPDF_TINT_PNG) eq \"1\"} {
  set ::safepdf::tintRgba 0; set ::safepdf::getAlpha 0
}
# A PNG chunk: length, type, data, CRC-32 of type and data.
proc ::safepdf::pngChunk {type data} {
  set td [encoding convertto iso8859-1 $type]$data
  return [binary format I [string length $data]]$td[binary format I [zlib crc32 $td]]
}
# A one-pixel PNG (8-bit RGBA, colour type 6) of colour rgb (6 hex digits) at alpha a (2 hex
# digits).
proc ::safepdf::rgbaPng {rgb a} {
  scan $rgb$a %2x%2x%2x%2x r g b al
  set px [binary format c5 [list 0 $r $g $b $al]]
  return [binary format H* 89504e470d0a1a0a][::safepdf::pngChunk IHDR [binary format IIc5 1 1 {8 6 0 0 0}]][::safepdf::pngChunk IDAT [zlib compress $px]][::safepdf::pngChunk IEND {}]
}
# Fills photo img (w x h) with colour rgb at alpha a.
proc ::safepdf::tintFill {img rgb a w h} {
  if {$::safepdf::tintRgba} {
    $img put [list [list #$rgb$a]] -to 0 0 $w $h
    return
  }
  set src ::safepdf::tintpx_${rgb}_$a
  if {[catch {image type $src}]} {
    image create photo $src -format png -data [binary encode base64 [::safepdf::rgbaPng $rgb $a]]
  }
  $img copy $src -to 0 0 $w $h -compositingrule set
}
proc ::safepdf::tint {c x0 y0 x1 y1 rgb a tags} {
  set w [expr {$x1 - $x0}]; set h [expr {$y1 - $y0}]
  if {$w < 1 || $h < 1} return
  set img ::safepdf::tint_${rgb}_${a}_${w}_$h
  if {[catch {image type $img}]} {
    image create photo $img -width $w -height $h
    ::safepdf::tintFill $img $rgb $a $w $h
  }
  $c create image $x0 $y0 -anchor nw -image $img -tags $tags
}
# The pixel (x, y) of photo img as `R G B A` (smoke probes): Tk 9's `get -withalpha`; on Tk 8.6
# the pixel written as a one-pixel PNG and decoded (IHDR colour type, inflated IDAT; with one
# pixel every PNG filter leaves the bytes as they are).
proc ::safepdf::pixel {img x y} {
  if {$::safepdf::getAlpha} { return [$img get $x $y -withalpha] }
  set d [$img data -format png -from $x $y [expr {$x + 1}] [expr {$y + 1}]]
  if {[string range $d 1 3] ne \"PNG\"} { set d [binary decode base64 $d] }
  set i 8; set idat {}; set ct 6
  while {$i + 12 <= [string length $d]} {
    binary scan $d @${i}Iua4 n t
    set body [string range $d [expr {$i + 8}] [expr {$i + 7 + $n}]]
    if {$t eq \"IHDR\"} { binary scan $body @9cu ct }
    if {$t eq \"IDAT\"} { append idat $body }
    incr i [expr {12 + $n}]
  }
  binary scan [zlib decompress $idat] @1cu* px
  switch -- $ct {
    0 { return [list [lindex $px 0] [lindex $px 0] [lindex $px 0] 255] }
    4 { return [list [lindex $px 0] [lindex $px 0] [lindex $px 0] [lindex $px 1]] }
    2 { return [concat [lrange $px 0 2] 255] }
    default { return [lrange $px 0 3] }
  }
}
# Deletes the tint photos no canvas item shows any more (after a redraw of the overlays).
proc ::safepdf::tintGc {} {
  foreach img [image names] {
    if {[string match ::safepdf::tint_* $img] && ![image inuse $img]} { image delete $img }
  }
}
# Icons (16 px, centred on a 32 px button; PDF.js's icons re-drawn, not copied). Items tagged
# inkf are coloured through -fill, inko through -outline.
proc ::safepdf::icon::sidebar {c} {
  ::safepdf::rrect $c 8 9 24 23 2 -fill {} -outline black -width 1.5 -tags inko
  $c create line 13 9 13 23 -width 1.5 -tags inkf
}
proc ::safepdf::icon::up {c} {
  $c create line 10 19 16 13 22 19 -width 1.8 -capstyle round -joinstyle round -tags inkf
}
proc ::safepdf::icon::down {c} {
  $c create line 10 13 16 19 22 13 -width 1.8 -capstyle round -joinstyle round -tags inkf
}
proc ::safepdf::icon::minus {c} { $c create line 10 16 22 16 -width 1.8 -capstyle round -tags inkf }
proc ::safepdf::icon::plus {c} {
  $c create line 10 16 22 16 -width 1.8 -capstyle round -tags inkf
  $c create line 16 10 16 22 -width 1.8 -capstyle round -tags inkf
}
proc ::safepdf::icon::select {c} {
  $c create line 12.5 8.5 14.5 8.5 16 10 17.5 8.5 19.5 8.5 -width 1.5 -capstyle round -joinstyle round -tags inkf
  $c create line 12.5 23.5 14.5 23.5 16 22 17.5 23.5 19.5 23.5 -width 1.5 -capstyle round -joinstyle round -tags inkf
  $c create line 16 10 16 22 -width 1.5 -tags inkf
  $c create line 13.5 16 18.5 16 -width 1.2 -capstyle round -tags inkf
}
proc ::safepdf::icon::highlight {c} {
  $c create polygon 19 8 24 13 15 22 10 17 -fill {} -outline black -width 1.5 -joinstyle round -tags inko
  $c create polygon 10 17 15 22 12 24 8 24 8 20 -fill black -outline {} -tags inkf
}
proc ::safepdf::icon::comment {c} {
  ::safepdf::rrect $c 8 8 24 20 3 -fill {} -outline black -width 1.5 -tags inko
  $c create line 12 20 12 25 17 20 -width 1.5 -joinstyle round -tags inkf
  $c create line 12 12 20 12 -width 1.2 -tags inkf
  $c create line 12 15.5 18 15.5 -width 1.2 -tags inkf
}
proc ::safepdf::icon::text {c} {
  $c create line 9 10 23 10 -width 2 -capstyle round -tags inkf
  $c create line 16 10 16 23 -width 2 -capstyle round -tags inkf
}
proc ::safepdf::icon::draw {c} {
  $c create polygon 20 8 24 12 13 23 9 23 9 19 -fill {} -outline black -width 1.5 -joinstyle round -tags inko
  $c create line 18 10 22 14 -width 1.5 -tags inkf
}
proc ::safepdf::icon::image {c} {
  ::safepdf::rrect $c 8 9 24 23 2 -fill {} -outline black -width 1.5 -tags inko
  $c create line 9 21 14 15 18 19 20 17 23 20 -width 1.5 -joinstyle round -tags inkf
  $c create oval 18 11.5 21 14.5 -fill black -outline {} -tags inkf
}
proc ::safepdf::icon::print {c} {
  $c create rectangle 11 8 21 13 -outline black -width 1.5 -tags inko
  ::safepdf::rrect $c 8 13 24 21 2 -fill {} -outline black -width 1.5 -tags inko
  $c create rectangle 11 18 21 24 -fill $::safepdf::col(bar) -outline black -width 1.5 -tags {inko paper}
}
proc ::safepdf::icon::save {c} {
  $c create line 16 8 16 19 -width 1.6 -capstyle round -tags inkf
  $c create line 11.5 14.5 16 19 20.5 14.5 -width 1.6 -capstyle round -joinstyle round -tags inkf
  $c create line 9 19 9 24 23 24 23 19 -width 1.6 -joinstyle round -tags inkf
}
# Sidebar view buttons (9.r9): thumbnails, outline, attachments, layers.
proc ::safepdf::icon::thumbs {c} {
  ::safepdf::rrect $c 11 7 21 14.5 1.5 -fill {} -outline black -width 1.5 -tags inko
  ::safepdf::rrect $c 11 17.5 21 25 1.5 -fill {} -outline black -width 1.5 -tags inko
}
proc ::safepdf::icon::outline {c} {
  foreach {x y} {8 10 11 16 11 22} {
    $c create oval $x [expr {$y - 1.2}] [expr {$x + 2.4}] [expr {$y + 1.2}] -fill black -outline {} -tags inkf
    $c create line [expr {$x + 5}] $y 24 $y -width 1.5 -capstyle round -tags inkf
  }
}
proc ::safepdf::icon::attach {c} {
  $c create line 20 12 13.5 18.5 13.5 21 15.5 22.5 17.5 21.5 23 16 23.5 12 21 9 18 9 \\
    10.5 16.5 10 21 -smooth 1 -width 1.5 -capstyle round -tags inkf
}
proc ::safepdf::icon::layers {c} {
  $c create polygon 16 8 24 12 16 16 8 12 -fill {} -outline black -width 1.5 -joinstyle round -tags inko
  $c create line 8 16 16 20 24 16 -width 1.5 -joinstyle round -capstyle round -tags inkf
  $c create line 8 20 16 24 24 20 -width 1.5 -joinstyle round -capstyle round -tags inkf
}
proc ::safepdf::icon::more {c} {
  $c create line 10 11 15 16 10 21 -width 1.6 -capstyle round -joinstyle round -tags inkf
  $c create line 17 11 22 16 17 21 -width 1.6 -capstyle round -joinstyle round -tags inkf
}
# Toolbar buttons: a 32 px canvas with a round background (hover, pressed, toggled as in
# PDF.js) and an icon; disabled buttons draw the icon dimmed and ignore clicks. State in
# ::safepdf::btn(KEY,PATH). The optional bg names the colour behind the button (col(bg)).
set ::safepdf::tipId {}
proc ::safepdf::iconButton {w icon tip cmd {bg bar}} {
  canvas $w -width 32 -height 32 -background $::safepdf::col($bg) -highlightthickness 0 \\
    -borderwidth 0 -takefocus 0
  $w create oval 1 1 31 31 -fill $::safepdf::col($bg) -outline {} -tags bg
  ::safepdf::icon::$icon $w
  foreach {k v} [list st normal tog 0 in 0 down 0 cmd $cmd tip $tip bg $bg] { set ::safepdf::btn($k,$w) $v }
  bind $w <Enter> {::safepdf::btnEnter %W}
  bind $w <Leave> {::safepdf::btnLeave %W}
  bind $w <ButtonPress-1> {set ::safepdf::btn(down,%W) 1; ::safepdf::btnPaint %W}
  bind $w <ButtonRelease-1> {::safepdf::btnRelease %W %x %y}
  ::safepdf::btnPaint $w
}
proc ::safepdf::btnPaint {w} {
  upvar #0 ::safepdf::btn b ::safepdf::col c
  set on [expr {$b(st,$w) eq {normal}}]
  if {$on && $b(down,$w) && $b(in,$w)} { set bg $c(press) } elseif {$on && $b(in,$w)} {
    set bg $c(hover) } elseif {$b(tog,$w)} { set bg $c(toggled) } else { set bg $c($b(bg,$w)) }
  $w itemconfigure bg -fill $bg
  $w itemconfigure paper -fill $bg
  set ink [expr {$on ? $c(ink) : $c(inkOff)}]
  $w itemconfigure inkf -fill $ink
  $w itemconfigure inko -outline $ink
}
proc ::safepdf::btnEnter {w} {
  set ::safepdf::btn(in,$w) 1
  ::safepdf::btnPaint $w
  after cancel $::safepdf::tipId
  set ::safepdf::tipId [after 600 [list ::safepdf::tipShow $w]]
}
proc ::safepdf::btnLeave {w} {
  set ::safepdf::btn(in,$w) 0
  ::safepdf::btnPaint $w
  after cancel $::safepdf::tipId
  destroy .tip
}
proc ::safepdf::btnRelease {w x y} {
  set was $::safepdf::btn(down,$w)
  set ::safepdf::btn(down,$w) 0
  ::safepdf::btnPaint $w
  if {$was && $x >= 0 && $y >= 0 && $x < [winfo width $w] && $y < [winfo height $w]} {
    ::safepdf::btnInvoke $w
  }
}
proc ::safepdf::btnInvoke {w} {
  if {$::safepdf::btn(st,$w) eq {normal}} { uplevel #0 $::safepdf::btn(cmd,$w) }
}
proc ::safepdf::btnState {w {s {}}} {
  if {$s ne {}} { set ::safepdf::btn(st,$w) $s; ::safepdf::btnPaint $w }
  return $::safepdf::btn(st,$w)
}
proc ::safepdf::btnToggled {w on} { set ::safepdf::btn(tog,$w) $on; ::safepdf::btnPaint $w }
proc ::safepdf::tipShow {w} {
  if {![winfo exists $w] || !$::safepdf::btn(in,$w)} return
  destroy .tip
  toplevel .tip -background $::safepdf::col(fieldLine) -borderwidth 0
  wm overrideredirect .tip 1
  label .tip.l -text $::safepdf::btn(tip,$w) -font ::safepdf::fBar -background white \\
    -foreground $::safepdf::col(text) -padx 6 -pady 3
  pack .tip.l -padx 1 -pady 1
  wm geometry .tip +[winfo rootx $w]+[expr {[winfo rooty $w] + [winfo height $w] + 6}]
}
proc ::safepdf::vsep {w} {
  frame $w -width 1 -height 20 -background $::safepdf::col(sep)
}
# Packs toolbar widget w into group frame g (w is a child of .bar, so raise it above g).
proc ::safepdf::barPack {w g args} {
  pack $w -in $g -side left {*}$args
  raise $w
}
frame .bar -background $::safepdf::col(bar) -height 40
pack propagate .bar 0
foreach g {.bar.l .bar.m .bar.r} { frame $g -background $::safepdf::col(bar) }
pack .bar.l -side left -padx 4
pack .bar.r -side right -padx 4
place .bar.m -relx 0.5 -rely 0.5 -anchor center
frame .barline -height 1 -background $::safepdf::col(line)
# Page field (PDF.js #pageNumber + #numPages): Enter jumps, Escape or leaving reverts.
proc ::safepdf::pageField {} {
  upvar #0 ::safepdf::col c
  canvas .bar.pg -width 56 -height 28 -background $c(bar) -highlightthickness 0 -borderwidth 0
  ::safepdf::rrect .bar.pg 1 1 55 27 4 -fill $c(field) -outline $c(fieldLine) -tags frame
  entry .bar.pg.e -textvariable ::safepdf::pageText -width 4 -justify right -borderwidth 0 \\
    -relief flat -highlightthickness 0 -background $c(field) -foreground $c(text) \\
    -disabledbackground $c(field) -font ::safepdf::fBar -insertwidth 1
  .bar.pg create window 49 14 -anchor e -window .bar.pg.e -width 42 -height 20
  label .bar.of -text {} -background $c(bar) -foreground $c(text) -font ::safepdf::fBar
  ::safepdf::barPack .bar.pg .bar.l -padx {6 0}
  ::safepdf::barPack .bar.of .bar.l -padx {6 4}
  bindtags .bar.pg.e [list .bar.pg.e Entry all]
  bind .bar.pg.e <Return> {::safepdf::emit pageEntry $::safepdf::pageText; break}
  bind .bar.pg.e <KP_Enter> {::safepdf::emit pageEntry $::safepdf::pageText; break}
  bind .bar.pg.e <Escape> {focus .c; ::safepdf::emit pageRevert; break}
  bind .bar.pg.e <FocusIn> {.bar.pg itemconfigure frame -outline $::safepdf::col(focus); %W selection range 0 end}
  bind .bar.pg.e <FocusOut> {.bar.pg itemconfigure frame -outline $::safepdf::col(fieldLine); ::safepdf::emit pageRevert}
  bind .bar.pg.e <Control-q> {::safepdf::emit quit}
}
proc ::safepdf::setPage {text of on} {
  set ::safepdf::pageText $text
  .bar.of configure -text $of
  .bar.pg.e configure -state [expr {$on ? {normal} : {disabled}}]
}
# Zoom drop-down (PDF.js #scaleSelect): a rounded button showing the current choice; the
# menu .zoommenu holds the choices (radio entries on ::safepdf::zoomSel).
set ::safepdf::zoomSel auto
set ::safepdf::zoomOn 0
proc ::safepdf::zoomBox {} {
  upvar #0 ::safepdf::col c
  canvas .bar.zoom -width 192 -height 32 -background $c(bar) -highlightthickness 0 \\
    -borderwidth 0 -takefocus 0
  ::safepdf::rrect .bar.zoom 1 1 191 31 15 -fill $c(field) -outline $c(fieldLine) -tags frame
  .bar.zoom create text 16 16 -anchor w -text {} -font ::safepdf::fZoom -fill $c(text) -tags label
  .bar.zoom create line 164 13.5 169 18.5 174 13.5 -width 1.6 -fill $c(ink) -capstyle round \\
    -joinstyle round -tags chev
  ::safepdf::barPack .bar.zoom .bar.m -padx {8 0}
  bind .bar.zoom <Enter> {if {$::safepdf::zoomOn} {.bar.zoom itemconfigure frame -fill $::safepdf::col(hover)}}
  bind .bar.zoom <Leave> {.bar.zoom itemconfigure frame -fill $::safepdf::col(field)}
  bind .bar.zoom <ButtonPress-1> ::safepdf::postZoom
  menu .zoommenu -tearoff 0 -background white -activebackground $c(hover) \\
    -activeforeground $c(text) -foreground $c(text) -font ::safepdf::fBar -relief solid \\
    -borderwidth 1 -activeborderwidth 0 -selectcolor $c(ink)
}
proc ::safepdf::postZoom {} {
  if {!$::safepdf::zoomOn} return
  tk_popup .zoommenu [winfo rootx .bar.zoom] [expr {[winfo rooty .bar.zoom] + [winfo height .bar.zoom] + 2}]
}
proc ::safepdf::zoomShow {label sel on} {
  set ::safepdf::zoomOn $on
  set ::safepdf::zoomSel $sel
  .bar.zoom itemconfigure label -text $label \\
    -fill [expr {$on ? $::safepdf::col(text) : $::safepdf::col(inkOff)}]
  .bar.zoom itemconfigure chev -fill [expr {$on ? $::safepdf::col(ink) : $::safepdf::col(inkOff)}]
}
# View-mode drop-down (9.r4) next to the page count: a small rounded button with the icon of
# the current mode (::safepdf::icon::view-KEY) and a chevron; the menu .viewmenu holds the four
# modes (radio entries on ::safepdf::viewSel, set by Lean from the scroll and spread modes).
proc ::safepdf::icon::view-single {c} {
  $c create rectangle 11 8 21 24 -outline black -width 1.5 -tags inko
}
proc ::safepdf::icon::view-vertical {c} {
  $c create rectangle 11 6 21 14 -outline black -width 1.5 -tags inko
  $c create rectangle 11 18 21 26 -outline black -width 1.5 -tags inko
}
proc ::safepdf::icon::view-two {c} {
  $c create rectangle 7 9 15 23 -outline black -width 1.5 -tags inko
  $c create rectangle 17 9 25 23 -outline black -width 1.5 -tags inko
}
proc ::safepdf::icon::view-two-scroll {c} {
  $c create rectangle 8 6 15 14 -outline black -width 1.5 -tags inko
  $c create rectangle 17 6 24 14 -outline black -width 1.5 -tags inko
  $c create rectangle 8 18 15 26 -outline black -width 1.5 -tags inko
  $c create rectangle 17 18 24 26 -outline black -width 1.5 -tags inko
}
set ::safepdf::viewSel vertical
set ::safepdf::viewOn 0
set ::safepdf::viewShown {}
proc ::safepdf::viewBox {} {
  upvar #0 ::safepdf::col c
  canvas .bar.vmode -width 56 -height 32 -background $c(bar) -highlightthickness 0 \
    -borderwidth 0 -takefocus 0
  ::safepdf::rrect .bar.vmode 1 1 55 31 15 -fill $c(field) -outline $c(fieldLine) -tags frame
  .bar.vmode create line 36 13.5 40.5 18 45 13.5 -width 1.6 -fill $c(ink) -capstyle round \
    -joinstyle round -tags chev
  ::safepdf::barPack .bar.vmode .bar.l -padx {2 0}
  foreach {k v} {in 0 tip {}} { set ::safepdf::btn($k,.bar.vmode) $v }
  bind .bar.vmode <Enter> {
    if {$::safepdf::viewOn} {.bar.vmode itemconfigure frame -fill $::safepdf::col(hover)}
    set ::safepdf::btn(in,.bar.vmode) 1
    after cancel $::safepdf::tipId
    set ::safepdf::tipId [after 600 [list ::safepdf::tipShow .bar.vmode]]
  }
  bind .bar.vmode <Leave> {
    .bar.vmode itemconfigure frame -fill $::safepdf::col(field)
    set ::safepdf::btn(in,.bar.vmode) 0
    after cancel $::safepdf::tipId
    destroy .tip
  }
  bind .bar.vmode <ButtonPress-1> ::safepdf::postView
  menu .viewmenu -tearoff 0 -background white -activebackground $c(hover) \
    -activeforeground $c(text) -foreground $c(text) -font ::safepdf::fBar -relief solid \
    -borderwidth 1 -activeborderwidth 0 -selectcolor $c(ink)
}
proc ::safepdf::postView {} {
  if {!$::safepdf::viewOn} return
  after cancel $::safepdf::tipId
  destroy .tip
  tk_popup .viewmenu [winfo rootx .bar.vmode] [expr {[winfo rooty .bar.vmode] + [winfo height .bar.vmode] + 2}]
}
# Shows mode KEY (tooltip TIP) on the button, enabled or not; the icon is redrawn on change.
proc ::safepdf::viewShow {key tip on} {
  set ::safepdf::viewOn $on
  set ::safepdf::viewSel $key
  set ::safepdf::btn(tip,.bar.vmode) $tip
  set w .bar.vmode
  if {$::safepdf::viewShown ne $key} {
    set ::safepdf::viewShown $key
    $w delete vicon
    ::safepdf::icon::view-$key $w
    $w addtag vicon withtag inkf
    $w addtag vicon withtag inko
    $w dtag inkf inkf
    $w dtag inko inko
    $w move vicon 3 0
  }
  set ink [expr {$on ? $::safepdf::col(ink) : $::safepdf::col(inkOff)}]
  foreach i [$w find withtag vicon] {
    if {[$w type $i] eq {line}} { $w itemconfigure $i -fill $ink } else { $w itemconfigure $i -outline $ink }
  }
  $w itemconfigure chev -fill $ink
}
# Overflow menu (PDF.js's secondary toolbar), posted under the right edge of the » button.
menu .more -tearoff 0 -background white -activebackground $::safepdf::col(hover) \\
  -activeforeground $::safepdf::col(text) -foreground $::safepdf::col(text) \\
  -font ::safepdf::fBar -relief solid -borderwidth 1 -activeborderwidth 0
proc ::safepdf::postMore {} {
  set x [expr {[winfo rootx .bar.more] + [winfo width .bar.more] - [winfo reqwidth .more]}]
  tk_popup .more $x [expr {[winfo rooty .bar.more] + [winfo height .bar.more] + 2}]
}
# The sidebar toggle is shown with a document (9.r9: thumbnails need no outline).
proc ::safepdf::showToggle {on} {
  if {$on} {
    if {![winfo ismapped .bar.sidebar]} {
      pack .bar.sidebar .bar.s0 -in .bar.l -side left -padx 2 -before .bar.prev
      raise .bar.sidebar; raise .bar.s0
    }
  } else { pack forget .bar.sidebar .bar.s0 }
}
# Outline sidebar (8.2d, restyled after PDF.js in 9.7): a panel titled Document outline with
# a text widget drawn as a tree; row K has tag oK (title), tK (disclosure triangle), the
# margin tag dN/lN of its depth and uA for every ancestor A (a closed ancestor elides it).
ttk::panedwindow .pw -orient horizontal
frame .ol -background $::safepdf::col(body) -padx 6 -pady 6
frame .ol.p -background $::safepdf::col(panel) -highlightthickness 1 \\
  -highlightbackground $::safepdf::col(line) -highlightcolor $::safepdf::col(line)
label .ol.h -text {Document outline} -font ::safepdf::fOlHead -background $::safepdf::col(panel) \\
  -foreground $::safepdf::col(text) -anchor w -padx 10 -pady 8
text .ol.t -wrap word -width 30 -height 10 -borderwidth 0 -highlightthickness 0 \\
  -background $::safepdf::col(panel) -foreground $::safepdf::col(text) -font ::safepdf::fOl \\
  -cursor arrow -padx 4 -pady 2 -spacing1 4 -spacing3 4 -state disabled -takefocus 0 \\
  -insertwidth 0 -yscrollcommand ::safepdf::olScroll -selectbackground $::safepdf::col(panel) \\
  -inactiveselectbackground {} -exportselection 0
ttk::scrollbar .ol.s -orient vertical -command {.ol.t yview}
pack .ol.p -in .ol -fill both -expand 1
grid .ol.h -in .ol.p -row 0 -column 0 -columnspan 2 -sticky ew
grid .ol.t -in .ol.p -row 1 -column 0 -sticky nsew -padx {4 0} -pady {0 6}
grid .ol.s -in .ol.p -row 1 -column 1 -sticky ns
grid rowconfigure .ol.p 1 -weight 1
grid columnconfigure .ol.p 0 -weight 1
raise .ol.h; raise .ol.t; raise .ol.s
.ol.t tag configure tri -foreground $::safepdf::col(tri) -font ::safepdf::fTri -offset 1
# The sidebar scroll bar shows only when the tree does not fit (PDF.js has overlay bars).
proc ::safepdf::olScroll {a b} {
  .ol.s set $a $b
  if {$::safepdf::panel ne {outline}} return
  if {$a <= 0.0 && $b >= 1.0} { grid remove .ol.s } else { grid .ol.s }
}
# Sidebar panels (9.r9, after PDF.js's sidebar views): a row of view buttons .ol.sw above
# the panel (made by buildToolbar from Sidebar.panels, shown per content); each panel grids
# its widgets into row 1 of .ol.p (::safepdf::panelWidgets(KEY)), ::safepdf::showPanel KEY
# TITLE shows one and runs ::safepdf::panelShown::KEY when it exists (scroll bar state).
frame .ol.sw -background $::safepdf::col(body)
pack .ol.sw -in .ol -side top -fill x -pady {0 6} -before .ol.p
namespace eval ::safepdf::panelShown {}
set ::safepdf::panelWidgets(outline) {.ol.t .ol.s}
proc ::safepdf::panelShown::outline {} { ::safepdf::olScroll {*}[.ol.t yview] }
proc ::safepdf::showPanel {key title} {
  foreach k [array names ::safepdf::panelWidgets] {
    if {$k ne $key} { foreach w $::safepdf::panelWidgets($k) { grid remove $w } }
  }
  set ::safepdf::panel $key
  .ol.h configure -text $title
  foreach w $::safepdf::panelWidgets($key) { grid $w }
  if {[info procs ::safepdf::panelShown::$key] ne {}} { ::safepdf::panelShown::$key }
}
# Thumbnails (9.r9): a canvas whose scroll region is centred on x = 0 (thRegion), one image
# per page (tags thi thiN, photo ::safepdf::thN) on a white frame (thf thfN) with its page
# label (thl); the current page has a rounded background (thsel), the keyboard selection a
# focus ring (thfocus). Every change of the view is reported once per idle moment (thView).
canvas .ol.th -width 200 -height 10 -background $::safepdf::col(panel) -highlightthickness 0 \\
  -borderwidth 0 -takefocus 1 -yscrollincrement 20 -confine 1 -yscrollcommand ::safepdf::thScroll
ttk::scrollbar .ol.ts -orient vertical -command {.ol.th yview}
grid .ol.th -in .ol.p -row 1 -column 0 -sticky nsew -padx {4 0} -pady {0 6}
grid .ol.ts -in .ol.p -row 1 -column 1 -sticky ns
raise .ol.th; raise .ol.ts
grid remove .ol.th .ol.ts
set ::safepdf::panelWidgets(thumbnails) {.ol.th .ol.ts}
set ::safepdf::thH 1
set ::safepdf::thPending 0
proc ::safepdf::thRegion {} {
  set w [winfo width .ol.th]
  if {$w < 2} { set w [winfo reqwidth .ol.th] }
  set x0 [expr {-($w / 2)}]
  .ol.th configure -scrollregion [list $x0 0 [expr {$x0 + $w}] $::safepdf::thH]
}
proc ::safepdf::thScroll {a b} {
  .ol.ts set $a $b
  if {$::safepdf::panel eq {thumbnails}} {
    if {$a <= 0.0 && $b >= 1.0} { grid remove .ol.ts } else { grid .ol.ts }
  }
  if {!$::safepdf::thPending} {
    set ::safepdf::thPending 1
    after idle {set ::safepdf::thPending 0; ::safepdf::emit thView}
  }
}
proc ::safepdf::panelShown::thumbnails {} {
  ::safepdf::thRegion
  ::safepdf::thScroll {*}[.ol.th yview]
}
bind .ol.th <Configure> {::safepdf::thRegion}
# Attachments panel (9.r10): the embedded files as a list .ol.at in row 1 of .ol.p (item aN =
# attachment N: name and size; description and details as a tooltip, ::safepdf::attTip(aN),
# refreshed by `attProbe N` before it shows). Double-click, Return and the context menu's
# Save attachment as... save the decoded bytes to a chosen file; nothing here ever opens or
# runs an attachment.
ttk::style configure Att.Treeview -font ::safepdf::fOl -background $::safepdf::col(panel) -fieldbackground $::safepdf::col(panel) -foreground $::safepdf::col(text) -borderwidth 0 -rowheight [expr {[font metrics ::safepdf::fOl -linespace] + 10}]
ttk::treeview .ol.at -style Att.Treeview -columns size -show tree -selectmode browse -height 10 -yscrollcommand ::safepdf::attScroll
.ol.at column #0 -stretch 1 -width 150 -minwidth 60
.ol.at column size -stretch 0 -width 70 -anchor e
ttk::scrollbar .ol.as -orient vertical -command {.ol.at yview}
grid .ol.at -in .ol.p -row 1 -column 0 -sticky nsew -padx {4 0} -pady {0 6}
grid .ol.as -in .ol.p -row 1 -column 1 -sticky ns
raise .ol.at; raise .ol.as
grid remove .ol.at .ol.as
set ::safepdf::panelWidgets(attachments) {.ol.at .ol.as}
proc ::safepdf::attScroll {a b} {
  .ol.as set $a $b
  if {$::safepdf::panel ne {attachments}} return
  if {$a <= 0.0 && $b >= 1.0} { grid remove .ol.as } else { grid .ol.as }
}
proc ::safepdf::panelShown::attachments {} { ::safepdf::attScroll {*}[.ol.at yview] }
menu .attmenu -tearoff 0
.attmenu add command -label {Save attachment as…} -command ::safepdf::attSaveSel
proc ::safepdf::attSaveSel {} {
  set i [lindex [.ol.at selection] 0]
  if {$i ne {}} { ::safepdf::emit attSave [string range $i 1 end] }
}
proc ::safepdf::attMenu {x y rx ry} {
  set i [.ol.at identify item $x $y]
  if {$i eq {}} return
  .ol.at selection set $i
  .ol.at focus $i
  tk_popup .attmenu $rx $ry
}
set ::safepdf::attHoverItem {}
proc ::safepdf::attHover {x y} {
  set i [.ol.at identify item $x $y]
  if {$i eq $::safepdf::attHoverItem} return
  set ::safepdf::attHoverItem $i
  after cancel $::safepdf::tipId
  destroy .tip
  if {$i ne {}} { set ::safepdf::tipId [after 600 [list ::safepdf::attTipShow $i]] }
}
proc ::safepdf::attTipShow {i} {
  if {![.ol.at exists $i]} return
  ::safepdf::emit attProbe [string range $i 1 end]
  set b [.ol.at bbox $i]
  if {$b eq {} || ![info exists ::safepdf::attTip($i)] || $::safepdf::attTip($i) eq {}} return
  destroy .tip
  toplevel .tip -background $::safepdf::col(fieldLine) -borderwidth 0
  wm overrideredirect .tip 1
  label .tip.l -text $::safepdf::attTip($i) -font ::safepdf::fBar -background white -foreground $::safepdf::col(text) -padx 6 -pady 3 -justify left -wraplength 360
  pack .tip.l -padx 1 -pady 1
  wm geometry .tip +[expr {[winfo rootx .ol.at] + [lindex $b 0] + 16}]+[expr {[winfo rooty .ol.at] + [lindex $b 1] + [lindex $b 3] + 4}]
}
proc ::safepdf::attTipHide {} {
  set ::safepdf::attHoverItem {}
  after cancel $::safepdf::tipId
  destroy .tip
}
proc ::safepdf::attClear {} {
  ::safepdf::attTipHide
  .ol.at delete [.ol.at children {}]
  array unset ::safepdf::attTip
}
bind .ol.at <Double-Button-1> {if {[.ol.at identify item %x %y] ne {}} ::safepdf::attSaveSel}
bind .ol.at <Return> ::safepdf::attSaveSel
bind .ol.at <<TreeviewSelect>> {set ::safepdf::attSel [lindex [.ol.at selection] 0]; if {$::safepdf::attSel ne {}} {::safepdf::emit attSelect [string range $::safepdf::attSel 1 end]}}
bind .ol.at <Button-3> {::safepdf::attMenu %x %y %X %Y}
if {[tk windowingsystem] eq {aqua}} {
  # The secondary click on a Mac: Button-2 or Button-3 (depending on the Tk version) and
  # Control-click.
  bind .ol.at <Button-2> {::safepdf::attMenu %x %y %X %Y}
  bind .ol.at <Control-Button-1> {::safepdf::attMenu %x %y %X %Y; break}
}
bind .ol.at <Motion> {::safepdf::attHover %x %y}
bind .ol.at <Leave> ::safepdf::attTipHide
# The save dialog of an attachment (no -filetypes: any file type; on aqua the Format pop-up
# would overflow, 9.r6); ::safepdf::autoPath answers it in smoke mode.
proc ::safepdf::askAttachSave {dir file args} {
  set ::safepdf::lastDialog [list $dir $file {*}$args]
  if {$::safepdf::autoPath ne {}} { return $::safepdf::autoPath }
  return [tk_getSaveFile -parent . -title {Save attachment as} -initialdir $dir -initialfile $file {*}$args]
}
# Layers panel (9.r11b, after PDF.js's layer viewer): a text widget .ol.ly drawn as a tree as
# the outline is. Row K is a heading (tag hK: an /Order label) or a group with a
# ttk::checkbutton .ol.ly.cK on ::safepdf::ly(K), disabled when the group is locked; tK is its
# disclosure triangle, dN/lN the margin of its depth, uA every ancestor A (a closed ancestor
# elides the row, its checkbox included). A checkbox emits `layer K`; the Lean side then sets
# every ::safepdf::ly from the new state (radio buttons, locked groups).
ttk::style configure Ly.TCheckbutton -font ::safepdf::fOl -background $::safepdf::col(panel) -foreground $::safepdf::col(text)
ttk::style map Ly.TCheckbutton -background [list disabled $::safepdf::col(panel) active $::safepdf::col(panel)]
font create ::safepdf::fLyHead -family $::safepdf::family -size -13 -weight bold
font create ::safepdf::fLyItal -family $::safepdf::family -size -13 -slant italic
text .ol.ly -wrap word -width 30 -height 10 -borderwidth 0 -highlightthickness 0 -background $::safepdf::col(panel) -foreground $::safepdf::col(text) -font ::safepdf::fOl -cursor arrow -padx 4 -pady 2 -spacing1 2 -spacing3 2 -state disabled -takefocus 0 -insertwidth 0 -yscrollcommand ::safepdf::lyScroll -selectbackground $::safepdf::col(panel) -inactiveselectbackground {} -exportselection 0
ttk::scrollbar .ol.ls -orient vertical -command {.ol.ly yview}
grid .ol.ly -in .ol.p -row 1 -column 0 -sticky nsew -padx {4 0} -pady {0 6}
grid .ol.ls -in .ol.p -row 1 -column 1 -sticky ns
raise .ol.ly; raise .ol.ls
grid remove .ol.ly .ol.ls
set ::safepdf::panelWidgets(layers) {.ol.ly .ol.ls}
.ol.ly tag configure tri -foreground $::safepdf::col(tri) -font ::safepdf::fTri -offset 1
.ol.ly tag configure head -font ::safepdf::fLyHead
.ol.ly tag configure headi -font ::safepdf::fLyItal
.ol.ly tag configure locked -foreground #8f8f9d
bindtags .ol.ly [list .ol.ly . all]
proc ::safepdf::lyScroll {a b} {
  .ol.ls set $a $b
  if {$::safepdf::panel ne {layers}} return
  if {$a <= 0.0 && $b >= 1.0} { grid remove .ol.ls } else { grid .ol.ls }
}
proc ::safepdf::panelShown::layers {} { ::safepdf::lyScroll {*}[.ol.ly yview] }
proc ::safepdf::lyClear {} {
  foreach w [winfo children .ol.ly] { destroy $w }
  .ol.ly configure -state normal
  .ol.ly delete 1.0 end
  foreach t [.ol.ly tag names] { if {$t ni {sel tri head headi locked}} { .ol.ly tag delete $t } }
  .ol.ly configure -state disabled
  array unset ::safepdf::ly
}
# lyRow K TRI TAGS LABEL KIND LOCKED: appends row K (KIND group: a checkbox and its name, tag
# gK, which wraps in the panel's width and toggles the checkbox when clicked, as PDF.js's
# <label>; heading: a bold label; italic: the Additional Layers heading) with the disclosure triangle TRI (empty for a leaf) and TAGS.
proc ::safepdf::lyRow {k tri tags label kind locked} {
  .ol.ly configure -state normal
  set a [.ol.ly index {end - 1c}]
  if {$tri ne {}} { .ol.ly insert end $tri [list tri t$k] }
  if {$kind eq {group}} {
    set ::safepdf::ly($k) 0
    set w .ol.ly.c$k
    ttk::checkbutton $w -style Ly.TCheckbutton -variable ::safepdf::ly($k) -takefocus 0 -command [list ::safepdf::emit layer $k]
    if {$locked} { $w state disabled }
    bindtags $w [list $w TCheckbutton LyWheel . all]
    .ol.ly window create end -window $w -align center -padx 2
    .ol.ly insert end $label [expr {$locked ? [list g$k locked] : [list g$k]}]
  } else {
    .ol.ly insert end $label [list [expr {$kind eq {italic} ? {headi} : {head}}] h$k]
  }
  .ol.ly insert end \\n
  foreach t $tags { .ol.ly tag add $t $a {end - 1c} }
  .ol.ly configure -state disabled
}
proc ::safepdf::lySetTri {n tri} {
  lassign [.ol.ly tag ranges t$n] a b
  if {$a eq {}} return
  set tags [.ol.ly tag names $a]
  .ol.ly configure -state normal
  .ol.ly delete $a $b
  .ol.ly insert $a $tri $tags
  .ol.ly configure -state disabled
}
proc ::safepdf::lyClick {x y} {
  set i [.ol.ly index @$x,$y]
  set d [.ol.ly dlineinfo $i]
  if {$d eq {} || $y > [lindex $d 1] + [lindex $d 3]} return
  foreach t [.ol.ly tag names $i] {
    if {[regexp {^[th]([0-9]+)$} $t -> n]} { ::safepdf::emit lyToggle $n; return }
    if {[regexp {^g([0-9]+)$} $t -> n]} { .ol.ly.c$n invoke; return }
  }
}
bind .ol.ly <ButtonRelease-1> {::safepdf::lyClick %x %y}
foreach w {.ol.ly LyWheel} {
  bind $w <MouseWheel> {.ol.ly yview scroll [expr {%D > 0 ? -2 : 2}] units; break}
  bind $w <Button-4> {.ol.ly yview scroll -2 units; break}
  bind $w <Button-5> {.ol.ly yview scroll 2 units; break}
  catch {
    bind $w <TouchpadScroll> {
      lassign [tk::PreciseScrollDeltas %D] ::safepdf::tdx ::safepdf::tdy
      if {$::safepdf::tdy != 0} { .ol.ly yview scroll [expr {-int($::safepdf::tdy)}] pixels }
      break
    }
  }
}
bind .ol.th <ButtonRelease-1> {focus .ol.th; ::safepdf::emit thClick [%W canvasy %y]}
bind .ol.th <Key-Up> {::safepdf::emit thKey up; break}
bind .ol.th <Key-Down> {::safepdf::emit thKey down; break}
bind .ol.th <Key-Return> {::safepdf::emit thKey go; break}
bind .ol.th <Key-KP_Enter> {::safepdf::emit thKey go; break}
bind .ol.th <FocusOut> {::safepdf::emit thBlur}
bind .ol.th <MouseWheel> {.ol.th yview scroll [expr {%D > 0 ? -2 : 2}] units; break}
bind .ol.th <Button-4> {.ol.th yview scroll -2 units; break}
bind .ol.th <Button-5> {.ol.th yview scroll 2 units; break}
catch {
  bind .ol.th <TouchpadScroll> {
    lassign [tk::PreciseScrollDeltas %D] ::safepdf::tdx ::safepdf::tdy
    lassign [.ol.th yview] ::safepdf::tha ::safepdf::thb
    .ol.th yview moveto [expr {$::safepdf::tha - $::safepdf::tdy / double(max($::safepdf::thH, 1))}]
    break
  }
}
.ol.t tag configure hover -background $::safepdf::col(olHover)
.ol.t tag configure cur -background $::safepdf::col(olCur)
bindtags .ol.t [list .ol.t . all]
proc ::safepdf::olRowAt {x y} {
  set i [.ol.t index @$x,$y]
  set d [.ol.t dlineinfo $i]
  if {$d eq {} || $y > [lindex $d 1] + [lindex $d 3]} return
  foreach t [.ol.t tag names $i] {
    if {[regexp {^([ot])([0-9]+)$} $t -> k n]} { return [list $k $n] }
  }
}
proc ::safepdf::olClick {x y} {
  lassign [::safepdf::olRowAt $x $y] k n
  if {$k eq {t}} { ::safepdf::emit olToggle $n } elseif {$k eq {o}} { ::safepdf::emit outline o$n }
}
proc ::safepdf::olHover {x y} {
  .ol.t tag remove hover 1.0 end
  lassign [::safepdf::olRowAt $x $y] k n
  if {$k ne {}} {
    set i [.ol.t index @$x,$y]
    .ol.t tag add hover \"$i linestart\" \"$i lineend + 1c\"
  }
}
proc ::safepdf::olMark {n} {
  .ol.t tag remove cur 1.0 end
  set r [.ol.t tag ranges o$n]
  if {$r ne {}} {
    .ol.t tag add cur \"[lindex $r 0] linestart\" \"[lindex $r 0] lineend + 1c\"
    .ol.t see [lindex $r 0]
  }
}
proc ::safepdf::olSetTri {n tri} {
  lassign [.ol.t tag ranges t$n] a b
  if {$a eq {}} return
  set tags [.ol.t tag names $a]
  .ol.t configure -state normal
  .ol.t delete $a $b
  .ol.t insert $a $tri $tags
  .ol.t configure -state disabled
}
proc ::safepdf::olClear {} {
  .ol.t configure -state normal
  .ol.t delete 1.0 end
  foreach t [.ol.t tag names] {
    if {$t ni {sel tri hover cur}} { .ol.t tag delete $t }
  }
}
bind .ol.t <ButtonRelease-1> {::safepdf::olClick %x %y}
bind .ol.t <Motion> {::safepdf::olHover %x %y}
bind .ol.t <Leave> {.ol.t tag remove hover 1.0 end}
bind .ol.t <MouseWheel> {.ol.t yview scroll [expr {%D > 0 ? -2 : 2}] units; break}
bind .ol.t <Button-4> {.ol.t yview scroll -2 units; break}
bind .ol.t <Button-5> {.ol.t yview scroll 2 units; break}
ttk::frame .v
# View modes (9.3): radio variables of the View and overflow menus; in the vertical modes every
# change of the vertical view (keys, scroll bar, wheel) is reported once per idle moment as
# `viewChanged` (current page, renders).
set ::safepdf::scrollMode vertical
set ::safepdf::spreadMode none
set ::safepdf::continuous 1
set ::safepdf::vcPending 0
proc ::safepdf::yscroll {a b} {
  .ys set $a $b
  if {$::safepdf::continuous && !$::safepdf::vcPending} {
    set ::safepdf::vcPending 1
    after idle {set ::safepdf::vcPending 0; ::safepdf::emit viewChanged}
  }
}
canvas .c -background $::safepdf::col(body) -highlightthickness 0 -takefocus 1 -confine 1 \\
  -xscrollcommand {.xs set} -yscrollcommand ::safepdf::yscroll
ttk::scrollbar .ys -orient vertical -command {.c yview}
ttk::scrollbar .xs -orient horizontal -command {.c xview}
grid .c -in .v -row 0 -column 0 -sticky nsew
grid .ys -in .v -row 0 -column 1 -sticky ns
grid .xs -in .v -row 1 -column 0 -sticky ew
grid rowconfigure .v 0 -weight 1
grid columnconfigure .v 0 -weight 1
label .status -text {} -anchor w -background $::safepdf::col(bar) \\
  -foreground $::safepdf::col(dim) -font ::safepdf::fBar -padx 6 -pady 2 -borderwidth 0
frame .statusline -height 1 -background $::safepdf::col(line)
# Task 12.5: the trusted identity line (`syncIdentity`), packed above the status line while
# the document has the window in full screen or hides parts of it.
label .ident -text {} -anchor w -background $::safepdf::col(text) -foreground #ffffff \\
  -font ::safepdf::fBar -padx 6 -pady 3 -borderwidth 0
pack .bar -side top -fill x
pack .barline -side top -fill x
pack .status -side bottom -fill x
pack .statusline -side bottom -fill x
.pw add .v -weight 1
pack .pw -side top -fill both -expand 1
# Scroll along axis (x or y) by dir (1 or -1) units or pages; past the end of the page,
# move to the next/previous page.
proc ::safepdf::step {axis dir what} {
  lassign [.c ${axis}view] a b
  if {$dir > 0 && $b >= 1.0} { ::safepdf::emit next; return }
  if {$dir < 0 && $a <= 0.0} {
    if {$axis eq {y}} { ::safepdf::emit prevEnd } else { ::safepdf::emit prev }
    return
  }
  .c ${axis}view scroll $dir $what
}
# Wheel (9.2): the delta goes to Lean (`View.wheelStep`), which scrolls, accumulates small
# deltas and turns the page after a push past the edge. Kinds: notch (%D in 1/120 notches,
# Tk >= 8.7 everywhere and Windows), line (Tk 8.6 on macOS: %D in lines), pixel (Tk 9
# <TouchpadScroll>, macOS trackpads).
set ::safepdf::wheelKind notch
if {[tk windowingsystem] eq {aqua} && [package vcompare [package provide Tk] 8.7] < 0} {
  set ::safepdf::wheelKind line
}
proc ::safepdf::wheel {axis kind d} {
  if {$d != 0} { ::safepdf::emit wheel $axis $kind $d }
}
proc ::safepdf::wheelZoom {d x y} {
  if {$d > 0} { ::safepdf::emit zoom in $x $y } elseif {$d < 0} { ::safepdf::emit zoom out $x $y }
}
bind . <Key-Next> {::safepdf::step y 1 pages}
bind . <Key-space> {::safepdf::step y 1 pages}
bind . <Key-Prior> {::safepdf::step y -1 pages}
bind . <Shift-Key-space> {::safepdf::step y -1 pages}
bind . <Key-BackSpace> {::safepdf::emit backspace}
bind . <Key-Down> {::safepdf::step y 1 units}
bind . <Key-Up> {::safepdf::step y -1 units}
bind . <Key-Right> {::safepdf::step x 1 units}
bind . <Key-Left> {::safepdf::step x -1 units}
bind . <Key-Home> {::safepdf::emit first}
bind . <Key-End> {::safepdf::emit last}
foreach k {plus equal KP_Add} {
  bind . <Key-$k> {::safepdf::emit zoom in}
  bind . <Control-Key-$k> {::safepdf::emit zoom in}
}
foreach k {minus KP_Subtract} {
  bind . <Key-$k> {::safepdf::emit zoom out}
  bind . <Control-Key-$k> {::safepdf::emit zoom out}
}
bind . <Key-0> {::safepdf::emit zoom actual}
bind . <Control-Key-0> {::safepdf::emit zoom actual}
bind . <Key-f> {::safepdf::emit zoom fitpage}
bind . <Key-w> {::safepdf::emit zoom fitwidth}
bind . <Key-r> {::safepdf::emit rotate cw}
bind . <Key-R> {::safepdf::emit rotate ccw}
bind .c <MouseWheel> {::safepdf::wheel y $::safepdf::wheelKind %D; break}
bind .c <Shift-MouseWheel> {::safepdf::wheel x $::safepdf::wheelKind %D; break}
bind .c <Control-MouseWheel> {::safepdf::wheelZoom %D %x %y; break}
bind .c <Button-4> {::safepdf::wheel y notch 120; break}
bind .c <Button-5> {::safepdf::wheel y notch -120; break}
bind .c <Shift-Button-4> {::safepdf::wheel x notch 120; break}
bind .c <Shift-Button-5> {::safepdf::wheel x notch -120; break}
# Tk 9 trackpads (macOS): pixel deltas; Shift is not needed, the gesture has both axes.
catch {
  bind .c <TouchpadScroll> {
    lassign [tk::PreciseScrollDeltas %D] ::safepdf::tdx ::safepdf::tdy
    ::safepdf::wheel x pixel $::safepdf::tdx
    ::safepdf::wheel y pixel $::safepdf::tdy
    break
  }
}
bind .c <Control-Button-4> {::safepdf::wheelZoom 1 %x %y; break}
bind .c <Control-Button-5> {::safepdf::wheelZoom -1 %x %y; break}
bind . <Control-o> {::safepdf::emit open}
bind . <Control-w> {::safepdf::emit close}
bind . <Control-q> {::safepdf::emit quit}
# Resizes are debounced (a window drag sends many); for 300 ms after ::safepdf::resizeSoon
# (the outline sidebar opens or closes, 9.r4) a change of the canvas width is reported at
# once, from inside the <Configure> binding: Tk calls it while laying out the panes, before
# the canvas is painted at its new size, so the pages never show at the old layout in the new
# width. Height-only changes (find bar, go-to bar) stay debounced.
set ::safepdf::resizeNow 0
set ::safepdf::resizeNowId {}
set ::safepdf::confW 0
proc ::safepdf::resizeSoon {} {
  set ::safepdf::resizeNow 1
  after cancel $::safepdf::resizeNowId
  set ::safepdf::resizeNowId [after 300 {set ::safepdf::resizeNow 0}]
}
bind .c <Configure> {
  after cancel $::safepdf::resizeId
  set ::safepdf::confW0 $::safepdf::confW
  set ::safepdf::confW %w
  if {$::safepdf::resizeNow && %w != $::safepdf::confW0} {
    ::safepdf::emit resize %w %h
  } else {
    set ::safepdf::resizeId [after 100 {::safepdf::emit resize [winfo width .c] [winfo height .c]}]
  }
}
# Selection (8.2c): press/drag/release and double-click on the page, context menu.
bind .c <ButtonPress-1> {focus .c; ::safepdf::emit press %x %y}
bind .c <B1-Motion> {::safepdf::emit drag %x %y}
bind .c <ButtonRelease-1> {::safepdf::emit release %x %y}
bind .c <Double-Button-1> {focus .c; ::safepdf::emit word %x %y}
menu .pop -tearoff 0
.pop add command -label Copy -accelerator Ctrl+C -command {::safepdf::emit copy}
.pop add command -label {Select all} -accelerator Ctrl+A -command {::safepdf::emit selectall}
.pop add command -label {Find...} -accelerator Ctrl+F -command ::safepdf::showFind
bind .c <Button-3> {focus .c; ::safepdf::emit popup %x %y %X %Y}
bind . <Control-c> {::safepdf::emit copy}
bind . <Control-a> {::safepdf::emit selectall}
# Search bar (hidden until Ctrl+F). The entry does not carry the toplevel's bind tag, so
# typing in it never triggers the viewer's single-key bindings.
ttk::frame .find
ttk::label .find.l -text {Find:}
ttk::entry .find.e -textvariable ::safepdf::query -width 32
ttk::button .find.prev -text {Previous} -command {::safepdf::emit find prev $::safepdf::query}
ttk::button .find.next -text {Next} -command {::safepdf::emit find next $::safepdf::query}
ttk::button .find.close -text {Close} -command ::safepdf::hideFind
pack .find.l .find.e .find.prev .find.next .find.close -side left -padx 2 -pady 2
bindtags .find.e [list .find.e TEntry all]
proc ::safepdf::showFind {} {
  ::safepdf::emit opening find
  if {![winfo ismapped .find]} { pack .find -side top -fill x -after .barline }
  focus .find.e
  .find.e selection range 0 end
  .find.e icursor end
}
# Closing a bar gives the focus back to the page only when it was in the bar (a click-away
# on another entry keeps that entry focused; task 10.6).
proc ::safepdf::refocus {bar} {
  set f [focus]
  if {$f eq {} || $f eq $bar || [string match $bar.* $f]} { focus .c }
}
proc ::safepdf::hideFind {} { pack forget .find; ::safepdf::refocus .find; ::safepdf::emit find close }
bind .find.e <Return> {::safepdf::emit find next $::safepdf::query; break}
bind .find.e <KP_Enter> {::safepdf::emit find next $::safepdf::query; break}
bind .find.e <Shift-Return> {::safepdf::emit find prev $::safepdf::query; break}
bind .find.e <F3> {::safepdf::emit find next $::safepdf::query; break}
bind .find.e <Shift-F3> {::safepdf::emit find prev $::safepdf::query; break}
bind .find.e <Escape> {::safepdf::hideFind; break}
bind .find.e <Control-q> {::safepdf::emit quit}
bind . <Control-f> ::safepdf::showFind
bind . <F3> {::safepdf::emit find next $::safepdf::query}
bind . <Shift-F3> {::safepdf::emit find prev $::safepdf::query}
# Links (8.2d): hover shows the target, a click (press and release in place) activates it.
bind .c <Motion> {::safepdf::emit hover %x %y}
bind .c <Leave> {::safepdf::emit hover {} {}}
bind . <Alt-Key-Left> {::safepdf::emit back}
bind . <Alt-Key-Right> {::safepdf::emit forward}
bind . <F9> {::safepdf::emit outlineToggle}
.pop add separator
.pop add command -label {Sidebar} -accelerator F9 -command {::safepdf::emit outlineToggle}
.pop add command -label {Back} -accelerator Alt+Left -command {::safepdf::emit back}
.pop add command -label {Forward} -accelerator Alt+Right -command {::safepdf::emit forward}
.pop add command -label {Go to page...} -accelerator Ctrl+G -command ::safepdf::showGoto
# Go-to-page bar (Ctrl+G): a page number or a page label.
ttk::frame .goto
ttk::label .goto.l -text {Go to page (number or label):}
ttk::entry .goto.e -textvariable ::safepdf::gotoText -width 16
ttk::button .goto.go -text {Go} -command {::safepdf::emit goto $::safepdf::gotoText}
ttk::button .goto.close -text {Close} -command ::safepdf::hideGoto
pack .goto.l .goto.e .goto.go .goto.close -side left -padx 2 -pady 2
bindtags .goto.e [list .goto.e TEntry all]
proc ::safepdf::showGoto {} {
  ::safepdf::emit opening goto
  if {![winfo ismapped .goto]} { pack .goto -side top -fill x -after .barline }
  focus .goto.e
  .goto.e selection range 0 end
  .goto.e icursor end
}
proc ::safepdf::hideGoto {} { pack forget .goto; ::safepdf::refocus .goto }
bind .goto.e <Return> {::safepdf::emit goto $::safepdf::gotoText; break}
bind .goto.e <KP_Enter> {::safepdf::emit goto $::safepdf::gotoText; break}
bind .goto.e <Escape> {::safepdf::hideGoto; break}
bind .goto.e <Control-q> {::safepdf::emit quit}
bind . <Control-g> ::safepdf::showGoto
# External-link confirmation: shows the exact address (a read-only text widget filled by
# variable substitution, never parsed as script) and returns 1 only when the user chooses
# to copy it. Nothing is opened. In smoke mode (autoConfirm) the dialog confirms itself.
proc ::safepdf::askUri {uri} {
  set w .uri
  destroy $w
  toplevel $w
  wm title $w {External link}
  wm transient $w .
  ttk::label $w.msg -justify left -wraplength 460 -text {This link points outside the \\
document, to the address below. SafePDF never opens it; it can copy the address to the \\
clipboard.}
  text $w.t -wrap char -width 60 -height 4 -relief sunken -borderwidth 1
  $w.t insert end $uri
  $w.t configure -state disabled
  ttk::frame $w.b
  ttk::button $w.b.copy -text {Copy address} -command {set ::safepdf::uriAnswer 1}
  ttk::button $w.b.cancel -text {Cancel} -command {set ::safepdf::uriAnswer 0}
  pack $w.b.cancel $w.b.copy -side right -padx 4 -pady 4
  pack $w.msg -side top -fill x -padx 8 -pady 6
  pack $w.t -side top -fill both -expand 1 -padx 8
  pack $w.b -side bottom -fill x
  wm protocol $w WM_DELETE_WINDOW {set ::safepdf::uriAnswer 0}
  bind $w <Escape> {set ::safepdf::uriAnswer 0}
  ::safepdf::cancelBind $w {set ::safepdf::uriAnswer 0}
  set ::safepdf::uriAnswer {}
  if {$::safepdf::autoConfirm} {
    after 300 {
      set ::safepdf::shownUri [.uri.t get 1.0 {end - 1 chars}]
      .uri.b.copy invoke
    }
  }
  catch {grab $w}
  focus $w.b.cancel
  vwait ::safepdf::uriAnswer
  catch {grab release $w}
  destroy $w
  return $::safepdf::uriAnswer
}
set ::safepdf::autoConfirm 0
# Save (9.5c): questions (a Tk message box; its answer yes/no/cancel) and the Save As dialog.
# In smoke mode ::safepdf::autoAnswer and ::safepdf::autoPath answer them; the last question
# is kept in ::safepdf::lastAsk. Window close and Ctrl+Q go through the viewer (unsaved marks).
set ::safepdf::autoAnswer {}
set ::safepdf::autoPath {}
set ::safepdf::lastAsk {}
proc ::safepdf::ask {type title msg} {
  set ::safepdf::lastAsk $msg
  if {$::safepdf::autoAnswer ne {}} { return $::safepdf::autoAnswer }
  return [tk_messageBox -parent . -icon question -type $type -title $title -message $msg]
}
# Three-way questions (9.r2: Overwrite / Save As... / Cancel, Save / Don't Save / Cancel): a
# modal dialog with the buttons given as key label pairs in display order (Save.*Buttons; on
# aqua the macOS order), the default key (focused at first; Return presses the focused
# button) and the cancel key (Escape, the dialog's close button); the focus goes back where it
# was. Returns the chosen key. Smoke mode: ::safepdf::autoAnswer answers.
proc ::safepdf::choose {title msg default cancel args} {
  set ::safepdf::lastAsk $msg
  if {$::safepdf::autoAnswer ne {}} { return $::safepdf::autoAnswer }
  set w .choose
  destroy $w
  toplevel $w
  wm withdraw $w
  wm title $w $title
  wm transient $w .
  wm resizable $w 0 0
  ttk::frame $w.f -padding 14
  ttk::label $w.f.msg -justify left -wraplength 440 -text $msg
  ttk::frame $w.f.b
  set ::safepdf::chooseAnswer {}
  foreach {key label} $args {
    ttk::button $w.f.b.$key -text $label -command [list set ::safepdf::chooseAnswer $key]
    if {$key eq $default} { $w.f.b.$key configure -default active }
    pack $w.f.b.$key -side left -padx 4
  }
  pack $w.f.msg -side top -fill x -pady {0 12}
  pack $w.f.b -side right
  pack $w.f -fill both -expand 1
  wm protocol $w WM_DELETE_WINDOW [list set ::safepdf::chooseAnswer $cancel]
  bind $w <Escape> [list set ::safepdf::chooseAnswer $cancel]
  ::safepdf::cancelBind $w [list set ::safepdf::chooseAnswer $cancel]
  # Return (and keypad Enter) presses the focused button, as in tk_messageBox: after Tab to
  # Cancel, Return must cancel, not run the default (9.r6); the default has the focus first.
  bind $w <Return> [list ::safepdf::chooseReturn $w $default]
  bind $w <KP_Enter> [list ::safepdf::chooseReturn $w $default]
  ::tk::PlaceWindow $w widget .
  set old [focus]
  wm deiconify $w
  catch {grab $w}
  focus $w.f.b.$default
  vwait ::safepdf::chooseAnswer
  catch {grab release $w}
  destroy $w
  if {$old ne {} && [winfo exists $old]} { catch {focus $old} }
  return $::safepdf::chooseAnswer
}
proc ::safepdf::chooseReturn {w default} {
  set f [focus]
  if {$f ne {} && [string equal [winfo parent $f] $w.f.b]} { $f invoke } else { $w.f.b.$default invoke }
}
# Every way of quitting goes through this one proc (9.r2; task 9.r3's key bindings call it):
# the viewer asks about unsaved marks and quits only when the answer allows it.
proc ::safepdf::quit {} { ::safepdf::emit quit }
if {[tk windowingsystem] eq {aqua}} {
  # The application menu's Quit and Cmd+Q (Tk calls this; returning without exiting cancels).
  proc ::tk::mac::Quit {} { ::safepdf::quit }
}
# The save dialogs take their type options from Save.saveDialogOptions (9.r6: none of
# -filetypes on aqua, whose Format: pop-up overflows the panel); the last options are kept in
# ::safepdf::lastDialog for the smoke test.
set ::safepdf::lastDialog {}
proc ::safepdf::askSavePath {dir file args} {
  set ::safepdf::lastDialog [list $dir $file {*}$args]
  if {$::safepdf::autoPath ne {}} { return $::safepdf::autoPath }
  return [tk_getSaveFile -parent . -title {Save As} -initialdir $dir -initialfile $file {*}$args]
}
# XFDF import/export (9.11): the file dialogs; ::safepdf::autoPath answers them in smoke mode.
proc ::safepdf::askXfdfOpen {dir} {
  if {$::safepdf::autoPath ne {}} { return $::safepdf::autoPath }
  return [tk_getOpenFile -parent . -title {Import annotations} -initialdir $dir \\
    -filetypes {{XFDF {.xfdf}} {{All files} *}}]
}
proc ::safepdf::askXfdfSave {dir file args} {
  set ::safepdf::lastDialog [list $dir $file {*}$args]
  if {$::safepdf::autoPath ne {}} { return $::safepdf::autoPath }
  return [tk_getSaveFile -parent . -title {Export annotations} -initialdir $dir -initialfile $file \\
    {*}$args]
}
wm protocol . WM_DELETE_WINDOW ::safepdf::quit
bind . <Control-s> {::safepdf::emit save}
bind . <Control-S> {::safepdf::emit saveAs}
# Marks (9.4): current highlight colour, the right-clicked point, keys, the note icon and the note popup.
set ::safepdf::hlColor yellow
set ::safepdf::popX {}
set ::safepdf::popY {}
bind . <Key-h> {::safepdf::emit highlight}
bind . <Key-Delete> {::safepdf::emit markDelete}
bind . <Control-z> {::safepdf::emit undo}
bind . <Control-Z> {::safepdf::emit redo}
# A note icon (a speech bubble, after the /Text annotation's Comment icon) in the box
# x0 y0 x1 y1 of canvas c, filled with colour fill; selected: a blue ring.
proc ::safepdf::noteIcon {c x0 y0 x1 y1 fill tags} {
  set w [expr {$x1 - $x0}]; set h [expr {$y1 - $y0}]
  set r [expr {max(1.0, $w / 8.0)}]
  set by [expr {$y0 + $h * 0.75}]
  ::safepdf::rrect $c $x0 $y0 $x1 $by $r -fill $fill -outline #3b3b44 -width 1 -tags $tags
  $c create polygon [expr {$x0 + $w * 0.25}] [expr {$by - 0.5}] [expr {$x0 + $w * 0.25}] $y1 \
    [expr {$x0 + $w * 0.5}] [expr {$by - 0.5}] -fill $fill -outline #3b3b44 -width 1 -tags $tags
  $c create line [expr {$x0 + $w * 0.25}] [expr {$by - 0.5}] [expr {$x0 + $w * 0.5}] [expr {$by - 0.5}] \
    -fill $fill -width 2 -tags $tags
  foreach f {0.28 0.5} {
    set y [expr {$y0 + $h * $f}]
    $c create line [expr {$x0 + $w * 0.22}] $y [expr {$x1 - $w * 0.22}] $y -fill #3b3b44 \
      -width [expr {max(1.0, $h / 16.0)}] -tags $tags
  }
}
# Note popup: a small window with the note text (inserted by variable substitution, never
# parsed as script); Save (Ctrl+Return) sends the text back as one word, Delete removes the
# note. Closing it without Save — Escape (bound on the toplevel, so it works in the text
# widget), Cancel or the window's close button — sends the text as `noteClose` and Lean
# decides (Marks.Store.onUnsavedClose, 9.r12): a note with a stored text keeps it (the edits
# are discarded); a new note (stored text empty) gets the typed text, or is deleted when the
# popup is empty or white space only. Opening another note's popup first closes this one
# the same way; reopening the same note's popup keeps it and its edits.
set ::safepdf::noteId {}
proc ::safepdf::noteEdit {id text x y} {
  set w .note
  if {[winfo exists $w]} {
    if {$::safepdf::noteId eq $id} { raise $w; focus $w.t; return }
    ::safepdf::noteDone $::safepdf::noteId close
  }
  destroy $w
  set ::safepdf::noteId $id
  toplevel $w -background $::safepdf::col(panel)
  wm title $w Note
  wm transient $w .
  wm geometry $w +$x+$y
  wm protocol $w WM_DELETE_WINDOW [list ::safepdf::noteDone $id close]
  text $w.t -wrap word -width 36 -height 6 -font ::safepdf::fOl -relief solid -borderwidth 1 \
    -undo 1 -background #ffffe8 -foreground $::safepdf::col(text) -padx 6 -pady 4
  $w.t insert end $text
  ttk::frame $w.b
  ttk::button $w.b.save -text Save -command [list ::safepdf::noteDone $id save]
  ttk::button $w.b.del -text Delete -command [list ::safepdf::noteDone $id delete]
  ttk::button $w.b.cancel -text Cancel -command [list ::safepdf::noteDone $id close]
  pack $w.b.cancel $w.b.save -side right -padx 4 -pady 4
  pack $w.b.del -side left -padx 4 -pady 4
  pack $w.b -side bottom -fill x
  pack $w.t -side top -fill both -expand 1 -padx 6 -pady {6 0}
  bind $w <Escape> [list ::safepdf::noteDone $id close]
  ::safepdf::cancelBind $w [list ::safepdf::noteDone $id close]
  # break: the popup is gone after noteDone, so the Text class binding must not run.
  ::safepdf::primaryBind $w.t Return \"[list ::safepdf::noteDone $id save]; break\"
  focus $w.t
}
proc ::safepdf::noteDone {id what} {
  if {![winfo exists .note]} return
  set t [.note.t get 1.0 {end - 1 chars}]
  destroy .note
  set ::safepdf::noteId {}
  switch -- $what {
    save { ::safepdf::emit noteSave $id $t }
    delete { ::safepdf::emit noteDelete $id }
    default { ::safepdf::emit noteClose $id $t }
  }
}
# Note id was deleted elsewhere (Delete key, Edit → Delete mark, its highlight deleted): its
# open popup goes too (called by Lean's deleteMark).
proc ::safepdf::noteGone {id} {
  if {[winfo exists .note] && $::safepdf::noteId eq $id} { destroy .note; set ::safepdf::noteId {} }
}
# Selection bubble, colour picker and Highlight pop-over (9.8), after PDF.js's editToolbar,
# colorPicker and #editorHighlightParamsToolbar; positions come from Bubble.lean. Colours
# sampled from Firefox's PDF.js (docs/viewer-reference/pdfjs-firefox.png).
array set ::safepdf::col {
  bubInk #6a5b92 bubLine #d0cfd5 shadow #e4e4e9 accent #6b45d3 swLine #b7b7c1 track #c6c5c7
  trackOn #c1b0ec thumb #c3b5ee dot #b7b7c1 popLine #d7d7db off #8f8f9d
}
set ::safepdf::hlTool 0
set ::safepdf::showAll 1
proc ::safepdf::icon::trash {c} {
  $c create line 9.5 11 22.5 11 -width 1.5 -capstyle round -tags inkf
  $c create line 13.5 11 13.5 8.5 18.5 8.5 18.5 11 -width 1.5 -joinstyle round -tags inkf
  $c create line 11 11 12 24 20 24 21 11 -width 1.5 -joinstyle round -tags inkf
  $c create line 14.5 14.5 14.5 20.5 -width 1.3 -tags inkf
  $c create line 17.5 14.5 17.5 20.5 -width 1.3 -tags inkf
}
# A toolbar icon (32 px box) drawn on canvas c centred at cx cy in ink colour, with tags.
proc ::safepdf::bubIcon {c name cx cy tags} {
  $c dtag inkf inkf; $c dtag inko inko
  ::safepdf::icon::$name $c
  $c itemconfigure inkf -fill $::safepdf::col(bubInk)
  $c itemconfigure inko -outline $::safepdf::col(bubInk)
  foreach t $tags { $c addtag $t withtag inkf; $c addtag $t withtag inko }
  $c move inkf [expr {$cx - 16}] [expr {$cy - 16}]
  $c move inko [expr {$cx - 16}] [expr {$cy - 16}]
  $c dtag inkf inkf; $c dtag inko inko
}
# The bubble's rounded box (a pill) with a soft shadow.
proc ::safepdf::bubBox {c x0 y0 x1 y1 r tags} {
  ::safepdf::rrect $c $x0 [expr {$y0 + 2}] $x1 [expr {$y1 + 2}] $r -fill $::safepdf::col(shadow) -outline {} -tags $tags
  ::safepdf::rrect $c $x0 $y0 $x1 $y1 $r -fill white -outline $::safepdf::col(bubLine) -width 1 -tags $tags
}
proc ::safepdf::bubDivider {c x y0 y1 tags} {
  $c create line $x $y0 $x $y1 -fill $::safepdf::col(bubLine) -width 1 -tags $tags
}
# The colour button: a 16 px swatch and a chevron (pointing up while the picker is open).
proc ::safepdf::bubColor {c bx cy hex open tags} {
  $c create oval [expr {$bx + 4}] [expr {$cy - 8}] [expr {$bx + 20}] [expr {$cy + 8}] -fill $hex -outline $::safepdf::col(swLine) -width 1 -tags $tags
  set d [expr {$open ? -1.8 : 1.8}]
  $c create line [expr {$bx + 26.5}] [expr {$cy - $d}] [expr {$bx + 30}] [expr {$cy + $d}] [expr {$bx + 33.5}] [expr {$cy - $d}] -fill $::safepdf::col(bubInk) -width 1.3 -capstyle round -joinstyle round -tags $tags
}
# A swatch at cx cy of diameter d; the selected one ringed (2 px, 2 px away).
# Tooltips of the bubble's buttons (9.r4): canvas item tag b:NAME, shown under its button.
proc ::safepdf::bubTip {tag text} {
  after cancel $::safepdf::tipId
  set ::safepdf::tipId [after 600 [list ::safepdf::bubTipShow $tag $text]]
}
proc ::safepdf::bubTipShow {tag text} {
  set b [.c bbox $tag]
  if {$b eq {}} return
  destroy .tip
  toplevel .tip -background $::safepdf::col(fieldLine) -borderwidth 0
  wm overrideredirect .tip 1
  label .tip.l -text $text -font ::safepdf::fBar -background white \
    -foreground $::safepdf::col(text) -padx 6 -pady 3
  pack .tip.l -padx 1 -pady 1
  set x [expr {[winfo rootx .c] + round([lindex $b 0] - [.c canvasx 0])}]
  set y [expr {[winfo rooty .c] + round([lindex $b 3] - [.c canvasy 0]) + 8}]
  wm geometry .tip +$x+$y
}
proc ::safepdf::bubTipHide {} {
  after cancel $::safepdf::tipId
  destroy .tip
}
proc ::safepdf::swatch {c cx cy d hex sel tags} {
  set r [expr {$d / 2.0}]
  if {$sel} {
    $c create oval [expr {$cx - $r - 3}] [expr {$cy - $r - 3}] [expr {$cx + $r + 3}] [expr {$cy + $r + 3}] -outline $::safepdf::col(accent) -width 2 -tags $tags
  }
  $c create oval [expr {$cx - $r}] [expr {$cy - $r}] [expr {$cx + $r}] [expr {$cy + $r}] -fill $hex -outline $::safepdf::col(swLine) -width 1 -tags $tags
}
# The Highlight pop-over: a canvas placed under the toolbar, drawn by Lean (drawPopover).
canvas .hlbar -width 220 -height 190 -background $::safepdf::col(body) -highlightthickness 0 -borderwidth 0 -takefocus 0 -cursor arrow
bind .hlbar <ButtonPress-1> {::safepdf::emit popClick %x %y}
bind .hlbar <B1-Motion> {::safepdf::emit popDrag %x %y}
proc ::safepdf::popShow {x} {
  set y [expr {[winfo rooty .barline] - [winfo rooty .] + 5}]
  place .hlbar -in . -x $x -y $y
  raise .hlbar
}
proc ::safepdf::popHide {} { place forget .hlbar }
# Add text and Draw (9.9): the parameter pop-over .edbar (drawn by Lean, drawEdPop), the
# free-text editor (a text widget in a canvas window, tag ftedit; typed keys stay in it) and
# the stroke being drawn (canvas line, tag inkcur).
canvas .edbar -width 220 -height 196 -background $::safepdf::col(body) -highlightthickness 0 -borderwidth 0 -takefocus 0 -cursor arrow
bind .edbar <ButtonPress-1> {::safepdf::emit edClick %x %y}
bind .edbar <B1-Motion> {::safepdf::emit edDrag %x %y}
proc ::safepdf::edShow {x h} {
  .edbar configure -height $h
  set y [expr {[winfo rooty .barline] - [winfo rooty .] + 5}]
  place .edbar -in . -x $x -y $y
  raise .edbar
}
proc ::safepdf::edHide {} { place forget .edbar }
proc ::safepdf::ftOpen {x y text px fg} {
  destroy .c.ft
  .c delete ftedit
  text .c.ft -wrap none -borderwidth 0 -highlightthickness 1 -highlightcolor #0060df \
    -highlightbackground #0060df -relief flat -font [list Helvetica -$px] -foreground $fg \
    -background white -insertbackground $fg -undo 1 -padx 1 -pady 0 -width 4 -height 1
  .c.ft insert end $text
  bindtags .c.ft [list .c.ft Text all]
  bind .c.ft <Escape> {::safepdf::emit ftCommit; break}
  bind .c.ft <KeyRelease> ::safepdf::ftFit
  ::safepdf::primaryBind .c.ft q {::safepdf::emit quit}
  .c create window $x $y -anchor nw -window .c.ft -tags ftedit
  ::safepdf::ftFit
  focus .c.ft
}
proc ::safepdf::ftFit {} {
  if {![winfo exists .c.ft]} return
  set ls [split [.c.ft get 1.0 {end - 1 chars}] \n]
  set w 4
  foreach l $ls { if {[string length $l] + 2 > $w} { set w [expr {[string length $l] + 2}] } }
  .c.ft configure -width $w -height [expr {max(1, [llength $ls])}]
}
proc ::safepdf::ftConf {px fg} {
  if {[winfo exists .c.ft]} {
    .c.ft configure -font [list Helvetica -$px] -foreground $fg -insertbackground $fg
    ::safepdf::ftFit
  }
}
proc ::safepdf::inkStart {x y w fg} {
  .c delete inkcur
  set ::safepdf::inkPts [list $x $y $x $y]
  .c create line {*}$::safepdf::inkPts -width $w -fill $fg -capstyle round -joinstyle round -tags inkcur
}
proc ::safepdf::inkAdd {x y} {
  lappend ::safepdf::inkPts $x $y
  .c coords inkcur {*}$::safepdf::inkPts
}
bind . <Key-Escape> {::safepdf::emit escape}
# Click-away (task 10.6, Toolbar.onClick): a press anywhere in the main window closes the open
# transients it lies outside of. Bound on the tag all, so it runs after the widget's own
# bindings and the press still does its job; presses in other toplevels (the note popup,
# menus, dialogs) are not click-aways.
proc ::safepdf::clickAway {w} {
  if {[catch {winfo toplevel $w} top] || $top ne {.}} return
  ::safepdf::emit clickAway $w
}
bind all <ButtonPress-1> {+::safepdf::clickAway %W}
focus .c
"

/-! ## The document worker (task 12.2c) -/

/-- How long a worker request may run before the worker is killed (ms). Smoke mode may set
another value with `SAFEPDF_WORKER_DEADLINE_MS`. -/
def workerDeadlineMs : Nat := 20000

/-- Marks an error text that comes from the document worker (`workerErr`, `pageErr`). -/
def workerTag : String := "\x00worker:"

/-- An error the document worker reported (or the failure of a worker request), as an `Error`
whose text `pageErr` shows as it is. -/
def workerErr (msg : String) : Error := .unsupported (workerTag ++ msg)

/-- The text of a page's render error: `renderError`, or the worker's own text. -/
def pageErr (e : Error) : String :=
  match e with
  | .unsupported w =>
    if w.startsWith workerTag then String.ofList (w.toList.drop workerTag.length)
    else renderError e
  | _ => renderError e

/-- What went wrong with a worker request, as text. -/
def failText : Worker.ClientError → String
  | .notEncodable => "the request does not fit the protocol"
  | .timeout => "no answer in time"
  | .exited d => d
  | .tooLong n => s!"its answer of {n} bytes is above the cap"
  | .badFrame _ => "its answer does not decode"

/-- The status text of a render that hit the deadline. -/
def timeoutText (deadlineMs : Nat) : String :=
  let t := if deadlineMs % 1000 == 0 then s!"{deadlineMs / 1000} s" else s!"{deadlineMs} ms"
  s!"rendering stopped: the document took too long (no answer within {t}; its worker was stopped)"

/-- A render job's outcome from the worker's reply. The image is checked against its size
before Tk sees it (`Shim.photoPut` reads `4·w·h` bytes). -/
def outOfReply (deadlineMs : Nat) : Worker.Reply → RenderOut
  | .response (.image w h data _) ns =>
    if data.size == 4 * w * h then some (.ok ⟨w, h, data⟩, ns)
    else some (.error (workerErr
      s!"the document worker sent a malformed image ({w}x{h}, {data.size} bytes)"), ns)
  | .response (.error _ msg) ns => some (.error (workerErr msg), ns)
  | .response _ ns => some (.error (workerErr "the document worker answered with another message"), ns)
  | .failed .timeout => some (.error (workerErr (timeoutText deadlineMs)), 0)
  | .failed e => some (.error (workerErr s!"the document worker stopped: {failText e}"), 0)
  | .cancelled => none

/-- Task 13.4d: whether a render's reply is a **partial page** (an image the worker marked
`complete := false` whose size checks out; a malformed image is an error, not a page). -/
def incompleteOfReply : Worker.Reply → Bool
  | .response (.image w h data false) _ => data.size == 4 * w * h
  | _ => false

/-- The status text of a partial page (task 13.4d), also the page's overlay text. -/
def partialText : String := "page drawn partly: render work limit reached"

/-- The worker session and document id to render `doc`'s pages with (task 12.2c): a session
exists and the bytes fit the protocol. Since task 12.2d the worker renders under the layers
state of the request and with the viewer's own font search (`workerStart`), so neither keeps a
render in this process. Sends the bytes (`State.view`'s when saved marks are previewed) to the
session when the document changed (`srcSerial`). -/
def workerFor (st : IO.Ref State) (doc : Doc) : IO (Option (Worker.Session × Nat)) := do
  let s ← st.get
  let some ses := s.worker | return none
  let d := s.view.getD doc
  if d.file.bytes.size > limits.maxInputBytes then return none
  if s.workerSrc != some s.srcSerial then
    ses.setDoc (some (s.srcSerial, d.file.bytes, true))
    st.modify ({ · with workerSrc := some s.srcSerial })
  return some (ses, s.srcSerial)

/-- The worker session for the open document's text index and links (task 12.2d): as
`workerFor`, but only while the pages are rendered from `doc` itself (`State.view` none) —
the text index and the links are read from `doc`, never from a preview of edited saved marks
(those are read in this process, as before). -/
def workerForText (st : IO.Ref State) (doc : Doc) : IO (Option (Worker.Session × Nat)) := do
  if (← st.get).view.isSome then return none
  workerFor st doc

/-! ## The reservation pool (task 12.3, `Budget`) -/

/-- Releases reservation `t` (none: nothing). Releasing a ticket twice changes nothing
(`Budget.Pool.release_release`). -/
def releaseTicket (st : IO.Ref State) (t : Option Budget.Ticket) : IO Unit :=
  if let some t := t then st.modify fun s => { s with pool := s.pool.release t } else pure ()

/-- Releases the reservations of the text and links requests whose reply is there (the reply
is a small value; the reservation covered the request in flight). -/
def sweepSide (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let sweep (js : Array SideJob) : IO (Array SideJob × List Budget.Ticket) := do
    let mut out := #[]
    let mut freed := []
    for j in js do
      if let some t := j.ticket then
        if ← IO.hasFinished j.task then
          out := out.push { j with ticket := none }
          freed := t :: freed
          continue
      out := out.push j
    return (out, freed)
  let (ts, f1) ← sweep s.textJobs
  let (ls, f2) ← sweep s.linkJobs
  st.modify fun s => { s with textJobs := ts, linkJobs := ls,
                              pool := (f1 ++ f2).foldl Budget.Pool.release s.pool }

/-- **Asks the pool for operation `o`** (after `sweepSide`): on `reserved` the new pool is
kept and the peak updated; waits, lowered quality and refusals are counted. -/
def admit (st : IO.Ref State) (o : Budget.Op) : IO Budget.Outcome := do
  sweepSide st
  let s ← st.get
  let out := s.pool.admit Budget.ceilings o
  match out with
  | .reserved _ q k =>
    st.modify fun s => { s with pool := q, poolPeak := max s.poolPeak q.used,
                                budgetDegraded := s.budgetDegraded + (if k > 0 then 1 else 0) }
  | .wait => st.modify fun s => { s with budgetWaits := s.budgetWaits + 1 }
  | .refuse => st.modify fun s => { s with budgetRefused := s.budgetRefused + 1 }
  return out

/-- `b` bytes in MiB, rounded up. -/
def mibOf (b : Nat) : Nat := (b + 1048575) / 1048576

/-- **Reserves an output of `bytes`** (task 12.3b: Save, XFDF export, `Budget.Op.output`) in
the work pool: its ticket, or why not — larger than the whole pool (refused), or the work in
flight leaves too little now. -/
def reserveOutput (st : IO.Ref State) (bytes : Nat) : IO (Except String Budget.Ticket) := do
  match ← admit st (.output bytes) with
  | .reserved t _ _ => return .ok t
  | .refuse =>
    return .error s!"it needs about {mibOf bytes} MiB in memory, more than the viewer's \
      {mibOf (← st.get).pool.ceiling} MiB budget for work in flight"
  | .wait =>
    let p := (← st.get).pool
    return .error s!"it needs about {mibOf bytes} MiB in memory and the pages being rendered \
      hold {mibOf p.used} of the viewer's {mibOf p.ceiling} MiB budget for work in flight; \
      try again when they are done"

/-- Runs `k` with an output of `bytes` reserved (`reserveOutput`), released afterwards
whatever happens; `refused` with the reason when it cannot be reserved. -/
def withOutput {α : Type} (st : IO.Ref State) (bytes : Nat) (refused : String → IO α)
    (k : IO α) : IO α := do
  match ← reserveOutput st bytes with
  | .error m => refused m
  | .ok t =>
    try k finally releaseTicket st (some t)

/-- The pixel size of the render `key` of `doc` (the renderer crops at `Limits.maxPageSide`). -/
def keyPixels (doc : Doc) (key : View.Key) : Nat × Nat :=
  match doc.pages[key.page]? with
  | some page =>
    let (w, h) := View.pixelSize key.zoom (rotAdd page.rotate key.rot) (Box.ofRect page.cropBox)
    (min w limits.maxPageSide, min h limits.maxPageSide)
  | none => (0, 0)

/-- The reservation of a text or links request: reserved at once, or (`optional`) `none` when
the pool says wait; otherwise the GUI waits for text requests in flight to answer (they release
their reservations) and asks again. Images leave `Budget.Ceilings.textReserve` to text, so only
text requests can make text wait; should none be in flight, the request goes without a
reservation and is counted (`budgetUnreserved`, expected 0). -/
def textTicket (st : IO.Ref State) (optional : Bool) : IO (Option (Option Budget.Ticket)) := do
  for _ in [0:64] do
    match ← admit st .text with
    | .reserved t _ _ => return some (some t)
    | .refuse => break
    | .wait =>
      if optional then return none
      let s ← st.get
      let busy := (s.textJobs ++ s.linkJobs).filter (·.ticket.isSome)
      let some j := busy[0]? | break
      discard <| IO.wait j.task
  st.modify fun s => { s with budgetUnreserved := s.budgetUnreserved + 1 }
  return some none

/-- The worker request of page `p`'s text index (`links := false`) or links: the one queued for
the current generation, raised to `prio` when that is more urgent, else a new one with priority
`prio`, which first reserves its bytes in the pool (task 12.3, `textTicket`; `optional`: give
up, `none`, rather than wait for the pool). Requests of other generations are cancelled and
forgotten (their reservations released). -/
def sideJob (st : IO.Ref State) (ses : Worker.Session) (src : Nat) (links : Bool) (p prio : Nat)
    (optional : Bool := false) : IO (Option SideJob) := do
  let s ← st.get
  let jobs := if links then s.linkJobs else s.textJobs
  let (old, cur) := jobs.partition (·.gen != s.gen)
  for j in old do
    ses.cancel j.id
    releaseTicket st j.ticket
  let set (js : Array SideJob) (s : State) : State :=
    if links then { s with linkJobs := js } else { s with textJobs := js }
  match cur.find? (·.page == p) with
  | some j =>
    ses.raise j.id prio
    st.modify (set cur)
    return some j
  | none =>
    st.modify (set cur)
    let some ticket ← textTicket st optional | return none
    let req := if links then Worker.Protocol.Request.viewLinks p else .pageIndex p s.oc
    let (id, task) ← ses.submit src req prio
    let j : SideJob := ⟨p, s.gen, id, task, ticket⟩
    st.modify fun s => set ((if links then s.linkJobs else s.textJobs).push j) s
    return some j

/-- Takes the answered request `j` out of the queued text or links requests. -/
def dropSideJob (st : IO.Ref State) (links : Bool) (j : SideJob) : IO Unit := do
  let s ← st.get
  let held := ((if links then s.linkJobs else s.textJobs).find? (·.id == j.id)).bind (·.ticket)
  releaseTicket st held
  st.modify fun s => if links then { s with linkJobs := s.linkJobs.filter (·.id != j.id) }
    else { s with textJobs := s.textJobs.filter (·.id != j.id) }

/-- Shown while a page's text index is still with the worker (`pageIndex … (wait := false)`). -/
def pendingText : String := "the page text is being read"

/-- A page's text index from the worker's reply (task 12.2d): the cells, line directions and
hidden flags it sent, with the normalised search text computed here (`Select.normChars`); an
error text for a failed request; `none` when the request was cancelled (not cached). -/
def indexOfReply : Worker.Reply → Option (Except String Select.PageIndex)
  | .response (.pageIndex cs ds hs) _ =>
    if hs.length != cs.length then
      some (.error "the document worker sent a malformed text index")
    else
      let cells := (cs.map fun c =>
        ({ text := c.text, sep := c.sep, box := c.box, line := c.line } : Select.Cell)).toArray
      some (.ok (Select.PageIndex.ofCells cells ds.toArray hs.toArray))
  | .response (.error _ m) _ => some (.error m)
  | .response _ _ => some (.error "the document worker answered with another message")
  | .failed e => some (.error s!"the document worker stopped: {failText e}")
  | .cancelled => none

/-! ## Text index and highlights (task 8.2c) -/

/-- The text index of page `p`: extracted on first use (`Annot.extractDocPageAnnots` with a
fresh budget, as the text view and the renderer) and cached for the open document. Content
hidden by the layers' state (`State.oc`, task 9.r11b) is not in it, so it can be neither
selected nor found. Task 12.2d: with a document worker (`workerForText`) the worker extracts it
(`Worker.Protocol.Request.pageIndex`, the same calls under the same layers state) and this
process only waits for the reply — with `wait := false` (pointer motion) it does not wait and
gives `pendingText` until the reply is there. A request that failed (the worker stopped, the
deadline passed) is cached as an error: the page's text is then never parsed in this process. -/
def pageIndex (st : IO.Ref State) (p : Nat) (wait : Bool := true) :
    IO (Except String Select.PageIndex) := do
  let s ← st.get
  let some doc := s.doc | return .error "no document"
  match s.texts[p]? with
  | some (some r) => return r
  | _ =>
    let some page := doc.pages[p]? | return .error "page index out of range"
    if let some (ses, src) ← workerForText st doc then
      let some j ← sideJob st ses src false p (if wait then 0 else 1)
        | return .error "the page text request was not made"
      if !wait && !(← IO.hasFinished j.task) then return .error pendingText
      let reply ← IO.wait j.task
      dropSideJob st false j
      match indexOfReply reply with
      | none => return .error "the page text request was cancelled"
      | some r =>
        st.modify fun s =>
          if s.gen == j.gen then { s with texts := s.texts.modify p (fun _ => some r),
                                          workerTexts := s.workerTexts + 1 } else s
        return r
    let r ← IO.lazyPure fun _ =>
      match (SafePdf.Core.Annot.extractDocPageAnnots limits doc page
          (SafePdf.Core.Filter.Budget.init limits) (oc := s.oc)).1 with
      | .ok pt => .ok (Select.PageIndex.ofText pt)
      | .error e => .error (renderError e)
    let gen := s.gen
    st.modify fun s =>
      if s.gen == gen then { s with texts := s.texts.modify p (fun _ => some r) } else s
    return r

/-- Box of the shown page (CropBox), when a page is shown. -/
def shownBox (s : State) : Option Box := do
  let doc ← s.doc
  let page ← doc.pages[s.page]?
  if s.shown.isNone || !(0 < s.shownZoom) then none
  some (Box.ofRect page.cropBox)

/-- Canvas rectangle `(x0, y0, x1, y1)` of a page-space box on the shown image. -/
def canvasRect (s : State) (bx : Box) (b : Box) : Rat × Rat × Rat × Rat :=
  let p0 := toScreen s.shownZoom s.shownRot bx ⟨b.llx, b.lly⟩
  let p1 := toScreen s.shownZoom s.shownRot bx ⟨b.urx, b.ury⟩
  (min p0.x p1.x + s.imgX, min p0.y p1.y + s.imgY, max p0.x p1.x + s.imgX,
   max p0.y p1.y + s.imgY)

/-- `canvasRect` as a `Bubble.Rect` (the current page). -/
def canvasR (s : State) (bx b : Box) : Bubble.Rect :=
  let (x0, y0, x1, y1) := canvasRect s bx b
  ⟨x0, y0, x1, y1⟩

/-- The two numbers of an `xview`/`yview` result. -/
def viewFracs (s : String) : Option (Rat × Rat) :=
  match (s.splitOn " ").filter (!·.isEmpty) with
  | [a, b] => do return (← View.parseDecimal a, ← View.parseDecimal b)
  | _ => none

/-- Canvas coordinates of window position `(wx, wy)`. -/
def canvasPos (wx wy : Int) : IO (Option (Rat × Rat)) := do
  let cx ← run [".c", "canvasx", toString wx]
  let cy ← run [".c", "canvasy", toString wy]
  return match View.parseDecimal cx, View.parseDecimal cy with
    | some x, some y => some (x, y)
    | _, _ => none

/-- The page under window position `(wx, wy)` (the one whose image contains it, else the
nearest, `View.pageAt`; task 9.3) and the page point there (`Geom.toPage`, C2). -/
def pagePointAt (st : IO.Ref State) (wx wy : Int) : IO (Option (Nat × Pt)) := do
  let s ← st.get
  if s.shown.isNone then return none
  let some (cx, cy) ← canvasPos wx wy | return none
  let some p := View.pageAt s.places cx.floor.toNat cy.floor.toNat | return none
  let some sl := slotOf s p | return none
  return some (p, sl.toPage cx cy)

/-- The point of page `p` at window position `(wx, wy)`, also outside its image (a drag that
started on `p`). -/
def pagePointOn (st : IO.Ref State) (p : Nat) (wx wy : Int) : IO (Option Pt) := do
  let s ← st.get
  if s.shown.isNone then return none
  let some sl := slotOf s p | return none
  let some (cx, cy) ← canvasPos wx wy | return none
  return some (sl.toPage cx cy)

/-- The marks of page `p` that are drawn: all of them, or only the notes while "Show all" is
off (task 9.8). -/
def visibleMarks (s : State) (p : Nat) : List Marks.Mark :=
  let ms := s.marks.onPage p
  if s.ui.showAll then ms else ms.filter (!·.isHighlight)

/-- The visible marks of page `p` the viewer draws itself: not the saved ones, which are in the
file and drawn by the renderer from their appearance streams (task 9.5c; after an edit, from
the preview `State.view`, task 9.5g). A comment's icon is a canvas item (`drawMarks`): the
popup form written for it has no appearance of its own. -/
def drawnMarks (s : State) (p : Nat) : List Marks.Mark :=
  (visibleMarks s p).filter (!s.marks.isSaved ·.id)

/-- Whether the renderer can paint a saved free text (task 9.r5): its appearance stream uses
the non-embedded standard-14 Helvetica (rule A13), which the renderer paints only with a
substitute program (`Shell.Fonts.findFiles`, task 7.7). Without one — e.g. macOS without
Ghostscript's or TeX Gyre's fonts — the appearance draws nothing, so `drawMarks` draws saved
free text on the canvas like unsaved free text (else it stayed invisible until a double click
opened its text box). -/
def State.paintsHelvetica (s : State) : Bool :=
  (s.subst.get? SafePdf.Core.Font.Std14.helvetica).isSome

/-- `Slot.rect` as a `Bubble.Rect`. -/
def Slot.rectR (sl : Slot) (b : Box) : Bubble.Rect :=
  let (x0, y0, x1, y1) := sl.rect b
  ⟨x0, y0, x1, y1⟩

/-- The Tk font of free text at font size `size` on a page drawn at `zoom` (Helvetica, the size
in pixels). -/
def ftFont (size : Nat) (zoom : Rat) : String :=
  s!"Helvetica -{max 1 (((size : Rat) * zoom + 1 / 2).floor.toNat)}"

/-- The stipple that approximates an opacity in percent on the canvas (Tk has no alpha). -/
def stippleOf (o : Nat) : List String :=
  if o ≥ 88 then [] else if o ≥ 63 then ["-stipple", "gray75"]
  else if o ≥ 38 then ["-stipple", "gray50"] else ["-stipple", "gray25"]

/-- Draws an unsaved free text (one canvas text item per line, first baseline `ftPad` + size
below the top as the appearance stream Save writes) or drawing (a line per stroke, a dot for a
one-point stroke) on the page of slot `sl` (task 9.9). -/
def drawEditorMark (s : State) (sl : Slot) (m : Marks.Mark) (tags : String) : IO Unit := do
  let at' (q : Pt) : Rat × Rat := let (x, y, _, _) := sl.rect ⟨q.x, q.y, q.x, q.y⟩; (x, y)
  match m.kind with
  | .freeText t p sz c =>
    let font := ftFont sz sl.vp.zoom
    let asc : Nat := ((← run ["font", "metrics", font, "-ascent"]).toNat?).getD 0
    let lines := t.splitOn "\n"
    let lf := SafePdf.Core.Write.Annots.lineFactor
    let pad := SafePdf.Core.Write.Annots.ftPad
    -- Task 9.r5: the line's top-left corner (baseline + ascent, in page space) through the
    -- page transform, and the text turned with the page (Tk's `-angle` is counter-clockwise
    -- and turns about the anchor), so it also sits right on a rotated page.
    let ascPage : Rat := (asc : Rat) / (if sl.vp.zoom > 0 then sl.vp.zoom else 1)
    let angle : String := match sl.vp.rot with
      | .r0 => "0" | .r90 => "270" | .r180 => "180" | .r270 => "90"
    for (l, i) in lines.zip (List.range lines.length) do
      let (x, y) := at' ⟨p.x + pad, p.y - pad - (sz : Rat) - (i : Rat) * lf * (sz : Rat) + ascPage⟩
      discard <| run [".c", "create", "text", num x, num y, "-anchor", "nw", "-angle", angle,
        "-text", l, "-font", font, "-fill", Marks.rgbHex c, "-tags", s!"{tags} ft"]
  | .ink ss w o c =>
    let wpx := max 1 ((w : Rat) * sl.vp.zoom)
    let stip := if s.stipple then stippleOf o else []
    for st in ss do
      match st with
      | [q] =>
        let (x, y) := at' q
        discard <| run ([".c", "create", "oval", num (x - wpx / 2), num (y - wpx / 2),
          num (x + wpx / 2), num (y + wpx / 2), "-fill", Marks.rgbHex c, "-outline", ""] ++ stip ++
          ["-tags", s!"{tags} ink"])
      | _ =>
        let coords := st.flatMap fun q => let (x, y) := at' q; [num x, num y]
        discard <| run ([".c", "create", "line"] ++ coords ++ ["-width", num wpx, "-fill",
          Marks.rgbHex c, "-capstyle", "round", "-joinstyle", "round"] ++ stip ++
          ["-tags", s!"{tags} ink"])
  | _ => pure ()

/-- Draws the canvas items of the marks of the page of slot `sl` (tag `mark`, task 9.4): note
icons (`::safepdf::noteIcon`, tag `note` and `mID`), the dashed quads a note is anchored to,
and the outline of the selected mark (tag `marksel`). Highlight fills are pixels
(`showPhoto`). -/
def drawMarks (s : State) (sl : Slot) : IO Unit := do
  let bx := sl.vp.box
  for m in visibleMarks s sl.place.page do
    let tags := s!"mark m{m.id}"
    if m.isNote then
      for q in m.quads do
        let (x0, y0, x1, y1) := sl.rect q
        discard <| run [".c", "create", "rectangle", toString x0.floor, toString y0.floor,
          toString x1.ceil, toString y1.ceil, "-outline", "#c99a00", "-dash", "4 2",
          "-width", "1", "-tags", tags]
      if let some ib := (if s.marks.isSaved m.id && !s.marks.isComment m then none
          else m.iconBox bx) then
        let (x0, y0, x1, y1) := sl.rect ib
        discard <| run ["::safepdf::noteIcon", ".c", toString x0.floor, toString y0.floor,
          toString x1.ceil, toString y1.ceil, m.color.hex, s!"{tags} note"]
    if (!s.marks.isSaved m.id || (m.isFreeText && !s.paintsHelvetica)) &&
        (s.ftEdit.bind (·.id)) != some m.id then
      drawEditorMark s sl m tags
    if s.markSel == some m.id then
      let boxes := if m.isNote then (m.iconBox bx).toList
        else if m.isEditor then m.box.toList else m.quads
      for q in boxes do
        let (x0, y0, x1, y1) := sl.rect q
        discard <| run [".c", "create", "rectangle", toString (x0.floor - 2),
          toString (y0.floor - 2), toString (x1.ceil + 2), toString (y1.ceil + 2),
          "-outline", "#0060df", "-width", "2", "-tags", s!"{tags} marksel"]

/-- Draws the bubble (canvas items tagged `bub`, task 9.8; `Bubble`): after a text selection
(not while dragging) the float bubble with the Highlight and Add comment buttons (task 9.r4;
each button with a hover tooltip, `Bubble.Btn.tip`), on a selected highlight the
edit bubble (colour swatch and chevron, Comment, Delete) and, when open, its colour picker.
Placed by `Bubble.place` in canvas coordinates inside the scroll region, on the page of the
selection or the mark (task 9.3: any laid-out page), so it scrolls with the page; every redraw
(zoom, rotation, page change) places it again. Records what is drawn in `State.bubble` /
`State.pickerAt` for the clicks. -/
def drawBubble (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let selRects ← match s.sel with
    | some (p, a, b) =>
      match slotOf s p with
      | some sl =>
        if s.pressPt.isNone then
          match ← pageIndex st p with
          | .ok ix => pure ((Select.rangeBoxes ix.cells a b).map sl.rectR)
          | .error _ => pure []
        else pure []
      | none => pure []
    | none => pure []
  let mark := (s.markSel.bind s.marks.find?).filter (·.isHighlight)
  let markRects := (mark.bind fun m => (slotOf s m.page).map fun sl => m.quads.map sl.rectR).getD []
  let area : Bubble.Rect := ⟨0, 0, (s.regionW : Rat), (s.regionH : Rat)⟩
  -- A selected free text or drawing gets the editor bubble with Delete (task 9.9).
  let edRects := ((s.markSel.bind s.marks.find?).filter (·.isEditor)).bind (fun m =>
    (slotOf s m.page).bind fun sl => m.box.map fun b => [sl.rectR b]) |>.getD []
  let placed := if selRects.isEmpty && !edRects.isEmpty && s.ftEdit.isNone &&
      s.inkStroke.isNone then
      (Bubble.place edRects Bubble.Kind.editor.width Bubble.height area).map (.editor, ·)
    else (Bubble.kindFor (!selRects.isEmpty) (!markRects.isEmpty) s.ui).bind fun k =>
      (Bubble.place (if k == .float then selRects else markRects) k.width Bubble.height area).map
        (k, ·)
  let picker := match placed with
    | some (.edit, r) => if s.ui.picker then some (Bubble.pickerRect r area) else none
    | _ => none
  st.modify ({ · with bubble := placed, pickerAt := picker })
  let some (k, r) := placed | return
  let cy := (r.y0 + r.y1) / 2
  discard <| run ["::safepdf::bubBox", ".c", num r.x0, num r.y0, num r.x1, num r.y1,
    num (Bubble.height / 2), "bub"]
  for d in k.dividers do
    discard <| run ["::safepdf::bubDivider", ".c", num (r.x0 + d), num (r.y0 + 1),
      num (r.y1 - 1), "bub"]
  for (b, x0, x1) in k.layout do
    let tags := s!"bub b:{b.name}"
    let cx := r.x0 + (x0 + x1) / 2
    -- The button's area (white, under its icon) carries the hover tooltip (task 9.r4).
    discard <| run [".c", "create", "rectangle", num (r.x0 + x0), num (r.y0 + Bubble.pad),
      num (r.x0 + x1), num (r.y1 - Bubble.pad), "-fill", "white", "-outline", "", "-tags", tags]
    discard <| run [".c", "bind", s!"b:{b.name}", "<Enter>",
      s!"::safepdf::bubTip b:{b.name} \{{b.tip}}"]
    discard <| run [".c", "bind", s!"b:{b.name}", "<Leave>", "::safepdf::bubTipHide"]
    match b with
    | .color =>
      let hex := (mark.map (·.color.hex)).getD s.hlColor.hex
      discard <| run ["::safepdf::bubColor", ".c", num (r.x0 + x0), num cy, hex,
        if s.ui.picker then "1" else "0", tags]
    | .highlight => discard <| run ["::safepdf::bubIcon", ".c", "highlight", num cx, num cy, tags]
    | .comment => discard <| run ["::safepdf::bubIcon", ".c", "comment", num cx, num cy, tags]
    | .delete => discard <| run ["::safepdf::bubIcon", ".c", "trash", num cx, num cy, tags]
  if let some pr := picker then
    discard <| run ["::safepdf::bubBox", ".c", num pr.x0, num pr.y0, num pr.x1, num pr.y1, "6",
      "bub picker"]
    for (c, x, y) in Bubble.pickerSwatches pr do
      let cur := mark.any (·.color == c)
      discard <| run ["::safepdf::swatch", ".c", num x, num y, num Bubble.swatch, c.hex,
        if cur then "1" else "0", s!"bub picker c:{c.name}"]

/-- How the overlays of one kind are filled (task 10.10): the colour as six hex digits, the
alpha (0–255) of the translucent fill on Aqua and the X11 stipple fill's colour. -/
structure Tint where
  /-- Colour, six hex digits (no `#`). -/
  rgb : String
  /-- Opacity of the Aqua fill, 0–255. -/
  alpha : Nat
  deriving Repr, BEq

/-- The selection: macOS's accent blue at 35 % (over white ≈ `#b9cefa`). -/
def Tint.sel : Tint := ⟨"3874f2", 90⟩
/-- A search hit: yellow at 50 %. -/
def Tint.hit : Tint := ⟨"ffff00", 128⟩
/-- The current search hit: orange at 50 %. -/
def Tint.cur : Tint := ⟨"ffa500", 128⟩

/-- Two lower-case hex digits of `n mod 256`. -/
def hex2 (n : Nat) : String :=
  let d (k : Nat) : Char := "0123456789abcdef".toList.getD k '0'
  String.ofList [d (n % 256 / 16), d (n % 16)]

/-- The alpha suffix `::safepdf::tint` takes (two hex digits; Tk's `#RRGGBBAA`). -/
def Tint.alphaHex (t : Tint) : String := hex2 (min 255 t.alpha)

/-- The `-fill` colour of the X11 stipple fill. -/
def Tint.fill (t : Tint) : String := "#" ++ t.rgb

/-- Composite of a fill channel `f` at alpha `a` over a page channel `p` (what the canvas
shows; the smoke test's expectation). -/
def Tint.over (a f p : Nat) : Nat := (f * a + p * (255 - a) + 127) / 255

#guard Tint.sel.alphaHex == "5a" && Tint.hit.alphaHex == "80" && hex2 0 == "00" && hex2 255 == "ff"
#guard Tint.sel.fill == "#3874f2"
-- Over white the selection is a light blue; over black ink the ink stays dark.
#guard (Tint.over 90 0x38 255, Tint.over 90 0x74 255, Tint.over 90 0xf2 255) == (185, 206, 250)
#guard Tint.over 90 0xf2 0 < 90

/-- The slots that get overlays: the pages with a photo and the current page (task 9.3). -/
def overlaySlots (s : State) : List Slot :=
  s.slots.toList.filter fun sl => sl.place.page == s.page || s.hasPhoto sl.place.page

/-- Redraws the overlays of the pages on screen (`overlaySlots`): the marks' canvas items
(`drawMarks`), all search hits (tag `hit`, the current one in orange), the selection (tag
`sel`) and the bubble (tag `bub`, `drawBubble`), in that stacking order. Hits are `Tint`
fills: stippled rectangles on X11, translucent photos on Aqua (task 10.10; photos no item shows
any more are deleted, `::safepdf::tintGc`). The selection is a translucent photo band per line
on both platforms (`Select.PageIndex.bands`, task 10.18). -/
def drawOverlay (st : IO.Ref State) : IO Unit := do
  discard <| run [".c", "delete", "sel", "hit", "mark", "bub"]
  st.modify ({ · with bubble := none, pickerAt := none })
  let s ← st.get
  if s.shown.isNone then return
  let slots := overlaySlots s
  for sl in slots do drawMarks s sl
  -- X11: a stippled rectangle; Aqua (no stipples): a translucent photo (task 10.10).
  let rect (sl : Slot) (b : Box) (t : Tint) (tag : String) : IO Unit := do
    let (x0, y0, x1, y1) := sl.rect b
    let c := [toString x0.floor, toString y0.floor, toString x1.ceil, toString y1.ceil]
    if s.stipple then
      discard <| run ([".c", "create", "rectangle"] ++ c ++
        ["-fill", t.fill, "-stipple", "gray50", "-outline", "", "-tags", tag])
    else discard <| run (["::safepdf::tint", ".c"] ++ c ++ [t.rgb, t.alphaHex, tag])
  if !s.query.isEmpty then
    for sl in slots do
      let pg := sl.place.page
      if let .ok ix ← pageIndex st pg then
        let hits := ix.hits s.query
        for i in [0:hits.size] do
          if let some (a, b) := hits[i]? then
            let t := if s.hit == some (pg, i) then Tint.cur else Tint.hit
            for b in Select.rangeBoxes ix.cells a b do rect sl b t "hit"
  -- The selection: one translucent band per line on both platforms (task 10.18,
  -- `Select.selBands`), edges rounded to the nearest pixel so that joined bands share a pixel
  -- edge (no gap, no doubly tinted overlap).
  if let some (p, a, b) := s.sel then
    if let some sl := slotOf s p then
      if let .ok ix ← pageIndex st p then
        for b in ix.bands a b do
          let (x0, y0, x1, y1) := sl.rect b
          let r (v : Rat) : String := toString (v + 1 / 2).floor
          discard <| run (["::safepdf::tint", ".c", r x0, r y0, r x1, r y1] ++
            [Tint.sel.rgb, Tint.sel.alphaHex, "sel"])
  discard <| run ["::safepdf::tintGc"]
  -- The free-text editor follows zoom, rotation and scrolling (task 9.9).
  if let some fe := s.ftEdit then
    if let some sl := slotOf s fe.page then
      let pad := SafePdf.Core.Write.Annots.ftPad
      let (x, y, _, _) := sl.rect ⟨fe.pos.x + pad, fe.pos.y - pad, fe.pos.x + pad, fe.pos.y - pad⟩
      discard <| run [".c", "coords", "ftedit", num x, num y]
      discard <| run ["::safepdf::ftConf",
        toString ((max 1 (((fe.size : Rat) * sl.vp.zoom + 1 / 2).floor.toNat))),
        Marks.rgbHex fe.rgb]
  drawBubble st

/-! ## Rendering -/

/-- Renders page `p` of `doc` at `zoom` and user rotation `rot` with a fresh budget (the
inspector's `raster` view does the same), under the optional content state `oc` (task 9.r11b;
`none`: the document's default). -/
def renderPageP (doc : Doc) (p : Nat) (zoom : Rat) (rot : SafePdf.Core.Doc.Rotation)
    (subst : SafePdf.Core.Raster.Subst.SubstFonts := {})
    (oc : Option Core.Doc.OptionalContent.State := none) :
    IO (Except Error SafePdf.Core.Raster.Glyph.PageRender) := do
  match doc.pages[p]? with
  | some page =>
    IO.lazyPure fun _ =>
      (SafePdf.Core.Raster.Glyph.renderDocPagePartial limits doc page zoom rot
        (SafePdf.Core.Filter.Budget.init limits) (subst := subst) (oc := oc)).1
  | none => return .error (.malformed 0 "page index out of range")

/-- Task 13.4d: `renderPageP`'s image (task 12.2c's worker-equal call), a partial page included. -/
def renderPage (doc : Doc) (p : Nat) (zoom : Rat) (rot : SafePdf.Core.Doc.Rotation)
    (subst : SafePdf.Core.Raster.Subst.SubstFonts := {})
    (oc : Option Core.Doc.OptionalContent.State := none) :
    IO (Except Error Clip.Image) := do
  return (← renderPageP doc p zoom rot subst oc).map (·.image)

/-- The cache key of the page in slot `sl`. -/
def keyOf (s : State) (sl : Slot) : View.Key :=
  ⟨s.gen, sl.place.page, sl.vp.zoom, s.rot⟩

/-- The cached render result for `key` (and marks it used). -/
def cached (st : IO.Ref State) (key : View.Key) : IO (Option (Except Error Clip.Image)) := do
  let (hit, cache) := (← st.get).cache.find? key
  st.modify ({ · with cache })
  return hit


/-- Starts rendering `key`: queued for the document worker with priority `prio` when it can
render it (`workerFor`), else on a dedicated thread in this process (task 8.8: the task only
runs the pure renderer on the document (`State.view`, else `doc`) and the substitute fonts; it
never touches Tk or the state). Returns the task and the worker request id. -/
def renderTask (st : IO.Ref State) (doc : Doc) (key : View.Key) (prio : Nat) :
    IO (Task RenderOut × Task Bool × Option Nat) := do
  if let some (ses, src) ← workerFor st doc then
    let (id, t) ← ses.submit src
      (.render key.page key.zoom (Worker.rotationToNat key.rot) (← st.get).oc) prio
    return (t.map (sync := true) (outOfReply ses.cfg.deadlineMs),
      t.map (sync := true) incompleteOfReply, some id)
  let s ← st.get
  let d := s.view.getD doc
  let subst := s.subst
  let oc := s.oc
  let task ← IO.asTask (prio := .dedicated) do
    let t0 ← IO.monoNanosNow
    let r ← renderPageP d key.page key.zoom key.rot subst oc
    let t1 ← IO.monoNanosNow
    return (r, t1 - t0)
  let out : Except IO.Error (Except Error SafePdf.Core.Raster.Glyph.PageRender × Nat) → RenderOut
    | .ok (r, ns) => some (r.map (·.image), ns)
    | .error e => some (.error (.malformed 0 s!"render failed: {e}"), 0)
  let inc : Except IO.Error (Except Error SafePdf.Core.Raster.Glyph.PageRender × Nat) → Bool
    | .ok (.ok r, _) => r.exceeded
    | _ => false
  return (task.map (sync := true) out, task.map (sync := true) inc, none)

/-- Starts rendering `key` (`renderTask`, priority `prio`: 0 for the page that must be shown
now), unless a render of it is already running. -/
def submit (st : IO.Ref State) (doc : Doc) (key : View.Key) (prio : Nat := 1) : IO Unit := do
  let s ← st.get
  if s.jobs.any (·.key == key) then return
  -- Task 12.3: the image's bytes are reserved before dispatch; without room the page waits
  -- (`poll` asks again after a release); an image larger than the pool is refused.
  let (w, h) := keyPixels doc key
  let ticket ← match ← admit st (.page w h) with
    | .reserved t _ _ => pure t
    | .wait =>
      st.modify ({ · with budgetWait := true })
      return
    | .refuse =>
      st.modify fun s => { s with cache := s.cache.insert key (.error (.limitExceeded .imagePixels)) }
      return
  let start ← IO.monoNanosNow
  let (task, incomplete, id) ← renderTask st doc key prio
  st.modify fun s => { s with jobs := s.jobs.push { key, start, task, id, ticket := some ticket,
                                                    incomplete } }
  -- Task 12.2d: with the worker, a page in view also gets its links asked for (after the
  -- renders of its priority), so that pointer motion finds them without waiting; the current
  -- page (priority 0) its text index too.
  if id.isSome && prio ≤ 1 then
    if let some (ses, src) ← workerForText st doc then
      let s ← st.get
      if !(s.links[key.page]?.any (·.isSome)) then
        discard <| sideJob st ses src true key.page 1 (optional := true)
      if prio == 0 && !(s.texts[key.page]?.any (·.isSome)) then
        discard <| sideJob st ses src false key.page 1 (optional := true)

/-- Whether a render of `key` is running. -/
def State.running (s : State) (key : View.Key) : Bool :=
  s.jobs.any (·.key == key)

/-- Raises the worker render of `key`, if one is queued, to priority `prio` (task 12.2c: a
neighbour that became the current page). -/
def raiseJob (st : IO.Ref State) (key : View.Key) (prio : Nat) : IO Unit := do
  let s ← st.get
  let some ses := s.worker | return
  for j in s.jobs do
    if j.key == key then
      if let some id := j.id then ses.raise id prio

/-- Takes the finished job `j` out of `jobs` and returns its result and render time; the
result goes into the cache when it is for the open document. A cancelled worker render
(task 12.2c) gives `none` and counts as a dropped stale result. -/
def finish (st : IO.Ref State) (j : Job) : IO RenderOut := do
  releaseTicket st j.ticket
  st.modify fun s => { s with jobs := s.jobs.filter (·.key != j.key) }
  match j.task.get with
  | none =>
    st.modify fun s => { s with staleDropped := s.staleDropped + 1,
                                cancelledRenders := s.cancelledRenders + 1 }
    return none
  | some (r, ns) =>
    if j.key.gen == (← st.get).gen then
      let w := if j.id.isSome then 1 else 0
      -- Task 13.4d: a partial page is a successful page with the flag set (no retry).
      if let .ok _ := r then
        if j.incomplete.get then
          st.modify fun s =>
            let ks := (s.partialKeys.filter (· != j.key)).push j.key
            { s with partialKeys :=
                if ks.size > partialKeysMax then ks.extract (ks.size - partialKeysMax) ks.size
                else ks }
      st.modify fun s => { s with cache := s.cache.insert j.key r, renderNs := s.renderNs + ns,
                                  renders := s.renders + 1, workerRenders := s.workerRenders + w,
                                  workerNs := s.workerNs + w * ns }
    return some (r, ns)

/-- Cancels the worker renders whose result would be dropped (task 12.2c): pages of another
document generation or now laid out at another zoom or rotation, thumbnails of another
generation or rotation. Queued ones are dropped; a running one is killed after
`Worker.SessionConfig.preemptMs`. -/
def cancelStale (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some ses := s.worker | return
  for j in s.jobs do
    if let some id := j.id then
      let stale := j.key.gen != s.gen || (match slotOf s j.key.page with
        | some sl => keyOf s sl != j.key
        | none => false)
      if stale then ses.cancel id
  for j in s.thJobs do
    if let some id := j.id then
      if j.key.gen != s.gen || j.key.rot != s.rot then ses.cancel id

/-! ## Live photos (task 12.3b, `Budget.Pool.admitPhoto`) -/

/-- Releases the photo reservation of Tk image `name`; whether it held one. -/
def photoUnreserve (st : IO.Ref State) (name : String) : IO Bool := do
  match (← st.get).photoTix.find? (·.1 == name) with
  | some (_, t) =>
    st.modify fun s => { s with photoPool := s.photoPool.release t,
                                photoTix := s.photoTix.filter (·.1 != name) }
    return true
  | none => return false

/-- Reserves `bytes` for Tk image `name` in the photo pool (`Budget.Pool.admitPhoto`, after
releasing `name`'s own reservation), evicting from `cands` (photo names, in eviction order)
as needed: the names whose reservations were released for it (the caller deletes those
photos), or `none` when it does not fit (nothing else is released). -/
def photoAdmit (st : IO.Ref State) (name : String) (bytes : Nat) (thumb : Bool)
    (cands : List String) : IO (Option (List String)) := do
  discard <| photoUnreserve st name
  let s ← st.get
  let tix := cands.filterMap fun n => (s.photoTix.find? (·.1 == n)).map (·.2)
  match s.photoPool.admitPhoto Budget.ceilings bytes thumb tix with
  | some (es, t, q) =>
    let names := es.filterMap fun e => (s.photoTix.find? (·.2 == e)).map (·.1)
    let tix := (s.photoTix.filter (fun x => !names.contains x.1)).push (name, t)
    st.modify fun s => { s with photoPool := q, photoTix := tix,
                                photoPeak := max s.photoPeak q.used,
                                photoEvicted := s.photoEvicted + names.length }
    return some names
  | none => return none

-- The kept thumbnails are those `Budget.thumbs_fit_reserve` counts (98 px wide).
#guard Sidebar.thumbBudget ≤ Budget.ceilings.thumbsKept && Sidebar.thumbW == 98

/-- The prefix of the message a page in view shows when its photo was refused. -/
def photoRefusal : String := "not shown"

/-- The pages in view now (`View.visiblePages` of the canvas's view band). -/
def inView (s : State) : IO (List Nat) := do
  let some (a, b) := viewFracs (← run [".c", "yview"]) | return [s.page]
  let px (f : Rat) : Nat := (f * (s.regionH : Rat) + 1 / 2).floor.toNat
  return View.visiblePages s.places (px a) (px b)

/-- Removes page `p`'s photo and its canvas items without asking for the deferred pages
again (`dropPhoto`). -/
def dropPhotoOnly (st : IO.Ref State) (p : Nat) : IO Unit := do
  discard <| run [".c", "delete", s!"w{p}"]
  if (← st.get).hasPhoto p then
    try discard <| run ["image", "delete", photoOf p] catch _ => pure ()
    discard <| run [".c", "delete", s!"p{p}", s!"e{p}"]
    st.modify fun s => { s with photos := s.photos.filter (·.1 != p) }

/-- Removes page `p`'s photo and its canvas items (task 9.3: pages that left the view) and
releases its reservation (task 12.3b). A release may make room: the deferred neighbours and
the pages in view whose photo was refused are asked for again (their refusal messages go). -/
def dropPhoto (st : IO.Ref State) (p : Nat) : IO Unit := do
  dropPhotoOnly st p
  if ← photoUnreserve st (photoOf p) then
    let ds := (← st.get).photoDeferred
    st.modify ({ · with photoDeferred := [] })
    for q in ds do
      if (← st.get).photos.any fun (r, x) => r == q && (match x with
          | .error m => m.startsWith photoRefusal
          | .ok _ => false) then
        dropPhotoOnly st q

/-- Removes every page photo and page item from the canvas (task 9.3) and releases their
reservations. -/
def clearPages (st : IO.Ref State) : IO Unit := do
  for (p, _) in (← st.get).photos do
    try discard <| run ["image", "delete", photoOf p] catch _ => pure ()
    discard <| photoUnreserve st (photoOf p)
  discard <| run [".c", "delete", "pageframe", "pimg", "perr", "pwait", "ppart"]
  st.modify ({ · with photos := #[], photoDeferred := [] })

/-- Draws the layout on the canvas (task 9.3): a white page frame with a 1 px grey border per
slot (tags `pageframe fN`; the placeholder until the page's photo arrives) and the scroll
region. -/
def buildCanvas (st : IO.Ref State) : IO Unit := do
  clearPages st
  let s ← st.get
  for sl in s.slots do
    let pl := sl.place
    discard <| run [".c", "create", "rectangle", toString (pl.x - 1), toString (pl.y - 1),
      toString (pl.x + pl.w), toString (pl.y + pl.h), "-outline", "#c8c8d0", "-fill", "white",
      "-width", "1", "-tags", s!"pageframe f{pl.page}"]
  discard <| run [".c", "configure", "-scrollregion", s!"0 0 {s.regionW} {s.regionH}"]

/-- Shows a render result in slot `sl`: the image (with the page's marks multiplied in,
`Marks.composite`) in the page's photo `::safepdf::pgN` on canvas item `pimg pN`, created
below the overlays; or the error, as text in the page frame (tag `perr eN`). -/
def showPhoto (st : IO.Ref State) (sl : Slot) (res : Except Error Clip.Image) : IO Unit := do
  let p := sl.place.page
  discard <| run [".c", "delete", s!"w{p}"]
  let s ← st.get
  match res with
  | .ok img =>
    -- Task 12.3b: the photo's bytes are reserved in the photo pool first. A page in view may
    -- evict the photos of pages not in view (farthest from the current page first); a
    -- neighbour may not, and waits (deferred) instead; a page in view that still does not fit
    -- shows a message.
    let vis ← inView s
    let visible := p == s.page || vis.contains p
    let dist (q : Nat) : Nat := if q ≥ s.page then q - s.page else s.page - q
    let cands : List Nat := if !visible then [] else
      ((s.photos.toList.map (·.1)).filter fun q => q != p && q != s.page && !vis.contains q)
        |>.mergeSort fun a b => dist a ≥ dist b
    let bytes := Budget.photoBytes img.w img.h
    match ← photoAdmit st (photoOf p) bytes false (cands.map photoOf) with
    | none =>
      st.modify fun s => { s with photoRefused := s.photoRefused + 1,
                                  photoDeferred := p :: s.photoDeferred.filter (· != p) }
      dropPhotoOnly st p
      if visible then
        let pl := sl.place
        let s ← st.get
        let msg := s!"{photoRefusal}: its image ({img.w}x{img.h} px) needs {bytes / 1048576} MiB \
          and the page images in view already hold {s.photoPool.used / 1048576} of the \
          {s.photoPool.ceiling / 1048576} MiB for page images; zoom out or scroll"
        discard <| run [".c", "create", "text", toString (pl.x + pl.w / 2),
          toString (pl.y + pl.h / 2), "-text", s!"page {p + 1}: {msg}", "-width",
          toString (max 40 (pl.w - 20)), "-fill", "#5b5b66", "-justify", "center",
          "-tags", s!"perr e{p}"]
        discard <| run [".c", "lower", s!"e{p}"]
        discard <| run [".c", "lower", "pageframe"]
        st.modify fun s => { s with photos := s.photos.push (p, .error msg) }
      return
    | some evicted =>
      for q in cands do
        if evicted.contains (photoOf q) then dropPhotoOnly st q
    let s ← st.get
    if !s.hasPhoto p then
      discard <| run ["image", "create", "photo", photoOf p]
      discard <| run [".c", "create", "image", toString sl.place.x, toString sl.place.y,
        "-anchor", "nw", "-image", photoOf p, "-tags", s!"pimg p{p}"]
      discard <| run [".c", "lower", s!"p{p}"]
      discard <| run [".c", "lower", "pageframe"]
    Shim.photoPut (photoOf p) img.w.toUInt32 img.h.toUInt32
      (Marks.composite sl.vp.zoom sl.vp.rot sl.vp.box img.w img.h img.data (drawnMarks s p))
    -- Task 13.4d: a partial page carries a small note in its top-left corner (tags `ppart eN`,
    -- removed with the photo); the status line says the same (`showStatus`).
    discard <| run [".c", "delete", s!"e{p}"]
    if s.partialKeys.contains (keyOf s sl) then
      discard <| run [".c", "create", "text", toString (sl.place.x + 6), toString (sl.place.y + 4),
        "-anchor", "nw", "-text", partialText, "-fill", "#9a3412", "-font", "::safepdf::fBar",
        "-tags", s!"ppart e{p}"]
    st.modify fun s => { s with photos := (s.photos.filter (·.1 != p)).push (p, .ok img) }
  | .error e =>
    dropPhoto st p
    let pl := sl.place
    discard <| run [".c", "create", "text", toString (pl.x + pl.w / 2), toString (pl.y + pl.h / 2),
      "-text", s!"page {p + 1}: cannot render: {pageErr e}", "-width",
      toString (max 40 (pl.w - 20)), "-fill", "#5b5b66", "-justify", "center",
      "-tags", s!"perr e{p}"]
    discard <| run [".c", "lower", s!"e{p}"]
    discard <| run [".c", "lower", "pageframe"]
    st.modify fun s => { s with photos := (s.photos.filter (·.1 != p)).push (p, .error (pageErr e)) }

/-- The placeholder of a page whose render is pending (task 8.8, after PDF.js's loading
state): its white frame (`buildCanvas`) with a small grey "Rendering…" in the middle (tag
`pwait wN`, removed by `showPhoto`). -/
def showWaiting (sl : Slot) : IO Unit := do
  let pl := sl.place
  if (← run [".c", "find", "withtag", s!"w{pl.page}"]).isEmpty then
    discard <| run [".c", "create", "text", toString (pl.x + pl.w / 2), toString (pl.y + pl.h / 2),
      "-text", "Rendering…", "-fill", "#5b5b66", "-font", "::safepdf::fBar",
      "-tags", s!"pwait w{pl.page}"]
    discard <| run [".c", "lower", s!"w{pl.page}"]
    discard <| run [".c", "lower", "pageframe"]

/-- Makes `sl` the current page's slot: `shown` and the mirrored position, zoom and rotation
(`imgX`, `imgY`, `shownZoom`, `shownRot`). -/
def setMirror (st : IO.Ref State) (sl : Slot) : IO Unit :=
  st.modify fun s =>
    let k : View.Key := ⟨s.gen, sl.place.page, sl.vp.zoom, s.rot⟩
    { s with shown := some k, imgX := sl.place.x, imgY := sl.place.y, shownZoom := sl.vp.zoom,
             shownRot := sl.vp.rot }

/-- The status line for the current page: file, page, zoom, rotation, image size, `how` it
was obtained (render time, "from cache", "rendering…"), notes (zoom limited, cropped), the
view mode (task 9.3); or the page's render error. -/
def showStatus (st : IO.Ref State) (how : String) : IO Unit := do
  let s ← st.get
  let some path := s.path | return
  let some sl := slotOf s s.page | return
  let vp := sl.vp
  let page := Links.pageText s.labels s.page s.pageCount
  let r : Option (Except String Clip.Image) := (s.photos.find? (·.1 == s.page)).map (·.2)
  match r with
  | some (.error e) => setStatus s!"{path}: {page}: cannot render: {e}"
  | r =>
    let (w, h) := match r with
      | some (.ok img) => (img.w, img.h)
      | _ => (sl.place.w, sl.place.h)
    let how := if r.isSome then how else "rendering..."
    let pct := match s.zoomSel.mode with
      | some (.scale p) => if vp.capped then View.zoomPct vp.zoom s.scaling else p
      | _ => View.zoomPct vp.zoom s.scaling
    let notes := (if s.partialKeys.contains (keyOf s sl) then s!"; {partialText}" else "") ++
      (if vp.capped then
        s!"; zoom limited to {Budget.ceilings.pagePixels / 1048576} Mpx per page" else "") ++
      (if vp.cropped then s!"; cropped to {limits.maxPageSide} px per side" else "")
    setStatus s!"{path}: {page}, {pct}% ({modeName s.zoomSel}), \
      rotation {View.rotDeg s.rot}, {w}x{h} px, {how}{notes}{modeNote s}{s.openNote}"

/-- Shows the current page in the toolbar's page field (`Toolbar.entryText`: the number, or
the label when the document has labels) and the "of N" label next to it (task 9.7). -/
def showPageField (s : State) : IO Unit := do
  discard <| run ["::safepdf::setPage", Toolbar.entryText s.labels s.page,
    Toolbar.ofText s.labels s.page s.pageCount, "1"]

/-- Makes `p` the current page without moving the view (task 9.3: the page under the window
centre while scrolling in the vertical modes): title, page field, status line. -/
def setCurrent (st : IO.Ref State) (p : Nat) : IO Unit := do
  let s ← st.get
  let some sl := slotOf s p | return
  st.modify ({ · with page := p, hover := none })
  setMirror st sl
  let s ← st.get
  discard <| run ["wm", "title", ".", s.title]
  st.modify ({ · with titleShown := s.title })
  showPageField s
  showStatus st "shown"

/-- The visible band of the view: top, bottom, left and right in scroll-region pixels. -/
def viewBand (s : State) : IO (Option (Nat × Nat × Nat × Nat)) := do
  let some (a, b) := viewFracs (← run [".c", "yview"]) | return none
  let some (xa, xb) := viewFracs (← run [".c", "xview"]) | return none
  let px (f : Rat) (r : Nat) : Nat := (f * (r : Rat) + 1 / 2).floor.toNat
  return some (px a s.regionH, px b s.regionH, px xa s.regionW, px xb s.regionW)

/-- The pages to show for the view (`View.wantedPages`: visible, and one more each side) that
have no photo yet, nearest to the current page first; neighbours deferred for lack of photo
room (task 12.3b) are left out until a photo is released. -/
def missingPages (st : IO.Ref State) : IO (List Nat) := do
  let s ← st.get
  if s.doc.isNone || s.shown.isNone then return []
  let some (top, bot, _, _) ← viewBand s | return []
  -- Task 12.3b: neighbours whose photo did not fit wait for a release (`photoDeferred`).
  let vis := View.visiblePages s.places top bot
  let miss := (View.wantedPages s.places top bot).filter fun p =>
    !s.hasPhoto p && (!s.photoDeferred.contains p || vis.contains p || p == s.page)
  let d (p : Nat) : Nat := if p ≥ s.page then p - s.page else s.page - p
  return miss.mergeSort fun a b => d a ≤ d b

/-- The pages that may be shown now: every laid-out page in the page scroll mode, else the
pages in view and their neighbours (`View.wantedPages`) and the current page. -/
def wantedNow (st : IO.Ref State) : IO (List Nat) := do
  let s ← st.get
  if s.scroll == .page then return s.slots.toList.map (·.place.page)
  let some (top, bot, _, _) ← viewBand s | return [s.page]
  return s.page :: View.wantedPages s.places top bot

/-- Shows the result of the finished job `j` (task 8.8) when it is still wanted: the open
document, its page laid out with the same zoom and rotation (`keyOf`), in `want`, without a
photo. Also records the time from the request to the display in the Tcl array
`::safepdf::ttd` (ms; read by `scripts/viewer-corpus.sh`) and, for the current page, puts
the render time into the status line. Results for another document, zoom or rotation count
in `staleDropped`. Returns whether the page was shown. -/
def place (st : IO.Ref State) (want : List Nat) (j : Job) (r : Except Error Clip.Image)
    (ns : Nat) : IO Bool := do
  let s ← st.get
  let p := j.key.page
  let stale := j.key.gen != s.gen || (match slotOf s p with
    | some sl => keyOf s sl != j.key
    | none => false)
  if stale then
    st.modify fun s => { s with staleDropped := s.staleDropped + 1 }
    return false
  let some sl := slotOf s p | return false
  if s.doc.isNone || s.hasPhoto p || !want.contains p then return false
  showPhoto st sl r
  let t ← IO.monoNanosNow
  discard <| run ["set", s!"::safepdf::ttd({p})", formatMs (t - j.start)]
  if p == s.page then showStatus st s!"rendered in {formatMs ns} ms"
  return true

/-- Schedules a `poll` event while renders are running (task 8.8). -/
def ensurePoll (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  if (!s.jobs.isEmpty || !s.thJobs.isEmpty || s.budgetWait) && !s.pollQueued then
    st.modify ({ · with pollQueued := true })
    discard <| run ["after", toString pollMs, "::safepdf::emit poll"]

/-- Shows pages that must be on screen now (task 8.8: the current page, in the page scroll
mode its spread; the smoke tests' `settle`): from the cache at once, else rendered by
workers (`submit`, within `maxJobs`). The event waits for those renders at most `wait` ms
(`none`: until they are done, then also for any render that holds a slot they need); pages
still missing get the placeholder (`showWaiting`) and arrive through `poll`. -/
def showNow (st : IO.Ref State) (pages : List Nat) (wait : Option Nat) : IO Unit := do
  let some doc := (← st.get).doc | return
  cancelStale st
  let t0 ← IO.monoNanosNow
  for _ in [0:64] do
    let mut keys : List View.Key := []
    let mut blocked := false
    for p in pages do
      let s ← st.get
      let some sl := slotOf s p | continue
      if s.hasPhoto p then continue
      let key := keyOf s sl
      match ← cached st key with
      | some r =>
        showPhoto st sl r
        if p == s.page then showStatus st "from cache"
      | none =>
        if !s.running key && s.jobs.size < maxJobs then submit st doc key 0
        else raiseJob st key 0
        if (← st.get).running key then keys := key :: keys else blocked := true
    -- Wait for the renders of these pages (or, without a time limit and with a page still
    -- waiting for a slot, for every running render).
    let wanted (j : Job) : Bool := keys.contains j.key || (wait.isNone && blocked)
    for _ in [0:1000000] do
      let js := (← st.get).jobs.filter wanted
      if js.isEmpty then break
      let fin ← js.filterM (IO.hasFinished ·.task)
      for j in fin do
        if let some (r, ns) ← finish st j then discard <| place st pages j r ns
      if fin.size == js.size then break
      match wait with
      | none =>
        if fin.isEmpty then
          if let some j := js[0]? then discard <| IO.wait j.task
      | some ms =>
        if (← IO.monoNanosNow) - t0 ≥ ms * 1000000 then break
        IO.sleep 1
    if wait.isSome || !blocked then break
  let s ← st.get
  for p in pages do
    if let some sl := slotOf s p then
      if !s.hasPhoto p then showWaiting sl
  ensurePoll st

/-- After the view moved (task 9.3): in the vertical modes the current page becomes the page
under the window centre (`View.pageAt`), unless the view is still where the viewer put it
(`ownTop`); photos of pages no longer wanted (`View.wantedPages`) are deleted, which bounds the
memory Tk holds; missing pages are rendered one per event-loop turn (`renderMore`), so the
window stays responsive and shows the white page frames meanwhile. -/
def viewChanged (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  if s.doc.isNone || s.shown.isNone || s.slots.isEmpty then return
  let some (top, bot, left, right) ← viewBand s | return
  if s.scroll == .vertical && s.ownTop != some top then
    st.modify ({ · with ownTop := none })
    if let some p := View.pageAt s.places ((left + right) / 2) ((top + bot) / 2) then
      if p != s.page then setCurrent st p
  let s ← st.get
  let want := View.wantedPages s.places top bot
  let mut dropped := false
  for (p, _) in s.photos do
    if !want.contains p && p != s.page then
      dropPhoto st p
      dropped := true
  if dropped then drawOverlay st
  let s ← st.get
  if !s.renderQueued && want.any (!s.hasPhoto ·) then
    st.modify ({ · with renderQueued := true })
    discard <| run ["after", "1", "::safepdf::emit renderMore"]

/-- Shows the missing pages in view and their neighbours (`missingPages`, nearest to the
current page first; task 9.3): cached ones at once, the others get a placeholder and a
worker render while slots are free (task 8.8: the current page may use every slot of
`maxJobs`, the others leave one free); `poll` shows them as they finish. -/
def renderMore (st : IO.Ref State) : IO Unit := do
  st.modify ({ · with renderQueued := false })
  let some doc := (← st.get).doc | return
  cancelStale st
  let mut shown := false
  for p in ← missingPages st do
    let s ← st.get
    let some sl := slotOf s p | continue
    let key := keyOf s sl
    match ← cached st key with
    | some r =>
      showPhoto st sl r
      shown := true
      if p == s.page then showStatus st "from cache"
    | none =>
      let slots := if p == s.page then maxJobs else maxJobs - 1
      if !s.running key && s.jobs.size < slots then submit st doc key (if p == s.page then 0 else 1)
      else if p == s.page then raiseJob st key 0
      showWaiting sl
  if shown then drawOverlay st
  ensurePoll st

/-! ## Thumbnails (task 9.r9) -/

/-- Most thumbnail renders running at once (task 9.r9), on top of the page renders' `maxJobs`.
They start only while the page renders leave a slot free, so the main view goes first. -/
def thumbJobs : Nat := 2

/-- Tk photo of the thumbnail of page `p`. -/
def thumbPhoto (p : Nat) : String := s!"::safepdf::th{p}"

/-- Rotated size of page `p` of `doc` in page units (`/Rotate` plus the user rotation). -/
def pageSizeRot (s : State) (doc : Doc) (p : Nat) : Rat × Rat :=
  match doc.pages[p]? with
  | some page => View.boxSize (rotAdd page.rotate s.rot) (Box.ofRect page.cropBox)
  | none => (0, 0)

/-- The zoom of page `p`'s thumbnail: `Sidebar.thumbW` pixels across its rotated width. -/
def thumbZoom (s : State) (doc : Doc) (p : Nat) : Rat :=
  let (pw, _) := pageSizeRot s doc p
  if pw ≤ 0 then 1 else (Sidebar.thumbW : Rat) / pw

/-- Removes the thumbnail image of page `p` (eviction, task 9.r9). -/
def dropThumb (st : IO.Ref State) (p : Nat) : IO Unit := do
  try discard <| run ["image", "delete", thumbPhoto p] catch _ => pure ()
  discard <| photoUnreserve st (thumbPhoto p)
  discard <| run [".ol.th", "delete", s!"thi{p}"]
  st.modify fun s => { s with thHave := s.thHave.filter (· != p) }

/-- Deletes every thumbnail image and canvas item (a new document, a rotation, Close). Running
thumbnail renders finish on their own; `thumbPoll` drops their results. -/
def clearThumbs (st : IO.Ref State) : IO Unit := do
  for p in (← st.get).thHave do
    try discard <| run ["image", "delete", thumbPhoto p] catch _ => pure ()
    discard <| photoUnreserve st (thumbPhoto p)
  discard <| run [".ol.th", "delete", "all"]
  st.modify ({ · with thHave := [], thSlots := #[], thHeight := 0, thKey := none,
                      thMarked := none, thSel := none })

/-- Lays the thumbnails of the open document out (`Sidebar.thumbLayout`, sizes from each
page's rotated crop box, `Sidebar.thumbSize`): a white frame (the placeholder until the image
arrives, tags `thf thfN`) and the page label (the page label when the document has labels,
else the number; tags `thl thlN`) per page, the scroll region, the view at the top. Nothing is
rendered here (`thumbView`). -/
def buildThumbs (st : IO.Ref State) : IO Unit := do
  clearThumbs st
  let s ← st.get
  let some doc := s.doc | return
  let sizes := (List.range doc.pages.size).map fun p =>
    let (pw, ph) := pageSizeRot s doc p
    Sidebar.thumbSize pw ph
  let (ts, h) := Sidebar.thumbLayout sizes
  for t in ts do
    let x0 : Int := -((t.w / 2 : Nat) : Int)
    discard <| run [".ol.th", "create", "rectangle", toString (x0 - 1), toString ((t.y : Int) - 1),
      toString (x0 + t.w), toString (t.y + t.h), "-outline", "#c8c8d0", "-fill", "white",
      "-tags", s!"thf thf{t.page}"]
    discard <| run [".ol.th", "create", "text", "0", toString (t.y + t.h + 11), "-text",
      Toolbar.entryText s.labels t.page, "-font", "::safepdf::fBar", "-fill", "#5b5b66",
      "-tags", s!"thl thl{t.page}"]
  discard <| run ["set", "::safepdf::thH", toString h]
  discard <| run ["::safepdf::thRegion"]
  discard <| run [".ol.th", "yview", "moveto", "0"]
  st.modify ({ · with thSlots := ts, thHeight := h, thKey := some (s.gen, s.rot) })

/-- The visible band of the thumbnails panel (canvas pixels: top, bottom); `none` while the
panel is not laid out on screen (so that nothing is rendered for an unmapped panel). -/
def thumbBand (s : State) : IO (Option (Nat × Nat)) := do
  let some (a, _) := viewFracs (← run [".ol.th", "yview"]) | return none
  let some hgt := (← run ["winfo", "height", ".ol.th"]).toNat? | return none
  if hgt < 2 || (← run ["winfo", "ismapped", ".ol.th"]) != "1" then return none
  let top := (a * (s.thHeight : Rat) + 1 / 2).floor.toNat
  return some (top, top + hgt)

/-- Scrolls the thumbnails panel so that slot `t` is fully visible (with a small margin). -/
def thumbSee (st : IO.Ref State) (t : Sidebar.ThumbSlot) : IO Unit := do
  let s ← st.get
  let some (top, bot) ← thumbBand s | return
  let hgt : Rat := (max s.thHeight 1 : Nat)
  let y0 := t.y - min t.y 8
  let y1 := t.bottom + 8
  if y0 < top then
    discard <| run [".ol.th", "yview", "moveto", fmtFracFine ((y0 : Rat) / hgt)]
  else if y1 > bot then
    discard <| run [".ol.th", "yview", "moveto", fmtFracFine (((y1 - (bot - top) : Nat) : Rat) / hgt)]

/-- Highlights the current page's thumbnail (a rounded background, tag `thsel`, as PDF.js's
selected thumbnail) and scrolls it into view (PDF.js `scrollThumbnailIntoView`). -/
def markThumb (st : IO.Ref State) : IO Unit := do
  discard <| run [".ol.th", "delete", "thsel"]
  let s ← st.get
  st.modify ({ · with thMarked := some s.page })
  let some t := s.thSlots[s.page]? | return
  -- Until the panel is on screen it cannot be scrolled: try again after the next event.
  if (← thumbBand s).isNone then st.modify ({ · with thMarked := none })
  let x0 : Int := -((t.w / 2 : Nat) : Int) - 6
  discard <| run ["::safepdf::rrect", ".ol.th", toString x0, toString ((t.y : Int) - 6),
    toString (x0 + t.w + 12), toString (t.bottom + 2), "5", "-fill", "#d2d2d9", "-outline", "",
    "-tags", "thsel"]
  discard <| run [".ol.th", "lower", "thsel"]
  thumbSee st t

/-- Draws the keyboard selection's focus ring (tag `thfocus`) around thumbnail `p`. -/
def thumbFocus (st : IO.Ref State) (p : Nat) : IO Unit := do
  discard <| run [".ol.th", "delete", "thfocus"]
  let some t := (← st.get).thSlots[p]? | return
  let x0 : Int := -((t.w / 2 : Nat) : Int) - 4
  discard <| run ["::safepdf::rrect", ".ol.th", toString x0, toString ((t.y : Int) - 4),
    toString (x0 + t.w + 8), toString t.bottom, "4", "-fill", "", "-outline", "#0a84ff",
    "-width", "2", "-tags", "thfocus"]
  thumbSee st t

/-- Starts rendering the thumbnail `key` (as `submit`; priority 2 for the document worker,
after every page render). -/
def thumbSubmit (st : IO.Ref State) (doc : Doc) (key : View.Key)
    (ticket : Option Budget.Ticket := none) : IO Unit := do
  let start ← IO.monoNanosNow
  let (task, incomplete, id) ← renderTask st doc key 2
  st.modify fun s => { s with thJobs := s.thJobs.push { key, start, task, id, ticket, incomplete } }

/-- **Lazy thumbnail rendering** (task 9.r9): for the visible band of the panel
(`thumbBand`), the visible thumbnails and `Sidebar.thumbMargin` more on each side
(`Sidebar.thumbsWanted`) are rendered on worker threads — at most `thumbJobs` at once and only
while the page renders leave a slot free (`maxJobs`) — and thumbnails beyond
`Sidebar.thumbBudget` are dropped, farthest first (`Sidebar.thumbEvict`). Nothing while the
panel is hidden. -/
def thumbView (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  if !s.outlineShown || s.panel != .thumbnails || s.thKey != some (s.gen, s.rot) then return
  let some doc := s.doc | return
  let some (top, bot) ← thumbBand s | return
  let want := Sidebar.thumbsWanted s.thSlots top bot Sidebar.thumbMargin
  let center := (want.head?).getD s.page
  for p in Sidebar.thumbEvict s.thHave want Sidebar.thumbBudget center do dropThumb st p
  for p in want do
    let s ← st.get
    if s.thHave.contains p then continue
    let key : View.Key := ⟨s.gen, p, thumbZoom s doc p, s.rot⟩
    if s.thJobs.any (fun j => j.key.page == p && j.key.gen == s.gen && j.key.rot == s.rot) then
      continue
    if s.thJobs.size ≥ thumbJobs || s.jobs.size ≥ maxJobs then break
    -- Task 12.3: reserved before dispatch; without room at full size the thumbnail is
    -- rendered at ½, ¼ or ⅛ of its zoom (`Budget.Pool.admit`), else it waits.
    let (w, h) := keyPixels doc key
    match ← admit st (.thumb w h) with
    | .reserved t _ k => thumbSubmit st doc { key with zoom := key.zoom / ((2 ^ k : Nat) : Rat) } t
    | _ => break
  ensurePoll st

/-- Takes the finished thumbnail renders (task 9.r9) and shows those still laid out for the
open document and rotation: the image in photo `::safepdf::thN` on its frame (tags
`thi thiN`); a page that cannot be rendered keeps its empty frame. Others are dropped. -/
def thumbPoll (st : IO.Ref State) : IO Unit := do
  let done ← (← st.get).thJobs.filterM (IO.hasFinished ·.task)
  for j in done do
    releaseTicket st j.ticket
    st.modify fun s => { s with thJobs := s.thJobs.filter (·.key != j.key) }
    let s ← st.get
    let p := j.key.page
    if s.thKey != some (j.key.gen, j.key.rot) || j.key.gen != s.gen || s.thHave.contains p then
      continue
    let some t := s.thSlots[p]? | continue
    -- A cancelled worker render (task 12.2c) leaves the thumbnail to be asked for again.
    let some out := j.task.get | continue
    match out with
    | (.ok img, _) =>
      -- Task 12.3b: a thumbnail reserves its photo in the photo pool (in the thumbnails'
      -- reserve, which the kept thumbnails always fit: `Budget.thumbs_fit_reserve`).
      if (← photoAdmit st (thumbPhoto p) (Budget.photoBytes img.w img.h) true []).isNone then
        st.modify fun s => { s with photoRefused := s.photoRefused + 1 }
        continue
      discard <| run ["image", "create", "photo", thumbPhoto p]
      Shim.photoPut (thumbPhoto p) img.w.toUInt32 img.h.toUInt32 img.data
      let x0 : Int := -((img.w / 2 : Nat) : Int)
      discard <| run [".ol.th", "create", "image", toString x0, toString t.y, "-anchor", "nw",
        "-image", thumbPhoto p, "-tags", s!"thi thi{p}"]
      discard <| run [".ol.th", "raise", s!"thi{p}", s!"thf{p}"]
    | _ => pure ()
    let now ← IO.monoNanosNow
    st.modify fun s => { s with thHave := p :: s.thHave, thRendered := s.thRendered + 1,
                                thFirstNs := s.thFirstNs <|> some (now - s.thOpenNs) }

/-- Brings the thumbnails panel up to date (task 9.r9; after every event, `syncMenus`): while
it is shown, lays the thumbnails out again for a new document or rotation and moves the
current-page highlight with the main view. -/
def syncThumbs (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  if s.doc.isNone || !s.outlineShown || s.panel != .thumbnails then return
  if s.thKey != some (s.gen, s.rot) then
    buildThumbs st
    markThumb st
    -- Rendered once Tk has laid the panel out (`thumbBand`), after the event that showed it.
    discard <| run ["after", "idle", "::safepdf::emit thView"]
  else if s.thMarked != some s.page then markThumb st

/-- Handles `poll` (task 8.8, every `pollMs` while renders run): takes the finished renders
(`finish`, into the cache), shows those still wanted (`place`), starts more (`renderMore`). -/
def poll (st : IO.Ref State) : IO Unit := do
  st.modify ({ · with pollQueued := false })
  cancelStale st
  sweepSide st
  -- Task 12.3: a page that waited for the pool is asked for again.
  if (← st.get).budgetWait then
    st.modify ({ · with budgetWait := false })
    if (← st.get).doc.isSome then renderMore st
  let done ← (← st.get).jobs.filterM (IO.hasFinished ·.task)
  if !done.isEmpty then
    let want ← wantedNow st
    let mut shown := false
    for j in done do
      if let some (r, ns) ← finish st j then
        if ← place st want j r ns then shown := true
    if shown then drawOverlay st
    if (← st.get).doc.isSome then renderMore st
  -- Thumbnails (task 9.r9): finished ones shown, more started while page renders leave room.
  thumbPoll st
  thumbView st
  ensurePoll st

/-- Renders every missing page now and waits for every running render (smoke tests and
benchmarks). -/
def settle (st : IO.Ref State) : IO Unit := do
  cancelStale st
  viewChanged st
  for _ in [0:256] do
    let want ← wantedNow st
    for j in (← st.get).jobs do
      discard <| IO.wait j.task
      if let some (r, ns) ← finish st j then discard <| place st want j r ns
    match ← missingPages st with
    | [] => break
    | miss => showNow st miss none
  drawOverlay st

/-- Applies the pending scroll (`State.pending`) to the current layout. In the page scroll mode
top and bottom are the region's ends; in the vertical modes the current page's place
(`View.topFor`, `View.bottomFor`). Anchors and destinations map page points with
`Geom.toScreen` on their page's slot (C2). In the vertical modes the resulting view top is
remembered (`ownTop`). -/
def applyScroll (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some pend := s.pending | return
  st.modify ({ · with pending := none })
  let rw : Rat := (max s.regionW 1 : Nat)
  let rh : Rat := (max s.regionH 1 : Nat)
  let moveX (x : Rat) : IO Unit := discard <| run [".c", "xview", "moveto", fmtFrac (x / rw)]
  let moveY (y : Rat) : IO Unit := discard <| run [".c", "yview", "moveto", fmtFrac (y / rh)]
  let cur := slotOf s s.page
  match pend with
  | .top =>
    match s.scroll, cur with
    | .vertical, some sl => moveY (View.topFor sl.place : Nat)
    | _, _ => discard <| run [".c", "yview", "moveto", "0"]
  | .bottom =>
    match s.scroll, cur with
    | .vertical, some sl => moveY (View.bottomFor sl.place s.canvasH : Nat)
    | _, _ => discard <| run [".c", "yview", "moveto", "1"]
  | .anchor pg wx wy p =>
    if let some sl := slotOf s pg then
      if 0 < sl.vp.zoom then
        let q := toScreen sl.vp.zoom sl.vp.rot sl.vp.box p
        moveX (q.x + (sl.place.x : Rat) - (wx : Rat))
        moveY (q.y + (sl.place.y : Rat) - (wy : Rat))
  | .dest left top =>
    if let some sl := cur then
      if 0 < sl.vp.zoom then
        let q := toScreen sl.vp.zoom sl.vp.rot sl.vp.box
          ⟨left.getD sl.vp.box.llx, top.getD sl.vp.box.ury⟩
        moveX (q.x + (sl.place.x : Rat))
        moveY (q.y + (sl.place.y : Rat))
  | .frac x y =>
    discard <| run [".c", "xview", "moveto", fmtFrac x]
    discard <| run [".c", "yview", "moveto", fmtFrac y]
  | .within pg f =>
    if let some sl := slotOf s pg then
      moveY ((sl.place.y : Rat) + f * (sl.place.h : Rat))
  if s.scroll == .vertical then
    if let some (top, _, _, _) ← viewBand s then st.modify ({ · with ownTop := some top })

/-- Shows the current view mode on the view-mode drop-down (task 9.r4,
`Toolbar.ViewChoice.ofModes`): its icon, tooltip and checked entry, enabled with a document. -/
def showViewChoice (s : State) (on : Bool) : IO Unit := do
  let c := Toolbar.ViewChoice.ofModes s.scroll s.spread
  discard <| run ["::safepdf::viewShow", c.key, s!"View mode: {c.label}", if on then "1" else "0"]

/-- Updates title, page field, zoom field and (when the layout or the current page changed, or
a scroll is pending) the page images. A new layout (`layoutKeyOf` changed: document, view
mode, zoom, rotation, window size, or the spread shown in the page scroll mode) is computed by
`computeLayout` and drawn by `buildCanvas`. The current page (in the page scroll mode its
whole spread) is rendered at once; the other pages in view follow one per event-loop turn
(`viewChanged`, `renderMore`). -/
def refresh (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  discard <| run ["wm", "title", ".", s.title]
  st.modify ({ · with titleShown := s.title })
  match s.path, s.doc with
  | some _, some doc =>
    showPageField s
    discard <| run ["::safepdf::zoomShow", s.zoomSel.label, s.zoomSel.selected, "1"]
    showViewChoice s true
    if doc.pages.size == 0 then return
    let key := layoutKeyOf s
    let relaid := s.layoutKey != some key
    if relaid then
      -- A new layout of the vertical modes keeps the view's place in the current page.
      if s.scroll == .vertical && s.pending.isNone && s.layoutKey.isSome then
        if let (some sl, some (top, _, _, _)) := (slotOf s s.page, ← viewBand s) then
          if sl.place.h > 0 then
            st.modify ({ · with pending := some (.within s.page
              (((top : Int) - (sl.place.y : Int) : Rat) / (sl.place.h : Rat))) })
      let s ← st.get
      let (slots, rw, rh) := computeLayout s doc
      st.modify ({ · with slots, regionW := rw, regionH := rh, layoutKey := some key,
                          ownTop := none, shown := none })
      buildCanvas st
    let s ← st.get
    let some sl := slotOf s s.page | return
    let curKey : View.Key := ⟨s.gen, s.page, sl.vp.zoom, s.rot⟩
    if !relaid && s.shown == some curKey && s.pending.isNone then return
    setMirror st sl
    -- The current page (its spread in the page scroll mode) now, waiting for its render at
    -- most `syncWaitMs` (task 8.8); the status line says how it came.
    let had := s.hasPhoto s.page
    let renders0 := s.renders
    let now := if s.scroll == .page then s.slots.toList.map (·.place.page) else [s.page]
    showNow st now s.syncWaitMs
    applyScroll st
    viewChanged st
    drawOverlay st
    let s ← st.get
    if had || (s.hasPhoto s.page && s.renders == renders0) then showStatus st "from cache"
    else if !s.hasPhoto s.page then showStatus st "rendering..."
    let s ← st.get
    if s.scroll == .page && View.nextPage s.spread s.pageCount s.page != s.page then
      discard <| run ["after", "100", "::safepdf::emit prefetch"]
  | _, _ =>
    discard <| run ["::safepdf::setPage", "", "", "0"]
    discard <| run ["::safepdf::zoomShow", s.zoomSel.label, s.zoomSel.selected, "0"]
    showViewChoice s false
    discard <| run [".c", "delete", "sel", "hit", "mark", "bub"]
    discard <| run ["::safepdf::tintGc"]
    st.modify ({ · with bubble := none, pickerAt := none, slots := #[], layoutKey := none,
                        shown := none })
    clearPages st

/-- Shows the page images again with the marks of each page multiplied in, and redraws the
overlays (after a mark was added, removed or recoloured; task 9.4). -/
def repaint (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  for (p, r) in s.photos do
    if let (.ok img, some sl) := (r, slotOf s p) then
      Shim.photoPut (photoOf p) img.w.toUInt32 img.h.toUInt32
        (Marks.composite sl.vp.zoom sl.vp.rot sl.vp.box img.w img.h img.data (drawnMarks s p))
  drawOverlay st

/-- Renders the pages of the next spread (page scroll mode; the next page in the single-page
view) into the cache when they are small enough (`prefetchPixels`) and not cached yet. The
vertical modes render their neighbours through `viewChanged` instead. -/
def prefetch (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some doc := s.doc | return
  if s.scroll != .page then return
  let q := View.nextPage s.spread s.pageCount s.page
  if q == s.page then return
  let (slots, _, _) := computeLayout { s with page := q } doc
  for sl in slots do
    let key : View.Key := ⟨s.gen, sl.place.page, sl.vp.zoom, s.rot⟩
    let s ← st.get
    if !s.cache.contains key && !s.running key && sl.place.w * sl.place.h ≤ prefetchPixels &&
        s.jobs.size + 1 < maxJobs then
      submit st doc key
  ensurePoll st

/-! ## Outline panel (task 8.2d) -/

/-- Shows or hides the outline sidebar (the left pane of `.pw`); the sidebar toggle button
looks pressed while it is shown (PDF.js's `toggled`). The canvas's next width changes are
reported at once instead of after the 100 ms resize debounce (`::safepdf::resizeSoon`), so
the pages are laid out for the new width before the canvas is painted at it: at Page Fit the
page goes straight to its new place (task 9.r4). -/
def showOutline (st : IO.Ref State) (on : Bool) : IO Unit := do
  let s ← st.get
  -- The View → Outline check entry toggles its variable before it runs the command; set it
  -- back to the panel's real state whatever happens below.
  discard <| run ["set", Menu.outlineVar, if s.outlineShown then "1" else "0"]
  if on == s.outlineShown then return
  -- The canvas changes width: lay the pages out again as soon as it has its new size, before
  -- Tk paints it (task 9.r4, `::safepdf::resizeSoon`).
  discard <| run ["::safepdf::resizeSoon"]
  if on then discard <| run [".pw", "insert", "0", ".ol", "-weight", "0"]
  else discard <| run [".pw", "forget", ".ol"]
  discard <| run ["set", Menu.outlineVar, if on then "1" else "0"]
  discard <| run ["::safepdf::btnToggled", ".bar.sidebar", if on then "1" else "0"]
  st.modify ({ · with outlineShown := on })

/-- Fills the outline tree `.ol.t` from `State.outline` (task 9.7, model `Sidebar.rows`): one
line per entry — the disclosure triangle (tag `tK`, only for entries with children) and the
title (tag `oK`, one quoted word) — indented by depth (margin tags `dN` for rows with a
triangle, `lN` for leaves, aligned with their siblings' titles) and tagged `uA` for each
ancestor `A`, so that closing `A` elides the whole subtree. -/
def fillOutline (st : IO.Ref State) : IO Unit := do
  let es := (← st.get).outline.toList
  let rs := Sidebar.rows es
  let isOpen := Sidebar.initialOpen es
  st.modify ({ · with olRows := rs, olOpen := isOpen })
  discard <| run ["::safepdf::olClear"]
  let triW := ((← run ["font", "measure", "::safepdf::fTri", Sidebar.triangle true false]).toNat?).getD 14
  let mut depths : List Nat := []
  for (r, e) in rs.zip es do
    if !depths.contains r.depth then depths := r.depth :: depths
    let base := [if r.hasKids then s!"d{r.depth}" else s!"l{r.depth}"] ++ r.ancestors.map (s!"u{·}")
    let tri := Sidebar.triangle r.hasKids (isOpen.getD r.index false)
    discard <| run [".ol.t", "insert", "end",
      tri, " ".intercalate (base ++ ["tri", s!"t{r.index}"]),
      e.title ++ "\n", " ".intercalate (base ++ [s!"o{r.index}"])]
  for d in depths do
    let ind := Sidebar.indentPx d
    discard <| run [".ol.t", "tag", "configure", s!"d{d}", "-lmargin1", toString ind,
      "-lmargin2", toString (ind + triW)]
    discard <| run [".ol.t", "tag", "configure", s!"l{d}", "-lmargin1", toString (ind + triW),
      "-lmargin2", toString (ind + triW)]
  for r in rs do
    if r.hasKids && !isOpen.getD r.index false then
      discard <| run [".ol.t", "tag", "configure", s!"u{r.index}", "-elide", "1"]
  discard <| run [".ol.t", "configure", "-state", "disabled"]
  discard <| run [".ol.t", "yview", "moveto", "0"]

/-- Handles `olToggle K`: opens or closes outline row `K` (its disclosure triangle). -/
def olToggle (st : IO.Ref State) (k : String) : IO Unit := do
  let some i := k.toNat? | return
  let s ← st.get
  let o := Sidebar.toggle s.olRows s.olOpen i
  if o == s.olOpen then return
  st.modify ({ · with olOpen := o })
  let on := o.getD i false
  discard <| run [".ol.t", "tag", "configure", s!"u{i}", "-elide", if on then "" else "1"]
  discard <| run ["::safepdf::olSetTri", toString i, Sidebar.triangle true on]

/-! ## Sidebar panels (task 9.r9) -/

/-- What the open document offers the sidebar (task 9.r9: which panel buttons show). -/
def contentOf (s : State) : Sidebar.Content :=
  { hasOutline := !s.outline.isEmpty, hasAttachments := !s.attList.isEmpty,
    hasLayers := !s.lyRows.isEmpty }

/-- Shows the switcher buttons of the panels the document has (`Sidebar.buttons`, in order)
and presses the shown panel's button (PDF.js's toggled view button). -/
def syncPanelButtons (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let bs := Sidebar.buttons (contentOf s)
  let keys := bs.map (·.key)
  if s.panelButtons != some keys then
    for i in Sidebar.panels do discard <| run ["pack", "forget", i.button]
    for i in bs do discard <| run ["pack", i.button, "-in", ".ol.sw", "-side", "left", "-padx", "1"]
    st.modify ({ · with panelButtons := some keys })
  for i in Sidebar.panels do
    discard <| run ["::safepdf::btnToggled", i.button, if i.panel == s.panel then "1" else "0"]

/-- Shows panel `p` in the sidebar (task 9.r9, `::safepdf::showPanel`): its widgets, heading
and pressed button; the thumbnails are laid out and rendered when they become visible
(`syncThumbs`). -/
def showPanel (st : IO.Ref State) (p : Sidebar.Panel) : IO Unit := do
  st.modify ({ · with panel := p })
  discard <| run ["::safepdf::showPanel", p.info.key, p.info.title]
  syncPanelButtons st
  syncThumbs st

/-- Opens the sidebar on panel `p`, or closes it (`none`) (task 9.r9; `showOutline` moves the
pane). -/
def showSidebar (st : IO.Ref State) (p : Option Sidebar.Panel) : IO Unit := do
  if let some q := p then showPanel st q
  showOutline st p.isSome
  syncThumbs st

/-- Handles `panel KEY` (a switcher button): shows that panel when the document has it. -/
def panelClick (st : IO.Ref State) (k : String) : IO Unit := do
  let s ← st.get
  let some p := Sidebar.Panel.ofKey k | return
  if s.doc.isSome && p.available (contentOf s) then showPanel st p

/-! ## Attachments panel (task 9.r10) -/

/-- Writes row `i` of the attachments list (`.ol.at` item `aN`): its size column and tooltip
from what is known (`Attach.sizeColumn`, `Attach.tooltip`). -/
def attRow (s : State) (i : Nat) : IO Unit := do
  let some a := s.attList[i]? | return
  let pr := (s.attStatus[i]?).getD none
  discard <| run [".ol.at", "set", s!"a{i}", "size", Attach.sizeColumn a pr]
  discard <| run ["set", s!"::safepdf::attTip(a{i})", Attach.tooltip a pr]

/-- Fills the attachments list `.ol.at` from `State.attList` (model `Attach`): one item `aN`
per attachment with its name, size column and tooltip. Nothing is decoded here: sizes come
from `/Params /Size`, `/DL` or an unfiltered stream's length (`Attachments.listedSize`). -/
def fillAttachments (st : IO.Ref State) : IO Unit := do
  discard <| run ["::safepdf::attClear"]
  let s ← st.get
  for i in [0:s.attList.size] do
    let some a := s.attList[i]? | continue
    discard <| run [".ol.at", "insert", "", "end", "-id", s!"a{i}", "-text", a.name]
    attRow s i

/-- Keeps what decoding attachment `i` gave and updates its row. -/
def attRecord (st : IO.Ref State) (i : Nat) (pr : Attach.Probe) : IO Unit := do
  st.modify fun s => { s with attStatus := s.attStatus.modify i (fun _ => some pr) }
  attRow (← st.get) i

/-- Handles `attProbe N` (its tooltip is about to show): decodes attachment `N` once, under the
viewer's limits with the per-stream cap lowered to `Attach.probeLimit`, so that hovering never
decodes more than 16 MB (a larger file is decoded only when saved). -/
def attProbe (st : IO.Ref State) (i : Nat) : IO Unit := do
  let s ← st.get
  let (some doc, some a) := (s.doc, s.attList[i]?) | return
  if ((s.attStatus[i]?).getD none).isSome || a.stream.isNone then return
  let lim := { limits with maxDecodedStreamBytes := min limits.maxDecodedStreamBytes Attach.probeLimit }
  let r ← IO.lazyPure fun _ => (Core.Doc.Attachments.decode doc lim a).map ByteArray.size
  attRecord st i <| match r with
    | .ok n => .decoded n
    | .error (.limitExceeded .decodedStreamBytes) => .large
    | .error e => .failed (renderError e)

/-- The status line text of attachment `i`. -/
def attText (s : State) (i : Nat) : Option String :=
  (s.attList[i]?).map fun a => Attach.selectedText a ((s.attStatus[i]?).getD none)

/-- Selects attachment `i` (a click on its annotation's icon on the page): opens the sidebar
on the attachments panel, selects and shows its row, describes it in the status line. -/
def attSelect (st : IO.Ref State) (i : Nat) : IO Unit := do
  if i ≥ (← st.get).attList.size then return
  showSidebar st (some .attachments)
  discard <| run [".ol.at", "selection", "set", s!"a{i}"]
  discard <| run [".ol.at", "focus", s!"a{i}"]
  discard <| run [".ol.at", "see", s!"a{i}"]
  if let some t := attText (← st.get) i then setStatus t

/-! ## Layers panel (task 9.r11b) -/

/-- Sets every checkbox variable of the layers panel (`::safepdf::ly(K)`) from the state
(`Sidebar.layerChecked`). -/
def syncLayerVars (s : State) : IO Unit := do
  let some oc := s.oc | return
  let mut i := 0
  for r in s.lyRows do
    if let some on := Sidebar.layerChecked oc r then
      discard <| run ["set", s!"::safepdf::ly({i})", if on then "1" else "0"]
    i := i + 1

/-- Fills the layers panel `.ol.ly` from `State.lyRows` (model `Sidebar.layerRows`, tree
`Sidebar.rows`): one line per row — the disclosure triangle (rows with children), then a
checkbox (a group; disabled when locked) or the bold label (a heading) — indented by depth,
tagged with its ancestors as the outline is (`fillOutline`). Every heading starts open except
Additional Layers (`Sidebar.layerEntries`). -/
def fillLayers (st : IO.Ref State) : IO Unit := do
  discard <| run ["::safepdf::lyClear"]
  let s ← st.get
  let rs := s.lyRows
  let es := Sidebar.layerEntries rs
  let tree := Sidebar.rows es
  let isOpen := Sidebar.initialOpen es
  st.modify ({ · with lyTree := tree, lyOpen := isOpen })
  let some cfg := s.ocCfg | return
  let triW := ((← run ["font", "measure", "::safepdf::fTri", Sidebar.triangle true false]).toNat?).getD 14
  let mut depths : List Nat := []
  for (t, r) in tree.zip rs do
    if !depths.contains t.depth then depths := t.depth :: depths
    let tags := [if t.hasKids then s!"d{t.depth}" else s!"l{t.depth}"] ++ t.ancestors.map (s!"u{·}")
    discard <| run ["::safepdf::lyRow", toString t.index,
      Sidebar.triangle t.hasKids (isOpen.getD t.index false), " ".intercalate tags, r.label,
      if r.group.isSome then "group" else if r.italic then "italic" else "heading",
      if Sidebar.layerLocked cfg r then "1" else "0"]
  for d in depths do
    let ind := Sidebar.indentPx d
    discard <| run [".ol.ly", "tag", "configure", s!"d{d}", "-lmargin1", toString ind,
      "-lmargin2", toString (ind + triW)]
    discard <| run [".ol.ly", "tag", "configure", s!"l{d}", "-lmargin1", toString (ind + triW),
      "-lmargin2", toString (ind + triW)]
  -- Headings that start closed (Additional Layers, as PDF.js) elide their rows.
  for t in tree do
    if t.hasKids && !isOpen.getD t.index false then
      discard <| run [".ol.ly", "tag", "configure", s!"u{t.index}", "-elide", "1"]
  discard <| run [".ol.ly", "yview", "moveto", "0"]
  syncLayerVars (← st.get)

/-- Handles `lyToggle K`: opens or closes layers row `K` (its disclosure triangle). -/
def lyToggle (st : IO.Ref State) (k : String) : IO Unit := do
  let some i := k.toNat? | return
  let s ← st.get
  let o := Sidebar.toggle s.lyTree s.lyOpen i
  if o == s.lyOpen then return
  st.modify ({ · with lyOpen := o })
  let on := o.getD i false
  discard <| run [".ol.ly", "tag", "configure", s!"u{i}", "-elide", if on then "" else "1"]
  discard <| run ["::safepdf::lySetTri", toString i, Sidebar.triangle true on]

/-- Shows the pages again under the layers' new state (task 9.r11b): a new generation (the
render cache, running renders and the thumbnails are stale: `syncThumbs` lays them out again
when the panel shows), the text indexes dropped (hidden text is neither selectable nor
found), the selection and the search hit cleared. -/
def applyLayers (st : IO.Ref State) : IO Unit := do
  st.modify fun s => { s with gen := s.gen + 1, cache := ({ budget := Budget.ceilings.cacheBytes } : View.Cache), shown := none,
                              texts := Array.replicate s.texts.size none, sel := none,
                              hit := none, pressPt := none }
  for (p, _) in (← st.get).photos do dropPhoto st p
  refresh st
  syncThumbs st

/-- Handles `layer K` (a click on row `K`'s checkbox): `Sidebar.layerToggle` (radio buttons
turn the others off; a locked group stays), every checkbox set from the result, the pages
rendered again (`applyLayers`). -/
def layerClick (st : IO.Ref State) (k : String) : IO Unit := do
  let some i := k.toNat? | return
  let s ← st.get
  let (some cfg, some oc) := (s.ocCfg, s.oc) | return
  let oc' := Sidebar.layerToggle cfg oc s.lyRows i
  st.modify ({ · with oc := some oc' })
  syncLayerVars (← st.get)
  if oc' == oc then
    if let some r := s.lyRows[i]? then
      if Sidebar.layerLocked cfg r then setStatus s!"layer {r.label} is locked"
    return
  applyLayers st

/-- Reads the optional content of the newly opened `doc` (task 9.r11b) and fills the layers
panel: the state is the document's default (`Config.initial`), except on the reopen after a
save where the previous state `keep` stays (when the groups are the same). -/
def loadLayers (st : IO.Ref State) (doc : Doc) (keep : Option Core.Doc.OptionalContent.State) :
    IO Unit := do
  let cfg ← IO.lazyPure fun _ =>
    (Core.Doc.OptionalContent.read (Core.Content.Run.resolve (Core.Text.docSource limits doc))
      limits (Core.Filter.Budget.init limits) doc.catalog).1
  let oc := cfg.map fun c =>
    let d := c.initial
    match keep with
    | some k => if k.known == d.known then k else d
    | none => d
  st.modify ({ · with ocCfg := cfg, oc, lyRows := (cfg.map Sidebar.layerRows).getD [] })
  fillLayers st

/-! ## Document open settings (task 9.r8) -/

/-- Sets the View menu's and the `»` menu's radio variables, `::safepdf::continuous` and the
view-mode drop-down to the state's view mode (as `setViewMode` does). -/
def syncViewVars (s : State) : IO Unit := do
  discard <| run ["set", Menu.scrollVar, s.scroll.key]
  discard <| run ["set", Menu.spreadVar, s.spread.key]
  discard <| run ["set", "::safepdf::continuous", if s.scroll == .vertical then "1" else "0"]
  showViewChoice s s.doc.isSome

/-- A file name or path as shown in the identity line: controls and bidi overrides
(`Links.unsafeChar`, which could reorder or hide the surrounding text) become spaces. -/
def identityClean (t : String) : String :=
  t.map fun c => if Links.unsafeChar c then ' ' else c

/-- **The trusted identity line** (task 12.5, Plan.md §6 Phase 12 "Honest UI for
degraded/hidden content"): which application shows which file — the file name and its path
(for a document opened from memory, bib-lean's, only its name), never anything the document
says about itself (no `/Title`). -/
def identityLine (path : Option String) (inMemory : Bool) : String :=
  match path with
  | none => s!"{Menu.appName}: no document"
  | some p =>
    let src := if inMemory then "opened from the library, not from a file" else identityClean p
    s!"{Menu.appName} is showing {identityClean (baseName p)} ({src}) - this line is drawn by \
      {Menu.appName}, never by the document"

#guard identityLine none false == "SafePDF: no document"
#guard identityLine (some "/a/b.pdf") false == "SafePDF is showing b.pdf (/a/b.pdf) - this line \
  is drawn by SafePDF, never by the document"
#guard identityLine (some "x\u202Eftp.pdf") true == "SafePDF is showing x ftp.pdf (opened from the \
  library, not from a file) - this line is drawn by SafePDF, never by the document"

/-- Whether the identity line is shown: a document is open and has the window in full screen
or hides parts of it (toolbar, menubar or scroll bars), where it could imitate another
application or a system dialog over the whole window. -/
def State.showsIdentity (s : State) : Bool :=
  s.doc.isSome && (s.fullScreen || s.hidden != (false, false, false))

#guard !({} : State).showsIdentity && !({ fullScreen := true } : State).showsIdentity

/-- Task 12.5: shows (with the current file) or hides the identity line `.ident`, a strip of
the viewer's own window above the status line, outside the page canvas, so nothing the
document draws can cover or imitate it in place (`identityLine`, `State.showsIdentity`).
`setFullScreen` calls it before the window enters full screen, `applyChrome` after hiding. -/
def syncIdentity (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let packed := (← run ["winfo", "manager", ".ident"]) == "pack"
  if s.showsIdentity then
    discard <| run [".ident", "configure", "-text", identityLine s.path s.inMemory]
    if !packed then
      discard <| run ["pack", ".ident", "-side", "bottom", "-fill", "x", "-after", ".statusline"]
  else if packed then
    discard <| run ["pack", "forget", ".ident"]

/-- Shows or hides the toolbar, the menubar and the scroll bars (task 9.r8,
`/ViewerPreferences /HideToolbar`, `/HideMenubar`, `/HideWindowUI`; `(false, false, false)`
shows them all). On aqua the menubar cannot be removed (Tk keeps a default one there). Task
12.5: the identity line follows (`syncIdentity`). -/
def applyChrome (st : IO.Ref State) (hidden : Bool × Bool × Bool) : IO Unit := do
  let (tb, mb, ui) := hidden
  let old := (← st.get).hidden
  if old == hidden then return
  if tb != old.1 then
    if tb then discard <| run ["pack", "forget", ".bar"]
    else discard <| run ["pack", ".bar", "-side", "top", "-fill", "x", "-before", ".barline"]
  if mb != old.2.1 then
    discard <| run [".", "configure", "-menu", if mb then "" else Menu.barPath]
  if ui != old.2.2 then
    if ui then discard <| run ["grid", "remove", ".ys", ".xs"]
    else discard <| run ["grid", ".ys", ".xs"]
  discard <| run ["::safepdf::resizeSoon"]
  st.modify ({ · with hidden })
  syncIdentity st

/-- Enters or leaves full screen (task 9.r8, `/PageMode /FullScreen`): `wm attributes .
-fullscreen`. Leaving applies the document's `/NonFullScreenPageMode` to the sidebar (task
9.r9: UseThumbs opens the thumbnails). Task 12.5: the identity line is shown before the window
enters full screen and hidden after it leaves (`syncIdentity`). -/
def setFullScreen (st : IO.Ref State) (on : Bool) : IO Unit := do
  let s ← st.get
  if on == s.fullScreen then return
  discard <| run ["::safepdf::resizeSoon"]
  st.modify ({ · with fullScreen := on })
  if on then syncIdentity st
  discard <| run ["wm", "attributes", ".", "-fullscreen", if on then "1" else "0"]
  if !on then syncIdentity st
  if !on && s.doc.isSome then
    showSidebar st (Sidebar.onLoad (some s.afterFullScreen) (contentOf s))

/-- The view a document without open settings gets (task 9.r8): the default view mode, left
to right, Automatic Zoom, full window UI, no document title, no notes. -/
def resetOpenView (st : IO.Ref State) : IO Unit := do
  setFullScreen st false
  applyChrome st (false, false, false)
  st.modify fun s => { s with scroll := s.defaultView.1, spread := s.defaultView.2, rtl := false,
                              zoomSel := .auto, docTitle := none, openNote := "",
                              afterFullScreen := .useNone }
  syncViewVars (← st.get)

/-- `/FitWindow` (task 9.r8): sizes the window so that the canvas shows page `p` at the zoom
choice's percentage (100 % for the fit choices), both pages of a spread side by side, at most
90 % of the screen. -/
def fitWindow (st : IO.Ref State) (doc : Doc) (p : Nat) : IO Unit := do
  let s ← st.get
  let some page := doc.pages[p]? | return
  let (pw, ph) := View.boxSize (rotAdd page.rotate s.rot) (Box.ofRect page.cropBox)
  let (fw, fh) := View.fitBox s.spread pw ph
  let pct := match s.zoomSel with | .pct q => q | _ => 100
  let z := View.pctZoom pct s.scaling
  let cw := (fw * z).ceil.toNat + 2 * View.margin + (if s.spread == .none then 0 else View.pageGap)
  let ch := (fh * z).ceil.toNat + 2 * View.margin
  let num (w : String) : IO (Option Nat) := return (← run ["winfo", w, "."]).toNat?
  let (some ww, some wh, some sw, some sh) :=
    (← num "width", ← num "height", ← num "screenwidth", ← num "screenheight") | return
  let w := min (sw * 9 / 10) (cw + (ww - s.canvasW))
  let h := min (sh * 9 / 10) (ch + (wh - s.canvasH))
  discard <| run ["wm", "geometry", ".", s!"{max w 480}x{max h 240}"]

/-- `/CenterWindow` (task 9.r8): puts the window in the middle of the screen. -/
def centerWindow : IO Unit := do
  discard <| run ["update", "idletasks"]
  let get (w : String) : IO Nat := return ((← run ["winfo", w, "."]).toNat?).getD 0
  let (ww, wh, sw, sh) := (← get "width", ← get "height", ← get "screenwidth", ← get "screenheight")
  discard <| run ["wm", "geometry", ".", s!"+{(sw - ww) / 2}+{(sh - wh) / 2}"]

/-- The status note while the document's preferences hide parts of the window. -/
def hiddenNote : String := "the document hides parts of the window (Escape shows them)"

/-- The status note while the document is shown in full screen. -/
def fullScreenNote : String := "full screen (Escape leaves)"

/-- **Applies the document's open settings** (task 9.r8, `Core.Doc.OpenSettings.read`) to the
state `resetOpenView` left: `/PageLayout` → view mode, `/Direction /R2L` → right-to-left
spreads, `/OpenAction` (a destination or a GoTo action only, never anything else) → page, zoom
and position, `/DisplayDocTitle` → the window title from `/Title`, the hiding preferences,
`/FullScreen`. Returns the page mode (for the outline), the viewer preferences (FitWindow and
CenterWindow are applied by `openWith` once the outline is laid out) and the notes for the
status line (what was not honoured). -/
def applyOpenSettings (st : IO.Ref State) (doc : Doc) :
    IO (Option Core.Doc.OpenSettings.PageMode × Core.Doc.OpenSettings.Prefs × List String) := do
  let o ← IO.lazyPure fun _ => Core.Doc.OpenSettings.read doc limits
  let pr := o.prefs
  if let some l := o.layout then
    let (sc, sp) := View.modesOf l
    st.modify ({ · with scroll := sc, spread := sp })
  let docTitle := if pr.displayDocTitle then
      (o.title.map Links.textString).filter (·.any (· != ' ')) else none
  st.modify fun s => { s with rtl := pr.direction == .r2l, docTitle,
                              afterFullScreen := pr.nonFullScreen }
  if let some d := o.dest then
    if let some j := Links.jumpOf d then
      let z := Core.Doc.OpenSettings.zoomOf d.fit
      st.modify fun s => { s with page := j.page, pending := some (.dest j.left j.top),
                                  zoomSel := Toolbar.zoomChoiceOf z s.zoomSel }
  syncViewVars (← st.get)
  applyChrome st (pr.hideToolbar, pr.hideMenubar, pr.hideWindowUI)
  let mut notes := o.issues.map (·.message)
  if pr.hideToolbar || pr.hideMenubar || pr.hideWindowUI then
    notes := notes ++ [hiddenNote]
  if o.mode == some .fullScreen then
    notes := notes ++ [fullScreenNote]
    -- Task 10.13: the note is stored before the window enters full screen: on Aqua that
    -- renders (and rebuilds the status line from `openNote`) at once, so storing it later
    -- left the old text until the next update. `openWith` stores the same value again.
    st.modify ({ · with openNote := String.join (notes.map ("; " ++ ·)) })
    setFullScreen st true
  return (o.mode, pr, notes)

/-- Escape's window part (task 9.r8): leaves full screen, else shows what the document's
viewer preferences hid. Returns whether it did anything. -/
def escapeWindow (st : IO.Ref State) : IO Bool := do
  let s ← st.get
  -- The status notes that told how to get here are done.
  st.modify fun s => { s with openNote := ((s.openNote.replace s!"; {fullScreenNote}" "").replace
    s!"; {hiddenNote}" "") }
  if s.fullScreen then
    setFullScreen st false
    return true
  if s.hidden != (false, false, false) then
    applyChrome st (false, false, false)
    setStatus "toolbar, menu bar and scroll bars shown"
    return true
  return false

/-! ## The document worker at open and close (task 12.2c) -/

/-- Display text from the worker (outline titles, names): unsafe characters
(`Links.unsafeChar`: controls, bidi overrides) as spaces, at most `Links.maxTitle` characters,
as `Links.textString` does for the titles read in this process. -/
def safeText (s : String) : String :=
  String.ofList ((s.toList.take Links.maxTitle).map fun c => if Links.unsafeChar c then ' ' else c)

/-- What activating an outline item of the worker does (as `Links.actionOf`; a URI is shown
percent-encoded by `Links.uriText`). -/
def actionOfTarget : Worker.Protocol.Target → Links.Action
  | .none => .none
  | .page i f => let (l, t) := Links.fitPos f; .goto ⟨i, l, t⟩
  | .danglingDest _ => .badPage
  | .unresolved n => .unresolved (safeText n)
  | .uri u => .uri (Links.uriText u.toUTF8.toList)
  | .action k => if k == "URI" then .other "URI (no address)" else .other (Links.uriText k.toUTF8.toList)

/-- An outline item of the worker as an outline entry (as `Links.outlineEntries`). -/
def entryOfItem (it : Worker.Protocol.OutlineItem) : Links.Entry :=
  { title := safeText it.title, depth := it.depth,
    isOpen := match it.count with | some c => decide (0 < c) | none => false,
    action := actionOfTarget it.target }

/-- Hands a newly opened document to the worker session (task 12.2c): a new `srcSerial`, the
bytes the viewer read (a new worker process for them) and a request for the outline. Returns
the outline reply's task (`none` without a session, or when the bytes do not fit the
protocol). -/
def workerOpen (st : IO.Ref State) (bytes : ByteArray) : IO (Option (Task Worker.Reply)) := do
  st.modify fun s => { s with srcSerial := s.srcSerial + 1, workerSrc := none }
  let s ← st.get
  let some ses := s.worker | return none
  if bytes.size > limits.maxInputBytes then
    ses.setDoc none
    return none
  ses.setDoc (some (s.srcSerial, bytes, true))
  st.modify ({ · with workerSrc := some s.srcSerial })
  let (_, t) ← ses.submit s.srcSerial .outline 0
  return some t

/-- No document any more (a failed open, Close): the worker is stopped. -/
def workerStop (st : IO.Ref State) : IO Unit := do
  st.modify fun s => { s with srcSerial := s.srcSerial + 1, workerSrc := none }
  if let some ses := (← st.get).worker then ses.setDoc none

/-- The outline of the open document: from the worker's reply `t?` (waits for it, at most the
worker deadline), else read in this process (`Links.outlineEntries`) — without a session, or
with a note when the worker gave no outline. -/
def outlineFor (doc : Doc) (t? : Option (Task Worker.Reply)) :
    IO (Array Links.Entry × Option String) := do
  let here : IO (Array Links.Entry) :=
    IO.lazyPure fun _ => (Links.outlineEntries doc limits).toArray
  let some t := t? | return (← here, none)
  match ← IO.wait t with
  | .response (.outline items) _ =>
    return ((Links.clampDepths 0 (items.map entryOfItem)).toArray, none)
  | .response (.error _ m) _ =>
    return (← here, some s!"outline read in this process (the document worker: {m})")
  | .response _ _ =>
    return (← here, some "outline read in this process (the document worker answered with another message)")
  | .failed e =>
    return (← here, some s!"outline read in this process (the document worker: {failText e})")
  | .cancelled => return (← here, none)

/-- Opens the document `load` gives under the name `path`: builds the page tree, shows page 1.
A failure (`load`'s message, e.g. `cannot read: …`) ends up in the status line with an empty
page. Shared by `openFile` and `openBytes`.

Task 9.r8: every open starts from the default view (`resetOpenView`: the start-up view mode,
Automatic Zoom, page 1, full window UI) and applies the document's open settings
(`applyOpenSettings`), so nothing carries over from the previous file. With `keepView` (the
reopen after Save / Save to library) the user's view mode, zoom, outline and window stay as
they were and the document's settings are not applied again. -/
def openWith (st : IO.Ref State) (path : String) (load : IO (Except String Doc))
    (keepView : Bool := false) : IO Unit := do
  let wasShown := (← st.get).outlineShown
  -- Task 9.r11b: the reopen after a save keeps the layers' state.
  let curOC := (← st.get).oc
  let prevOC := if keepView then curOC else none
  if !keepView then resetOpenView st
  clearThumbs st
  let t0 ← IO.monoNanosNow
  st.modify ({ · with thRendered := 0, thFirstNs := none, thOpenNs := t0 })
  st.modify fun s => { s with path := some path, doc := none, view := none, page := 0,
                              shown := none }
  st.modify fun s => { s with gen := s.gen + 1, cache := ({ budget := Budget.ceilings.cacheBytes } : View.Cache), pending := some .top,
                              texts := #[], sel := none, pressPt := none, hit := none,
                              labels := #[], outline := #[], links := #[], hover := none,
                              history := {}, marks := {}, markSel := none, markHist := {},
                              slots := #[], layoutKey := none, ownTop := none, ftEdit := none,
                              inkSession := none, inkStroke := none, moveFrom := none,
                              attList := #[], attIcons := [], attStatus := #[],
                              ocCfg := none, oc := none, lyRows := [] }
  clearPages st
  discard <| run ["::safepdf::attClear"]
  fillLayers st
  discard <| run ["destroy", ".note"]
  discard <| run ["destroy", ".c.ft"]
  discard <| run [".c", "delete", "ftedit", "inkcur"]
  fillOutline st
  showOutline st false
  st.modify ({ · with toggleShown := none })
  match ← load with
  | .error msg =>
    workerStop st
    refresh st
    setStatus s!"{path}: {msg}"
  | .ok doc =>
    -- Task 12.2c: the worker opens the same bytes meanwhile and reads the outline.
    let outlineT ← workerOpen st doc.file.bytes
    -- Our marks already in the file (task 9.5c): restored with their ids, saved.
    let marks ← IO.lazyPure fun _ => Marks.Store.load (Save.readMarks doc limits)
    st.modify ({ · with doc := some doc, texts := Array.replicate doc.pages.size none,
                        marks, markHist := Marks.History.start marks.marks })
    let labels ← IO.lazyPure fun _ => Links.labels doc limits
    st.modify ({ · with labels, links := Array.replicate doc.pages.size none })
    -- Task 9.r10: the attachments, listed without decoding any.
    let att ← IO.lazyPure fun _ => Core.Doc.Attachments.list doc limits
    st.modify ({ · with attList := att.entries.toArray, attIcons := att.icons,
                        attStatus := Array.replicate att.entries.length none })
    fillAttachments st
    -- Task 9.r11b: the layers, in the document's default state (kept on the reopen after a
    -- save).
    loadLayers st doc prevOC
    -- Task 12.2c: the outline, from the worker (waited for here, after the work above).
    let (outline, olNote) ← outlineFor doc outlineT
    st.modify ({ · with outline })
    fillOutline st
    -- Task 9.r8: the document's open settings, on every open except the reopen after a save
    -- (`keepView`: the user's view stays, outline included).
    let (mode, prefs, notes) ← if keepView then pure (none, {}, [])
      else applyOpenSettings st doc
    -- Before anything lays the window out: a `<Configure>` refresh shows the status line.
    let wNote := (← st.get).workerNote
    let notes := notes ++ olNote.toList ++ (if wNote.isEmpty then [] else [wNote])
    st.modify ({ · with openNote := String.join (notes.map ("; " ++ ·)) })
    -- Task 9.r9: the panel buttons for this document, the sidebar as the page mode says.
    let s1 ← st.get
    let content := contentOf s1
    syncPanelButtons st
    showSidebar st (if keepView then (if wasShown then some (Sidebar.pick s1.panel content)
        else none)
      else Sidebar.onLoad mode content)
    let readCanvas : IO Unit := do
      discard <| run ["update", "idletasks"]
      if let (some w, some h) := ((← run ["winfo", "width", ".c"]).toNat?,
          (← run ["winfo", "height", ".c"]).toNat?) then
        if w ≥ 2 && h ≥ 2 then st.modify ({ · with canvasW := w, canvasH := h })
    -- Lay the window out again so that the first render uses the canvas size beside the
    -- outline panel.
    readCanvas
    if !(← st.get).fullScreen then
      if prefs.fitWindow then
        fitWindow st doc (← st.get).page
        readCanvas
      if prefs.centerWindow then centerWindow
    if doc.pages.size == 0 then
      refresh st
      setStatus s!"{path}: the document has no pages"
    else
      refresh st
      if marks.marks.size > 0 then
        setStatus s!"{← run [".status", "cget", "-text"]}; {marks.marks.size} saved marks \
          restored from the file"

/-- The label of File → Save and the toolbar Save button's tooltip: "Save to library" while
the document belongs to a library (task 10.1b; bib-lean's own reader saves to the library
too), else "Save". -/
def setSaveLabels (library : Bool) : IO Unit := do
  if let some (m, i) := Menu.locate .save then
    discard <| run [m, "entryconfigure", toString i, "-label",
      if library then "Save to library" else Menu.Cmd.save.label]
  discard <| run ["set", "::safepdf::btn(tip,.bar.save)",
    ← keyText (if library then "Save to library (Ctrl+S)" else "Save (Ctrl+S)")]

/-- Opens the file `path` (`Inspect.load`: size check against `Limits.maxInputBytes`, then
`SafePdf.parseWith`). A local file: a library the window had (task 10.1b) is let go, its
pending posts still go out on their own thread. -/
def openFile (st : IO.Ref State) (path : String) (keepView : Bool := false) : IO Unit := do
  if (← st.get).library.isSome then setSaveLabels false
  st.modify ({ · with inMemory := false, titleOverride := none, library := none })
  openWith st path (keepView := keepView) do
    match ← Inspect.load {} path with
    | .error msg => return .error s!"cannot read: {msg}"
    | .ok input =>
      match Views.Pages.docOf limits input.result with
      | .error e => return .error s!"cannot open: {renderError e}"
      | .ok doc => return .ok doc

/-- **Opens a document from memory** (task 10.1b: bib-lean's reader mode fetches the file over
HTTP and never writes it to disk): `bytes` through `SafePdf.Api.openBytes` (the viewer's
limits, the lenient path allowed as for files), shown under the name `name` (the title uses
`titleOverride` when set). `State.library` and `titleOverride` are kept, so a library reopens
its saved bytes with this. -/
def openBytes (st : IO.Ref State) (name : String) (bytes : ByteArray) (keepView : Bool := false) :
    IO Unit := do
  st.modify ({ · with inMemory := true })
  openWith st name (keepView := keepView) do
    match SafePdf.Api.openBytes bytes { limits } with
    | .ok d => return .ok d.doc
    | .error e => return .error s!"cannot open: {e.message}"

/-- Moves to page `p` (clamped to the document), scrolled to `where`, and refreshes. -/
def goTo (st : IO.Ref State) (p : Nat) (whereTo : ScrollTo := .top) : IO Unit := do
  let s ← st.get
  if s.pageCount == 0 then return
  let p := min p (s.pageCount - 1)
  if p != s.page then
    let keep := s.scroll == .vertical
    st.modify ({ · with page := p, pending := some whereTo, sel := if keep then s.sel else none,
                        pressPt := none, hover := none, wheel := {},
                        markSel := if keep then s.markSel else none })
    discard <| run [".c", "configure", "-cursor", ""]
    refresh st

/-- Remembers the page point at window position `(wx, wy)` of the canvas (on the page under
it, task 9.3), so that the next refresh keeps it there (C2 anchoring). Nothing when no page is
shown. -/
def anchorAt (st : IO.Ref State) (wx wy : Nat) : IO Unit := do
  let some (pg, p) ← pagePointAt st wx wy | return
  st.modify ({ · with pending := some (.anchor pg wx wy p) })

/-- The window position to anchor at: the given one, else the canvas centre. -/
def anchorPos (s : State) (pos : Option (Nat × Nat)) : Nat × Nat :=
  pos.getD (s.canvasW / 2, s.canvasH / 2)

/-- Changes the zoom mode, keeping the page point at `pos` (default: the window centre)
in place. -/
def setMode (st : IO.Ref State) (zoomSel : Toolbar.ZoomChoice) (pos : Option (Nat × Nat)) :
    IO Unit := do
  let s ← st.get
  if s.doc.isNone then return
  let (wx, wy) := anchorPos s pos
  anchorAt st wx wy
  st.modify ({ · with zoomSel })
  refresh st

/-- Handles `zoom in|out|actual|fitpage|fitwidth|auto ?X Y?` and `zoom choose KEY` (the zoom
drop-down, `Toolbar.ZoomChoice.ofKey`). -/
def zoom (st : IO.Ref State) (what : String) (pos : Option (Nat × Nat)) : IO Unit := do
  let s ← st.get
  -- The current effective (quantised) zoom: the fixed percentage's, or the one a fit mode
  -- came out at. Zoom in/out step on it (task 10.12, `View.stepInZ`/`stepOutZ`): the result
  -- is always strictly larger/smaller; at the end of the range nothing changes.
  let cur := match s.zoomSel.mode with
    | some (.scale p) => View.pctZoom p s.scaling
    | _ => s.shownZoom
  match what with
  | "in" => if let some p := View.stepInZ cur s.scaling then setMode st (.pct p) pos
  | "out" => if let some p := View.stepOutZ cur s.scaling then setMode st (.pct p) pos
  | "actual" => setMode st .actual pos
  | "fitpage" => setMode st .pageFit pos
  | "fitwidth" => setMode st .pageWidth pos
  | "auto" => setMode st .auto pos
  | _ => setStatus s!"internal: unknown zoom {what}"

/-- Handles `zoom choose KEY` from the zoom drop-down. -/
def zoomChoose (st : IO.Ref State) (key : String) : IO Unit := do
  match Toolbar.ZoomChoice.ofKey key with
  | some c => setMode st c none
  | none => setStatus s!"internal: unknown zoom choice {key}"

/-- Handles `wheel AXIS KIND D` (task 9.2): a wheel or trackpad delta `D` of kind `KIND`
(`notch`, `line`, `pixel`; `View.WheelKind`) on axis `x` or `y`. `View.wheelStep` decides:
scroll within the page (small deltas accumulate), or, on the vertical axis after reaching the
edge and pushing on past it by `View.wheelThreshold`, turn to the top of the next page (spread)
or the bottom of the previous one, as the keys do. In the vertical modes the wheel only
scrolls (task 9.3). Task 9.r1: each axis has its own state (`View.Wheels`), no event is
swallowed after a turn, and the push beyond the threshold stays owed to the new page (kept
across `goTo`, which resets the wheel); a turn at either end of the document owes nothing. -/
def wheel (st : IO.Ref State) (axis kindS dS : String) : IO Unit := do
  let s ← st.get
  if s.doc.isNone || s.shown.isNone then return
  let some d := dS.toInt? | return
  let kind : View.WheelKind ← match kindS with
    | "notch" => pure .notch
    | "line" => pure .line
    | "pixel" => pure .pixel
    | _ => return
  let isY := axis == "y"
  let some (a, b) := viewFracs (← run [".c", if isY then "yview" else "xview"]) | return
  let region := if isY then s.regionH else s.regionW
  let r : Rat := region
  let top := (a * r + 1 / 2).floor.toNat
  let view := ((b - a) * r + 1 / 2).floor.toNat
  let now ← IO.monoMsNow
  -- In the vertical modes the wheel simply scrolls the whole document (task 9.3).
  let (w, act) := View.wheelStep (if isY then s.wheel.y else s.wheel.x) now
    (View.wheelPixels kind d view) (isY && s.scroll == .page) top view region
    (View.wheelThreshold kind view (region - view))
  let save (w : View.Wheel) : IO Unit :=
    st.modify fun s => { s with wheel := if isY then { s.wheel with y := w } else { s.wheel with x := w } }
  match act with
  | .none => save w
  | .scrollTo p =>
    save w
    -- Tk rounds `moveto` to the nearest pixel, so the fraction p / region lands on p.
    discard <| run [".c", if isY then "yview" else "xview", "moveto",
      fmtFracFine ((p : Rat) / (max region 1 : Nat))]
    viewChanged st
  | .next =>
    let q := View.nextPage s.spread s.pageCount s.page
    if q != s.page then
      goTo st q .top
      save w
    else save { w with acc := 0 }
  | .prev =>
    let q := View.prevPage s.spread s.page
    if q != s.page then
      goTo st q .bottom
      save w
    else save { w with acc := 0 }

/-- Rotates the view by a quarter turn (`cw` or `ccw`), keeping the window centre's page
point at the centre. -/
def rotate (st : IO.Ref State) (cw : Bool) : IO Unit := do
  let s ← st.get
  if s.doc.isNone then return
  let (wx, wy) := anchorPos s none
  anchorAt st wx wy
  st.modify fun s => { s with rot := if cw then View.rotCw s.rot else View.rotCcw s.rot }
  refresh st

/-- Handles `viewMode scroll KEY` / `viewMode spread KEY` (task 9.3; View menu and the overflow
menu's radio entries) and `viewMode view KEY` (task 9.r4, the toolbar's view-mode drop-down,
`Toolbar.ViewChoice.modes`): switches the scroll mode (`page`, `vertical`), the spread mode
(`none`, `odd`, `even`) or both, keeping the current page, shown from its top. The radio
variables (`Menu.scrollVar`, `Menu.spreadVar`, the drop-down's `::safepdf::viewSel` with its
icon) and `::safepdf::continuous` (which makes key scrolling report `viewChanged`) are set to
the state whatever happens, so the View menu, the `»` menu and the drop-down agree. -/
def setViewMode (st : IO.Ref State) (what key : String) : IO Unit := do
  let s ← st.get
  let s' := match what with
    | "scroll" => (View.ScrollMode.ofKey key).map fun m => { s with scroll := m }
    | "spread" => (View.SpreadMode.ofKey key).map fun m => { s with spread := m }
    | "view" => (Toolbar.ViewChoice.ofKey key).map fun (c : Toolbar.ViewChoice) =>
      let (sc, sp) := c.modes s.spread
      { s with scroll := sc, spread := sp }
    | _ => none
  let changed := match s' with
    | some s' => s.doc.isSome && (s'.scroll != s.scroll || s'.spread != s.spread)
    | none => false
  if changed then
    if let some s' := s' then
      st.modify ({ · with scroll := s'.scroll, spread := s'.spread, pending := some .top,
                          wheel := {} })
  let s ← st.get
  discard <| run ["set", Menu.scrollVar, s.scroll.key]
  discard <| run ["set", Menu.spreadVar, s.spread.key]
  discard <| run ["set", "::safepdf::continuous", if s.scroll == .vertical then "1" else "0"]
  showViewChoice s s.doc.isSome
  if changed then refresh st

/-! ## Saving (task 9.5c) -/

/-- After an edit of the marks (task 9.5g): when saved marks changed, renders the pages again
from the preview (`Save.preview`: the document as the next save writes those edits); else
from the document itself. On a preview error the pages stay as they are and the status line
says why (Save would report the same error). Returns whether the preview changed. -/
def updatePreview (st : IO.Ref State) : IO Bool := do
  let s ← st.get
  let some doc := s.doc | return false
  let had := s.view.isSome
  let edited := !s.marks.changedSaved.isEmpty || !s.marks.deletedSaved.isEmpty
  if !edited && !had then return false
  let date ← Save.nowDate
  let mut v : Option Doc := none
  if edited then
    match ← IO.lazyPure fun _ => Save.preview limits doc s.marks date with
    | .ok v' => v := v'
    | .error e =>
      setStatus s!"cannot show the change of a saved mark: {e}"
      return false
  st.modify fun s => { s with view := v, gen := s.gen + 1, cache := ({ budget := Budget.ceilings.cacheBytes } : View.Cache),
                              shown := none, srcSerial := s.srcSerial + 1 }
  for (p, _) in (← st.get).photos do dropPhoto st p
  refresh st
  return true

/-- Asks `msg` in a Tk message box of `type` (`yesno`, `yesnocancel`) titled `title`
(`::safepdf::ask`; smoke mode answers with `::safepdf::autoAnswer`). Returns `yes`, `no` or
`cancel`. -/
def ask (type title msg : String) : IO String := run ["::safepdf::ask", type, title, msg]

/-- Whether two paths name the same file (resolved when they exist, else compared as text). -/
def samePath (a b : String) : IO Bool := do
  let r (p : String) : IO String := do
    try return (← IO.FS.realPath p).toString catch _ => return p
  return (← r a) == (← r b)

/-- Whether this session wrote `path` (a further save into it asks nothing). -/
def isOwn (st : IO.Ref State) (path : String) : IO Bool := do
  for f in (← st.get).ownFiles do
    if ← samePath f path then return true
  return false

/-- Whether the window runs on aqua (macOS): the dialogs' button order follows it. -/
def isAqua : IO Bool := return (← run ["tk", "windowingsystem"]) == "aqua"

/-- Asks `msg` in the three-way dialog `::safepdf::choose` titled `title` with `buttons`
(key, label; display order from `Save.*Buttons`), `dflt` the default key, `cancel` the key of
Escape and the dialog's close button; smoke mode answers with `::safepdf::autoAnswer`. Returns
the chosen key. -/
def choose (title msg dflt : String) (buttons : List (String × String)) : IO String :=
  run (["::safepdf::choose", title, msg, dflt, "cancel"] ++ buttons.flatMap fun (k, l) => [k, l])

/-- Before the rename of a save (task 9.r2): copies the permissions of `target`, when it exists,
onto the temporary file `tmp` (Tcl `file attributes -permissions`; Unix only), so an
overwritten file keeps its mode. A failure aborts the save (the temporary file is removed). -/
def keepPermissions (target : String) (tmp : System.FilePath) : IO Unit := do
  if (← run ["set", "::tcl_platform(platform)"]) != "unix" then return
  if !(← System.FilePath.pathExists target) then return
  let mode ← run ["file", "attributes", target, "-permissions"]
  discard <| run ["file", "attributes", tmp.toString, "-permissions", mode]

/-- **Revision-retention notice** (task 12.5): appended to the status of a Save that deleted
`n` saved marks. The update is incremental — the original bytes stay a prefix of the file
(C7) — so the earlier revision, with the deleted annotations, is still inside the written
file and can be recovered from it; a user deleting a mark to remove what it says must know.
Empty when nothing saved was deleted. -/
def retentionNote (n : Nat) : String := Save.retentionNote n

#guard retentionNote 0 == ""
#guard retentionNote 2 == "; note: the 2 deleted mark(s) are still in the file's earlier \
  revision (Save only appends an update) and can be recovered from it"

/-- After a save wrote `o.path`: remembers it as written by this session (a further Save into
it asks nothing), reopens it on page `page` (the viewer goes on with the new bytes, so a second
Save works) and reports — with the revision-retention notice (`retentionNote`, task 12.5) when
saved marks were deleted. -/
def afterWrite (st : IO.Ref State) (page : Nat) (o : Save.Outcome) : IO Unit := do
  let deleted := (← st.get).marks.deletedSaved.length
  let own := (← st.get).ownFiles
  st.modify ({ · with ownFiles := o.path :: own.filter (· != o.path) })
  -- Task 9.r8: the reopen keeps the user's view (the document's open settings are not
  -- applied again).
  openFile st o.path (keepView := true)
  goTo st page
  setStatus (Save.savedStatus o.path o.marks o.appended o.total o.notes deleted)

/-- Writes the document with its unsaved marks to another file `target` (Save As…;
`Save.write`: the incremental update, checked by a strict reopen before anything is written,
then an atomic rename keeping the permissions of a file it replaces) and opens the written
file on the same page. Errors (an encrypted or repaired document, a failed check, a write
error) go to the status line; returns whether the file was written. -/
def saveTo (st : IO.Ref State) (target : String) : IO Bool := do
  let s ← st.get
  let some doc := s.doc | return false
  -- Task 12.3b: the output (original bytes plus the update) is reserved in the work pool.
  withOutput st (Save.outputEstimate doc s.marks)
    (fun m => do setStatus s!"cannot save to {baseName target}: {m}"; return false) do
  setStatus s!"saving to {target}..."
  match ← Save.write limits doc s.marks target (keepPermissions target) with
  | .error e =>
    setStatus s!"cannot save to {baseName target}: {e}"
    return false
  | .ok o =>
    afterWrite st s.page o
    return true

/-- **Save into the opened file** `path` (task 9.r2, Decision 2026-11-23): builds and checks
the bytes first (`Save.build`: original bytes a prefix, strict reopen, read-back — an
encrypted or repaired document is refused here, before any question); refuses a read-only
file or folder (`Save.writeProblem`); refuses when the file on disk no longer holds the bytes
the document was opened from (`Save.diskState`, checked before the question and again just
before writing) and then offers Save As…; with `ask` asks Overwrite / Save As… / Cancel; then
writes atomically (`Save.writeAtomic` to the resolved path, so a symbolic link stays one,
permissions kept) and reopens in place. Returns `some saved`, or `none` when the user chose
Save As…. -/
def overwriteInto (st : IO.Ref State) (path : String) (ask : Bool) : IO (Option Bool) := do
  let s ← st.get
  let some doc := s.doc | return some false
  let name := baseName path
  -- Task 12.3b: the output (original bytes plus the update) is reserved in the work pool.
  withOutput st (Save.outputEstimate doc s.marks)
    (fun m => do setStatus s!"cannot save to {name}: {m}"; return some false) do
  match ← Save.buildNow limits doc s.marks with
  | .error e =>
    setStatus s!"cannot save to {name}: {e}"
    return some false
  | .ok (bytes, got, n) =>
    let real ← try pure (← IO.FS.realPath path).toString catch _ => pure path
    let dir := match (real : System.FilePath).parent with
      | some d => if d.toString.isEmpty then "." else d.toString
      | none => "."
    if ← System.FilePath.pathExists real then
      let fw := (← run ["file", "writable", real]) == "1"
      let dw := (← run ["file", "writable", dir]) == "1"
      if let some p := Save.writeProblem name fw dw then
        setStatus s!"cannot save: {p}"
        return some false
    let disk : IO Save.DiskState := Save.diskStateAt doc.file.bytes real
    let changed (ds : Save.DiskState) : IO (Option Bool) := do
      let a ← choose "File changed on disk" (Save.changedQuestion name ds) "saveas"
        (Save.changedButtons (← isAqua))
      if a == "saveas" then return none
      setStatus s!"not saved: {name} changed on disk since it was opened; nothing was written \
        (Save As… writes a new file)"
      return some false
    let d0 ← disk
    if d0 != .same then return ← changed d0
    if ask then
      let a ← choose "Save" (Save.overwriteQuestion name s.marks.pending) "overwrite"
        (Save.overwriteButtons (← isAqua))
      if a == "saveas" then return none
      if a != "overwrite" then
        setStatus "save cancelled"
        return some false
    let d1 ← disk
    if d1 != .same then return ← changed d1
    setStatus s!"saving to {path}..."
    try
      Save.writeAtomic real bytes (keepPermissions real)
    catch e =>
      setStatus s!"cannot save to {name}: {Save.oneLine (toString e)}"
      return some false
    afterWrite st s.page { path, marks := n, appended := bytes.size - doc.file.bytes.size,
                           size := bytes.size, total := got.length,
                           notes := Save.notesFor limits doc n }
    return some true

/-- **Save to library** (task 10.1b, Save in bib-lean's reader mode): `Save.build`'s bytes (the
incremental update, checked by a strict reopen and read-back) go to the library
(`Library.onSaved`: bib-lean's `PUT`, which keeps the previous file) instead of a local file —
nothing is written to disk; then the window reopens those bytes from memory on the same page
(the marks become saved, drawn by the renderer) and reports the marks
(`Library.onMarksChanged`, posted after the file). Errors go to the status line. -/
def saveToLibrary (st : IO.Ref State) (lib : Library) (name : String) (doc : Doc) : IO Bool := do
  let s ← st.get
  -- Task 12.3b: the output (original bytes plus the update) is reserved in the work pool.
  withOutput st (Save.outputEstimate doc s.marks)
    (fun m => do setStatus s!"cannot save to the library: {m}"; return false) do
  setStatus "saving to the library..."
  match ← Save.buildNow limits doc s.marks with
  | .error e =>
    setStatus s!"cannot save to the library: {e}"
    return false
  | .ok (bytes, got, n) =>
    lib.onSaved bytes
    openBytes st name bytes (keepView := true)
    goTo st s.page
    marksChanged st
    let appended := bytes.size - doc.file.bytes.size
    setStatus s!"saved {n} new, changed or deleted mark(s) to the library ({appended} bytes \
      appended; {got.length} marks in its file){Save.notesText (Save.notesFor limits doc n)}\
      {retentionNote s.marks.deletedSaved.length}"
    return true

/-- The directory of `path` for a file dialog (`.` when it has none). -/
def dirOf (path : String) : String :=
  match (path : System.FilePath).parent with
  | some d => if d.toString.isEmpty then "." else d.toString
  | none => "."

#guard dirOf "paper.pdf" == "." && dirOf "/tmp/x/paper.pdf" == "/tmp/x"

/-- Whether the file dialogs take the aqua form (task 9.r6): the platform the keys were set
up for (`platformRef`, which the smoke test can force to aqua on X11). -/
def onAqua : IO Bool := return (← platformRef.get) == .aqua

/-- The folder a file dialog for the document `path` starts in (task 9.r6, `Save.dialogDir`):
the folder of the opened file when it is one on disk and that folder exists (and, with
`write`, is writable), else the home folder (a document from memory has no folder). -/
def dialogDirOf (s : State) (path : String) (write : Bool := true) : IO String := do
  let dir := dirOf path
  let mut usable := false
  if !s.inMemory then
    let isDir := (← run ["file", "isdirectory", dir]) == "1"
    let w := (← run ["file", "writable", dir]) == "1"
    usable := isDir && (w || !write)
  return Save.dialogDir dir usable (← IO.getEnv "HOME")

/-- The file a Save As… or Export dialog returned, made ready to write (task 9.r6): the
type's extension `ext` added when missing (`Save.withExt`; when that names an existing file,
which the dialog did not confirm, the user is asked first), then refused with a status
message when it is a folder, a read-only file, in a folder that is not writable or —
`export` — the opened document itself (`Save.targetProblem`). `none`: nothing is written. -/
def checkTarget (st : IO.Ref State) (chosen ext : String) (isExport : Bool) :
    IO (Option String) := do
  let s ← st.get
  let what := if isExport then "export" else "save"
  let target := Save.withExt chosen ext
  let name := baseName target
  if target != chosen && (← System.FilePath.pathExists target) then
    if (← ask "yesno" (if isExport then "Export annotations" else "Save As")
        (Save.replaceQuestion name)) != "yes" then
      setStatus s!"{what} cancelled"
      return none
  let isDir ← System.FilePath.isDir target
  let ex ← System.FilePath.pathExists target
  let fw := ex && (← run ["file", "writable", target]) == "1"
  let dw := (← run ["file", "writable", dirOf target]) == "1"
  let mut opened := false
  if isExport && !s.inMemory then
    if let some pdf := s.path then opened ← samePath target pdf
  match Save.targetProblem name isDir ex fw dw opened with
  | some p =>
    setStatus s!"cannot {what}: {p}"
    return none
  | none => return some target

/-- One round of Save As…: asks for a file (`tk_getSaveFile`, which confirms replacing an
existing file; options `Save.saveDialogOptions`, starting in `dialogDirOf`), proposing
`Save.defaultTarget` (`STEM-annotated.pdf`), checks it (`checkTarget`: `.pdf` added, folder /
read-only / unwritable folder refused; task 9.r6) and writes the unsaved marks there (a plain
copy when there are none). The opened file itself needs an explicit yes
(unless this session wrote it) and goes through `overwriteInto` (changed-on-disk check);
`none` when that asks for another file. For a library's document (task 10.1b) it writes a
local copy and stays on the library's document. -/
def saveAsOnce (st : IO.Ref State) : IO (Option Bool) := do
  let s ← st.get
  let (some path, some _) := (s.path, s.doc) | return some false
  let fp : System.FilePath := Save.defaultTarget path
  let chosen ← run (["::safepdf::askSavePath", ← dialogDirOf s path,
    fp.fileName.getD "document.pdf"] ++ Save.saveDialogOptions (← onAqua) "PDF files" "pdf")
  if chosen.isEmpty then
    setStatus "save cancelled"
    return some false
  let some chosen ← checkTarget st chosen "pdf" false | return some false
  -- A library's document (task 10.1b): a local copy; the window stays on the library's
  -- document and its marks stay unsaved there (Save sends them to the library).
  if s.library.isSome then
    let some doc := s.doc | return some false
    let r ← withOutput st (Save.outputEstimate doc s.marks) (fun m => pure (.error m))
      (Save.write limits doc s.marks chosen (keepPermissions chosen))
    match r with
    | .error e =>
      setStatus s!"cannot save to {baseName chosen}: {e}"
      return some false
    | .ok o =>
      setStatus s!"saved a local copy with {o.total} mark(s) to {o.path}; the library's file \
        is unchanged (Save to library sends the marks there){retentionNote s.marks.deletedSaved.length}"
      return some true
  if !s.inMemory && (← samePath chosen path) then
    if !(← isOwn st chosen) then
      let a ← ask "yesno" "Save As" (Save.openedOverwriteQuestion (baseName path))
      if a != "yes" then
        setStatus "save cancelled"
        return some false
    return ← overwriteInto st path (ask := false)
  return some (← saveTo st chosen)

/-- **Save As…** (Ctrl+Shift+S, File → Save As…): `saveAsOnce`, asked again (at most three
times) while the chosen file is the opened one and it changed on disk. Returns whether the
marks were written. -/
def saveAs (st : IO.Ref State) : IO Bool := do
  for _ in [0:3] do
    if let some r ← saveAsOnce st then return r
  return false

/-- **Save** (Ctrl+S, File → Save, the toolbar's Save; task 9.r2): `Save.route` — nothing to
do without unsaved marks; a library's document goes to the library; a document opened from
memory asks for a file (Save As…); otherwise the marks are written **into the opened file**
(`overwriteInto`), asking Overwrite / Save As… / Cancel before the first overwrite of this
session (`confirmed`: the unsaved-changes prompt already said so). Returns whether the marks
are saved afterwards. -/
def save (st : IO.Ref State) (confirmed : Bool := false) : IO Bool := do
  let s ← st.get
  let (some path, some doc) := (s.path, s.doc) | return false
  match Save.route s.marks.dirty s.library.isSome s.inMemory (confirmed || (← isOwn st path)) with
  | .nothing =>
    setStatus "no unsaved marks: nothing to save"
    return true
  | .library =>
    match s.library with
    | some lib => saveToLibrary st lib path doc
    | none => return false
  | .saveAs => saveAs st
  | .overwrite q =>
    match ← overwriteInto st path q with
    | some r => return r
    | none => saveAs st

/-- **The unsaved-changes prompt** (task 9.r2) before `what` (closing, quitting, opening
another file — every way a document goes away): with unsaved marks asks Save / Don't Save /
Cancel (`Save.unsavedQuestion`, `Save.unsavedButtons`: the macOS order on aqua). Save saves
(into the opened file without a second question, to the library in bib-lean mode, or through
Save As… for a document from memory); a failed or cancelled save and Cancel abort `what`
(`Save.closeGoesOn`). Returns whether to go on. Nothing is ever saved without this answer. -/
def confirmDiscard (st : IO.Ref State) (what : String) : IO Bool := do
  let s ← st.get
  let (some path, some _) := (s.path, s.doc) | return true
  if !s.marks.dirty then return true
  let name := s.titleOverride.getD (baseName path)
  let own ← isOwn st path
  let msg := Save.unsavedQuestion name what s.marks.pending s.library.isSome s.inMemory (!own)
  let ans := Save.onUnsavedAnswer (← choose "Unsaved marks" msg "save" (Save.unsavedButtons (← isAqua)))
  let saved ← if ans == some true then save st (confirmed := true) else pure false
  let go := Save.closeGoesOn true ans saved
  if !go then
    if ans.isNone then setStatus s!"{what} cancelled: there are unsaved marks"
    else setStatus s!"{← run [".status", "cget", "-text"]}; {what} cancelled"
  return go

/-! ## XFDF import and export (task 9.11) -/

/-- The proposed export file of the PDF `path`: `STEM.xfdf` next to it. -/
def xfdfTarget (path : String) : String := Xfdf.exportTarget path

#guard xfdfTarget "/tmp/x/paper.pdf" == "/tmp/x/paper.xfdf" && xfdfTarget "a.b.PDF" == "a.b.xfdf"

/-- The status line after an import of `name`: added, already present and skipped counts, and
the first skipped annotation's reason. -/
def importStatus (name : String) (added dups : Nat) (rep : Xfdf.Report) : String :=
  Xfdf.importStatus name added dups rep.skippedCount
    (rep.skipped.head?.map fun k => (k.element, k.reason))

#guard importStatus "a.xfdf" 3 1 {} == "a.xfdf: 3 imported, 1 already present, 0 skipped"

/-- **Import annotations…** (File menu, `»` menu): reads the XFDF file `path` (else asks for
one, `::safepdf::askXfdfOpen`) with the document's page count as bound, adds its marks to the
store as unsaved marks (`Xfdf.importItems`: marks already present are not added again) and
redraws. A refused or unreadable file only shows its error in the status line. -/
def importXfdf (st : IO.Ref State) (path : Option String := none) : IO Unit := do
  let s ← st.get
  let (some pdf, some _) := (s.path, s.doc) | return
  let path ← match path with
    | some p => pure p
    | none => run ["::safepdf::askXfdfOpen", ← dialogDirOf s pdf (write := false)]
  if path.isEmpty then
    setStatus "import cancelled"
    return
  match ← Xfdf.readFile {} path (pages := some s.pageCount) with
  | .error e => setStatus s!"cannot import {baseName path}: {e}"
  | .ok rep =>
    let s ← st.get
    let (marks, ids, dups) := Xfdf.importItems s.marks rep.items
    st.modify ({ · with marks })
    if !ids.isEmpty then
      marksChanged st
      if !(← updatePreview st) then repaint st
    setStatus (importStatus (baseName path) ids.length dups rep)

/-- **Export annotations…** (File menu, `»` menu): writes every mark of the store (saved or
not; `Xfdf.toXfdf`, dated now, `<f href>` the PDF's file name) to `path` (else asks,
`::safepdf::askXfdfSave`, proposing `xfdfTarget`) through `Save.writeAtomic`, after
`checkTarget` (`.xfdf` added; never onto the opened PDF, a folder or a read-only file; task
9.r6), keeping the permissions of a file it replaces. Errors go to the status line. -/
def exportXfdf (st : IO.Ref State) (path : Option String := none) : IO Unit := do
  let s ← st.get
  let (some pdf, some doc) := (s.path, s.doc) | return
  let path ← match path with
    | some p => pure p
    | none =>
      let fp : System.FilePath := xfdfTarget pdf
      run (["::safepdf::askXfdfSave", ← dialogDirOf s pdf, fp.fileName.getD "annotations.xfdf"]
        ++ Save.saveDialogOptions (← onAqua) "XFDF" "xfdf")
  if path.isEmpty then
    setStatus "export cancelled"
    return
  let some path ← checkTarget st path "xfdf" true | return
  -- Task 12.3b: the text (and its UTF-8 bytes) is reserved in the work pool first.
  withOutput st (2 * Xfdf.exportEstimate s.marks)
    (fun m => setStatus s!"cannot export to {baseName path}: {m}") do
  let xml := Xfdf.toXfdf s.marks (Save.pageBox doc) (← Save.nowDate) (some (baseName pdf))
  try
    Save.writeAtomic path xml.toUTF8 (keepPermissions path)
    setStatus s!"exported {s.marks.marks.size} mark(s) to {baseName path}"
  catch e => setStatus s!"cannot export to {baseName path}: {Save.oneLine (toString e)}"

/-- **Save attachment as…** (task 9.r10; double-click, Return or the context menu in the
attachments panel): decodes attachment `i` (`Core.Doc.Attachments.decode`: the filter chain
under the viewer's limits; an error is reported and nothing is asked; the result is kept for
its row), asks for a file (`::safepdf::askAttachSave`: `tk_getSaveFile` without `-filetypes`,
starting in the opened file's folder with the sanitized `Attachment.fileName`; Tk confirms
replacing a file), refuses a folder, the opened PDF, a read-only file and an unwritable folder
(`Attach.targetProblem`, the rules of task 9.r6) and writes exactly the decoded bytes
atomically (`Save.writeAtomic`). The attachment is never opened, launched or executed. -/
def saveAttachment (st : IO.Ref State) (i : Nat) : IO Unit := do
  let s ← st.get
  let (some doc, some a) := (s.doc, s.attList[i]?) | return
  if let some p := a.problem then
    setStatus s!"cannot save attachment {a.name}: {p.message}"
    return
  let bytes ← match ← IO.lazyPure fun _ => Core.Doc.Attachments.decode doc limits a with
    | .ok b =>
      attRecord st i (.decoded b.size)
      pure b
    | .error e =>
      attRecord st i (.failed (renderError e))
      setStatus s!"cannot save attachment {a.name}: {renderError e}"
      return
  let dir ← dialogDirOf s (s.path.getD "")
  let chosen ← run ["::safepdf::askAttachSave", dir, a.fileName]
  if chosen.isEmpty then
    setStatus "save attachment cancelled"
    return
  let name := baseName chosen
  let isDir ← System.FilePath.isDir chosen
  let ex ← System.FilePath.pathExists chosen
  let fw := ex && (← run ["file", "writable", chosen]) == "1"
  let dw := (← run ["file", "writable", dirOf chosen]) == "1"
  let opened ← match s.path with
    | some p => if s.inMemory then pure false else samePath chosen p
    | none => pure false
  match Attach.targetProblem name isDir ex fw dw opened with
  | some p => setStatus s!"cannot save attachment: {p}"
  | none =>
    try
      Save.writeAtomic chosen bytes (keepPermissions chosen)
      setStatus s!"saved attachment {a.name} ({bytes.size} bytes) to {name}"
    catch e => setStatus s!"cannot save attachment to {name}: {Save.oneLine (toString e)}"

/-- The `tk_getOpenFile` dialog (after the unsaved-marks question), starting in the opened
file's folder; opens the chosen file (nothing when cancelled). -/
def openDialog (st : IO.Ref State) : IO Unit := do
  if !(← confirmDiscard st "opening another file") then return
  let s ← st.get
  -- Start in the opened file's folder (task 9.r6); without a file Tk's own choice (the last
  -- folder of this session, else the working directory).
  let dir ← match s.path with
    | some p => pure ["-initialdir", ← dialogDirOf s p (write := false)]
    | none => pure []
  let path ← run (["tk_getOpenFile", "-parent", ".", "-title", "Open PDF"] ++ dir ++
    ["-filetypes", "{{PDF files} {.pdf .PDF}} {{All files} *}"])
  if path.isEmpty then setStatus "open cancelled"
  else openFile st path

/-! ## Menubar (task 9.1) -/

/-- Closes the document (File → Close, Ctrl+W): the window stays, empty, as after starting
without a file. A library's document is flushed first (`Library.flush`) and the library let go
(task 10.1b). -/
def closeFile (st : IO.Ref State) : IO Unit := do
  -- A library's document (task 10.1b): send what is pending now, then let the library go.
  if let some l := (← st.get).library then
    unless ← l.flush do setStatus "the library did not answer in time; still trying"
    setSaveLabels false
  st.modify fun s => { s with path := none, inMemory := false, titleOverride := none,
                              library := none, doc := none, view := none, page := 0, shown := none,
                              gen := s.gen + 1, cache := ({ budget := Budget.ceilings.cacheBytes } : View.Cache), pending := none,
                              texts := #[], sel := none, pressPt := none, query := #[],
                              hit := none, labels := #[], outline := #[], links := #[],
                              hover := none, history := {}, toggleShown := none,
                              marks := {}, markSel := none, markHist := {}, slots := #[],
                              layoutKey := none, ownTop := none,
                              ui := { s.ui with tool := false, popover := false,
                                                picker := false },
                              bubble := none, pickerAt := none, bubblePress := false,
                              ocCfg := none, oc := none, lyRows := [] }
  workerStop st
  fillLayers st
  discard <| run ["pack", "forget", ".find", ".goto"]
  discard <| run ["destroy", ".note"]
  discard <| run ["::safepdf::popHide"]
  discard <| run ["::safepdf::btnToggled", ".bar.highlight", "0"]
  discard <| run ["::safepdf::btnToggled", ".bar.select",
    if Toolbar.Mode.of (← st.get).ui == .select then "1" else "0"]
  discard <| run ["set", Menu.hlToolVar, "0"]
  fillOutline st
  showOutline st false
  clearThumbs st
  discard <| run [".c", "configure", "-cursor", ""]
  refresh st
  setStatus (← keyText "No file. Press Ctrl+O or Open... to choose a PDF.")

/-- Tk image of the swatch of colour `c` (a 14 px square, task 9.4). -/
def swatch (c : Marks.Color) : String := s!"::safepdf::sw::{c.name}"

/-- Creates the colour menu `path` (task 9.4): one radio entry per `Marks.Color` with its
swatch, on the shared variable `Menu.colorVar`, running `Menu.colorScript`. -/
def colorMenu (path : String) : IO Unit := do
  discard <| run ["menu", path, "-tearoff", "0"]
  for c in Marks.Color.all do
    discard <| run [path, "add", "radiobutton", "-label", c.label, "-image", swatch c,
      "-compound", "left", "-variable", Menu.colorVar, "-value", c.name,
      "-command", Menu.colorScript]

/-- Sets the application and window icon (task 9.r3): the embedded PNGs of `Icons.all`
become photo images `::safepdf::iconN` (Tk 9 reads PNG natively) and
`wm iconphoto . -default` gets them largest first (X11: `_NET_WM_ICON` with every size;
Windows: the window icons; macOS: the first image becomes the Dock and dialog icon of the
unbundled app). Embedded rather than read from `docs/branding/` so that an installed
`viewer` does not need the source tree (about 160 KB of base64 in the binary). A failure
only leaves Tk's default icon. -/
def setIcon : IO Unit := do
  try
    for (n, d) in Icons.all do
      discard <| run ["image", "create", "photo", s!"::safepdf::icon{n}", "-format", "png",
        "-data", d]
    discard <| run (["wm", "iconphoto", ".", "-default"] ++
      Icons.all.map fun (n, _) => s!"::safepdf::icon{n}")
  catch e => IO.eprintln s!"viewer: no icon: {e}"

/-- Builds the menubar `.menubar` from `Menu.menubar` (every word a literal through
`Tcl.quote`; the `-command` scripts are the model's constants) and attaches it to the main
window; then the mark entries of the context menu (`Menu.popupMarks`, task 9.4). -/
def buildMenus : IO Unit := do
  let plat ← platformRef.get
  for c in Marks.Color.all do
    discard <| run ["image", "create", "photo", swatch c, "-width", "14", "-height", "14"]
    discard <| run [swatch c, "put", "#8f8f9d", "-to", "0", "0", "14", "14"]
    discard <| run [swatch c, "put", c.hex, "-to", "1", "1", "13", "13"]
  discard <| run ["menu", Menu.barPath, "-tearoff", "0"]
  for m in Menu.menubar do
    discard <| run ["menu", m.path, "-tearoff", "0"]
    discard <| run [Menu.barPath, "add", "cascade", "-label", m.label, "-underline",
      toString m.underline, "-menu", m.path]
    for e in m.entries do
      match e with
      | .sep => discard <| run [m.path, "add", "separator"]
      | .colors path =>
        colorMenu path
        discard <| run [m.path, "add", "cascade", "-label", Menu.colorsLabel, "-menu", path]
      | .cmd c =>
        match c.radio? with
        | some (var, val) =>
          discard <| run [m.path, "add", "radiobutton", "-label", c.label, "-variable", var,
            "-value", val, "-underline", toString c.underline, "-command", c.script]
        | none =>
          discard <| run [m.path, "add", "command", "-label", c.label, "-accelerator", c.accelOn plat,
            "-underline", toString c.underline, "-command", c.script]
      | .check c var =>
        discard <| run [m.path, "add", "checkbutton", "-label", c.label, "-accelerator", c.accelOn plat,
          "-underline", toString c.underline, "-variable", var, "-onvalue", "1",
          "-offvalue", "0", "-command", c.script]
  discard <| run [".", "configure", "-menu", Menu.barPath]
  -- After Copy, Select all, Find… (entries 0–2 of the setup script's `.pop`).
  for (i, e) in (List.range Menu.popupMarks.length).zip Menu.popupMarks do
    let ix := toString (Menu.popFirst + i)
    match e with
    | .sep => discard <| run [Menu.popPath, "insert", ix, "separator"]
    | .colors path =>
      colorMenu path
      discard <| run [Menu.popPath, "insert", ix, "cascade", "-label", Menu.popColorsLabel,
        "-menu", path]
    | .cmd c | .check c _ =>
      discard <| run [Menu.popPath, "insert", ix, "command", "-label", c.label,
        "-accelerator", c.accelOn plat, "-command", c.popScript]

/-- Builds the toolbar from `Toolbar.layout` (task 9.7): icon buttons (`::safepdf::iconButton`
with the model's constant icon name, tooltip and script), separators, the page field and the
zoom drop-down (its menu `.zoommenu` lists `ZoomChoice.presets` as radio entries on
`::safepdf::zoomSel`), the view-mode drop-down (task 9.r4: `.bar.vmode`, menu `.viewmenu`
with `ViewChoice.all` as radio entries on `::safepdf::viewSel`), and the overflow menu `.more` (`Toolbar.overflow`). -/
def buildToolbar : IO Unit := do
  let plat ← platformRef.get
  for (g, items) in Toolbar.layout do
    for it in items do
      match it with
      | .button b =>
        discard <| run ["::safepdf::iconButton", b.path, b.icon, plat.keyText b.tip, b.script]
        discard <| run ["::safepdf::barPack", b.path, g, "-padx", "2", "-pady", "4"]
      | .sep w =>
        discard <| run ["::safepdf::vsep", w]
        discard <| run ["::safepdf::barPack", w, g, "-padx", "2"]
      | .pageField => discard <| run ["::safepdf::pageField"]
      | .zoomBox => discard <| run ["::safepdf::zoomBox"]
      | .viewBox => discard <| run ["::safepdf::viewBox"]
  -- Select text is the default tool (task 10.8, `Toolbar.Mode.of_default`).
  discard <| run ["::safepdf::btnToggled", ".bar.select", "1"]
  -- The sidebar's view buttons (task 9.r9, `Sidebar.panels`; packed per document by
  -- `syncPanelButtons`).
  for i in Sidebar.panels do
    discard <| run ["::safepdf::iconButton", i.button, i.icon, i.tip,
      s!"::safepdf::emit panel {i.key}", "body"]
  for c in Toolbar.ViewChoice.all do
    discard <| run [".viewmenu", "add", "radiobutton", "-label", c.label, "-value", c.key,
      "-variable", "::safepdf::viewSel",
      "-command", "::safepdf::emit viewMode view $::safepdf::viewSel"]
  for c in Toolbar.ZoomChoice.presets do
    discard <| run [".zoommenu", "add", "radiobutton", "-label", c.label, "-value", c.key,
      "-variable", "::safepdf::zoomSel",
      "-command", "::safepdf::emit zoom choose $::safepdf::zoomSel"]
  for e in Toolbar.overflow do
    match e with
    | none => discard <| run [Toolbar.morePath, "add", "separator"]
    | some c =>
      match c.radio? with
      | some (var, val) =>
        discard <| run [Toolbar.morePath, "add", "radiobutton", "-label", c.label, "-variable",
          var, "-value", val, "-command", c.script]
      | none =>
        discard <| run [Toolbar.morePath, "add", "command", "-label", c.label, "-accelerator",
          c.accelOn plat, "-command", c.script]

/-- The part of the state the enabled rules look at. -/
def menuCtx (s : State) : Menu.Ctx :=
  { hasDoc := s.doc.isSome && s.pageCount > 0, page := s.page, pages := s.pageCount,
    hasSel := s.sel.isSome, hasMark := s.markSel.isSome, hasOutline := !s.outline.isEmpty,
    canBack := !s.history.back.isEmpty, canForward := !s.history.fwd.isEmpty,
    dirty := s.doc.isSome && s.marks.dirty,
    canUndo := s.markHist.canUndo, canRedo := s.markHist.canRedo,
    onFirst := View.spreadOf s.spread s.page == 0,
    onLast := s.pageCount > 0 &&
      View.spreadOf s.spread s.page == View.spreadOf s.spread (s.pageCount - 1) }

/-- Sets the `-state` of every menubar entry, overflow-menu entry and toolbar button whose
enabled state (`Toolbar.states`) changed since the last call, and shows or hides the sidebar
toggle (`Sidebar.toggleVisible`). Runs after every event. Does nothing once the main window is
gone (the menubar command deleted): a handler that destroyed `.` (a smoke case ending, a quit) is followed by this sync, and
configuring the destroyed menubar would only print `invalid command name ".menubar.edit"`
(task 10.20). -/
def syncMenus (st : IO.Ref State) : IO Unit := do
  -- Tk deletes the widget commands (`.menubar…`) with the main window.
  if (← run ["info", "commands", Menu.barPath]) == "" then return
  let s ← st.get
  let c := menuCtx s
  let now := Toolbar.states c
  let old := if s.menuStates.length == now.length then s.menuStates else now.map (!·)
  for ((t, on), was) in (Toolbar.targets.zip now).zip old do
    if on != was then
      match t with
      | .entry p i =>
        discard <| run [p, "entryconfigure", toString i, "-state", if on then "normal" else "disabled"]
      | .button w => discard <| run ["::safepdf::btnState", w, if on then "normal" else "disabled"]
  let vis := Sidebar.toggleVisible c.hasDoc
  if s.toggleShown != some vis then
    discard <| run ["::safepdf::showToggle", if vis then "1" else "0"]
  let title := s.title
  if title != s.titleShown then discard <| run ["wm", "title", ".", title]
  st.modify ({ · with menuStates := now, toggleShown := some vis, titleShown := title })
  syncThumbs st

/-! ## Links, jumps, history, go to page (task 8.2d) -/

/-- A shown string from the worker that must be printable ASCII (`lo` = 0x21 for a URI as
`Links.uriText` makes it, 0x20 for an action name): kept when it is, else percent-encoded again
(`Links.uriText`), so a misbehaving worker cannot put control or bidi characters in the status
line or the URI dialog. An honest worker's strings are kept as they are. -/
def asciiOr (lo : Nat) (u : String) : String :=
  if u.toList.all (fun c => lo ≤ c.toNat && c.toNat ≤ 0x7E) then u
  else Links.uriText u.toUTF8.toList

/-- A link from the worker's reply (task 12.2d, `Worker.Protocol.ViewLink`) as a link of this
process: strings re-checked (`asciiOr`, `safeText`), a jump to a page outside the document is
`badPage`. Equal to `Links.pageLinks`' link for an honest worker. -/
def linkOfWire (n : Nat) (l : Worker.Protocol.ViewLink) : Links.Link :=
  { box := l.box,
    action := match l.action with
      | .goto pg lf tp => if pg < n then .goto ⟨pg, lf, tp⟩ else .badPage
      | .uri u => .uri (asciiOr 0x21 u)
      | .badPage => .badPage
      | .unresolved nm => .unresolved (safeText nm)
      | .other k => .other (asciiOr 0x20 k)
      | .none => .none }

/-- The links of page `p`, read on first use (`Links.pageLinks`) and cached. Task 12.2d: with a
document worker (`workerForText`) the worker reads them (`Request.viewLinks`; `submit` asks for
them when the page is rendered); with `wait := false` (pointer motion) nothing waits: `#[]`
until the reply is there. A failed request is cached as no links (never read in this
process). -/
def linksOf (st : IO.Ref State) (p : Nat) (wait : Bool := true) : IO (Array Links.Link) := do
  let s ← st.get
  let some doc := s.doc | return #[]
  match s.links[p]? with
  | some (some ls) => return ls
  | _ =>
    if let some (ses, src) ← workerForText st doc then
      let some j ← sideJob st ses src true p (if wait then 0 else 1) | return #[]
      if !wait && !(← IO.hasFinished j.task) then return #[]
      let reply ← IO.wait j.task
      dropSideJob st true j
      let ls? : Option (Array Links.Link) := match reply with
        | .response (.viewLinks ls) _ => some (ls.map (linkOfWire doc.pages.size)).toArray
        | .cancelled => none
        | _ => some #[]
      let some ls := ls? | return #[]
      st.modify fun s =>
        if s.gen == j.gen then { s with links := s.links.modify p (fun _ => some ls),
                                        workerLinks := s.workerLinks + 1 } else s
      return ls
    let ls ← IO.lazyPure fun _ => Links.pageLinks doc limits p
    let gen := s.gen
    st.modify fun s =>
      if s.gen == gen then { s with links := s.links.modify p (fun _ => some ls) } else s
    return ls

/-- The first number of an `xview`/`yview` result. -/
def firstFrac (s : String) : Rat :=
  ((s.splitOn " ").head?.bind View.parseDecimal).getD 0

/-- Where the view is now (page and scroll fractions), for the history. -/
def curLoc (st : IO.Ref State) : IO Links.Loc := do
  let s ← st.get
  return ⟨s.page, firstFrac (← run [".c", "xview"]), firstFrac (← run [".c", "yview"])⟩

/-- Shows page `p` (clamped) scrolled as `whereTo`, also when it is the current page. -/
def showAt (st : IO.Ref State) (p : Nat) (whereTo : ScrollTo) : IO Unit := do
  let s ← st.get
  if s.pageCount == 0 then return
  let p := min p (s.pageCount - 1)
  st.modify fun s => { s with page := p, pending := some whereTo, pressPt := none, hover := none,
                              sel := if p == s.page || s.scroll == .vertical then s.sel else none,
                              wheel := {} }
  discard <| run [".c", "configure", "-cursor", ""]
  refresh st

/-- Jumps to `j` (a link, an outline item, Ctrl+G), recording the current place in the
history. -/
def jumpTo (st : IO.Ref State) (j : Links.Jump) : IO Unit := do
  let s ← st.get
  if j.page ≥ s.pageCount then
    setStatus s!"destination page {j.page + 1} is not in the document"
    return
  let here ← curLoc st
  st.modify fun s => { s with history := s.history.push here }
  showAt st j.page (.dest j.left j.top)

/-- Handles `thClick Y` (task 9.r9): a click at canvas y `Y` of the thumbnails panel goes to
that thumbnail's page (recorded in the history, as PDF.js's thumbnail links). -/
def thumbClick (st : IO.Ref State) (ys : String) : IO Unit := do
  let s ← st.get
  let some y := (ys.splitOn ".").head?.bind (·.toInt?) | return
  let half : Int := (Sidebar.thumbGap / 2 : Nat)
  let some t := s.thSlots.find? fun t => (t.y : Int) - half ≤ y && y < (t.bottom : Int) + half
    | return
  st.modify ({ · with thSel := none })
  discard <| run [".ol.th", "delete", "thfocus"]
  if t.page != s.page then jumpTo st { page := t.page }

/-- Handles `thKey up|down|go` (task 9.r9): Up and Down move the keyboard selection in the
thumbnails panel (from the current page when there is none; `Sidebar.thumbStep`), Return goes
to the selected page. -/
def thumbKey (st : IO.Ref State) (k : String) : IO Unit := do
  let s ← st.get
  if s.doc.isNone || s.thSlots.isEmpty then return
  let cur := s.thSel.getD s.page
  match k with
  | "go" =>
    st.modify ({ · with thSel := none })
    discard <| run [".ol.th", "delete", "thfocus"]
    if cur != s.page then jumpTo st { page := cur }
  | _ =>
    let p := Sidebar.thumbStep s.thSlots.size cur (k == "down")
    st.modify ({ · with thSel := some p })
    thumbFocus st p

/-- Back (`back = true`, Alt+Left) or Forward (Alt+Right) in the history. -/
def histMove (st : IO.Ref State) (back : Bool) : IO Unit := do
  let s ← st.get
  if s.doc.isNone then return
  let here ← curLoc st
  match (if back then s.history.goBack here else s.history.goForward here) with
  | some (l, h) =>
    st.modify ({ · with history := h })
    showAt st l.page (.frac l.x l.y)
  | none => setStatus (if back then "nothing to go back to" else "nothing to go forward to")

/-- Asks whether to copy an external link's address (dialog `::safepdf::askUri`, which shows
the exact address); copies it to the clipboard only when confirmed. Nothing is opened. -/
def confirmUri (u : String) : IO Unit := do
  let ans ← run ["::safepdf::askUri", u]
  if ans == "1" then
    discard <| run ["clipboard", "clear"]
    discard <| run ["clipboard", "append", "--", u]
    setStatus s!"copied the link address to the clipboard (not opened): {u}"
  else setStatus s!"external link not followed: {u}"

/-- Activates a link or outline action. -/
def activate (st : IO.Ref State) (a : Links.Action) : IO Unit := do
  match a with
  | .goto j => jumpTo st j
  | .uri u => confirmUri u
  | a =>
    let s ← st.get
    setStatus (Links.describe s.labels s.pageCount a)

/-- The link under window position `(wx, wy)` (on the page under it, task 9.3), if any. -/
def linkUnder (st : IO.Ref State) (wx wy : Int) : IO (Option ((Nat × Nat) × Links.Link)) := do
  let some (pg, p) ← pagePointAt st wx wy | return none
  return (Links.linkAt (← linksOf st pg) p).map fun (i, l) => ((pg, i), l)

/-- What lies under window position `pos` of the page canvas for the cursor (task 10.8,
`Toolbar.hitOf`: a mark, else a link, else a glyph box of the page text) and the link there.
The text index is consulted only when the cursor depends on it (Select text and Highlight,
nothing above the text); it is the per-page cached index of the selection. -/
def pointerHit (st : IO.Ref State) (pos : Option (Int × Int)) :
    IO (Toolbar.Hit × Option ((Nat × Nat) × Links.Link)) := do
  let some (x, y) := pos | return (.empty, none)
  let some (pg, p) ← pagePointAt st x y | return (.empty, none)
  let s ← st.get
  let l := (Links.linkAt (← linksOf st pg (wait := false)) p).map fun (i, l) => ((pg, i), l)
  let store := if s.ui.showAll then s.marks
    else { s.marks with marks := s.marks.marks.filter (!·.isHighlight) }
  let mark := match slotOf s pg with
    | some sl => (store.hitAt sl.vp.box pg p).isSome
    | none => false
  let mode := Toolbar.Mode.of s.ui
  let text ← if mark || l.isSome || mode == .draw || mode == .text then pure false else
    match ← pageIndex st pg (wait := false) with
    | .ok ix => pure (ix.cells.any fun c => Links.Box.contains c.box p)
    | .error _ => pure false
  return (Toolbar.hitOf mark l.isSome text, l)

/-- Sets the page canvas cursor to `c`, calling Tk only when it changes. -/
def setCursor (c : String) : IO Unit := do
  if (← run [".c", "cget", "-cursor"]) != c then
    discard <| run [".c", "configure", "-cursor", c]

/-- Brings the page canvas cursor in step with the active tool at the last pointer position
(task 10.8; after a tool change without pointer motion). -/
def refreshCursor (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let (h, _) ← pointerHit st s.pointer
  setCursor (Toolbar.cursorFor (Toolbar.Mode.of s.ui) h)

/-- Pointer motion: the cursor telegraphs what a press does there (task 10.8,
`Toolbar.cursorFor`: I-beam over text, hand over links and marks, crosshair in Draw); over a
link the status line shows the target (the full address of a URI); leaving it restores the
status line. -/
def hover (st : IO.Ref State) (pos : Option (Int × Int)) : IO Unit := do
  let s ← st.get
  if s.pressPt.isSome then return
  st.modify ({ · with pointer := pos })
  let (h, l) ← pointerHit st pos
  setCursor (Toolbar.cursorFor (Toolbar.Mode.of s.ui) h)
  let idx := l.map (·.1)
  if idx == s.hover then return
  if s.hover.isNone then
    let cur ← run [".status", "cget", "-text"]
    st.modify ({ · with savedStatus := cur })
  st.modify ({ · with hover := idx })
  match l with
  | some (_, k) => setStatus (Links.describe s.labels s.pageCount k.action)
  | none => setStatus (← st.get).savedStatus

/-- Handles `outline ID`: activates the outline entry of outline row `oK`. -/
def outlineClick (st : IO.Ref State) (id : String) : IO Unit := do
  let s ← st.get
  let some k := (id.drop 1).toString.toNat? | return
  if !id.startsWith "o" then return
  let some e := s.outline[k]? | return
  discard <| run ["::safepdf::olMark", toString k]
  activate st e.action

/-- Handles `goto TEXT` (Ctrl+G): a page label or number (`Links.gotoPage`). -/
def gotoText (st : IO.Ref State) (txt : String) : IO Unit := do
  let s ← st.get
  if s.doc.isNone then return
  match Links.gotoPage s.labels txt with
  | some p =>
    discard <| run ["::safepdf::hideGoto"]
    jumpTo st ⟨p, none, none⟩
  | none => setStatus s!"no page with label or number \"{txt}\""

/-- Handles `pageEntry TEXT` (Enter in the toolbar's page field, task 9.7): jumps to the page
it names (`Toolbar.pageEntry`: label, number, label ignoring case; recorded in the history as
PDF.js does); an invalid entry reverts the field to the current page. -/
def pageEntry (st : IO.Ref State) (txt : String) : IO Unit := do
  let s ← st.get
  if s.doc.isNone || s.pageCount == 0 then return
  let (p, ok) := Toolbar.pageEntry s.labels s.pageCount s.page txt
  if ok && p != s.page then jumpTo st ⟨p, none, none⟩
  else
    showPageField s
    if !ok then setStatus s!"no page \"{txt}\" (enter a page number or label)"

/-! ## Highlights and notes (task 9.4) -/

/-- What the status line calls a mark. -/
def markName (m : Marks.Mark) : String :=
  match m.kind with
  | .note .. => "note"
  | .highlight _ => s!"{m.color.name} highlight"
  | .freeText .. => "text box"
  | .ink .. => "drawing"

/-- Draws the Highlight pop-over `.hlbar` (task 9.8, layout `Bubble.Popover`, after PDF.js's
`#editorHighlightParamsToolbar`): "Highlight color" with the five swatches (the current colour
ringed), "Thickness" with the small and large example dots and the slider, a divider, and the
"Show all" switch. -/
def drawPopover (s : State) : IO Unit := do
  let c := ".hlbar"
  let W := Bubble.Popover.width
  let H := Bubble.Popover.height
  let px := Bubble.Popover.padX
  let sy := Bubble.Popover.sliderY
  let text (y : Rat) (t : String) : IO Unit := do
    discard <| run [c, "create", "text", num px, num y, "-anchor", "w", "-text", t, "-font",
      "::safepdf::fBar", "-fill", "#15141a"]
  discard <| run [c, "delete", "all"]
  discard <| run ["::safepdf::rrect", c, "0.5", "0.5", num (W - 1 / 2), num (H - 1 / 2), "8",
    "-fill", "white", "-outline", "#d7d7db"]
  text Bubble.Popover.titleY "Highlight color"
  for (i, col) in (List.range Marks.Color.all.length).zip Marks.Color.all do
    discard <| run ["::safepdf::swatch", c, num (Bubble.Popover.swatchX i),
      num Bubble.Popover.swatchY, num Bubble.Popover.swatchD, col.hex,
      if col == s.hlColor then "1" else "0", s!"c:{col.name}"]
  text Bubble.Popover.thickY "Thickness"
  discard <| run [c, "create", "oval", num px, num (sy - 4), num (px + 8), num (sy + 4), "-fill",
    "#b7b7c1", "-outline", ""]
  discard <| run [c, "create", "oval", num (W - px - 24), num (sy - 12), num (W - px),
    num (sy + 12), "-fill", "#b7b7c1", "-outline", ""]
  let x0 := Bubble.Popover.sliderX0
  let tx := Bubble.Popover.thumbX s.ui.thickness
  discard <| run [c, "create", "line", num x0, num sy, num Bubble.Popover.sliderX1, num sy,
    "-fill", "#c6c5c7", "-width", "2", "-capstyle", "round"]
  discard <| run [c, "create", "line", num x0, num sy, num tx, num sy, "-fill", "#c1b0ec",
    "-width", "2", "-capstyle", "round"]
  discard <| run ["::safepdf::rrect", c, num (tx - 7), num (sy - 7), num (tx + 7), num (sy + 7),
    "3", "-fill", "#c3b5ee", "-outline", "#b3a3e6", "-tags", "thumb"]
  discard <| run [c, "create", "line", num px, num Bubble.Popover.dividerY, num (W - px),
    num Bubble.Popover.dividerY, "-fill", "#d7d7db"]
  text Bubble.Popover.toggleY "Show all"
  let t := Bubble.Popover.toggleRect
  let on := s.ui.showAll
  discard <| run ["::safepdf::rrect", c, num t.x0, num t.y0, num t.x1, num t.y1, "8", "-fill",
    if on then "#6b45d3" else "white", "-outline", if on then "#6b45d3" else "#8f8f9d",
    "-tags", "switch"]
  let (k0, k1) := if on then (t.x1 - 14, t.x1 - 3) else (t.x0 + 3, t.x0 + 14)
  discard <| run [c, "create", "oval", num k0, num (t.y0 + 5 / 2), num k1, num (t.y1 - 5 / 2),
    "-fill", if on then "white" else "#8f8f9d", "-outline", "", "-tags", "knob"]

/-- The slider of row `row` of the Add text / Draw pop-over and its current value. -/
def edSlider (u : Bubble.Ui) (row : Nat) : Bubble.Slider × Nat :=
  match u.editor, row with
  | .draw, 2 => (Bubble.EdPop.opacity, u.inkOpacity)
  | .draw, _ => (Bubble.EdPop.thickness, u.inkThick)
  | _, _ => (Bubble.EdPop.fontSize, u.ftSize)

/-- Draws the Add text / Draw pop-over `.edbar` (task 9.9, after PDF.js's
`.editorParamsToolbar`: 220 px, 10 px padding, a label per row with its control): the colour
swatches (`Bubble.EdPop.palette`, the current one ringed), then Font size, or Thickness and
Opacity, as sliders with their value at the right. -/
def drawEdPop (s : State) : IO Unit := do
  let c := ".edbar"
  let e := s.ui.editor
  let W := Bubble.EdPop.width
  let H := Bubble.EdPop.height e
  let px := Bubble.EdPop.padX
  let text (x y : Rat) (anchor t : String) : IO Unit := do
    discard <| run [c, "create", "text", num x, num y, "-anchor", anchor, "-text", t, "-font",
      "::safepdf::fBar", "-fill", "#15141a"]
  discard <| run [c, "delete", "all"]
  discard <| run ["::safepdf::rrect", c, "0.5", "0.5", num (W - 1 / 2), num (H - 1 / 2), "8",
    "-fill", "white", "-outline", "#d7d7db"]
  let labels := Bubble.EdPop.labels e
  let cur := if e == .draw then s.ui.inkColor else s.ui.ftColor
  text px (Bubble.EdPop.labelY 0) "w" (labels.headD "")
  let pal := Bubble.EdPop.palette
  for (i, col) in (List.range pal.length).zip pal do
    discard <| run ["::safepdf::swatch", c, num (Bubble.EdPop.swatchX i),
      num (Bubble.EdPop.ctrlY 0), num Bubble.EdPop.swatchD, Marks.rgbHex col,
      if col == cur then "1" else "0", s!"c:{i}"]
  for row in [1:labels.length] do
    let (sl, v) := edSlider s.ui row
    text px (Bubble.EdPop.labelY row) "w" (labels.getD row "")
    text (W - px) (Bubble.EdPop.labelY row) "e" (if e == .draw && row == 2 then s!"{v}%" else toString v)
    let y := Bubble.EdPop.ctrlY row
    let tx := sl.thumbX v
    discard <| run [c, "create", "line", num Bubble.EdPop.sliderX0, num y,
      num Bubble.EdPop.sliderX1, num y, "-fill", "#c6c5c7", "-width", "2", "-capstyle", "round"]
    discard <| run [c, "create", "line", num Bubble.EdPop.sliderX0, num y, num tx, num y,
      "-fill", "#c1b0ec", "-width", "2", "-capstyle", "round"]
    discard <| run ["::safepdf::rrect", c, num (tx - 7), num (y - 7), num (tx + 7), num (y + 7),
      "3", "-fill", "#c3b5ee", "-outline", "#b3a3e6", "-tags", s!"thumb{row}"]

/-- Brings the Tk side in step with the Add text / Draw mode (task 9.9): the toggled look of
their buttons and the pop-over `.edbar`, placed under the active button (right-aligned, as the
Highlight pop-over). -/
def syncEditor (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let b (v : Bool) : String := if v then "1" else "0"
  discard <| run ["::safepdf::btnToggled", ".bar.text", b (s.ui.editor == .text)]
  discard <| run ["::safepdf::btnToggled", ".bar.draw", b (s.ui.editor == .draw)]
  if s.ui.edPop && s.ui.editor != .none && s.doc.isSome then
    drawEdPop s
    let w := if s.ui.editor == .draw then ".bar.draw" else ".bar.text"
    let num? (ws : List String) : IO Rat := return (View.parseDecimal (← run ws)).getD 0
    let bx := (← num? ["winfo", "rootx", w]) - (← num? ["winfo", "rootx", "."])
    let bw ← num? ["winfo", "width", w]
    let ww ← num? ["winfo", "width", "."]
    discard <| run ["::safepdf::edShow", toString (Bubble.Popover.left bx bw ww).floor,
      toString (Bubble.EdPop.height s.ui.editor).floor]
  else discard <| run ["::safepdf::edHide"]

/-- Brings the Tk side in step with the Highlight tool state (task 9.8): the Edit menu's check
variables, the toolbar button's toggled look, and the pop-over (drawn and placed under the
Highlight button, right-aligned with it, `Bubble.Popover.left`; hidden when closed). -/
def syncTool (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let b (v : Bool) : String := if v then "1" else "0"
  discard <| run ["set", Menu.hlToolVar, b s.ui.tool]
  discard <| run ["set", Menu.showAllVar, b s.ui.showAll]
  discard <| run ["::safepdf::btnToggled", ".bar.select", b (Toolbar.pressed s.ui .select)]
  discard <| run ["::safepdf::btnToggled", ".bar.highlight", b s.ui.tool]
  if s.ui.popover && s.doc.isSome then
    drawPopover s
    let num? (w : List String) : IO Rat := return (View.parseDecimal (← run w)).getD 0
    let bx := (← num? ["winfo", "rootx", ".bar.highlight"]) - (← num? ["winfo", "rootx", "."])
    let bw ← num? ["winfo", "width", ".bar.highlight"]
    let ww ← num? ["winfo", "width", "."]
    discard <| run ["::safepdf::popShow", toString (Bubble.Popover.left bx bw ww).floor]
  else discard <| run ["::safepdf::popHide"]
  syncEditor st
  refreshCursor st

/-- Sets the current highlight colour (and the colour menus' radio variable; the pop-over's
ring follows). -/
def setColor (st : IO.Ref State) (c : Marks.Color) : IO Unit := do
  st.modify ({ · with hlColor := c })
  discard <| run ["set", Menu.colorVar, c.name]
  if (← st.get).ui.popover then syncTool st

/-- Handles `highlight [COLOR]` (toolbar, `h`, Edit → Highlight selection, a colour entry):
with a selection, highlights it (its quads are the C3 glyph boxes of the selected line runs,
`Select.rangeBoxes`) in `COLOR` or the current colour, selects the new mark and clears the
text selection; else, with a selected mark and a colour, recolours that mark; else only
makes `COLOR` the current colour. Hook for the selection bubble (task 9.8). -/
def highlight (st : IO.Ref State) (color : Option String) : IO Unit := do
  let s ← st.get
  if s.doc.isNone then return
  let chosen := color.bind Marks.Color.ofName
  let c := chosen.getD s.hlColor
  setColor st c
  match s.sel with
  | some (p, a, b) =>
    let .ok ix ← pageIndex st p | return
    match s.marks.addHighlight p c (Select.rangeBoxes ix.cells a b) with
    | some (marks, id) =>
      st.modify ({ · with marks, markSel := some id, sel := none })
      marksChanged st
      repaint st
      setStatus s!"page {p + 1}: highlighted {(Select.rangeText ix.cells a b).length} \
        characters in {c.name} (click it to select it; Delete removes it)"
    | none => setStatus "nothing to highlight"
  | none =>
    match s.markSel, chosen with
    | some id, some c =>
      if ((s.marks.find? id).map (·.isEditor)).getD false then
        setStatus s!"highlight colour: {c.name} (a text box or drawing takes its colour from \
          its own pop-over)"
      else
      st.modify ({ · with marks := s.marks.recolor id c })
      marksChanged st
      if !(← updatePreview st) then repaint st
      setStatus s!"mark recoloured: {c.name}"
    | _, some c => setStatus s!"highlight colour: {c.name} (select text, then Highlight)"
    | _, none => setStatus "select text first (drag over it or double-click a word), then Highlight"

/-- Opens the popup of note `id` next to its icon. -/
def openNote (st : IO.Ref State) (id : Nat) : IO Unit := do
  let s ← st.get
  let some m := s.marks.find? id | return
  let some sl := slotOf s m.page | return
  let some ib := m.iconBox sl.vp.box | return
  let (_, y0, x1, _) := sl.rect ib
  let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
    View.parseDecimal (← run [".c", "canvasy", "0"])) | return
  let (some rx, some ry) := ((← run ["winfo", "rootx", ".c"]).toInt?,
    (← run ["winfo", "rooty", ".c"]).toInt?) | return
  let x := rx + (x1 - vx).ceil + 8
  let y := ry + (y0 - vy).floor
  discard <| run ["::safepdf::noteEdit", toString id, m.text, toString (max 0 x),
    toString (max 0 y)]

/-- Handles `note [X Y]` (Edit → Add note…, the selection bubble's Add comment, or the context
menu at window position `(X, Y)`). Without a position: a note anchored to the selection on the
shown page (a comment on that text); else, with a highlight selected, opens that highlight's
comment (the note anchored to its quads, `Marks.Store.noteOn`) or adds one in its colour (task
9.8); else a note at the window centre. With a position (right-click → Add note…, task 10.17):
a note at the page point under it, unless the click is inside the selection's highlight boxes
(`Marks.noteAnchor`), which makes it a comment on the selection. Selects it, opens its popup. -/
def addNote (st : IO.Ref State) (pos : Option (Int × Int)) : IO Unit := do
  let s ← st.get
  if s.doc.isNone || (shownBox s).isNone then return
  let mut anchor : Option Marks.Anchor := none
  let mut page := s.page
  -- The point under the click, and the selection's boxes on that page (empty: not there).
  let click ← match pos with
    | some (wx, wy) => pagePointAt st wx wy
    | none => pure none
  let mut selQs : List Box := []
  let mut selPage := s.page
  if let some (p, a, b) := s.sel then
    if (slotOf s p).isSome then
      if let .ok ix ← pageIndex st p then
        selQs := Select.rangeBoxes ix.cells a b
        selPage := p
  if let some (pg, pt) := click then
    -- A click on another page than the selection is never inside it.
    anchor := Marks.noteAnchor (if pg == selPage then selQs else []) (some pt)
    page := if (anchor.map fun | .quads _ => true | _ => false) == some true then selPage else pg
  else if pos.isNone then
    anchor := Marks.noteAnchor selQs none
    page := selPage
  -- The comment of the selected highlight (the edit bubble's Comment, task 9.8): its note,
  -- or a new note anchored to its quads in its colour.
  let mut color := Marks.Color.yellow
  if anchor.isNone && pos.isNone then
    if let some m := s.markSel.bind s.marks.find? then
      if (slotOf s m.page).isSome && !m.isNote && !m.quads.isEmpty then
        if let some id := s.marks.noteOn m.page m.quads then
          setStatus s!"page {m.page + 1}: comment of the {m.color.name} highlight"
          openNote st id
          return
        anchor := some (.quads m.quads)
        page := m.page
        color := m.color
  if anchor.isNone then
    let (wx, wy) := (((s.canvasW / 2 : Nat) : Int), ((s.canvasH / 2 : Nat) : Int))
    if let some (pg, p) ← pagePointAt st wx wy then
      anchor := some (.point p)
      page := pg
  let some anc := anchor | return
  let (marks, id) := s.marks.addNote page color "" anc
  st.modify ({ · with marks, markSel := some id, sel := none })
  marksChanged st
  repaint st
  setStatus s!"page {page + 1}: note added (type its text, then Save)"
  openNote st id

/-- Handles `noteSave ID TEXT` from the note popup. -/
def noteSave (st : IO.Ref State) (idS text : String) : IO Unit := do
  let some id := idS.toNat? | return
  let s ← st.get
  let some m := s.marks.find? id | return
  if m.text == text then
    setStatus "note unchanged"
    return
  st.modify ({ · with marks := s.marks.setText id text })
  marksChanged st
  if !(← updatePreview st) then drawOverlay st
  setStatus s!"note saved ({text.length} characters)"

/-- Removes mark `id` (Delete, Edit → Delete mark, the note popup's Delete). -/
def deleteMark (st : IO.Ref State) (id : Nat) : IO Unit := do
  let s ← st.get
  let some m := s.marks.find? id | return
  st.modify ({ · with marks := s.marks.removeWithComment id,
                      markSel := if s.markSel == some id then none else s.markSel })
  marksChanged st
  if !(← updatePreview st) then repaint st
  -- An open popup of a note that is gone now (the note, or a deleted highlight's comment).
  if let some nid := (← run ["set", "::safepdf::noteId"]).toNat? then
    if ((← st.get).marks.find? nid).isNone then discard <| run ["::safepdf::noteGone", toString nid]
  setStatus s!"{markName m} deleted"

/-- Handles `noteClose ID TEXT`: the note popup closed without Save (Escape, Cancel, the
window's close button; task 9.r12) showing `TEXT`; `Marks.Store.onUnsavedClose` decides
between keeping the stored text, saving the typed text of a new note, and deleting an empty
note (the Delete path: a highlight's comment goes, the highlight stays). -/
def noteClose (st : IO.Ref State) (idS text : String) : IO Unit := do
  let some id := idS.toNat? | return
  match (← st.get).marks.onUnsavedClose id text with
  | .keep => if ((← st.get).marks.find? id).isSome then setStatus "note edits discarded"
  | .save t => noteSave st idS t
  | .delete =>
    deleteMark st id
    setStatus "empty note removed"

/-- Handles `markDelete`: removes the selected mark. -/
def markDelete (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  match s.markSel with
  | some id => deleteMark st id
  | none => if s.doc.isSome then setStatus "no mark selected (click a highlight or note)"

/-- Selects the mark under point `p` of page `pg`, if any (a note also opens its
popup when `openIt` is set). Returns whether there was one. -/
def selectMarkAt (st : IO.Ref State) (pg : Nat) (p : Pt) (openIt : Bool) : IO Bool := do
  let s ← st.get
  let some sl := slotOf s pg | return false
  let store := if s.ui.showAll then s.marks
    else { s.marks with marks := s.marks.marks.filter (!·.isHighlight) }
  match store.hitAt sl.vp.box pg p with
  | some id =>
    st.modify ({ · with markSel := some id })
    drawOverlay st
    if let some m := s.marks.find? id then
      setStatus s!"{markName m} selected (Delete removes it; a colour in the Highlight menu \
        recolours it)"
      if openIt && m.isNote then openNote st id
    return true
  | none => return false

/-- Handles `popup X Y RX RY` (right button at window `(X, Y)`, screen `(RX, RY)`): remembers
the point for Add note…, selects the mark under it (or deselects the selected one when there
is none), sets the states of the mark entries and
posts the context menu. -/
def popup (st : IO.Ref State) (x y rx ry : String) : IO Unit := do
  discard <| run ["set", "::safepdf::popX", x]
  discard <| run ["set", "::safepdf::popY", y]
  if let (some wx, some wy) := (x.toInt?, y.toInt?) then
    if let some (pg, p) ← pagePointAt st wx wy then
      if !(← selectMarkAt st pg p false) && (← st.get).markSel.isSome then
        st.modify ({ · with markSel := none })
        drawOverlay st
  let s ← st.get
  let on (b : Bool) : String := if b then "normal" else "disabled"
  let doc := s.doc.isSome && s.shown.isSome
  discard <| run [Menu.popPath, "entryconfigure", Menu.popColorsLabel, "-state", on doc]
  discard <| run [Menu.popPath, "entryconfigure", Menu.Cmd.addNote.label, "-state", on doc]
  discard <| run [Menu.popPath, "entryconfigure", Menu.Cmd.deleteMark.label, "-state",
    on (doc && s.markSel.isSome)]
  if s.smokeDir.isNone then discard <| run ["tk_popup", Menu.popPath, rx, ry]

/-- Status line after the Highlight tool was turned on or off. -/
def toolStatus (st : IO.Ref State) : IO Unit := do
  if (← st.get).ui.tool then
    setStatus "Highlight tool on: choose the highlight colour, then select text (it is \
      highlighted at once; Escape closes the pop-over, the button ends the tool)"
  else setStatus "Highlight tool off"

/-- The toolbar's Highlight button (`Bubble.Ui.toolClick`): with a selection, highlights it in
the current colour (task 9.4); without one, turns the Highlight tool on with its pop-over, or
off (task 9.8, PDF.js's editor mode button). -/
def toolHighlight (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let (u, hl) := s.ui.toolClick s.sel.isSome
  if hl then highlight st none
  else
    st.modify ({ · with ui := u })
    syncTool st
    toolStatus st

/-- Edit → Highlight tool: turns the tool (and its pop-over) on or off (task 9.8). -/
def hlToolToggle (st : IO.Ref State) : IO Unit := do
  if (← st.get).doc.isNone then return
  st.modify fun s => { s with ui := s.ui.toggleTool }
  syncTool st
  toolStatus st

/-- "Show all" (the pop-over switch, Edit → Show all highlights; task 9.8): hides or shows all
highlights of the page view (notes stay); a hidden highlight cannot stay selected. -/
def toggleShowAll (st : IO.Ref State) : IO Unit := do
  st.modify fun s =>
    let on := !s.ui.showAll
    let keep := on || ((s.markSel.bind s.marks.find?).map (!·.isHighlight)).getD true
    { s with ui := { s.ui with showAll := on }, markSel := if keep then s.markSel else none }
  repaint st
  syncTool st
  setStatus (if (← st.get).ui.showAll then "highlights shown" else "highlights hidden (Show all is off)")

/-- A press in the pop-over at `(x, y)` (`Bubble.Popover.hit`): a swatch makes its colour the
current one and recolours a selected highlight (PDF.js applies the parameters to the selected
editor); the slider sets the thickness (and follows drags, `popDrag`); the switch toggles
"Show all". -/
def popClick (st : IO.Ref State) (xs ys : String) : IO Unit := do
  let (some x, some y) := (xs.toInt?, ys.toInt?) | return
  st.modify ({ · with popSlide := false })
  match Bubble.Popover.hit x y with
  | some (.color c) =>
    setColor st c
    let s ← st.get
    match s.markSel.bind s.marks.find? with
    | some m =>
      if m.isHighlight then
        st.modify ({ · with marks := s.marks.recolor m.id c })
        marksChanged st
        if !(← updatePreview st) then repaint st
        setStatus s!"highlight recoloured: {c.name}"
      else setStatus s!"highlight colour: {c.name}"
    | none => setStatus s!"highlight colour: {c.name}"
  | some .slider =>
    st.modify fun s => { s with popSlide := true,
                                ui := s.ui.setThickness (Bubble.Popover.thicknessAt x) }
    syncTool st
    setStatus s!"thickness {(← st.get).ui.thickness} (used by free highlights)"
  | some .toggle => toggleShowAll st
  | none => pure ()

/-- A drag in the pop-over after a press on the slider moves it (`Bubble.Popover.thicknessAt`). -/
def popDrag (st : IO.Ref State) (xs _ys : String) : IO Unit := do
  let some x := xs.toInt? | return
  let s ← st.get
  if !s.popSlide then return
  let v := Bubble.Popover.thicknessAt x
  if v == s.ui.thickness then return
  st.modify fun s => { s with ui := s.ui.setThickness v }
  syncTool st
  setStatus s!"thickness {v} (used by free highlights)"

/-! ## Dismissing transients (task 10.6) -/

/-- The transients open now (`Toolbar.Transient`, in `Transient.order`): the note popup and
the bars from Tk (a bar counts as open while it is packed), the picker and the pop-overs
from the tool state (a pop-over only with a document, as `syncTool` shows it). -/
def openTransients (st : IO.Ref State) : IO (List Toolbar.Transient) := do
  let s ← st.get
  let packed (w : String) : IO Bool := do
    return !(← try run ["winfo", "manager", w] catch _ => pure "").isEmpty
  let note := (← try run ["winfo", "exists", ".note"] catch _ => pure "0") == "1"
  let goto ← packed ".goto"
  let find ← packed ".find"
  let hl := s.ui.popover && s.doc.isSome
  let ed := s.ui.edPop && s.ui.editor != .none && s.doc.isSome
  return Toolbar.Transient.order.filter fun
    | .note => note
    | .picker => s.pickerAt.isSome || s.ui.picker
    | .hlPop => hl
    | .edPop => ed
    | .goto => goto
    | .find => find

/-- Closes transient `t` the way its own Close does: the note popup through `noteDone … close`
(task 9.r12: a typed text is kept, an empty new note removed; never a bare `destroy .note`),
the bars through `hideFind` / `hideGoto`, the picker and the pop-overs in the tool state
(`Transient.closeUi`: the tool and the mode stay on). -/
def dismiss (st : IO.Ref State) (t : Toolbar.Transient) : IO Unit := do
  match t with
  | .note =>
    let id ← try run ["set", "::safepdf::noteId"] catch _ => pure ""
    discard <| run ["::safepdf::noteDone", id, "close"]
  | .goto => discard <| run ["::safepdf::hideGoto"]
  | .find => discard <| run ["::safepdf::hideFind"]
  | .picker =>
    st.modify fun s => { s with ui := t.closeUi s.ui }
    drawOverlay st
  | .hlPop | .edPop =>
    st.modify fun s => { s with ui := t.closeUi s.ui }
    syncTool st

/-- Handles `clickAway W` (task 10.6): a mouse press on widget `W` of the main window closes
the open transients it lies outside of (`Toolbar.onClick`). The press is not consumed: the
widget's own bindings have already run (the binding sits on the tag `all`). -/
def clickAway (st : IO.Ref State) (w : String) : IO Unit := do
  for t in Toolbar.onClick (← openTransients st) w do dismiss st t

/-- Handles `opening find` / `opening goto` (task 10.6): before a bar opens, its rival closes
(`Toolbar.onOpen`; the pop-overs' rivalry is in `Bubble.Ui`). -/
def opening (st : IO.Ref State) (name : String) : IO Unit := do
  let t : Option Toolbar.Transient := match name with
    | "find" => some .find
    | "goto" => some .goto
    | _ => none
  let some t := t | return
  for u in Toolbar.onOpen (← openTransients st) t do dismiss st u

/-- Escape (tasks 9.8, 10.6): closes the topmost open transient (`Toolbar.onEscape`: the note
popup, the picker, a pop-over, then the go-to or find bar); only when none was open does it
leave full screen or bring back what the document hid (task 9.r8, `escapeWindow`). Every
Escape also dismisses the bubble (the text selection and the selected mark are cleared, the
picker with it) and ends a drawing session; the Highlight tool and the Add text / Draw mode
stay on. -/
def escape (st : IO.Ref State) : IO Unit := do
  let closed := Toolbar.onEscape (← openTransients st)
  for t in closed do dismiss st t
  if closed.isEmpty then discard <| escapeWindow st
  st.modify fun s => { s with ui := { s.ui with picker := false }, sel := none, markSel := none,
                              pressPt := none, inkSession := none }
  drawOverlay st
  syncTool st

/-- A mouse press at window `(wx, wy)` on the bubble or its colour picker (task 9.8): a picker
row recolours the selected highlight; the colour button opens or closes the picker; the other
buttons run their `Menu.Cmd` script (`Bubble.Btn.cmd?`) at the next idle moment, as a menu
entry would. Returns whether the press was on them (then it is not a text selection). -/
def bubbleClick (st : IO.Ref State) (wx wy : Int) : IO Bool := do
  let s ← st.get
  if s.bubble.isNone && s.pickerAt.isNone then return false
  let some (cx, cy) ← canvasPos wx wy | return false
  if let some pr := s.pickerAt then
    if pr.contains cx cy then
      st.modify ({ · with bubblePress := true })
      if let some c := Bubble.pickerHit pr cx cy then
        st.modify fun s => { s with ui := { s.ui with picker := false } }
        highlight st (some c.name)
      return true
  if let some (k, r) := s.bubble then
    if r.contains cx cy then
      st.modify ({ · with bubblePress := true })
      discard <| run ["::safepdf::bubTipHide"]
      match Bubble.hit k r cx cy with
      | some .color =>
        st.modify fun s => { s with ui := { s.ui with picker := !s.ui.picker } }
        drawOverlay st
      | some b =>
        if let some c := b.cmd? then discard <| run ["after", "idle", c.script]
      | none => pure ()
      return true
  return false

/-! ## Add text and Draw (task 9.9) -/

/-- Opens the free-text editor on page `pg` with its box's upper-left corner at `pos` (page
space), holding `text`, at font size `size` in colour `rgb`; `id` is the mark it edits
(`none`: a new one). -/
def ftOpenAt (st : IO.Ref State) (id : Option Nat) (pg : Nat) (pos : Pt) (text : String)
    (size : Nat) (rgb : Marks.Rgb) : IO Unit := do
  let s ← st.get
  let some sl := slotOf s pg | return
  let pad := SafePdf.Core.Write.Annots.ftPad
  let (x, y, _, _) := sl.rect ⟨pos.x + pad, pos.y - pad, pos.x + pad, pos.y - pad⟩
  discard <| run ["::safepdf::ftOpen", num x, num y, text,
    toString (max 1 (((size : Rat) * sl.vp.zoom + 1 / 2).floor.toNat)), Marks.rgbHex rgb]
  st.modify ({ · with ftEdit := some ⟨id, pg, pos, size, rgb⟩, sel := none, pressPt := none })
  drawOverlay st
  setStatus s!"page {pg + 1}: type the text (a click elsewhere or Escape finishes it)"

/-- Commits the open free-text editor (a click elsewhere, Escape, a tool change, Save): a new
box becomes a free-text mark (dropped when empty); an edited one gets the new text (deleted
when emptied). Returns whether an editor was open. -/
def commitFt (st : IO.Ref State) : IO Bool := do
  let s ← st.get
  let some fe := s.ftEdit | return false
  let raw ← try run [".c.ft", "get", "1.0", "end - 1 chars"] catch _ => pure ""
  discard <| run ["destroy", ".c.ft"]
  discard <| run [".c", "delete", "ftedit"]
  discard <| run ["focus", ".c"]
  st.modify ({ · with ftEdit := none })
  let t := String.ofList ((raw.toList.reverse.dropWhile (· == '\n')).reverse)
  let blank := t.all Char.isWhitespace
  match fe.id with
  | none =>
    if blank then
      drawOverlay st
      setStatus "empty text box discarded"
    else
      let (marks, id) := s.marks.add fe.page .yellow (.freeText t fe.pos fe.size fe.rgb)
      st.modify ({ · with marks, markSel := some id })
      marksChanged st
      drawOverlay st
      setStatus s!"page {fe.page + 1}: text added ({t.length} characters; drag it to move it, \
        double-click to edit, Delete removes it)"
  | some id =>
    if blank then
      st.modify fun s => { s with marks := s.marks.remove id,
                                  markSel := if s.markSel == some id then none else s.markSel }
      marksChanged st
      if !(← updatePreview st) then drawOverlay st
      setStatus "text box deleted (emptied)"
    else if ((s.marks.find? id).map (·.text)) == some t then
      drawOverlay st
      setStatus "text unchanged"
    else
      st.modify ({ · with marks := s.marks.setText id t, markSel := some id })
      marksChanged st
      if !(← updatePreview st) then drawOverlay st
      setStatus s!"text edited ({t.length} characters)"
  return true

/-- Status line after the Add text / Draw mode changed. -/
def editorStatus (st : IO.Ref State) : IO Unit := do
  match (← st.get).ui.editor with
  | .text => setStatus "Add text: click on the page to place a text box (font colour and size in \
      the pop-over; Escape closes it, the button ends the mode)"
  | .draw => setStatus "Draw: drag on the page to draw (colour, thickness and opacity in the \
      pop-over; the strokes until Escape or the end of the mode form one drawing)"
  | .none => setStatus "Add text / Draw off"

/-- The toolbar's Add text or Draw button: turns that mode on (with its pop-over; the Highlight
tool off) or off (`Bubble.Ui.selectEditor`); an open text box is committed and a drawing
session ends. -/
def toggleEditor (st : IO.Ref State) (e : Bubble.Editor) : IO Unit := do
  if (← st.get).doc.isNone then return
  discard <| commitFt st
  st.modify fun s => { s with ui := s.ui.selectEditor e, inkSession := none }
  syncTool st
  editorStatus st

/-- Applies a pop-over change to the selected mark when it is of the mode's kind (`pred`),
as PDF.js applies the parameters to the selected editor. `merge`: a step of a slider drag
(one undo step per drag, task 10.7). -/
def edApply (st : IO.Ref State) (pred : Marks.Mark → Bool)
    (f : Marks.Store → Nat → Marks.Store) (merge : Bool := false) : IO Unit := do
  let s ← st.get
  let some m := s.markSel.bind s.marks.find? | return
  if !pred m then return
  st.modify ({ · with marks := f s.marks m.id })
  marksChanged st merge
  if !(← updatePreview st) then drawOverlay st

/-- Whether a mark is free text / ink. -/
def isFt (m : Marks.Mark) : Bool := match m.kind with | .freeText .. => true | _ => false
/-- See `isFt`. -/
def isInk (m : Marks.Mark) : Bool := match m.kind with | .ink .. => true | _ => false

/-- Sets slider `row` of the pop-over to the value at x position `x`. -/
def edSlideTo (st : IO.Ref State) (row : Nat) (x : Rat) : IO Unit := do
  let s ← st.get
  let (sl, old) := edSlider s.ui row
  let v := sl.valueAt x
  if v == old then return
  match s.ui.editor, row with
  | .draw, 2 =>
    st.modify fun s => { s with ui := { s.ui with inkOpacity := v } }
    edApply st isInk (fun ms id => ms.setOpacity id v) (merge := true)
    setStatus s!"opacity {v}%"
  | .draw, _ =>
    st.modify fun s => { s with ui := { s.ui with inkThick := v } }
    edApply st isInk (fun ms id => ms.setSize id v) (merge := true)
    setStatus s!"thickness {v}"
  | _, _ =>
    st.modify fun s => { s with ui := { s.ui with ftSize := v },
                                ftEdit := s.ftEdit.map ({ · with size := v }) }
    edApply st isFt (fun ms id => ms.setSize id v) (merge := true)
    setStatus s!"font size {v}"
  syncTool st
  drawOverlay st

/-- A press in the Add text / Draw pop-over at `(x, y)` (`Bubble.EdPop.hit`): a swatch sets
the colour, a slider row its value (drags follow, `edDrag`); both apply to the selected mark
of the mode's kind and to an open text box. -/
def edClick (st : IO.Ref State) (xs ys : String) : IO Unit := do
  let (some x, some y) := (xs.toInt?, ys.toInt?) | return
  st.modify ({ · with edSlide := none })
  let s ← st.get
  match Bubble.EdPop.hit s.ui.editor x y with
  | some (.color i) =>
    let some c := Bubble.EdPop.palette[i]? | return
    if s.ui.editor == .draw then
      st.modify fun s => { s with ui := { s.ui with inkColor := c } }
      edApply st isInk fun ms id => ms.setRgb id c
    else
      st.modify fun s => { s with ui := { s.ui with ftColor := c },
                                  ftEdit := s.ftEdit.map ({ · with rgb := c }) }
      edApply st isFt fun ms id => ms.setRgb id c
    syncTool st
    drawOverlay st
    setStatus s!"colour {Marks.rgbHex c}"
  | some (.slider row) =>
    -- A new drag: its steps form one undo step of their own (task 10.7).
    st.modify fun s => { s with edSlide := some row, markHist := s.markHist.seal }
    edSlideTo st row x
  | none => pure ()

/-- A drag in the pop-over after a press on a slider moves it. -/
def edDrag (st : IO.Ref State) (xs _ys : String) : IO Unit := do
  let some x := xs.toInt? | return
  let some row := (← st.get).edSlide | return
  edSlideTo st row x

/-- Starts a stroke at point `p` of page `pg` (Draw mode, task 9.9): canvas line `inkcur` in
the drawing's colour and thickness. -/
def inkBegin (st : IO.Ref State) (pg : Nat) (p : Pt) : IO Unit := do
  let s ← st.get
  let some sl := slotOf s pg | return
  let (x, y, _, _) := sl.rect ⟨p.x, p.y, p.x, p.y⟩
  st.modify ({ · with inkStroke := some (pg, #[p]), sel := none, pressPt := none,
                      bubble := none })
  discard <| run [".c", "delete", "bub"]
  discard <| run ["::safepdf::inkStart", num x, num y,
    num (max 1 ((s.ui.inkThick : Rat) * sl.vp.zoom)), Marks.rgbHex s.ui.inkColor]

/-- Ends the stroke being drawn: it joins the session's drawing when that is still unsaved and
on the same page, else it starts a new drawing (one ink mark per session, as PDF.js). -/
def inkEnd (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some (pg, pts) := s.inkStroke | return
  st.modify ({ · with inkStroke := none })
  discard <| run [".c", "delete", "inkcur"]
  let stroke := pts.toList
  let joins := s.inkSession.bind fun id => (s.marks.find? id).filter fun m =>
    m.page == pg && !s.marks.isSaved id && isInk m
  let (marks, id, n) := match joins with
    | some m => (s.marks.addStroke m.id stroke, m.id, match m.kind with
        | .ink ss .. => ss.length + 1
        | _ => 1)
    | none =>
      let (ms, id) := s.marks.add pg .yellow
        (.ink [stroke] s.ui.inkThick s.ui.inkOpacity s.ui.inkColor)
      (ms, id, 1)
  st.modify ({ · with marks, inkSession := some id, markSel := some id })
  marksChanged st
  drawOverlay st
  setStatus s!"page {pg + 1}: drawing with {n} stroke(s) (Escape ends it; Delete removes it)"

/-- A drag to window `(wx, wy)` while a stroke is drawn: adds the point when it is at least a
pixel away from the last one; on release the stroke ends (`inkEnd`). -/
def inkMove (st : IO.Ref State) (wx wy : Int) (final : Bool) : IO Unit := do
  let s ← st.get
  let some (pg, pts) := s.inkStroke | return
  if let some p ← pagePointOn st pg wx wy then
    if let (some sl, some last) := (slotOf s pg, pts.back?) then
      let d := sl.vp.zoom * (max (p.x - last.x) (last.x - p.x) + max (p.y - last.y) (last.y - p.y))
      if d ≥ 1 then
        st.modify ({ · with inkStroke := some (pg, pts.push p) })
        let (x, y, _, _) := sl.rect ⟨p.x, p.y, p.x, p.y⟩
        discard <| run ["::safepdf::inkAdd", num x, num y]
  if final then inkEnd st

/-- A drag of a free text or drawing (task 9.9): its canvas items follow the pointer; on
release the mark is moved by the distance dragged (`Marks.Store.translate`). -/
def moveDrag (st : IO.Ref State) (wx wy : Int) (final : Bool) : IO Unit := do
  let s ← st.get
  let some (id, p0, last) := s.moveFrom | return
  let some m := s.marks.find? id | return
  let some sl := slotOf s m.page | return
  let some p ← pagePointOn st m.page wx wy | return
  let (ax, ay, _, _) := sl.rect ⟨last.x, last.y, last.x, last.y⟩
  let (bx, by', _, _) := sl.rect ⟨p.x, p.y, p.x, p.y⟩
  discard <| run [".c", "move", s!"m{id}", num (bx - ax), num (by' - ay)]
  st.modify ({ · with moveFrom := if final then none else some (id, p0, p) })
  if final then
    let dx := p.x - p0.x
    let dy := p.y - p0.y
    if sl.vp.zoom * (max dx (-dx) + max dy (-dy)) ≥ 2 then
      st.modify fun s => { s with marks := s.marks.translate id dx dy }
      marksChanged st
      if !(← updatePreview st) then drawOverlay st
      setStatus s!"{markName m} moved"
    else drawOverlay st

/-- **Undo** (`undo`, Ctrl+Z, Edit → Undo) or **Redo** (Ctrl+Shift+Z, Edit → Redo) of a mark
edit (task 10.7, `Marks.History`): an open text box is committed first (its edit becomes the
step undone); the marks go back (forward) one step and are drawn again — saved marks through
the preview (9.5g), so a saved mark whose edit or deletion is undone shows as in the file and
the title's `*` goes when nothing is left to save. The selection is kept when its mark is
still there; a drawing session ends; an open note popup whose note is gone or changed closes. -/
def undoRedo (st : IO.Ref State) (undo : Bool) : IO Unit := do
  if (← st.get).doc.isNone then return
  discard <| commitFt st
  -- In step with the store (every edit records itself; this only makes sure).
  st.modify fun s => { s with markHist := s.markHist.record s.marks.marks }
  let s ← st.get
  let some (h, marks) := (if undo then s.markHist.undo s.marks else s.markHist.redo s.marks) | do
    setStatus (if undo then "nothing to undo" else "nothing to redo")
  let sel := s.markSel.filter fun id => (marks.find? id).isSome
  st.modify ({ · with marks, markHist := h, markSel := sel, inkSession := none,
                      moveFrom := none })
  marksChanged st
  if !(← updatePreview st) then repaint st
  if let some nid := (← run ["set", "::safepdf::noteId"]).toNat? then
    if ((marks.find? nid).map (·.text)) != ((s.marks.find? nid).map (·.text)) then
      discard <| run ["::safepdf::noteGone", toString nid]
  let n := (if undo then h.future else h.past).length
  let left := if undo then h.past.length else h.future.length
  setStatus (← keyText (if undo then
      s!"undone ({left} more to undo, {n} to redo with Ctrl+Shift+Z)"
    else s!"redone ({left} more to redo, {n} to undo with Ctrl+Z)"))

/-- The free text or drawing under page point `p` of page `pg` (`Marks.Store.hitAt`). -/
def editorAt (s : State) (pg : Nat) (p : Pt) : Option Marks.Mark := do
  let sl ← slotOf s pg
  let id ← s.marks.hitAt sl.vp.box pg p
  (s.marks.find? id).filter (·.isEditor)

/-- The Select text button (task 10.8, `Toolbar.selectTool`): turns Highlight, Add text and
Draw off with their pop-overs (an open text box is committed, a drawing session ends); Select
text is then the active tool. Pressing it while it is active changes nothing. -/
def selectToolOn (st : IO.Ref State) : IO Unit := do
  if (← st.get).doc.isNone then return
  discard <| commitFt st
  st.modify fun s => { s with ui := Toolbar.selectTool s.ui, inkSession := none }
  syncTool st
  setStatus "Select text: drag over the text to select it; click a link to follow it, a mark \
    to select it"

/-- Handles `tool NAME` (an annotation tool or Save): Select text (task 10.8), Highlight (task 9.4), Add comment
(a note, `addNote`), Add text and Draw (task 9.9); Add image is not available yet (Print has no button for now). -/
def tool (st : IO.Ref State) (name : String) : IO Unit := do
  match Toolbar.toolOf name with
  | some .select => selectToolOn st
  | some .highlight => toolHighlight st
  | some .comment => addNote st none
  | some .text => toggleEditor st .text
  | some .draw => toggleEditor st .draw
  | some t => setStatus s!"{t.tip}: not available yet ({t.task})"
  | none => setStatus s!"internal: unknown tool {name}"

/-! ## Selection, copy and search (task 8.2c) -/

/-- Status line after a selection change. -/
def selStatus (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some (p, a, b) := s.sel | return
  if let .ok ix ← pageIndex st p then
    setStatus s!"page {p + 1}: selected {(Select.rangeText ix.cells a b).length} characters \
      ({← keyText "Ctrl+C"} copies)"

/-- Mouse press at window position `(wx, wy)`: clears the selection and remembers the page
point where a drag starts. -/
def press (st : IO.Ref State) (wx wy : Int) : IO Unit := do
  st.modify ({ · with bubblePress := false, moveFrom := none })
  if ← bubbleClick st wx wy then return
  -- Task 9.9: a click elsewhere commits an open text box (and does nothing else, as PDF.js);
  -- in Draw mode a press starts a stroke; a press on a free text or drawing selects it and
  -- starts moving it.
  if ← commitFt st then
    st.modify ({ · with bubblePress := true })
    return
  if (← st.get).ui.editor == .draw then
    if let some (pg, p) ← pagePointAt st wx wy then inkBegin st pg p
    return
  if let some (pg, p) ← pagePointAt st wx wy then
    if let some m := editorAt (← st.get) pg p then
      st.modify fun s => { s with sel := none, pressPt := none, markSel := some m.id,
                                  moveFrom := some (m.id, p, p), ui := { s.ui with picker := false } }
      drawOverlay st
      let dbl := if isFt m then "; double-click edits it" else ""
      setStatus s!"{markName m} selected (drag to move it; Delete removes it{dbl})"
      return
  st.modify fun s => { s with sel := none, pressPt := none, markSel := none,
                              ui := { s.ui with picker := false } }
  if let some (pg, p) ← pagePointAt st wx wy then
    st.modify ({ · with pressPt := some p, pressPage := pg })
  drawOverlay st

/-- Mouse drag (`final`: release) to `(wx, wy)`: selects the glyphs from the one nearest to
the press point to the one nearest to this point, in reading order. A release where the press
was (a click) selects nothing. -/
def dragTo (st : IO.Ref State) (wx wy : Int) (final : Bool) : IO Unit := do
  let s ← st.get
  if s.bubblePress then
    if final then st.modify ({ · with bubblePress := false })
    return
  if s.inkStroke.isSome then inkMove st wx wy final; return
  if s.moveFrom.isSome then moveDrag st wx wy final; return
  let some p0 := s.pressPt | return
  if final then st.modify ({ · with pressPt := none })
  -- The drag selects on the page it started on (task 9.3).
  let pg := s.pressPage
  let some p1 ← pagePointOn st pg wx wy | return
  if final && p0 == p1 then
    -- A click in place: select the mark under it (task 9.4; marks lie above links), else
    -- activate the link under it (task 8.2d).
    if ← selectMarkAt st pg p1 true then return
    -- Add text mode: a click places a text box (task 9.9).
    if s.ui.editor == .text then
      ftOpenAt st none pg p1 "" s.ui.ftSize s.ui.ftColor
      return
    -- A file attachment annotation's icon selects its row in the attachments panel (task
    -- 9.r10); the attachment is not opened.
    if let some i := Attach.iconAt s.attIcons pg p1 then
      attSelect st i
      return
    if let some (_, l) := Links.linkAt (← linksOf st pg) p1 then activate st l.action
    return
  -- Add text mode: dragging selects nothing.
  if s.ui.editor == .text then return
  match ← pageIndex st pg with
  | .ok ix =>
    if let some (a, b) := Select.dragRange ix.cells p0 p1 then
      st.modify ({ · with sel := some (pg, a, b) })
      drawOverlay st
      if final then
        selStatus st
        -- With the Highlight tool on, the mouse-up highlights at once (PDF.js, task 9.8).
        if (← st.get).ui.highlightOnRelease true then highlight st none
  | .error e => setStatus s!"page {pg + 1}: no text: {e}"

/-- Double click at `(wx, wy)`: selects the word of the nearest glyph (`Select.wordAt`). -/
def selectWord (st : IO.Ref State) (wx wy : Int) : IO Unit := do
  st.modify ({ · with pressPt := none, moveFrom := none })
  let s ← st.get
  -- The second click of a double click on the bubble is not a word selection (task 9.8).
  if let some (cx, cy) ← canvasPos wx wy then
    if (s.bubble.any fun (_, r) => r.contains cx cy) || (s.pickerAt.any (·.contains cx cy)) then
      return
  -- Task 9.9: in Draw mode the second press draws; an open text box keeps the double click;
  -- a double click on a text box edits it.
  if s.ui.editor == .draw then
    if let some (pg, p) ← pagePointAt st wx wy then inkBegin st pg p
    return
  if s.ftEdit.isSome then return
  if let some (pg, p) ← pagePointAt st wx wy then
    if let some m := editorAt s pg p then
      if let .freeText t pos sz c := m.kind then
        st.modify ({ · with markSel := some m.id })
        ftOpenAt st (some m.id) pg pos t sz c
      return
  let some (pg, p) ← pagePointAt st wx wy | return
  match ← pageIndex st pg with
  | .ok ix =>
    if let some i := Select.nearest ix.cells p then
      let (a, b) := Select.wordAt ix.cells i
      st.modify ({ · with sel := some (pg, a, b) })
      drawOverlay st
      selStatus st
      if (← st.get).ui.highlightOnRelease true then highlight st none
  | .error e => setStatus s!"page {pg + 1}: no text: {e}"

/-- Selects all the text of the current page (Ctrl+A). -/
def selectAll (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  if s.doc.isNone then return
  match ← pageIndex st s.page with
  | .ok ix =>
    if ix.cells.size == 0 then setStatus s!"page {s.page + 1}: no text"
    else
      st.modify ({ · with sel := some (s.page, 0, ix.cells.size - 1) })
      drawOverlay st
      selStatus st
  | .error e => setStatus s!"page {s.page + 1}: no text: {e}"

/-- Copies the selected text to the clipboard (Ctrl+C); the text is one quoted Tcl word.
Invisible text (`Tr 3`/`Tr 7`) is copied and counted in the status (`copyStatus`, task 12.5);
text outside the CropBox or clipped away is never in the selection. -/
def copySel (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  match s.sel with
  | some (p, a, b) =>
    if let .ok ix ← pageIndex st p then
      let t := Select.rangeText ix.cells a b
      discard <| run ["clipboard", "clear"]
      discard <| run ["clipboard", "append", "--", t]
      setStatus (Select.copyStatus t.length (ix.hiddenChars a b))
  | none => setStatus (← keyText "nothing selected (drag over text, double-click a word, or Ctrl+A)")

/-- Scrolls the current search hit into view (centred on an axis where it is not visible). -/
def scrollToHit (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some (p, k) := s.hit | return
  let some sl := slotOf s p | return
  let .ok ix ← pageIndex st p | return
  let some (a, b) := (ix.hits s.query)[k]? | return
  let some u := (Select.rangeBoxes ix.cells a b).foldl (fun acc b =>
    some (match acc with | some u => Select.Box.union u b | none => b)) none | return
  let (x0, y0, x1, y1) := sl.rect u
  let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
    View.parseDecimal (← run [".c", "canvasy", "0"])) | return
  let cw : Rat := s.canvasW
  let ch : Rat := s.canvasH
  if x0 < vx || vx + cw < x1 then
    discard <| run [".c", "xview", "moveto", fmtFrac (((x0 + x1) / 2 - cw / 2) / (s.regionW : Rat))]
  if y0 < vy || vy + ch < y1 then
    discard <| run [".c", "yview", "moveto", fmtFrac (((y0 + y1) / 2 - ch / 2) / (s.regionH : Rat))]
  viewChanged st

/-- Whether page `p`'s text index is cached (searching it costs no work). -/
def textCached (s : State) (p : Nat) : Bool :=
  match s.texts[p]? with
  | some (some _) => true
  | _ => false

/-- How a search ended: a hit (page, index on the page, hits on the page, wrapped around), no
hit, or (task 12.3) stopped after indexing this many pages because its shared work allowance
(`Budget.Allowance`) was used up. -/
inductive SearchEnd where
  /-- A hit. -/
  | hit (p k c : Nat) (wrapped : Bool)
  /-- No hit in the document. -/
  | none
  /-- The work allowance ran out after indexing `pages` pages. -/
  | stopped (pages : Nat)

/-- The next (`forward`) or previous search hit after the current one. Searches the current
page, then the following (preceding) pages, wrapping around to the current page. Task 12.3:
the whole search shares **one work allowance** (`Budget.Allowance`: pages to index and wall
time); a page whose index is cached costs nothing, every other page spends one page of it, and
when it is used up the search stops (`SearchEnd.stopped`; the next Find goes on from where the
indexed pages end, since they are cached now). -/
def nextHit (st : IO.Ref State) (forward : Bool) : IO SearchEnd := do
  let s ← st.get
  let n := s.pageCount
  let q := s.query
  let cur := match s.hit with
    | some (p, k) => if p == s.page then some k else none
    | none => none
  let mut allow := Budget.Allowance.start Budget.ceilings (← IO.monoMsNow)
  let mut spent := 0
  if !textCached s s.page then
    match allow.spend (← IO.monoMsNow) with
    | some a => allow := a; spent := spent + 1
    | none => return .stopped spent
  if let .ok ix ← pageIndex st s.page then
    let c := (ix.hits q).size
    if let some k := Select.hitOnCurrent c cur forward then return .hit s.page k c false
  for p in Select.searchPages n s.page forward do
    if !textCached (← st.get) p then
      match allow.spend (← IO.monoMsNow) with
      | some a => allow := a; spent := spent + 1
      | none =>
        st.modify fun s => { s with searchStops := s.searchStops + 1 }
        return .stopped spent
    if let .ok ix ← pageIndex st p then
      let c := (ix.hits q).size
      if c > 0 then
        return .hit p (Select.firstHitOn forward c) c (Select.wrappedTo forward s.page p)
  return .none

/-- Handles `find next|prev QUERY` and `find close`. -/
def find (st : IO.Ref State) (args : List String) : IO Unit := do
  match args with
  | ["close"] =>
    st.modify ({ · with query := #[], hit := none })
    drawOverlay st
  | [dir, query] =>
    let s ← st.get
    if s.doc.isNone then return
    let q := Select.normQuery query
    let qs := String.ofList q.toList
    if q.isEmpty then
      st.modify ({ · with query := #[], hit := none })
      drawOverlay st
      setStatus "search: empty query"
      return
    if q != s.query then st.modify ({ · with query := q, hit := none })
    match ← nextHit st (dir != "prev") with
    | .none =>
      st.modify ({ · with hit := none })
      drawOverlay st
      setStatus s!"\"{qs}\": not found"
    | .stopped n =>
      drawOverlay st
      setStatus s!"\"{qs}\": not found in the {n} pages searched so far (this search's work \
        allowance is used up); search again to go on"
    | .hit p k c wrapped =>
      st.modify ({ · with hit := some (p, k) })
      if p != s.page then goTo st p
      drawOverlay st
      scrollToHit st
      setStatus s!"\"{qs}\": hit {k + 1}/{c} on page {p + 1}{if wrapped then " (wrapped)" else ""}"
  | _ => setStatus s!"internal: bad find {args}"

/-! ## Smoke mode -/

/-- Sends the key `k` to the canvas through Tk (as a user would type it). -/
def sendKey (k : String) : IO Unit := do
  try
    discard <| run ["focus", "-force", ".c"]
    discard <| run ["event", "generate", ".c", s!"<Key-{k}>"]
  catch _ => pure ()

/-- Generates the Tk event `pat` (with options `opts`) on window `w`, as a user would. -/
def sendEvent (w pat : String) (opts : List String := []) : IO Unit := do
  try
    discard <| run ["focus", "-force", w]
    discard <| run (["event", "generate", w, pat] ++ opts)
  catch _ => pure ()

/-- Window position of the centre of cell `i` of the shown page. -/
def cellWindowPos (st : IO.Ref State) (ix : Select.PageIndex) (i : Nat) :
    IO (Option (String × String)) := do
  let s ← st.get
  let some bx := shownBox s | return none
  let some c := ix.cells[i]? | return none
  let (x0, y0, x1, y1) := canvasRect s bx c.box
  let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
    View.parseDecimal (← run [".c", "canvasy", "0"])) | return none
  return some (toString ((x0 + x1) / 2 - vx).floor, toString ((y0 + y1) / 2 - vy).floor)

/-- The clipboard's text (`<empty>` when it holds none). -/
def clipGet : IO String := do
  try run ["clipboard", "get"] catch _ => pure "<empty>"

/-- Number of canvas items with tag `tag`. -/
def tagCount (tag : String) : IO Nat := do
  return ((← run [".c", "find", "withtag", tag]).splitOn " ").filter (!·.isEmpty) |>.length

/-- Smoke steps of the selection/copy/search test (`SAFEPDF_VIEWER_SMOKE_MODE=text`, task
8.2c), on a document whose page 1 contains the words `safe` and `world` and page 2 the
phrase `zebra crossing`:
* step 0: Ctrl+A, Ctrl+C → `clip-all.txt` (clipboard text); a double click on the first glyph
  of `safe`, Ctrl+C → `word.txt`; a drag (press, motion with button 1, release) from the first
  glyph of the page to the last glyph of `world`, Ctrl+C → `drag.txt`; `sel.txt` (highlight
  rectangles after Ctrl+A, status);
* step 1: Ctrl+F, query `ZEBRA  crossing`, Return → `find.txt` (page, status, highlight
  count); F3 (wraps to the same hit), Shift+F3, an absent query, Escape (closes the search). -/
def smokeText (st : IO.Ref State) (dir : String) : IO Unit := do
  let s ← st.get
  st.modify ({ · with smokeStep := s.smokeStep + 1 })
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let status : IO String := run [".status", "cget", "-text"]
  let copy : IO String := do
    sendEvent ".c" "<Control-Key-c>"
    clipGet
  let click (pos : String × String) (pat : String) (state : List String := []) : IO Unit :=
    sendEvent ".c" pat (["-x", pos.1, "-y", pos.2] ++ state)
  match s.smokeStep with
  | 0 =>
    sendEvent ".c" "<Control-Key-a>"
    let selItems ← tagCount "sel"
    let selStatus ← status
    IO.FS.writeFile (file "clip-all.txt") (← copy)
    let mut word := "<no index>"
    let mut drag := "<no index>"
    if let .ok ix ← pageIndex st 0 then
      if let some (a, _) := (ix.hits (Select.normQuery "safe"))[0]? then
        if let some pos ← cellWindowPos st ix a then
          for _ in [0:2] do
            click pos "<ButtonPress-1>"
            click pos "<ButtonRelease-1>"
          word ← copy
          -- The word's highlight in image pixels, and the page image, for an ink check.
          let s' ← st.get
          IO.FS.writeFile (file "word-rect.txt")
            s!"{← run [".c", "bbox", "sel"]}\n{s'.imgX} {s'.imgY}\n"
          try discard <| run [photoOf 0, "write", file "text-page-1.ppm", "-format", "ppm"]
          catch _ => pure ()
      if let some (_, b) := (ix.hits (Select.normQuery "world"))[0]? then
        if let (some p0, some p1) := (← cellWindowPos st ix 0, ← cellWindowPos st ix b) then
          click p0 "<ButtonPress-1>"
          click p1 "<Motion>" ["-state", "256"]
          click p1 "<ButtonRelease-1>" ["-state", "256"]
          drag ← copy
    IO.FS.writeFile (file "word.txt") word
    IO.FS.writeFile (file "drag.txt") drag
    IO.FS.writeFile (file "sel.txt") s!"sel-items: {selItems}\nstatus: {selStatus}\n"
    discard <| run ["after", "300", "::safepdf::emit smoke"]
  | 1 =>
    sendEvent ".c" "<Control-Key-f>"
    discard <| run ["update", "idletasks"]
    discard <| run ["set", "::safepdf::query", "ZEBRA  crossing"]
    sendEvent ".find.e" "<Key-Return>"
    let page1 := (← st.get).page + 1
    let status1 ← status
    let hits1 ← tagCount "hit"
    sendEvent ".find.e" "<Key-F3>"
    let status2 ← status
    sendEvent ".find.e" "<Shift-Key-F3>"
    let status3 ← status
    discard <| run ["set", "::safepdf::query", "no such words"]
    sendEvent ".find.e" "<Key-Return>"
    let status4 ← status
    sendEvent ".find.e" "<Key-Escape>"
    let hits5 ← tagCount "hit"
    IO.FS.writeFile (file "find.txt")
      s!"page: {page1}\nstatus: {status1}\nhit-items: {hits1}\nstatus-f3: {status2}\n\
        status-shift-f3: {status3}\nstatus-absent: {status4}\nhit-items-closed: {hits5}\n"
    discard <| run ["destroy", "."]
  | _ => discard <| run ["destroy", "."]

/-- Window position of the centre of a page-space box on the shown page. -/
def boxWindowPos (st : IO.Ref State) (b : Box) : IO (Option (String × String)) := do
  let s ← st.get
  let some bx := shownBox s | return none
  let (x0, y0, x1, y1) := canvasRect s bx b
  let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
    View.parseDecimal (← run [".c", "canvasy", "0"])) | return none
  return some (toString ((x0 + x1) / 2 - vx).floor, toString ((y0 + y1) / 2 - vy).floor)

/-- Window position (in `.ol.t`) of the first character of outline row `id` (`oK`); `none`
when the row is hidden (elided under a closed parent) or scrolled away. -/
def olItemPos (id : String) : IO (Option (String × String)) := do
  let r ← run [".ol.t", "tag", "ranges", id]
  let some i := (r.splitOn " ").head? | return none
  if i.isEmpty then return none
  match ((← run [".ol.t", "bbox", i]).splitOn " ").filterMap String.toNat? with
  | [x, y, w, h] => return some (toString (x + w / 2), toString (y + h / 2))
  | _ => return none

/-- Smoke steps of the toolbar test (`SAFEPDF_VIEWER_SMOKE_MODE=toolbar`, task 9.7), on any
document of at least two pages: the toolbar layout, the sidebar (open on load only
when the document has an outline, its toggle always (task 9.r9); collapsing/expanding a row with children through its
disclosure triangle; the toggle button), the arrows (generated clicks), the page field
(Enter on a valid page, on an out-of-range number and on text: reverts), paging keys
updating the field, the zoom drop-down (choices, labels, custom percentages after − / +), the
overflow menu and the disabled tool buttons. Results go into `toolbar.txt` as `key: value`
lines. -/
def smokeToolbar (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let page : IO Nat := return (← st.get).page + 1
  let field : IO String := run ["set", "::safepdf::pageText"]
  let ofl : IO String := run [".bar.of", "cget", "-text"]
  let zlabel : IO String := run [".bar.zoom", "itemcget", "label", "-text"]
  let zsel : IO String := run ["set", "::safepdf::zoomSel"]
  let mut out : Array String := #[]
  discard <| run ["update"]
  let s ← st.get
  let n := s.pageCount
  out := out.push s!"pages: {n}"
  out := out.push s!"has-outline: {!s.outline.isEmpty}"
  out := out.push s!"sidebar-shown: {s.outlineShown}"
  out := out.push s!"panes: {← run [".pw", "panes"]}"
  out := out.push s!"toggle-mapped: {← run ["winfo", "ismapped", ".bar.sidebar"]}"
  let mut packed : Array String := #[]
  for g in [".bar.l", ".bar.m", ".bar.r"] do
    packed := packed.push s!"{g}={",".intercalate ((← run ["pack", "slaves", g]).splitOn " ")}"
  out := out.push s!"layout: {" ".intercalate packed.toList}"
  out := out.push s!"field0: {← field}"
  out := out.push s!"of0: {← ofl}"
  out := out.push s!"zoom-label0: {← zlabel}"
  out := out.push s!"zoom-sel0: {← zsel}"
  let mut zl : Array String := #[]
  let zn := (← run [".zoommenu", "index", "end"]).toNat?.getD 0
  for i in [0:zn + 1] do zl := zl.push (← run [".zoommenu", "entrycget", toString i, "-label"])
  out := out.push s!"zoom-menu: {"|".intercalate zl.toList}"
  let mut ml : Array String := #[]
  let mn := (← run [Toolbar.morePath, "index", "end"]).toNat?.getD 0
  for i in [0:mn + 1] do
    if (← run [Toolbar.morePath, "type", toString i]) != "separator" then
      ml := ml.push (← run [Toolbar.morePath, "entrycget", toString i, "-label"])
  out := out.push s!"more-menu: {"|".intercalate ml.toList}"
  let btnStates (ws : List String) : IO String := do
    let mut v : Array String := #[]
    for w in ws do v := v.push s!"{w}={← run ["::safepdf::btnState", w]}"
    return ",".intercalate v.toList
  out := out.push s!"states0: {← btnStates [".bar.prev", ".bar.next", ".bar.zout", ".bar.zin", ".bar.more"]}"
  out := out.push s!"tools: {← btnStates [".bar.highlight", ".bar.comment", ".bar.text", ".bar.draw", ".bar.image", ".bar.save"]}"
  -- A disabled tool ignores clicks.
  let click (w : String) : IO Unit := do
    sendEvent w "<ButtonPress-1>" ["-x", "16", "-y", "16"]
    sendEvent w "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
  let st0 ← run [".status", "cget", "-text"]
  click ".bar.image"
  out := out.push s!"status-unchanged-after-tool: {st0 == (← run [".status", "cget", "-text"])}"
  -- Arrows (generated clicks on the canvas buttons).
  click ".bar.next"
  out := out.push s!"after-next: {← page} {← field} {← ofl}"
  click ".bar.next"
  click ".bar.prev"
  out := out.push s!"after-next-prev: {← page} {← field}"
  click ".bar.prev"
  click ".bar.prev"
  out := out.push s!"after-prev-at-start: {← page} {← field}"
  -- The page field: a valid number, an out-of-range number, text (both revert).
  let enter (txt : String) : IO Unit := do
    sendEvent ".bar.pg.e" "<FocusIn>"
    discard <| run ["set", "::safepdf::pageText", txt]
    sendEvent ".bar.pg.e" "<Key-Return>"
  enter (toString n)
  out := out.push s!"entry-last: {← page} {← field}"
  enter "999"
  out := out.push s!"entry-999: {← page} {← field}"
  enter "abc"
  out := out.push s!"entry-abc: {← page} {← field}"
  enter (Toolbar.entryText s.labels 0)
  out := out.push s!"entry-first: {← page} {← field}"
  out := out.push s!"history-after-entry: {(← st.get).history.back.length}"
  -- Typing and leaving the field without Enter reverts it.
  discard <| run ["set", "::safepdf::pageText", "2"]
  discard <| run ["::safepdf::emit", "pageRevert"]
  out := out.push s!"entry-revert: {← page} {← field}"
  -- Paging keys update the field.
  sendKey "End"
  out := out.push s!"key-end: {← page} {← field}"
  sendKey "Home"
  out := out.push s!"key-home: {← page} {← field}"
  -- Zoom drop-down and buttons.
  let choose (lbl : String) : IO Unit := do
    discard <| run [".zoommenu", "invoke", lbl]
    discard <| run ["update", "idletasks"]
  let zoomNow : IO String := do
    let s ← st.get
    return s!"{← zlabel}|{← zsel}|{View.zoomPct s.shownZoom s.scaling}"
  choose "Page Width"
  out := out.push s!"zoom-page-width: {← zoomNow}"
  choose "Page Fit"
  out := out.push s!"zoom-page-fit: {← zoomNow}"
  choose "Actual Size"
  out := out.push s!"zoom-actual: {← zoomNow}"
  choose "150%"
  out := out.push s!"zoom-150: {← zoomNow}"
  click ".bar.zin"
  out := out.push s!"zoom-in-200: {← zoomNow}"
  click ".bar.zout"
  click ".bar.zout"
  out := out.push s!"zoom-out-125: {← zoomNow}"
  choose "50%"
  click ".bar.zout"
  out := out.push s!"zoom-custom-33: {← zoomNow}"
  choose "Automatic Zoom"
  out := out.push s!"zoom-auto: {← zoomNow}"
  -- Overflow menu.
  discard <| run [Toolbar.morePath, "invoke", "Last page"]
  out := out.push s!"more-last: {← page} {← field}"
  discard <| run [Toolbar.morePath, "invoke", "First page"]
  out := out.push s!"more-first: {← page} {← field}"
  -- Sidebar: disclosure triangles and the toggle button.
  let s ← st.get
  if let some r := s.olRows.find? (·.hasKids) then
    if let some k := s.olRows.find? (·.parent == some r.index) then
      discard <| run ["update"]
      out := out.push s!"child-visible: {(← olItemPos s!"o{k.index}").isSome}"
      if let some pos ← olItemPos s!"t{r.index}" then
        sendEvent ".ol.t" "<ButtonRelease-1>" ["-x", pos.1, "-y", pos.2]
        discard <| run ["update"]
        out := out.push s!"child-visible-after-collapse: {(← olItemPos s!"o{k.index}").isSome}"
        sendEvent ".ol.t" "<ButtonRelease-1>" ["-x", pos.1, "-y", pos.2]
        discard <| run ["update"]
        out := out.push s!"child-visible-after-expand: {(← olItemPos s!"o{k.index}").isSome}"
  if (← run ["winfo", "ismapped", ".bar.sidebar"]) == "1" then
    out := out.push s!"toggle-pressed0: {← run ["set", "::safepdf::btn(tog,.bar.sidebar)"]}"
    click ".bar.sidebar"
    out := out.push s!"after-toggle: {(← st.get).outlineShown} {← run [".pw", "panes"]} {← run ["set", "::safepdf::btn(tog,.bar.sidebar)"]}"
    click ".bar.sidebar"
    out := out.push s!"after-toggle2: {(← st.get).outlineShown} {← run [".pw", "panes"]}"
  IO.FS.writeFile (file "toolbar.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of the navigation test (`SAFEPDF_VIEWER_SMOKE_MODE=nav`, task 8.2d), on a
three-page document labelled `i`, `ii`, `1` whose page 1 has an internal link (to page 3) and
a URI link, and whose outline is `Intro` (page 1), `Chapter` (page 3, `/XYZ 0 400`) with child
`Section` (page 2, through a named destination). Everything is driven by Tk events (pointer
motion and clicks on the links and outline items, Alt+Left/Right, Ctrl+G, F9) and the results
go into `nav.txt` as `key: value` lines; the URI dialog confirms itself in smoke mode after
recording the address it shows (`::safepdf::shownUri`). -/
def smokeNav (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let status : IO String := run [".status", "cget", "-text"]
  let page : IO Nat := return (← st.get).page + 1
  let mut out : Array String := #[]
  discard <| run ["update"]
  let s ← st.get
  out := out.push s!"title0: {← run ["wm", "title", "."]}"
  out := out.push s!"outline-shown: {s.outlineShown}"
  out := out.push s!"outline-titles: {"|".intercalate (s.outline.toList.map (·.title))}"
  out := out.push s!"outline-depths: {s.outline.toList.map (·.depth)}"
  let at' (pos : String × String) (w pat : String) (opts : List String := []) : IO Unit :=
    sendEvent w pat (["-x", pos.1, "-y", pos.2] ++ opts)
  let clickAt (pos : String × String) : IO Unit := do
    at' pos ".c" "<ButtonPress-1>"
    at' pos ".c" "<ButtonRelease-1>"
  let ls ← linksOf st 0
  out := out.push s!"links-page1: {ls.size}"
  -- Internal link: hover, click, history.
  if let some l := ls[0]? then
    if let some pos ← boxWindowPos st l.box then
      at' pos ".c" "<Motion>"
      out := out.push s!"cursor-internal: {← run [".c", "cget", "-cursor"]}"
      out := out.push s!"status-hover-internal: {← status}"
      clickAt pos
      out := out.push s!"page-after-link: {← page}"
      out := out.push s!"title-after-link: {← run ["wm", "title", "."]}"
  sendEvent ".c" "<Alt-Key-Left>"
  out := out.push s!"page-after-back: {← page}"
  sendEvent ".c" "<Alt-Key-Right>"
  out := out.push s!"page-after-forward: {← page}"
  sendEvent ".c" "<Alt-Key-Left>"
  out := out.push s!"page-after-back2: {← page}"
  -- URI link: hover shows the address; a click shows the dialog (auto-confirmed).
  if let some l := ls[1]? then
    if let some pos ← boxWindowPos st l.box then
      at' pos ".c" "<Motion>"
      out := out.push s!"cursor-uri: {← run [".c", "cget", "-cursor"]}"
      out := out.push s!"status-hover-uri: {← status}"
      discard <| run ["set", "::safepdf::shownUri", "<no dialog>"]
      clickAt pos
      out := out.push s!"page-after-uri: {← page}"
      out := out.push s!"status-after-uri: {← status}"
      IO.FS.writeFile (file "uri-shown.txt") (← run ["set", "::safepdf::shownUri"])
      IO.FS.writeFile (file "uri-clip.txt") (← clipGet)
  -- Outline: click `Section` (o2), then `Chapter` (o1) at 200 %.
  discard <| run ["update"]
  let itemPos (id : String) : IO (Option (String × String)) := olItemPos id
  if let some pos ← itemPos "o2" then
    at' pos ".ol.t" "<ButtonRelease-1>"
  out := out.push s!"page-after-outline-section: {← page}"
  out := out.push s!"title-after-outline-section: {← run ["wm", "title", "."]}"
  sendKey "0"
  for _ in [0:3] do sendKey "plus"
  out := out.push s!"zoom: {View.zoomPct (← st.get).shownZoom (← st.get).scaling}"
  if let some pos ← itemPos "o1" then
    at' pos ".ol.t" "<ButtonRelease-1>"
  out := out.push s!"page-after-outline-chapter: {← page}"
  out := out.push s!"yview-after-outline-chapter: {← run [".c", "yview"]}"
  sendKey "f"
  -- Ctrl+G: "ii" is page 2; the label "1" is page 3 (labels win over page numbers).
  let gotoWith (txt : String) : IO Unit := do
    sendEvent ".c" "<Control-Key-g>"
    discard <| run ["update", "idletasks"]
    discard <| run ["set", "::safepdf::gotoText", txt]
    sendEvent ".goto.e" "<Key-Return>"
  gotoWith "ii"
  out := out.push s!"page-after-goto-ii: {← page}"
  gotoWith "1"
  out := out.push s!"page-after-goto-1: {← page}"
  out := out.push s!"title-after-goto-1: {← run ["wm", "title", "."]}"
  gotoWith "nope"
  out := out.push s!"page-after-goto-nope: {← page}"
  out := out.push s!"status-goto-nope: {← status}"
  discard <| run ["::safepdf::hideGoto"]
  sendEvent ".c" "<Key-F9>"
  out := out.push s!"outline-shown-after-f9: {(← st.get).outlineShown}"
  out := out.push s!"panes-after-f9: {← run [".pw", "panes"]}"
  IO.FS.writeFile (file "nav.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of the menubar test (`SAFEPDF_VIEWER_SMOKE_MODE=menu`, task 9.1), on the
three-page navigation document of `smokeNav`. Every action goes through the menubar: entries
are invoked by their `.menubar` path and label (`.menubar.go invoke {Next page}`), as a click
would; enabled states are read with `entrycget -state`. Results go into `menu.txt` as
`key: value` lines; the run ends with File → Quit. -/
def smokeMenu (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let status : IO String := run [".status", "cget", "-text"]
  let page : IO Nat := return (← st.get).page + 1
  let mut out : Array String := #[]
  discard <| run ["update"]
  let menuOf (c : Menu.Cmd) : String := ((Menu.locate c).map (·.1)).getD ".menubar"
  let invoke (c : Menu.Cmd) : IO Unit := do
    discard <| run [menuOf c, "invoke", c.label]
    discard <| run ["update", "idletasks"]
  let state (c : Menu.Cmd) : IO String := run [menuOf c, "entrycget", c.label, "-state"]
  out := out.push s!"menubar: {← run [".", "cget", "-menu"]}"
  let mut cascades : Array String := #[]
  for i in [0:Menu.menubar.length] do
    cascades := cascades.push (← run [Menu.barPath, "entrycget", toString i, "-label"])
  out := out.push s!"cascades: {"|".intercalate cascades.toList}"
  for m in Menu.menubar do
    let mut labels : Array String := #[]
    let n := (← run [m.path, "index", "end"]).toNat?.getD 0
    for i in [0:n + 1] do
      if (← run [m.path, "type", toString i]) != "separator" then
        labels := labels.push (← run [m.path, "entrycget", toString i, "-label"])
    out := out.push s!"entries{m.path}: {"|".intercalate labels.toList}"
  let statesOf (cs : List Menu.Cmd) : IO String := do
    let mut v : Array String := #[]
    for c in cs do v := v.push s!"{c.label}={← state c}"
    return ",".intercalate v.toList
  let goCmds : List Menu.Cmd := [.prevPage, .nextPage, .firstPage, .lastPage, .back, .forward]
  out := out.push s!"states-page1: {← statesOf (goCmds ++ [.copy, .outline])}"
  out := out.push s!"toolbar-prev-page1: {← run ["::safepdf::btnState", ".bar.prev"]}"
  invoke .nextPage
  out := out.push s!"page-after-next: {← page}"
  invoke .lastPage
  out := out.push s!"page-after-last: {← page}"
  out := out.push s!"states-page3: {← statesOf goCmds}"
  invoke .nextPage
  out := out.push s!"page-after-next-at-end: {← page}"
  invoke .firstPage
  out := out.push s!"page-after-first: {← page}"
  invoke .prevPage
  out := out.push s!"page-after-prev-at-start: {← page}"
  -- Go → Go to page… opens the go-to bar; a jump records history for Go → Back / Forward.
  invoke .gotoPage
  out := out.push s!"goto-bar-mapped: {← run ["winfo", "ismapped", ".goto"]}"
  discard <| run ["set", "::safepdf::gotoText", "ii"]
  sendEvent ".goto.e" "<Key-Return>"
  out := out.push s!"page-after-goto: {← page}"
  out := out.push s!"states-after-goto: {← statesOf [.back, .forward]}"
  invoke .back
  out := out.push s!"page-after-back: {← page}"
  invoke .forward
  out := out.push s!"page-after-forward: {← page}"
  -- View → Outline (a check entry) hides and shows the panel; the check follows.
  invoke .outline
  out := out.push s!"outline-after-view-outline: {(← st.get).outlineShown} {← run ["set", Menu.outlineVar]}"
  invoke .outline
  out := out.push s!"outline-after-view-outline2: {(← st.get).outlineShown} {← run ["set", Menu.outlineVar]}"
  -- View → zoom and rotation.
  invoke .actualSize
  -- The mode's percentage (the shown zoom is quantised to 1/64 and may print as 99 %).
  let pct : IO String := do
    match (← st.get).zoomSel.mode with
    | some (.scale p) => return toString p
    | _ => return modeName (← st.get).zoomSel
  out := out.push s!"zoom-actual: {← pct}"
  invoke .zoomIn
  out := out.push s!"zoom-in: {← pct}"
  invoke .zoomOut
  out := out.push s!"zoom-out: {← pct}"
  invoke .fitWidth
  out := out.push s!"mode-fit-width: {modeName (← st.get).zoomSel}"
  invoke .fitPage
  out := out.push s!"mode-fit-page: {modeName (← st.get).zoomSel}"
  invoke .rotateCw
  out := out.push s!"rot-after-right: {View.rotDeg (← st.get).rot}"
  invoke .rotateCcw
  out := out.push s!"rot-after-left: {View.rotDeg (← st.get).rot}"
  -- Edit → Find… opens the find bar; Edit → Select all on a page without text says so.
  invoke .find
  out := out.push s!"find-bar-mapped: {← run ["winfo", "ismapped", ".find"]}"
  discard <| run ["::safepdf::hideFind"]
  invoke .selectAll
  out := out.push s!"status-select-all: {← status}"
  -- Wheel across pages (task 9.2), with generated Tk 9 `<MouseWheel>` events (%D in 1/120
  -- notches), X11 Button-4/5 and Shift+wheel.
  let wheelEv (pat : String) (d : Int) : IO Unit :=
    sendEvent ".c" pat ["-delta", toString d, "-x", "200", "-y", "200"]
  let yv : IO String := run [".c", "yview"]
  let xv : IO String := run [".c", "xview"]
  let first (v : String) : String := ((viewFracs v).map (fun (a, _) => fmtFrac a)).getD "?"
  invoke .firstPage
  invoke .fitPage
  wheelEv "<MouseWheel>" (-120)
  out := out.push s!"page-after-wheel-fit-down: {← page}"
  wheelEv "<MouseWheel>" 120
  out := out.push s!"page-after-wheel-fit-up: {← page}"
  invoke .actualSize
  for _ in [0:3] do invoke .zoomIn
  out := out.push s!"wheel-zoom: {← pct}"
  discard <| run [".c", "yview", "moveto", "0"]
  out := out.push s!"y-start: {← yv}"
  -- Notches down until the page turns: the view must reach the bottom first, and only the
  -- one notch after that turns the page.
  let mut n := 0
  let mut atEnd := 0
  let mut yLast := ""
  while (← st.get).page == 0 && n < 200 do
    yLast ← yv
    if let some (_, b) := viewFracs yLast then
      if b ≥ 1 then atEnd := atEnd + 1
    wheelEv "<MouseWheel>" (-120)
    n := n + 1
  out := out.push s!"wheel-down-events: {n}"
  out := out.push s!"wheel-down-events-at-end: {atEnd}"
  out := out.push s!"y-before-turn: {yLast}"
  out := out.push s!"page-after-wheel-down: {← page}"
  out := out.push s!"y-after-wheel-down: {← yv}"
  -- Tiny deltas (1/12 notch) upwards at the top of page 2: eleven are not enough to turn
  -- back, the twelfth (one notch in all) is.
  for _ in [0:11] do wheelEv "<MouseWheel>" 10
  out := out.push s!"page-after-11-tiny-up: {← page}"
  wheelEv "<MouseWheel>" 10
  out := out.push s!"page-after-12-tiny-up: {← page}"
  out := out.push s!"y-after-tiny-up: {← yv}"
  -- Small deltas accumulate: twelve 1/12 notches scroll as far as one notch.
  let y0 ← yv
  for _ in [0:12] do wheelEv "<MouseWheel>" 10
  let y1 ← yv
  wheelEv "<MouseWheel>" 120
  let y2 ← yv
  out := out.push s!"y-frac: {first y0} {first y1} {first y2}"
  out := out.push s!"region-h: {(← st.get).regionH}"
  -- X11 legacy wheel buttons (Tk 8.6; Tk 9 turns real wheel buttons into <MouseWheel>).
  let b0 ← yv
  sendEvent ".c" "<Button-5>" ["-x", "200", "-y", "200"]
  let b1 ← yv
  sendEvent ".c" "<Button-4>" ["-x", "200", "-y", "200"]
  out := out.push s!"button-5-4: {first b0} {first b1} {first (← yv)}"
  -- Shift+wheel scrolls horizontally and never turns the page.
  let x0 ← xv
  wheelEv "<Shift-MouseWheel>" (-120)
  let x1 ← xv
  for _ in [0:60] do wheelEv "<Shift-MouseWheel>" (-120)
  out := out.push s!"shift-wheel: {first x0} {first x1} {← xv}"
  out := out.push s!"page-after-shift-wheel: {← page}"
  -- File → Close empties the window and disables the document commands.
  invoke .close
  out := out.push s!"title-after-close: {← run ["wm", "title", "."]}"
  out := out.push s!"states-after-close: {← statesOf [.close, .nextPage, .zoomIn, .openFile, .quit]}"
  IO.FS.writeFile (file "menu.txt") ("\n".intercalate out.toList ++ "\n")
  -- File → Quit ends the run.
  invoke .quit

/-- Smoke steps of the marks test (`SAFEPDF_VIEWER_SMOKE_MODE=marks`, task 9.4), on the text
PDF of `smokeText` (page 1: `Hello safe world` with a black marker under `safe`; the
non-embedded Helvetica is not painted, so the page is white except the marker): double-click
`world` + the toolbar's Highlight → the pixels there turn PDF.js yellow; Edit → Highlight
colour → Green recolours the selected highlight; `safe` + Edit → Highlight selection
highlights in green while the black marker stays black (multiply); a click selects the
`world` highlight and Delete removes it (white again); right-click at a blank point + Add
note… creates a note, its popup's text is set and saved, the icon is drawn; a click on the
icon reopens the popup with the text, which is edited; marks stay after zooming in,
rotating, going to page 2 (no marks there) and back; the note is deleted through Edit →
Delete mark. Results go into `marks.txt` as `key: value` lines. -/
def smokeMarks (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let status : IO String := run [".status", "cget", "-text"]
  let mut out : Array String := #[]
  discard <| run ["update"]
  -- The page image pixel at page point `p` ("R G B").
  let px (p : Pt) : IO String := do
    let s ← st.get
    let some bx := shownBox s | return "<no page>"
    let q := toScreen s.shownZoom s.shownRot bx p
    try run [photoOf s.page, "get", toString q.x.floor, toString q.y.floor]
    catch _ => pure "<outside>"
  let clickAt (pos : String × String) : IO Unit := do
    sendEvent ".c" "<ButtonPress-1>" ["-x", pos.1, "-y", pos.2]
    sendEvent ".c" "<ButtonRelease-1>" ["-x", pos.1, "-y", pos.2]
  let count : IO Nat := return (← st.get).marks.marks.size
  let .ok ix ← pageIndex st 0 | do
    IO.FS.writeFile (file "marks.txt") "error: no text index\n"
    discard <| run ["destroy", "."]
  let boxOf (q : String) : Option Box := do
    let (a, b) ← (ix.hits (Select.normQuery q))[0]?
    (Select.rangeBoxes ix.cells a b).head?
  let (some world, some safe) := (boxOf "world", boxOf "safe") | do
    IO.FS.writeFile (file "marks.txt") "error: words not found\n"
    discard <| run ["destroy", "."]
  let worldC : Pt := ⟨(world.llx + world.urx) / 2, (world.lly + world.ury) / 2⟩
  -- Inside the black marker (y 700–712.6) and above it, inside the box of `safe`.
  let safeIn : Pt := ⟨(safe.llx + safe.urx) / 2, 706⟩
  let safeAbove : Pt := ⟨(safe.llx + safe.urx) / 2, (712.6 + safe.ury) / 2⟩
  out := out.push s!"world-before: {← px worldC}"
  -- 1. Highlight `world` with the toolbar button (current colour yellow).
  let some wpos ← boxWindowPos st world | return
  for _ in [0:2] do clickAt wpos
  out := out.push s!"sel-before-highlight: {(← st.get).sel.isSome}"
  sendEvent ".bar.highlight" "<ButtonPress-1>" ["-x", "16", "-y", "16"]
  sendEvent ".bar.highlight" "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
  out := out.push s!"marks-after-highlight: {← count}"
  out := out.push s!"world-yellow: {← px worldC}"
  out := out.push s!"sel-after-highlight: {(← st.get).sel.isSome}"
  out := out.push s!"selected-after-highlight: {(← st.get).markSel.isSome}"
  -- 2. Recolour the selected highlight.
  discard <| run [".menubar.edit.hl", "invoke", Marks.Color.green.label]
  out := out.push s!"world-green: {← px worldC}"
  out := out.push s!"color-var: {← run ["set", Menu.colorVar]}"
  -- 3. Highlight `safe` from the Edit menu in the current colour (green).
  let some spos ← boxWindowPos st safe | return
  for _ in [0:2] do clickAt spos
  out := out.push s!"edit-highlight-state: {← run [".menubar.edit", "entrycget", Menu.Cmd.highlight.label, "-state"]}"
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.highlight.label]
  out := out.push s!"marks-after-edit-highlight: {← count}"
  out := out.push s!"safe-marker: {← px safeIn}"
  out := out.push s!"safe-above-marker: {← px safeAbove}"
  -- 4. Click the `world` highlight to select it, then Delete.
  clickAt wpos
  let selW := (← st.get).markSel
  out := out.push s!"selected-world: {selW.isSome && ((← st.get).marks.find? (selW.getD 0)).map (·.color) == some .green}"
  sendKey "Delete"
  out := out.push s!"marks-after-delete: {← count}"
  out := out.push s!"world-after-delete: {← px worldC}"
  -- 5. A note at a blank point through the context menu.
  let notePt : Pt := ⟨300, 400⟩
  let some npos ← boxWindowPos st ⟨300, 400, 300, 400⟩ | return
  sendEvent ".c" "<ButtonPress-3>" ["-x", npos.1, "-y", npos.2]
  out := out.push s!"pop-delete-state: {← run [Menu.popPath, "entrycget", Menu.Cmd.deleteMark.label, "-state"]}"
  out := out.push s!"pop-entries: {← run [Menu.popPath, "type", "3"]} {← run [Menu.popPath, "entrycget", "4", "-label"]}|{← run [Menu.popPath, "entrycget", "5", "-label"]}|{← run [Menu.popPath, "entrycget", "6", "-label"]}"
  discard <| run [Menu.popPath, "invoke", Menu.Cmd.addNote.label]
  discard <| run ["update", "idletasks"]
  out := out.push s!"note-popup: {← run ["winfo", "exists", ".note"]}"
  let text1 := "First note [exit 7] $HOME {x\" \\"
  discard <| run [".note.t", "insert", "end", text1]
  discard <| run [".note.b.save", "invoke"]
  let noteId := (← st.get).marks.marks.findSome? fun m => if m.isNote then some m.id else none
  let noteText : IO String := return (((← st.get).marks.find? (noteId.getD 0)).map (·.text)).getD "<none>"
  out := out.push s!"marks-after-note: {← count}"
  out := out.push s!"note-text-ok: {(← noteText) == text1}"
  out := out.push s!"note-popup-after-save: {← run ["winfo", "exists", ".note"]}"
  -- The icon is drawn where the model puts it (upper-left corner at the point).
  let iconOk : IO Bool := do
    let s ← st.get
    let some bx := shownBox s | return false
    let some m := s.marks.find? (noteId.getD 0) | return false
    let some ib := m.iconBox bx | return false
    let (x0, y0, x1, y1) := canvasRect s bx ib
    match ((← run [".c", "bbox", "note"]).splitOn " ").filterMap String.toInt? with
    | [a, b, c, d] =>
      return (a - x0.floor).natAbs ≤ 3 && (b - y0.floor).natAbs ≤ 3 &&
        (c - x1.ceil).natAbs ≤ 3 && (d - y1.ceil).natAbs ≤ 3
    | _ => return false
  out := out.push s!"note-icon: {decide ((← tagCount "note") > 0)} {← iconOk}"
  -- 6. A click on the icon reopens the popup with the text; edit it.
  let iconCentre : IO (Option (String × String)) := do
    let s ← st.get
    let some bx := shownBox s | return none
    let some m := s.marks.find? (noteId.getD 0) | return none
    let some ib := m.iconBox bx | return none
    boxWindowPos st ib
  if let some ipos ← iconCentre then clickAt ipos
  discard <| run ["update", "idletasks"]
  out := out.push s!"note-popup-reopened: {← run ["winfo", "exists", ".note"]}"
  let shown ← try run [".note.t", "get", "1.0", "end - 1 chars"] catch _ => pure "<none>"
  out := out.push s!"note-popup-text-ok: {shown == text1}"
  let text2 := "Edited: ünïcode ✓"
  try
    discard <| run [".note.t", "delete", "1.0", "end"]
    discard <| run [".note.t", "insert", "end", text2]
    discard <| run [".note.b.save", "invoke"]
  catch _ => pure ()
  out := out.push s!"note-edited-ok: {(← noteText) == text2}"
  -- 7. Zoom in twice, rotate, page 2 and back: the marks follow.
  out := out.push s!"zoom-pct0: {View.zoomPct (← st.get).shownZoom (← st.get).scaling}"
  sendKey "plus"; sendKey "plus"
  out := out.push s!"zoom-pct1: {View.zoomPct (← st.get).shownZoom (← st.get).scaling}"
  out := out.push s!"zoom-safe: {← px safeIn}|{← px safeAbove}"
  out := out.push s!"zoom-note-icon: {decide ((← tagCount "note") > 0)} {← iconOk}"
  sendKey "r"
  out := out.push s!"rot-deg: {View.rotDeg (← st.get).shownRot}"
  out := out.push s!"rot-safe: {← px safeIn}|{← px safeAbove}"
  out := out.push s!"rot-note-icon: {decide ((← tagCount "note") > 0)} {← iconOk}"
  sendKey "R"
  sendKey "End"
  out := out.push s!"page2-mark-items: {(← st.get).page + 1} {← tagCount "mark"}"
  sendKey "Home"
  out := out.push s!"back-safe: {(← st.get).page + 1} {← px safeIn}|{← px safeAbove}"
  out := out.push s!"back-note-icon: {decide ((← tagCount "note") > 0)} {← iconOk}"
  -- 8. Delete the note through the Edit menu after selecting it; a toolbar click without a
  -- selection asks for a colour.
  out := out.push s!"edit-delete-state0: {← run [".menubar.edit", "entrycget", Menu.Cmd.deleteMark.label, "-state"]}"
  if let some ipos ← iconCentre then clickAt ipos
  discard <| run ["destroy", ".note"]
  out := out.push s!"edit-delete-state1: {← run [".menubar.edit", "entrycget", Menu.Cmd.deleteMark.label, "-state"]}"
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.deleteMark.label]
  out := out.push s!"marks-after-note-delete: {← count} {← tagCount "note"}"
  sendEvent ".bar.highlight" "<ButtonPress-1>" ["-x", "16", "-y", "16"]
  sendEvent ".bar.highlight" "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
  out := out.push s!"status-highlight-nosel: {← status}"
  out := out.push s!"ids: {(← st.get).marks.marks.map (·.id) |>.toList} next {(← st.get).marks.nextId}"
  IO.FS.writeFile (file "marks.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of the selection bubble and the Highlight pop-over
(`SAFEPDF_VIEWER_SMOKE_MODE=bubble`, task 9.8), on the text PDF of `smokeText` (page 1 white
except the black marker under `safe`; substitute fonts off): a drag over `world` shows the
float bubble at the end of the selection; its Highlight button highlights in yellow and the
edit bubble replaces it; a click on blank paper dismisses it; a click on the highlight shows
the edit bubble again, which follows a zoom; its colour button opens the picker, whose blue
row recolours the highlight; its Delete removes it. The toolbar's Highlight button (no
selection) turns the tool on and opens the pop-over; its pink swatch makes pink current; a
drag over `safe` then highlights at once in pink; the slider sets the thickness (press and
drag); the "Show all" switch hides the highlight (white) and shows it again; the edit bubble's
Comment adds a note anchored to the highlight's quads and reopens it later; Escape closes the
pop-over and dismisses the bubble; with the tool off a new selection's bubble goes on Escape
and on a page change. Results go into `bubble.txt` as `key: value` lines. -/
def smokeBubble (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let mut out : Array String := #[]
  discard <| run ["update"]
  let px (p : Pt) : IO String := do
    let s ← st.get
    let some bx := shownBox s | return "<no page>"
    let q := toScreen s.shownZoom s.shownRot bx p
    try run [photoOf s.page, "get", toString q.x.floor, toString q.y.floor]
    catch _ => pure "<outside>"
  let idle : IO Unit := discard <| run ["update", "idletasks"]
  let clickAt (pos : String × String) : IO Unit := do
    let t := toString (← IO.monoMsNow)
    sendEvent ".c" "<ButtonPress-1>" ["-x", pos.1, "-y", pos.2, "-time", t]
    sendEvent ".c" "<ButtonRelease-1>" ["-x", pos.1, "-y", pos.2, "-time", t]
    idle
  -- Window position of a canvas point.
  let winOf (x y : Rat) : IO (String × String) := do
    let vx := (View.parseDecimal (← run [".c", "canvasx", "0"])).getD 0
    let vy := (View.parseDecimal (← run [".c", "canvasy", "0"])).getD 0
    return (toString (x - vx).floor, toString (y - vy).floor)
  let btnPos (b : Bubble.Btn) : IO (Option (String × String)) := do
    let some (k, r) := (← st.get).bubble | return none
    let some (_, x0, x1) := k.layout.find? (·.1 == b) | return none
    return some (← winOf (r.x0 + (x0 + x1) / 2) ((r.y0 + r.y1) / 2))
  let clickBtn (b : Bubble.Btn) : IO Unit := do
    if let some pos ← btnPos b then clickAt pos
  let kindName : IO String := return match (← st.get).bubble with
    | some (.float, _) => "float"
    | some (.edit, _) => "edit"
    | some (.editor, _) => "editor"
    | none => "none"
  let count : IO Nat := return (← st.get).marks.marks.size
  let popClickAt (x y : Rat) : IO Unit := do
    sendEvent ".hlbar" "<ButtonPress-1>" ["-x", toString x.floor, "-y", toString y.floor]
    sendEvent ".hlbar" "<ButtonRelease-1>" ["-x", toString x.floor, "-y", toString y.floor]
  let .ok ix ← pageIndex st 0 | do
    IO.FS.writeFile (file "bubble.txt") "error: no text index\n"
    discard <| run ["destroy", "."]
  let rangeOf (q : String) : Option (Nat × Nat) := (ix.hits (Select.normQuery q))[0]?
  let (some (wa, wb), some (sa, sb)) := (rangeOf "world", rangeOf "safe") | do
    IO.FS.writeFile (file "bubble.txt") "error: words not found\n"
    discard <| run ["destroy", "."]
  let dragSel (a b : Nat) : IO Unit := do
    if let (some p0, some p1) := (← cellWindowPos st ix a, ← cellWindowPos st ix b) then
      sendEvent ".c" "<ButtonPress-1>" ["-x", p0.1, "-y", p0.2]
      sendEvent ".c" "<Motion>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
      sendEvent ".c" "<ButtonRelease-1>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
      idle
  let some world := (Select.rangeBoxes ix.cells wa wb).head? | return
  let some safe := (Select.rangeBoxes ix.cells sa sb).head? | return
  let worldC : Pt := ⟨(world.llx + world.urx) / 2, (world.lly + world.ury) / 2⟩
  let safeAbove : Pt := ⟨(safe.llx + safe.urx) / 2, (712.6 + safe.ury) / 2⟩
  let some wpos ← boxWindowPos st world | return
  let some spos ← boxWindowPos st safe | return
  let some blank ← boxWindowPos st ⟨300, 400, 300, 400⟩ | return
  -- The bubble's right edge and top against the last point of the boxes `bs` (page space).
  let atEnd (bs : List Box) : IO Bool := do
    let s ← st.get
    let some bx := shownBox s | return false
    let some (_, r) := s.bubble | return false
    let some (lx, ly) := Bubble.lastPoint (bs.map (canvasR s bx)) | return false
    return r.x1 == lx && r.y0 == ly + Bubble.gap
  out := out.push s!"bubble0: {← kindName} {← tagCount "bub"}"
  -- 1. A drag over `world`: the float bubble at the end of the selection.
  dragSel wa wb
  out := out.push s!"sel-world: {(← st.get).sel.isSome}"
  out := out.push s!"bubble-float: {← kindName} {decide ((← tagCount "bub") > 0)}"
  out := out.push s!"bubble-at-end: {← atEnd [world]}"
  -- 2. Its Highlight button.
  clickBtn .highlight
  out := out.push s!"marks-after-bubble-highlight: {← count}"
  out := out.push s!"world-yellow: {← px worldC}"
  out := out.push s!"bubble-after-highlight: {← kindName} {← atEnd [world]}"
  -- 3. A click on blank paper dismisses it.
  clickAt blank
  out := out.push s!"bubble-after-blank: {← kindName} {← tagCount "bub"}"
  -- 4. A click on the highlight: the edit bubble; it follows a zoom.
  clickAt wpos
  out := out.push s!"bubble-edit: {← kindName} {(← st.get).markSel.isSome}"
  sendKey "plus"
  out := out.push s!"bubble-zoom: {← kindName} {← atEnd [world]}"
  sendKey "minus"
  -- 5. The colour button opens the picker; its blue row recolours the highlight.
  clickBtn .color
  out := out.push s!"picker-open: {(← st.get).pickerAt.isSome} {decide ((← tagCount "picker") > 0)}"
  if let some pr := (← st.get).pickerAt then
    if let some (_, x, y) := (Bubble.pickerSwatches pr).find? (·.1 == .blue) then
      clickAt (← winOf x y)
  out := out.push s!"world-blue: {← px worldC}"
  out := out.push s!"picker-closed: {(← st.get).pickerAt.isNone} {← tagCount "picker"}"
  out := out.push s!"bubble-after-pick: {← kindName}"
  -- 6. Delete.
  clickBtn .delete
  out := out.push s!"marks-after-bubble-delete: {← count}"
  out := out.push s!"world-after-delete: {← px worldC}"
  out := out.push s!"bubble-after-delete: {← kindName} {← tagCount "bub"}"
  -- 7. The toolbar's Highlight button without a selection: tool on, pop-over open.
  sendEvent ".bar.highlight" "<ButtonPress-1>" ["-x", "16", "-y", "16"]
  sendEvent ".bar.highlight" "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
  idle
  out := out.push s!"popover: {← run ["winfo", "ismapped", ".hlbar"]} {← run ["set", Menu.hlToolVar]} {← run ["set", "::safepdf::btn(tog,.bar.highlight)"]}"
  let px0 := (View.parseDecimal (← run ["winfo", "x", ".hlbar"])).getD 0
  let bR := (View.parseDecimal (← run ["winfo", "rootx", ".bar.highlight"])).getD 0 -
    (View.parseDecimal (← run ["winfo", "rootx", "."])).getD 0 +
    (View.parseDecimal (← run ["winfo", "width", ".bar.highlight"])).getD 0
  out := out.push s!"popover-right-aligned: {px0 + Bubble.Popover.width == bR}"
  popClickAt (Bubble.Popover.swatchX 3) Bubble.Popover.swatchY
  out := out.push s!"color-after-swatch: {(← st.get).hlColor.name} {← run ["set", Menu.colorVar]}"
  -- 8. With the tool on, a drag over `safe` highlights at once.
  dragSel sa sb
  out := out.push s!"marks-tool: {← count} {(← st.get).sel.isSome}"
  out := out.push s!"safe-pink: {← px safeAbove}"
  -- 9. The slider: a press sets the thickness, a drag moves it.
  popClickAt (Bubble.Popover.thumbX 20) Bubble.Popover.sliderY
  let t1 := (← st.get).ui.thickness
  sendEvent ".hlbar" "<ButtonPress-1>" ["-x", toString (Bubble.Popover.thumbX 20).floor, "-y",
    toString Bubble.Popover.sliderY.floor]
  sendEvent ".hlbar" "<B1-Motion>" ["-x", "300", "-y", toString Bubble.Popover.sliderY.floor,
    "-state", "256"]
  sendEvent ".hlbar" "<ButtonRelease-1>" ["-x", "300", "-y", toString Bubble.Popover.sliderY.floor,
    "-state", "256"]
  out := out.push s!"thickness: {t1} {(← st.get).ui.thickness}"
  -- 10. "Show all" off hides the highlight, on shows it again.
  let t := Bubble.Popover.toggleRect
  popClickAt ((t.x0 + t.x1) / 2) ((t.y0 + t.y1) / 2)
  out := out.push s!"showall-off: {← px safeAbove} {← run ["set", Menu.showAllVar]}"
  clickAt spos
  out := out.push s!"hidden-not-selectable: {(← st.get).markSel.isNone}"
  popClickAt ((t.x0 + t.x1) / 2) ((t.y0 + t.y1) / 2)
  out := out.push s!"showall-on: {← px safeAbove} {← run ["set", Menu.showAllVar]}"
  -- 11. Comment through the edit bubble: a note on the highlight's quads; reopened later.
  clickAt spos
  out := out.push s!"bubble-safe: {← kindName}"
  let hlId := (← st.get).markSel
  clickBtn .comment
  out := out.push s!"comment-popup: {← run ["winfo", "exists", ".note"]} {← count}"
  let anchored : IO Bool := do
    let s ← st.get
    let some h := hlId.bind s.marks.find? | return false
    return (s.marks.noteOn 0 h.quads).isSome
  out := out.push s!"comment-anchored: {← anchored}"
  try
    discard <| run [".note.t", "insert", "end", "On safe"]
    discard <| run [".note.b.save", "invoke"]
  catch _ => pure ()
  clickAt spos
  clickBtn .comment
  let shown ← try run [".note.t", "get", "1.0", "end - 1 chars"] catch _ => pure "<none>"
  out := out.push s!"comment-reopened: {← run ["winfo", "exists", ".note"]} {shown} {← count}"
  discard <| run ["destroy", ".note"]
  -- 12. Escape closes the pop-over and dismisses the bubble (the tool stays on). (Wait past
  -- Tk's double-click time first: generated clicks in quick succession count as a double
  -- click, which with the tool on would highlight the word.)
  discard <| run ["after", "600"]
  clickAt spos
  out := out.push s!"before-escape: {← kindName} {← run ["winfo", "ismapped", ".hlbar"]} {← count}"
  sendKey "Escape"
  out := out.push s!"after-escape: {← kindName} {← tagCount "bub"} {← run ["winfo", "ismapped", ".hlbar"]} {(← st.get).ui.tool}"
  -- 13. Tool off (Edit menu); a selection's bubble goes on Escape and on a page change.
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.hlTool.label]
  out := out.push s!"tool-off: {(← st.get).ui.tool} {← run ["set", Menu.hlToolVar]}"
  dragSel wa wb
  out := out.push s!"float-again: {← kindName} {← count}"
  sendKey "Escape"
  out := out.push s!"float-escape: {← kindName} {(← st.get).sel.isSome}"
  dragSel wa wb
  sendKey "End"
  out := out.push s!"page-change: {(← st.get).page + 1} {← kindName} {← tagCount "bub"}"
  IO.FS.writeFile (file "bubble.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Shared helpers of the save smoke steps (task 9.5c). -/
structure SaveKit where
  /-- `R G B` of the shown page image at a page point. -/
  px : Pt → IO String
  /-- Press and release button 1 at a window position. -/
  clickAt : String × String → IO Unit
  /-- The `-state` of a menubar command's entry. -/
  menuState : Menu.Cmd → IO String
  /-- The window title starts with `* ` (unsaved marks). -/
  star : IO Bool
  /-- Size of a file (0 when missing). -/
  size : String → IO Nat
  /-- The last question asked (`::safepdf::lastAsk`). -/
  lastAsk : IO String
  /-- The status line. -/
  status : IO String

/-- The helpers of `SaveKit`. -/
def saveKit (st : IO.Ref State) : SaveKit where
  px p := do
    let s ← st.get
    let some bx := shownBox s | return "<no page>"
    let q := toScreen s.shownZoom s.shownRot bx p
    try run [photoOf s.page, "get", toString q.x.floor, toString q.y.floor]
    catch _ => pure "<outside>"
  clickAt pos := do
    sendEvent ".c" "<ButtonPress-1>" ["-x", pos.1, "-y", pos.2]
    sendEvent ".c" "<ButtonRelease-1>" ["-x", pos.1, "-y", pos.2]
  menuState c := do
    let some (m, i) := Menu.locate c | return "?"
    run [m, "entrycget", toString i, "-state"]
  star := return (← run ["wm", "title", "."]).startsWith "* "
  size p := do
    try return (← (p : System.FilePath).metadata).byteSize.toNat catch _ => return 0
  lastAsk := run ["set", "::safepdf::lastAsk"]
  status := run [".status", "cget", "-text"]

/-- Adds a note at page point `(x, y)` of the shown page through the context menu, with
`text`. -/
def smokeNoteAt (st : IO.Ref State) (x y : Rat) (text : String) : IO Unit := do
  let some npos ← boxWindowPos st ⟨x, y, x, y⟩ | return
  sendEvent ".c" "<ButtonPress-3>" ["-x", npos.1, "-y", npos.2]
  discard <| run [Menu.popPath, "invoke", Menu.Cmd.addNote.label]
  discard <| run ["update", "idletasks"]
  discard <| run [".note.t", "insert", "end", text]
  discard <| run [".note.b.save", "invoke"]

/-- The note text of the save smoke steps (Tcl metacharacters and non-ASCII). -/
def smokeNoteText : String := "Saved note [exit 7] $HOME {x\" ü ✓"

/-- Our marks in the PDF file `path`, read back through the strict parser: (count, distinct
ids), or the error. -/
def fileMarks (path : String) : IO String := do
  try
    let bytes ← IO.FS.readBinFile path
    match SafePdf.Api.openBytes bytes { allowRepair := false } with
    | .ok d =>
      let ms := Save.readMarks d.doc limits
      return s!"{ms.length} {(ms.map (·.id)).eraseDups.length}"
    | .error e => return s!"error {e.message}"
  catch e => return s!"error {e}"

/-- Smoke steps of the save flow (`SAFEPDF_VIEWER_SMOKE_MODE=save`, tasks 9.5c, 9.r2) on a copy
of the text PDF of `smokeText` (substitute fonts off): nothing unsaved at first; a highlight on
`world` and a note at (300, 400) make the title start with `* ` and enable Save; Quit, Ctrl+W
and the window's close button (its `WM_DELETE_WINDOW` script) answered Cancel keep everything
(the unsaved-changes prompt asked each time); Ctrl+S asks before the first overwrite —
answered Cancel nothing is written, answered Overwrite the marks are written **into the opened
file** (its original bytes a prefix of the result), which is reopened (2 saved marks, title
without `*`, Save disabled), the highlight now drawn by the renderer from its appearance
stream (pixels yellow, no canvas note icon) and the note text restored (a copy of the file
goes to `first.pdf`); a second Ctrl+S has nothing to save (size unchanged); the saved
highlight can be selected; a new highlight on `safe` + Ctrl+S appends to the same file
without a question (3 marks, distinct ids, read back strictly); File → Save As… (`autoPath`)
writes `saveas.pdf` and opens it; with a new note, Ctrl+S on a read-only `saveas.pdf` is
refused (status, file unchanged), and on a `saveas.pdf` changed on disk (bytes appended
behind the viewer's back) refused with the changed-on-disk question (answered Cancel: file
unchanged, the note still unsaved); then Ctrl+W answered Don't Save closes without saving
and leaves `saveas.pdf` byte for byte as it was. Results in `save.txt`. -/
def smokeSave (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text index")
  let boxOf (q : String) : Option Box := do
    let (a, b) ← (ix.hits (Select.normQuery q))[0]?
    (Select.rangeBoxes ix.cells a b).head?
  let (some world, some safe) := (boxOf "world", boxOf "safe") |
    throw (IO.userError "words not found")
  let worldC : Pt := ⟨(world.llx + world.urx) / 2, (world.lly + world.ury) / 2⟩
  out := out.push s!"world-box: {num world.llx} {num world.lly} {num world.urx} {num world.ury}"
  let orig := (← st.get).path.getD ""
  let origBytes ← IO.FS.readBinFile orig
  out := out.push s!"dirty0: {(← st.get).marks.dirty} {← k.star} {← k.menuState .save} {← run ["::safepdf::btnState", ".bar.save"]}"
  -- 1. A highlight and a note.
  let some wpos ← boxWindowPos st world | throw (IO.userError "world not shown")
  for _ in [0:2] do k.clickAt wpos
  sendEvent ".bar.highlight" "<ButtonPress-1>" ["-x", "16", "-y", "16"]
  sendEvent ".bar.highlight" "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
  smokeNoteAt st 300 400 smokeNoteText
  out := out.push s!"dirty1: {(← st.get).marks.dirty} {← k.star} {← k.menuState .save} {← run ["::safepdf::btnState", ".bar.save"]} {(← st.get).marks.marks.size}"
  -- 2. Quit, Close and the window's close button answered Cancel.
  discard <| run ["set", "::safepdf::autoAnswer", "cancel"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.quit.label]
  discard <| run ["update"]
  out := out.push s!"quit-cancel: {← run ["winfo", "exists", "."]} {(← st.get).marks.dirty} {(← k.lastAsk).startsWith "2 mark(s) on text.pdf are not saved"}"
  discard <| run ["set", "::safepdf::lastAsk", ""]
  sendEvent ".c" "<Control-Key-w>"
  out := out.push s!"close-cancel: {(← st.get).doc.isSome} {(← k.lastAsk).startsWith "2 mark(s)"}"
  let wmDelete ← run ["wm", "protocol", ".", "WM_DELETE_WINDOW"]
  out := out.push s!"wm-delete: {wmDelete}"
  discard <| run ["set", "::safepdf::lastAsk", ""]
  discard <| Shim.eval wmDelete
  discard <| run ["update"]
  out := out.push s!"wm-close-cancel: {← run ["winfo", "exists", "."]} {(← st.get).doc.isSome} {(← st.get).marks.dirty} {(← k.lastAsk).startsWith "2 mark(s) on text.pdf are not saved. Save them before quitting?"}"
  -- 3. Ctrl+S: the first overwrite asks; Cancel writes nothing, Overwrite writes into the
  -- opened file and reopens it.
  discard <| run ["set", "::safepdf::lastAsk", ""]
  sendEvent ".c" "<Control-Key-s>"
  out := out.push s!"overwrite-cancel: {(← IO.FS.readBinFile orig).data == origBytes.data} {(← st.get).marks.dirty} {(← k.lastAsk).startsWith "Save 2 new or changed mark(s) into text.pdf?"} {((← k.lastAsk).splitOn "first revision").length == 2}"
  discard <| run ["set", "::safepdf::autoAnswer", "overwrite"]
  sendEvent ".c" "<Control-Key-s>"
  let s1 ← st.get
  let bytes1 ← IO.FS.readBinFile orig
  out := out.push s!"saved-path: {s1.path == some orig} {decide (bytes1.size > origBytes.size)} {Save.isPrefix origBytes bytes1}"
  out := out.push s!"after-save: {s1.marks.marks.size} {s1.marks.saved.length} {s1.marks.dirty} {← k.star} {← k.menuState .save}"
  out := out.push s!"world-after-save: {← k.px worldC}"
  out := out.push s!"note-after-save: {(s1.marks.marks.toList.find? (·.isNote)).map (·.text) == some smokeNoteText} {← tagCount "note"}"
  out := out.push s!"status-after-save: {← k.status}"
  IO.FS.writeBinFile (file "first.pdf") bytes1
  -- 4. Nothing new: nothing written.
  let size1 ← k.size orig
  sendEvent ".c" "<Control-Key-s>"
  out := out.push s!"save-nothing: {(← k.status).startsWith "no unsaved marks"} {size1 == (← k.size orig)}"
  -- 5. The saved highlight can be selected (its edits are `smokeEdit`'s, task 9.5g).
  k.clickAt wpos
  out := out.push s!"saved-selected: {(← st.get).markSel.isSome}"
  sendKey "Escape"
  -- 6. A new highlight, saved into the same file (no question, no duplicates). Any question
  -- would get the answer `unexpected` (= Cancel) and show in lastAsk.
  let some spos ← boxWindowPos st safe | throw (IO.userError "safe not shown")
  for _ in [0:2] do k.clickAt spos
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.highlight.label]
  out := out.push s!"dirty2: {(← st.get).marks.dirty} {← k.star}"
  discard <| run ["set", "::safepdf::autoAnswer", "unexpected"]
  discard <| run ["set", "::safepdf::lastAsk", ""]
  sendEvent ".c" "<Control-Key-s>"
  let s2 ← st.get
  out := out.push s!"second-save: {s2.path == some orig} {s2.marks.marks.size} {s2.marks.dirty} {(← k.lastAsk).isEmpty}"
  out := out.push s!"file-marks: {← fileMarks orig}"
  -- 7. Save As (no new marks: a copy).
  discard <| run ["set", "::safepdf::autoPath", file "saveas.pdf"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.saveAs.label]
  discard <| run ["set", "::safepdf::autoPath", ""]
  out := out.push s!"save-as: {(← st.get).path == some (file "saveas.pdf")} {(← k.size (file "saveas.pdf")) == (← k.size orig)} {(← st.get).marks.marks.size} {(← st.get).marks.dirty}"
  -- 8. A new note; Ctrl+S on a read-only file is refused.
  let sa := file "saveas.pdf"
  let saBytes ← IO.FS.readBinFile sa
  smokeNoteAt st 400 200 "discard me"
  out := out.push s!"dirty3: {(← st.get).marks.dirty} {← k.star}"
  let mode ← run ["file", "attributes", sa, "-permissions"]
  discard <| run ["file", "attributes", sa, "-permissions", "0444"]
  discard <| run ["set", "::safepdf::lastAsk", ""]
  sendEvent ".c" "<Control-Key-s>"
  out := out.push s!"read-only: {(← k.status).startsWith "cannot save: saveas.pdf is read-only"} {(← IO.FS.readBinFile sa).data == saBytes.data} {(← st.get).marks.dirty} {(← k.lastAsk).isEmpty}"
  discard <| run ["file", "attributes", sa, "-permissions", mode]
  -- 9. Changed on disk behind the viewer's back: refused, Save As… offered (Cancel).
  let tampered := saBytes ++ "% changed by another program\n".toUTF8
  IO.FS.writeBinFile sa tampered
  discard <| run ["set", "::safepdf::autoAnswer", "cancel"]
  sendEvent ".c" "<Control-Key-s>"
  out := out.push s!"changed-on-disk: {(← k.lastAsk).startsWith "saveas.pdf was changed on disk"} {(← IO.FS.readBinFile sa).data == tampered.data} {(← st.get).marks.dirty} {(← k.status).startsWith "not saved: saveas.pdf changed on disk"}"
  IO.FS.writeBinFile sa saBytes
  -- 10. Close answered Don't Save: closed, the file untouched.
  discard <| run ["set", "::safepdf::autoAnswer", "dontsave"]
  sendEvent ".c" "<Control-Key-w>"
  out := out.push s!"close-discard: {(← st.get).doc.isNone} {(← k.lastAsk).startsWith "1 mark(s) on saveas.pdf"} {← fileMarks sa} {(← IO.FS.readBinFile sa).data == saBytes.data}"
  IO.FS.writeFile (file "save.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of reopening a saved file (`SAFEPDF_VIEWER_SMOKE_MODE=reopen`, task 9.5c) on
the `text.pdf` that `smokeSave` overwrote: its 3 marks are restored (saved, title without
`*`), the highlight pixels are yellow (renderer), the note has no canvas icon but a click on
its place opens its popup with the saved text; after a new highlight (select all) Save As onto
the opened file answered No writes nothing, Yes appends; a further note, Quit answered Cancel
keeps the window (the unsaved-changes prompt asked, `quit-ask`), and Quit answered Save saves
into the same file (no further question: this session wrote it) and quits (task 9.r2: the
save on quit is the prompt's answer, never silent). Results in `reopen.txt` (written before
the quit). -/
def smokeReopen (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text index")
  let some world := ((ix.hits (Select.normQuery "world"))[0]?).bind fun (a, b) =>
      (Select.rangeBoxes ix.cells a b).head? | throw (IO.userError "world not found")
  let worldC : Pt := ⟨(world.llx + world.urx) / 2, (world.lly + world.ury) / 2⟩
  let s0 ← st.get
  out := out.push s!"restored: {s0.marks.marks.size} {s0.marks.saved.length} {s0.marks.dirty} {← k.star} {(← k.status).endsWith "3 saved marks restored from the file"}"
  out := out.push s!"world-px: {← k.px worldC}"
  let note := s0.marks.marks.toList.find? (·.isNote)
  out := out.push s!"note-text: {(note.map (·.text)) == some smokeNoteText} {← tagCount "note"}"
  -- A click on the note's place (drawn by the renderer) opens its popup.
  if let some m := note then
    if let some bx := shownBox s0 then
      if let some ib := m.iconBox bx then
        if let some pos ← boxWindowPos st ib then k.clickAt pos
  discard <| run ["update", "idletasks"]
  let shown ← try run [".note.t", "get", "1.0", "end - 1 chars"] catch _ => pure "<none>"
  out := out.push s!"note-popup: {← run ["winfo", "exists", ".note"]} {shown == smokeNoteText}"
  discard <| run ["destroy", ".note"]
  -- A new highlight; Save As onto the opened file: No, then Yes.
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.selectAll.label]
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.highlight.label]
  let path := (← st.get).path.getD ""
  let size0 ← k.size path
  out := out.push s!"dirty1: {(← st.get).marks.dirty} {← k.star}"
  discard <| run ["set", "::safepdf::autoPath", path]
  discard <| run ["set", "::safepdf::autoAnswer", "no"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.saveAs.label]
  out := out.push s!"overwrite-no: {size0 == (← k.size path)} {(← k.lastAsk).startsWith "Overwrite the opened file text.pdf?"} {(← st.get).marks.dirty}"
  discard <| run ["set", "::safepdf::autoAnswer", "yes"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.saveAs.label]
  discard <| run ["set", "::safepdf::autoPath", ""]
  out := out.push s!"overwrite-yes: {decide ((← k.size path) > size0)} {(← st.get).marks.dirty} {(← st.get).marks.marks.size} {← fileMarks path}"
  -- One more note; Quit answered Cancel keeps the window, Save saves (no further question:
  -- this session wrote the file) and quits.
  smokeNoteAt st 100 100 "before quit"
  out := out.push s!"dirty2: {(← st.get).marks.dirty} {← k.star}"
  discard <| run ["set", "::safepdf::autoAnswer", "cancel"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.quit.label]
  discard <| run ["update"]
  out := out.push s!"quit-ask: {← run ["winfo", "exists", "."]} {(← st.get).marks.dirty} {(← k.lastAsk).startsWith "1 mark(s) on text.pdf are not saved. Save them before quitting?"}"
  IO.FS.writeFile (file "reopen.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["set", "::safepdf::autoAnswer", "save"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.quit.label]

/-- Smoke steps of editing saved marks (`SAFEPDF_VIEWER_SMOKE_MODE=edit`, task 9.5g) on the
`text-annotated.pdf` left by `smokeReopen` (5 saved marks: highlights on `world`, `safe` and
the whole page, two notes). A click on `world` selects the whole-page highlight (the newest),
Delete removes it; a click on `world` then selects its highlight, which is recoloured green
(the pages are rendered from the preview at once: the pixels turn green) and gets a comment
(the edit bubble's Comment); the `safe` highlight is deleted (white again); the first note's
text is edited. Ctrl+S (the opened file: answered Overwrite) writes one update and reopens: 4 marks,
nothing unsaved, the comment restored with its id and the highlight's colour, the note text
and the colours as edited, each id once in the file. Then a second round on top: the world
highlight back to blue and its comment deleted, Ctrl+S, reopened: 3 marks. Results in
`edit.txt` (world/safe boxes for the external `mutool` check). -/
def smokeEdit (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text index")
  let boxOf (q : String) : Option Box := do
    let (a, b) ← (ix.hits (Select.normQuery q))[0]?
    (Select.rangeBoxes ix.cells a b).head?
  let (some world, some safe) := (boxOf "world", boxOf "safe") |
    throw (IO.userError "words not found")
  let ctr (b : Box) : Pt := ⟨(b.llx + b.urx) / 2, (b.lly + b.ury) / 2⟩
  -- Tinted (coloured) pixels among 7 × 3 points inside a box: 0 without a highlight.
  let tinted (b : Box) : IO Nat := do
    let mut n := 0
    for i in [1:8] do
      for j in [1:4] do
        let q : Pt := ⟨b.llx + (b.urx - b.llx) * i / 8, b.lly + (b.ury - b.lly) * j / 4⟩
        let cs := ((← k.px q).splitOn " ").filterMap String.toNat?
        if cs.length == 3 && (cs.foldl max 0) - (cs.foldl min 255) > 40 then n := n + 1
    return n
  out := out.push s!"world-box: {num world.llx} {num world.lly} {num world.urx} {num world.ury}"
  out := out.push s!"safe-box: {num safe.llx} {num safe.lly} {num safe.urx} {num safe.ury}"
  let path := (← st.get).path.getD ""
  let s0 ← st.get
  out := out.push s!"restored: {s0.marks.marks.size} {s0.marks.dirty} {← k.star}"
  let some wpos ← boxWindowPos st world | throw (IO.userError "world not shown")
  let some spos ← boxWindowPos st safe | throw (IO.userError "safe not shown")
  -- 1. The whole-page highlight (newest, on top) is deleted.
  k.clickAt wpos
  let selAll := (← st.get).markSel
  sendKey "Delete"
  out := out.push s!"del-all: {(← st.get).marks.marks.size} {(← st.get).marks.dirty} {← k.star} {(← st.get).view.isSome} {(selAll.bind (← st.get).marks.find?).isNone}"
  -- 2. The world highlight: recoloured green, then a comment.
  discard <| run ["after", "600"]
  k.clickAt wpos
  let wid := (← st.get).markSel.getD 0
  discard <| run [".menubar.edit.hl", "invoke", Marks.Color.green.label]
  out := out.push s!"recolour: {((← st.get).marks.find? wid).map (·.color.name)} {← k.px (ctr world)}"
  addNote st none
  discard <| run ["update", "idletasks"]
  discard <| run [".note.t", "insert", "end", "Comment ✓ [x]"]
  discard <| run [".note.b.save", "invoke"]
  discard <| run ["destroy", ".note"]
  let cid := ((← st.get).marks.find? wid).bind (← st.get).marks.commentOf |>.map (·.id)
  out := out.push s!"comment: {cid.isSome} {← tagCount "note"}"
  -- 3. The safe highlight is deleted.
  discard <| run ["after", "600"]
  k.clickAt spos
  let sid := (← st.get).markSel
  sendKey "Delete"
  out := out.push s!"del-safe: {sid.isSome} {decide ((← tinted safe) = 0)}"
  -- 4. The first note's text is edited.
  let sN ← st.get
  let note := sN.marks.marks.toList.find? fun m => m.isNote && !sN.marks.isComment m
  if let some n := note then noteSave st (toString n.id) "Edited note"
  let s1 ← st.get
  out := out.push s!"pending: {s1.marks.pending} {s1.marks.dirty} {← k.star}"
  -- 5. Save into the opened file (Overwrite), reopened.
  discard <| run ["set", "::safepdf::autoAnswer", "overwrite"]
  sendEvent ".c" "<Control-Key-s>"
  let s2 ← st.get
  let m2 := s2.marks.marks.toList
  out := out.push s!"saved: {s2.path == some path} {m2.length} {s2.marks.dirty} {← k.star} {s2.view.isNone}"
  out := out.push s!"after-world: {((s2.marks.find? wid).map (·.color.name))} {← k.px (ctr world)}"
  out := out.push s!"after-safe: {(sid.bind s2.marks.find?).isNone} {decide ((← tinted safe) = 0)}"
  out := out.push s!"after-comment: {(cid.bind s2.marks.find?).map (·.text) == some "Comment ✓ [x]"} {((s2.marks.find? wid).bind s2.marks.commentOf).map (·.id) == cid} {decide ((← tagCount "note") > 0)}"
  out := out.push s!"after-note: {(note.bind fun n => s2.marks.find? n.id).map (·.text) == some "Edited note"}"
  out := out.push s!"file-marks1: {← fileMarks path}"
  IO.FS.writeBinFile (file "edit1.pdf") (← IO.FS.readBinFile path)
  -- 6. A third revision: back to blue, the comment deleted.
  discard <| run ["after", "600"]
  k.clickAt wpos
  discard <| run [".menubar.edit.hl", "invoke", Marks.Color.blue.label]
  if let some c := cid then deleteMark st c
  sendEvent ".c" "<Control-Key-s>"
  let s3 ← st.get
  out := out.push s!"third: {s3.marks.marks.size} {s3.marks.dirty} {((s3.marks.find? wid).map (·.color.name))} {(cid.bind s3.marks.find?).isNone} {← k.px (ctr world)}"
  out := out.push s!"file-marks2: {← fileMarks path}"
  IO.FS.writeFile (file "edit.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke step of saving an encrypted document (`SAFEPDF_VIEWER_SMOKE_MODE=encrypted`, task
9.5c): a note at (100, 100), then Ctrl+S (answered Overwrite, should it ask). Until task 9.5f
the writer refuses encrypted files before any question (task 9.r2): the status line shows its
error, nothing is written and the mark stays unsaved; afterwards the opened file is written and
the mark saved. Either way the viewer keeps running. Results in `encrypted.txt`. -/
def smokeEncrypted (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  discard <| run ["update"]
  let orig := (← st.get).path.getD ""
  let target := orig
  let size0 ← k.size orig
  smokeNoteAt st 100 100 "encrypted"
  let before := (← st.get).marks.dirty
  discard <| run ["set", "::safepdf::autoAnswer", "overwrite"]
  discard <| run ["set", "::safepdf::lastAsk", ""]
  sendEvent ".c" "<Control-Key-s>"
  let s ← st.get
  let written := (← k.size orig) != size0
  let status ← k.status
  let outcome :=
    if !written && s.marks.dirty && status.startsWith "cannot save to" then "refused"
    else if written && !s.marks.dirty && s.path == some target then "saved"
    else "inconsistent"
  IO.FS.writeFile (file "encrypted.txt")
    s!"dirty-before: {before}\noutcome: {outcome}\nalive: {← run ["winfo", "exists", "."]}\nasked: {!(← k.lastAsk).isEmpty}\nstatus: {status}\n"
  discard <| run ["destroy", "."]

/-- Smoke steps of XFDF import/export (`SAFEPDF_VIEWER_SMOKE_MODE=xfdf`, task 9.11) on a copy
of the text PDF of `smokeText` (substitute fonts off, page 1 white): a yellow highlight on
`world` with a comment (the edit bubble's Comment) and a note at (300, 400) with
`smokeNoteText`; File → Export annotations… (`autoPath`) writes `marks.xfdf` (the comment as
`<contents>` inside the `<highlight>`); every mark is deleted (the `world` pixels white
again); `importXfdf` of `marks.xfdf` brings the three marks back (pixels yellow, the comment
still the highlight's, the note text equal, all unsaved) and the status line counts them;
importing it again adds nothing; the hostile samples copied into `DIR` (`billion-laughs.xfdf`,
`xxe.xfdf`, `undeclared-entity.xfdf`), a missing file and a non-XFDF file each show an error
and change nothing; Acrobat's sample imports 3 marks and skips 2. Results in `xfdf.txt`. -/
def smokeXfdf (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text index")
  let some world := ((ix.hits (Select.normQuery "world"))[0]?).bind fun (a, b) =>
      (Select.rangeBoxes ix.cells a b).head? | throw (IO.userError "world not found")
  let worldC : Pt := ⟨(world.llx + world.urx) / 2, (world.lly + world.ury) / 2⟩
  let some wpos ← boxWindowPos st world | throw (IO.userError "world not shown")
  -- A summary of the store: marks, notes, the world highlight's comment text, the plain
  -- note's text equal to `smokeNoteText`, unsaved.
  let summary : IO String := do
    let s ← st.get
    let ms := s.marks.marks.toList
    let hl := ms.find? (!·.isNote)
    let comment := (hl.bind s.marks.commentOf).map (·.text)
    let note := ms.find? fun m => m.isNote && !s.marks.isComment m
    let okC := comment == some "Comment ✓ <&>"
    let okN := (note.map (·.text)) == some smokeNoteText
    return s!"{ms.length} {(ms.filter (·.isNote)).length} {okC} {okN} {s.marks.dirty}"
  -- 1. Highlight, comment, note.
  for _ in [0:2] do k.clickAt wpos
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.highlight.label]
  sendKey "Escape"
  discard <| run ["after", "600"]
  k.clickAt wpos
  addNote st none
  discard <| run ["update", "idletasks"]
  discard <| run [".note.t", "insert", "end", "Comment ✓ <&>"]
  discard <| run [".note.b.save", "invoke"]
  discard <| run ["destroy", ".note"]
  sendKey "Escape"
  smokeNoteAt st 300 400 smokeNoteText
  discard <| run ["destroy", ".note"]
  out := out.push s!"marks: {← summary}"
  out := out.push s!"world-px: {← k.px worldC}"
  -- 2. Export through the File menu (the dialog answered by `autoPath`).
  out := out.push s!"menu-states: {← k.menuState .importXfdf} {← k.menuState .exportXfdf}"
  discard <| run ["set", "::safepdf::autoPath", file "marks.xfdf"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.exportXfdf.label]
  discard <| run ["set", "::safepdf::autoPath", ""]
  out := out.push s!"export-status: {← k.status}"
  out := out.push s!"export-default: {baseName (xfdfTarget ((← st.get).path.getD ""))}"
  -- 3. Every mark removed.
  for m in (← st.get).marks.marks.toList do deleteMark st m.id
  out := out.push s!"removed: {(← st.get).marks.marks.size} {← k.px worldC}"
  -- 4. Import: the marks are back.
  importXfdf st (some (file "marks.xfdf"))
  out := out.push s!"import-status: {← k.status}"
  out := out.push s!"imported: {← summary}"
  out := out.push s!"imported-px: {← k.px worldC} {← k.star}"
  -- 5. Again: nothing new.
  importXfdf st (some (file "marks.xfdf"))
  out := out.push s!"reimport-status: {← k.status}"
  out := out.push s!"reimported: {← summary}"
  -- 6. Hostile and broken files: an error, nothing changed.
  for name in ["billion-laughs.xfdf", "xxe.xfdf", "undeclared-entity.xfdf", "missing.xfdf",
      "not-xfdf.xfdf"] do
    let before ← summary
    importXfdf st (some (file name))
    let refused := (← k.status).startsWith s!"cannot import {name}: "
    let same := before == (← summary)
    out := out.push s!"hostile {name}: {refused} {same} {← run ["winfo", "exists", "."]}"
    out := out.push s!"hostile-status {name}: {← k.status}"
  -- 7. Another tool's export (Acrobat style): 3 marks, 2 skipped.
  importXfdf st (some (file "acrobat.xfdf"))
  out := out.push s!"acrobat-status: {← k.status}"
  out := out.push s!"acrobat: {(← st.get).marks.marks.size}"
  IO.FS.writeFile (file "xfdf.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Window position of the centre of a page-space box on page `p` (any laid-out page, task 9.3). -/
def boxWindowPosOn (st : IO.Ref State) (p : Nat) (b : Box) : IO (Option (String × String)) := do
  let s ← st.get
  let some sl := slotOf s p | return none
  let (x0, y0, x1, y1) := sl.rect b
  let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
    View.parseDecimal (← run [".c", "canvasy", "0"])) | return none
  return some (toString ((x0 + x1) / 2 - vx).floor, toString ((y0 + y1) / 2 - vy).floor)

/-- The pixel ("R G B") of page `p`'s photo at page point `q`. -/
def photoPixel (st : IO.Ref State) (p : Nat) (q : Pt) : IO String := do
  let s ← st.get
  let some sl := slotOf s p | return "<not laid out>"
  if !s.hasPhoto p then return "<no photo>"
  let d := toScreen sl.vp.zoom sl.vp.rot sl.vp.box q
  try run [photoOf p, "get", toString d.x.floor, toString d.y.floor]
  catch _ => pure "<outside>"

/-- Smoke steps of the view modes (`SAFEPDF_VIEWER_SMOKE_MODE=modes`, task 9.3), on a
three-page text PDF (substitute fonts off, so the pages are white) whose pages say `Alpha`,
`Bravo` and `zebra`. Every mode is chosen through its View menu entry. Continuous: three page
frames, the wheel scrolls through the document and the page field follows 1, 2, 3 without page
turns, Home goes back; Next page; a double click on `Bravo` (page 2) + `h` highlights it (photo
pixels yellow); a search for `zebra` from page 1 goes to page 3 and scrolls the hit into the
view. Continuous facing (odd): pages 1 and 2 side by side, the highlight still drawn. Facing
(page scrolling, odd spreads): two frames, Next moves 1 → 3, Previous back, Next disabled in the
last spread, a wheel notch at fit page turns to the next spread. Even spreads: page 1 alone,
Next → 2|3. Back to single page. Writes `modes.txt`. -/
def smokeModes (st : IO.Ref State) (dir : String) : IO Unit := do
  let mut out : Array String := #[]
  discard <| run ["update"]
  let invoke (c : Menu.Cmd) : IO Unit := do
    let path := ((Menu.locate c).map (·.1)).getD ".menubar.view"
    discard <| run [path, "invoke", c.label]
    discard <| run ["update", "idletasks"]
  let field : IO String := run ["set", "::safepdf::pageText"]
  let page : IO Nat := return (← st.get).page + 1
  let slotsStr : IO String := do
    return ",".intercalate ((← st.get).slots.toList.map fun sl => toString (sl.place.page + 1))
  let frames : IO Nat := tagCount "pageframe"
  let yv : IO String := run [".c", "yview"]
  let .ok ix2 ← pageIndex st 1 | throw (IO.userError "no text on page 2")
  let some (ba, bb) := (ix2.hits (Select.normQuery "Bravo"))[0]? | throw (IO.userError "no Bravo")
  let some bravo := (Select.rangeBoxes ix2.cells ba bb).head? | throw (IO.userError "no box")
  let bravoC : Pt := ⟨(bravo.llx + bravo.urx) / 2, (bravo.lly + bravo.ury) / 2⟩
  out := out.push s!"frames-single: {← frames}"
  -- 1. Continuous (Vertical Scrolling).
  invoke .scrollVertical
  settle st
  out := out.push s!"scroll-var: {← run ["set", Menu.scrollVar]}"
  out := out.push s!"frames-continuous: {← frames}"
  out := out.push s!"slots-continuous: {← slotsStr}"
  let s ← st.get
  out := out.push s!"region-vs-canvas: {s.regionH} {s.canvasH}"
  -- The wheel scrolls the whole document; the page field follows the page under the centre.
  let mut seen : Array String := #[← field]
  let mut maxPhotos := (← st.get).photos.size
  let mut notches := 0
  let mut lastTop : Rat := -1
  let mut monotone := true
  for _ in [0:400] do
    if let some (a, b) := viewFracs (← yv) then
      if b ≥ 1 then break
      if a < lastTop then monotone := false
      lastTop := a
    sendEvent ".c" "<MouseWheel>" ["-delta", "-120", "-x", "200", "-y", "200"]
    notches := notches + 1
    settle st
    let f ← field
    if seen.back? != some f then seen := seen.push f
    maxPhotos := max maxPhotos (← st.get).photos.size
  out := out.push s!"wheel-pages-seen: {",".intercalate seen.toList}"
  out := out.push s!"wheel-notches: {notches}"
  out := out.push s!"wheel-monotone: {monotone}"
  out := out.push s!"wheel-end: {← yv}"
  out := out.push s!"page-at-end: {← page}"
  out := out.push s!"max-photos: {maxPhotos}"
  sendKey "Home"
  settle st
  out := out.push s!"page-after-home: {← page} {← field}"
  out := out.push s!"y-after-home: {← yv}"
  -- 2. Next page; a highlight on page 2 (double click on `Bravo`, then `h`).
  invoke .nextPage
  settle st
  out := out.push s!"page-after-next: {← page} {← field}"
  -- Zooming in keeps the page point at the window centre there (C2 anchoring on its slot).
  let cx : Int := ((← st.get).canvasW / 2 : Nat)
  let cy : Int := ((← st.get).canvasH / 2 : Nat)
  let before ← pagePointAt st cx cy
  sendKey "plus"
  settle st
  let after ← pagePointAt st cx cy
  out := out.push s!"zoom-anchor: {match before, after with
    | some (p0, q0), some (p1, q1) =>
      decide (p0 == p1 ∧ (q0.x - q1.x) * (q0.x - q1.x) + (q0.y - q1.y) * (q0.y - q1.y) ≤ 4)
    | _, _ => false} {← page}"
  let some bpos ← boxWindowPosOn st 1 bravo | throw (IO.userError "page 2 not laid out")
  for _ in [0:2] do
    sendEvent ".c" "<ButtonPress-1>" ["-x", bpos.1, "-y", bpos.2]
    sendEvent ".c" "<ButtonRelease-1>" ["-x", bpos.1, "-y", bpos.2]
  out := out.push s!"sel-page: {((← st.get).sel.map (·.1 + 1)).getD 0}"
  sendKey "h"
  settle st
  out := out.push s!"marks: {(← st.get).marks.marks.toList.map (·.page + 1)}"
  out := out.push s!"hl-continuous: {← photoPixel st 1 bravoC}"
  -- 3. Search from page 1: the hit on page 3 is scrolled into view.
  sendKey "Home"
  settle st
  sendEvent ".c" "<Control-Key-f>"
  discard <| run ["update", "idletasks"]
  discard <| run ["set", "::safepdf::query", "zebra"]
  sendEvent ".find.e" "<Key-Return>"
  settle st
  out := out.push s!"find-status: {← run [".status", "cget", "-text"]}"
  out := out.push s!"page-after-find: {← page} {← field}"
  let hitBox := ((← run [".c", "bbox", "hit"]).splitOn " ").filterMap String.toInt?
  let vy := (View.parseDecimal (← run [".c", "canvasy", "0"])).getD 0
  let ch : Rat := (← st.get).canvasH
  out := out.push s!"hit-in-view: {match hitBox with
    | [_, y0, _, y1] => decide (vy ≤ (y0 : Rat) ∧ (y1 : Rat) ≤ vy + ch)
    | _ => false}"
  sendEvent ".find.e" "<Key-Escape>"
  -- 4. Continuous facing (odd spreads): pages 1 and 2 side by side.
  invoke .spreadOdd
  settle st
  out := out.push s!"spread-var: {← run ["set", Menu.spreadVar]}"
  let s ← st.get
  let ys := s.slots.toList.map fun sl => sl.place.y
  let xs := s.slots.toList.map fun sl => sl.place.x
  out := out.push s!"cfacing-rows: {match ys, xs with
    | [y0, y1, y2], [x0, x1, _] => decide (y0 == y1 ∧ x0 < x1 ∧ y2 > y0)
    | _, _ => false}"
  invoke .firstPage
  settle st
  out := out.push s!"hl-cfacing: {← photoPixel st 1 bravoC}"
  -- 5. Facing: page scrolling, odd spreads.
  invoke .scrollPage
  settle st
  out := out.push s!"facing-frames: {← frames} {← slotsStr} {← page}"
  out := out.push s!"hl-facing: {← photoPixel st 1 bravoC}"
  invoke .nextPage
  out := out.push s!"facing-next: {← page} {← field} {← slotsStr}"
  out := out.push s!"facing-next-state: {← run [".menubar.go", "entrycget", Menu.Cmd.nextPage.label, "-state"]}"
  invoke .nextPage
  out := out.push s!"facing-next-at-end: {← page}"
  invoke .prevPage
  out := out.push s!"facing-prev: {← page} {← slotsStr}"
  -- A wheel notch at fit page turns to the next spread.
  sendKey "f"
  sendEvent ".c" "<MouseWheel>" ["-delta", "-120", "-x", "200", "-y", "200"]
  out := out.push s!"facing-wheel: {← page} {← slotsStr}"
  sendEvent ".c" "<MouseWheel>" ["-delta", "120", "-x", "200", "-y", "200"]
  out := out.push s!"facing-wheel-up: {← page} {← slotsStr}"
  -- 6. Even spreads: page 1 alone, then 2|3.
  invoke .spreadEven
  out := out.push s!"even-first: {← page} {← slotsStr}"
  invoke .nextPage
  out := out.push s!"even-next: {← page} {← slotsStr}"
  out := out.push s!"even-next-state: {← run [".menubar.go", "entrycget", Menu.Cmd.nextPage.label, "-state"]}"
  out := out.push s!"hl-even: {← photoPixel st 1 bravoC}"
  -- 7. Back to the single page.
  invoke .spreadNone
  out := out.push s!"single-again: {← page} {← slotsStr} {← frames}"
  out := out.push s!"status: {← run [".status", "cget", "-text"]}"
  IO.FS.writeFile ((dir : System.FilePath) / "modes.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Scrolls the document from top to bottom with generated wheel notches in the view mode set
by `SAFEPDF_VIEWER_VIEW` (task 9.3; in the vertical modes the wheel scrolls the document, in
the page modes it turns the pages), rendering every page that comes into view before the next
notch (`SAFEPDF_VIEWER_SMOKE_MODE=scroll`; a benchmark, not part of the smoke test). Writes
`scroll.txt`: wall time, notches, pages rendered and the time spent rendering, the most photos
alive at once, the cache. -/
def smokeScroll (st : IO.Ref State) (dir : String) : IO Unit := do
  discard <| run ["update"]
  let t0 ← IO.monoNanosNow
  settle st
  let mut notches := 0
  let mut maxPhotos := (← st.get).photos.size
  for _ in [0:5000] do
    let s ← st.get
    if let some (_, b) := viewFracs (← run [".c", "yview"]) then
      if b ≥ 1 && s.page + 1 ≥ s.pageCount then break
    sendEvent ".c" "<MouseWheel>" ["-delta", "-120", "-x", "200", "-y", "200"]
    notches := notches + 1
    settle st
    maxPhotos := max maxPhotos (← st.get).photos.size
  let t1 ← IO.monoNanosNow
  let s ← st.get
  IO.FS.writeFile ((dir : System.FilePath) / "scroll.txt")
    s!"pages: {s.pageCount}\nnotches: {notches}\ntotal-ms: {formatMs (t1 - t0)}\n\
      renders: {s.renders}\nrender-ms: {formatMs s.renderNs}\n\
      max-photos: {maxPhotos}\ncache-entries: {s.cache.entries.size}\n\
      cache-mib: {s.cache.bytes / 1048576}\nlast-page: {s.page + 1}\n\
      canvas: {s.canvasW}x{s.canvasH}\nstatus: {← run [".status", "cget", "-text"]}\n"
  discard <| run ["destroy", "."]

/-- The current page and the view's top edge in scroll-region pixels (task 9.r1 traces). -/
def wheelPos (st : IO.Ref State) : IO (Nat × Nat) := do
  let s ← st.get
  let some (a, _) := viewFracs (← run [".c", "yview"]) | return (s.page, 0)
  return (s.page, (a * (s.regionH : Rat) + 1 / 2).floor.toNat)

/-- The `-delta` of a generated `<TouchpadScroll>` event with pixel deltas `dx`, `dy` (Tk 9
packs them as `dx << 16 | dy & 0xffff`; `tk::PreciseScrollDeltas` unpacks them). -/
def touchpadDelta (dx dy : Int) : Int :=
  dx * 65536 + (if dy < 0 then dy + 65536 else dy)

/-- Appends the line `l` to the file `f` (created if missing) and flushes it, so that a run
killed by the smoke script's timeout keeps what it wrote (task 10.c2). -/
def appendLine (f : System.FilePath) (l : String) : IO Unit := do
  let h ← IO.FS.Handle.mk f .append
  h.putStrLn l
  h.flush

/-- Prints `l` on stdout and flushes it (smoke progress lines that the smoke script shows even
when it kills the run, task 10.c2). -/
def progressLine (l : String) : IO Unit := do
  let o ← IO.getStdout
  o.putStrLn l
  o.flush

/-- One burst of wheel events for `smokeWheelFlow` (task 9.r1): from the top of page 1 in
the current view mode, sends `ev i` for `i = 0, 1, …` 8 ms apart with no pause (a trackpad
gesture or a fast wheel; between events only Tk's event loop runs, as for a user, no settling
of renders) until the current spread reaches the spread of page `target + 1`, or `maxEv`
events. Task 10.c2: the burst also stops after `stallCap` consecutive events that move nothing
(an event type the platform drops) or once it has run `budgetMs` (a slow display), and says
why (`stopped=`). Appends `label event ms page top` lines to `trace` and returns a summary
line: `reached`, `events`, the longest run of events that moved nothing (`max-stall`), moves
backwards (`back`), the largest move between two events on one page or, in the vertical
modes, in the document (`max-step`, pixels), and the largest top of a page just turned to in
the page modes (`turn-top`). -/
def flowBurst (st : IO.Ref State) (trace : IO.Ref (Array String)) (label : String)
    (ev : Nat → IO Unit) (target maxEv : Nat) (stallCap : Nat := 300)
    (budgetMs : Nat := 8000) : IO String := do
  sendKey "Home"
  settle st
  let s0 ← st.get
  let sp := s0.spread
  let goal := View.spreadOf sp (min target (s0.pageCount - 1))
  let vertical := s0.scroll == .vertical
  let t0 ← IO.monoMsNow
  let (p, y) ← wheelPos st
  let mut p0 := p
  let mut y0 := y
  let mut stall := 0
  let mut maxStall := 0
  let mut back := 0
  let mut maxStep := 0
  let mut turnTop := 0
  let mut events := 0
  let mut stopped := "none"
  for i in [0:maxEv] do
    if View.spreadOf sp (← st.get).page ≥ goal then break
    if stall ≥ stallCap then
      stopped := "stall"
      break
    if (← IO.monoMsNow) - t0 > budgetMs then
      stopped := "time"
      break
    ev i
    events := i + 1
    discard <| run ["update"]
    IO.sleep 8
    let (p1, y1) ← wheelPos st
    trace.modify (·.push s!"{label} {i} {(← IO.monoMsNow) - t0} {p1 + 1} {y1}")
    if p1 == p0 && y1 == y0 then
      stall := stall + 1
      maxStall := max maxStall stall
    else stall := 0
    if vertical then
      if y1 < y0 then back := back + 1
      maxStep := max maxStep (y1 - y0)
    else if p1 < p0 || (p1 == p0 && y1 < y0) then back := back + 1
    else if p1 == p0 then maxStep := max maxStep (y1 - y0)
    else turnTop := max turnTop y1
    p0 := p1
    y0 := y1
  let s ← st.get
  return s!"flow-{label}: reached={decide (View.spreadOf sp s.page ≥ goal)} page={s.page + 1} \
    events={events} max-stall={maxStall} back={back} max-step={maxStep} turn-top={turnTop} \
    view={s.canvasH} ms={(← IO.monoMsNow) - t0} stopped={stopped}"

/-- Wheel flow across page boundaries (`SAFEPDF_VIEWER_SMOKE_MODE=wheelflow`, task 9.r1): first
the view mode a freshly opened file is in (`default:`, the state and the View menu's radio
variables); then, in each of the four view modes at Page Width and in the single-page mode at
Page Fit, a trackpad-like burst of small `<TouchpadScroll>` deltas (12 px down, with ±1 px
of sideways jitter, as Tk 9 on macOS delivers them), a burst of third-notch `<MouseWheel>`
deltas (high-resolution wheels) and (task 10.c2) a burst of `<Button-5>` presses (the X11
wheel of Tk 8.6, one notch each) from page 1 to page 5 (`flowBurst`). Task 10.c2: every line
of `wheelflow.txt` and each burst's part of the per-event trace `wheelflow-trace.txt` are
written as soon as they are known, progress goes to stdout (`wheelflow-progress:`), and past
`totalMs` the run stops with an `error:` line instead of running into the smoke script's
timeout. -/
def smokeWheelFlow (st : IO.Ref State) (dir : String) (totalMs : Nat := 140000) : IO Unit := do
  let file := (dir : System.FilePath) / "wheelflow.txt"
  let traceFile := (dir : System.FilePath) / "wheelflow-trace.txt"
  IO.FS.writeFile file ""
  IO.FS.writeFile traceFile ""
  let tStart ← IO.monoMsNow
  let out (l : String) : IO Unit := appendLine file l
  let progress (l : String) : IO Unit := do
    progressLine s!"wheelflow-progress: {(← IO.monoMsNow) - tStart} ms {l}"
  progress "start"
  discard <| run ["update"]
  settle st
  let s0 ← st.get
  out s!"pages: {s0.pageCount}"
  out s!"default: scroll={s0.scroll.key} spread={s0.spread.key} \
    radio={← run ["set", Menu.scrollVar]} {← run ["set", Menu.spreadVar]} \
    continuous={← run ["set", "::safepdf::continuous"]}"
  let trace ← IO.mkRef (#[] : Array String)
  let tk ← run ["package", "provide", "Tk"]
  -- `<TouchpadScroll>` exists from Tk 8.7 on; on Tk 8.6 (Ubuntu's tk-dev) `bind` does not fail
  -- through `run`, so probing the binding reported a touchpad there (CI 50d5dd9) — test the
  -- version instead.
  let touchpad := (← run ["package", "vsatisfies", tk, "8.7-"]) == "1"
  let ws ← run ["tk", "windowingsystem"]
  out s!"tk: {tk} touchpad={touchpad} ws={ws}"
  progress s!"tk {tk} touchpad={touchpad} ws={ws}"
  let pad (i : Nat) : IO Unit :=
    sendEvent ".c" "<TouchpadScroll>"
      ["-delta", toString (touchpadDelta ([0, 1, 0, -1].getD (i % 4) 0) (-12)), "-x", "300", "-y", "300"]
  let fine (_ : Nat) : IO Unit :=
    sendEvent ".c" "<MouseWheel>" ["-delta", "-40", "-x", "300", "-y", "300"]
  let button (_ : Nat) : IO Unit := do
    sendEvent ".c" "<Button-5>" ["-x", "300", "-y", "300"]
    sendEvent ".c" "<ButtonRelease-5>" ["-x", "300", "-y", "300"]
  let cases : List (String × String × String × Toolbar.ZoomChoice) :=
    [("single", "page", "none", .pageWidth), ("continuous", "vertical", "none", .pageWidth),
     ("facing", "page", "odd", .pageWidth), ("continuous-facing", "vertical", "odd", .pageWidth),
     ("single-fit", "page", "none", .pageFit)]
  let burst (name : String) (ev : Nat → IO Unit) : IO Unit := do
    if (← IO.monoMsNow) - tStart > totalMs then
      throw <| IO.userError s!"time budget of {totalMs} ms used up before flow-{name}"
    progress s!"flow-{name} begins"
    trace.set #[]
    let l ← flowBurst st trace name ev 4 3000
    out l
    for t in (← trace.get) do appendLine traceFile t
    progress l
  for (label, sc, sp, z) in cases do
    progress s!"mode {label}"
    setViewMode st "scroll" sc
    setViewMode st "spread" sp
    setMode st z none
    settle st
    -- Task 10.c1: Tk 8.6 has no `<TouchpadScroll>` (generated ones are dropped, and the
    -- burst would run its 3000 events without moving).
    if touchpad then burst s!"{label}-pad" pad
    else out s!"flow-{label}-pad: skipped (Tk {tk} has no <TouchpadScroll>)"
    burst s!"{label}-fine" fine
    burst s!"{label}-button" button
  progress "done"
  discard <| run ["destroy", "."]

/-- Smoke steps of non-blocking rendering (`SAFEPDF_VIEWER_SMOKE_MODE=async`, task 8.8; the
viewer starts with `syncWaitMs := some 0`, so no event waits for a render) on a two-page PDF
whose page 1 takes the renderer seconds (`scripts/viewer-smoke-pdf.py --slow`). Step 0 (page 1
still rendering at the opening zoom Z0): records the placeholder, starts a Tcl timer that
counts its runs every 20 ms, and zooms in (`+`, zoom Z1): the event must return at once with
two renders running. Step 1 (400 ms later): the timer ran meanwhile, page 1 still has no photo,
both renders still run; `End` goes to the light page 2 at once. Step 2: page 2 shown and the
page field says 2 while page 1 still renders; `Home` goes back to page 1 (its Z1 render keeps
running). Later steps wait until no render runs, then record the dropped stale result (Z0),
page 1's photo size against its slot (Z1) and the status line, write `async.txt` and close. -/
def smokeAsync (st : IO.Ref State) (dir : String) : IO Unit := do
  let file : System.FilePath := (dir : System.FilePath) / "async.txt"
  let append (l : String) : IO Unit := do
    let old ← try IO.FS.readFile file catch _ => pure ""
    IO.FS.writeFile file (old ++ l ++ "\n")
  let s ← st.get
  st.modify ({ · with smokeStep := s.smokeStep + 1 })
  let next (ms : Nat) : IO Unit := discard <| run ["after", toString ms, "::safepdf::emit smoke"]
  let timed (act : IO Unit) : IO Nat := do
    let t0 ← IO.monoNanosNow
    act
    return ((← IO.monoNanosNow) - t0) / 1000000
  let running (p : Nat) (s : State) : Nat := (s.jobs.filter (·.key.page == p)).size
  match s.smokeStep with
  | 0 =>
    append s!"start: page {s.page + 1} photo {s.hasPhoto 0} jobs {s.jobs.size} placeholders {← tagCount "w0"}"
    append s!"status0: {← run [".status", "cget", "-text"]}"
    discard <| run ["set", "::safepdf::smkTicks", "0"]
    discard <| run ["proc", "::safepdf::smkTick", "",
      "incr ::safepdf::smkTicks; after 20 ::safepdf::smkTick"]
    discard <| run ["::safepdf::smkTick"]
    let ms ← timed (sendKey "plus")
    let s ← st.get
    append s!"zoom-event-ms: {ms}"
    append s!"after-zoom: jobs {running 0 s} photo {s.hasPhoto 0} placeholders {← tagCount "w0"}"
    next 400
  | 1 =>
    append s!"ticks: {← run ["set", "::safepdf::smkTicks"]}"
    append s!"during: jobs {running 0 s} photo {s.hasPhoto 0} placeholders {← tagCount "w0"}"
    let ms ← timed (sendKey "End")
    append s!"end-event-ms: {ms}"
    next 400
  | 2 =>
    append s!"page2: page {s.page + 1} field {← run ["set", "::safepdf::pageText"]} photo {s.hasPhoto 1} slow-jobs {running 0 s}"
    let ms ← timed (sendKey "Home")
    let s ← st.get
    append s!"home-event-ms: {ms}"
    append s!"home: page {s.page + 1} photo {s.hasPhoto 0} placeholders {← tagCount "w0"}"
    next 300
  | k =>
    if !s.jobs.isEmpty && k < 200 then next 300; return
    let sz ← match s.photos.find? (·.1 == 0), slotOf s 0 with
      | some (_, .ok img), some sl =>
        pure s!"{img.w}x{img.h} slot {sl.place.w}x{sl.place.h}"
      | _, _ => pure "none"
    append s!"final: page {s.page + 1} jobs {s.jobs.size} stale {s.staleDropped} renders {s.renders}"
    append s!"final-photo: {sz}"
    append s!"render-ms: {formatMs (s.renderNs / max 1 s.renders)} avg"
    append s!"status: {← run [".status", "cget", "-text"]}"
    append s!"ticks-end: {← run ["set", "::safepdf::smkTicks"]}"
    append "done"
    discard <| run ["destroy", "."]

/-- Median of a non-empty list of numbers (0 for none). -/
def median (xs : List Nat) : Nat :=
  let ys := xs.mergeSort
  ys.getD (ys.length / 2) 0

/-- Times the render of page `p` at its current zoom and rotation three times in this process
(`renderPage`) and three times through the document worker (request to answer, the image
sent over the pipe and decoded), and returns the medians (task 12.2c's measurement; blocks the
event loop: smoke mode only). -/
def measureRender (st : IO.Ref State) (p : Nat) : IO String := do
  let s ← st.get
  let some doc := s.doc | return "no document"
  let some sl := slotOf s p | return "no slot"
  let key := keyOf s sl
  let mut here : List Nat := []
  for _ in [0:3] do
    let t0 ← IO.monoNanosNow
    let r ← renderPage doc p key.zoom key.rot s.subst s.oc
    let ok := match r with | .ok _ => true | .error _ => false
    let t1 ← IO.monoNanosNow
    if ok then here := (t1 - t0) :: here
  let some (ses, src) ← workerFor st doc | return "no worker"
  let mut viaWorker : List Nat := []
  for _ in [0:3] do
    let (_, t) ← ses.submit src (.render p key.zoom (Worker.rotationToNat key.rot) (← st.get).oc) 0
    if let .response (.image ..) ns ← IO.wait t then viaWorker := ns :: viaWorker
  return s!"page {p + 1} {sl.place.w}x{sl.place.h} px: in-process {formatMs (median here)} ms, \
    worker {formatMs (median viaWorker)} ms (medians of {here.length} and {viaWorker.length})"

/-- What page `p` shows: `image WxH`, `error: …` or `none`. -/
def photoKind (s : State) (p : Nat) : String :=
  match s.photos.find? (·.1 == p) with
  | some (_, .ok img) => s!"image {img.w}x{img.h}"
  | some (_, .error e) => s!"error: {e}"
  | none => "none"

/-- Smoke steps of the document worker (`SAFEPDF_VIEWER_SMOKE_MODE=worker`, task 12.2c; run
with `SAFEPDF_WORKER_DEADLINE_MS`, e.g. 4000, and a second file `next.pdf` in the output
directory). Step 0: the opened pages came from the worker; render times in this process and
through the worker (`measureRender`); then **no-block** (a): the next workers sleep 1.5 s
before each render (`Worker.TestHooks`, through a new document id, so a new worker), no event
waits for renders (`syncWaitMs := some 0`), a 10 ms Tcl heartbeat records its largest gap, and
`+` zooms. Phase a waits for that render: the gap, the photo. **Kill/restart** (b): workers
sleep ten minutes, `+` again; phase b waits until the render ends: after the deadline the page
shows the timeout and the status says so. (c) the stall is lifted, `+` again: the same document
in a fresh worker (spawned with the bytes again). (d) `next.pdf` opens and renders through a
new worker; its render times. Writes `worker.txt`. -/
def smokeWorker (st : IO.Ref State) (dir : String) : IO Unit := do
  let file : System.FilePath := (dir : System.FilePath) / "worker.txt"
  let append (l : String) : IO Unit := do
    let old ← try IO.FS.readFile file catch _ => pure ""
    IO.FS.writeFile file (old ++ l ++ "\n")
  let s ← st.get
  st.modify ({ · with smokeStep := s.smokeStep + 1 })
  let next (ms : Nat) : IO Unit := discard <| run ["after", toString ms, "::safepdf::emit smoke"]
  let finish : IO Unit := do
    append "done"
    discard <| run ["destroy", "."]
  let some ses := s.worker | do
    append "error: no worker session"
    finish
  let stats : IO String := do
    let w ← ses.state.get
    return s!"spawns {w.spawns} timeouts {w.timeouts} kills {w.kills}"
  let timed (act : IO Unit) : IO Nat := do
    let t0 ← IO.monoNanosNow
    act
    return ((← IO.monoNanosNow) - t0) / 1000000
  let nowMs : IO Nat := return (← IO.monoNanosNow) / 1000000
  let hbReset : IO Unit := do
    discard <| run ["set", "::safepdf::hbMax", "0"]
    discard <| Shim.eval "set ::safepdf::hbLast [clock milliseconds]"
  let hbMax : IO String := run ["set", "::safepdf::hbMax"]
  let status : IO String := run [".status", "cget", "-text"]
  let phase ← Shim.eval "expr {[info exists ::safepdf::wkPhase] ? $::safepdf::wkPhase : {}}"
  let setPhase (p : String) : IO Unit := discard <| run ["set", "::safepdf::wkPhase", p]
  let waiting : Bool := !s.jobs.isEmpty && s.smokeStep < 200
  match phase with
  | "" =>
    append s!"open: page {s.page + 1} {photoKind s s.page} worker-renders {s.workerRenders} \
      renders {s.renders} {← stats}"
    append s!"measure-a: {← measureRender st s.page}"
    -- Task 12.2d: the page's text index and links come from the worker and equal the ones
    -- read in this process.
    let t0 ← IO.monoNanosNow
    let ix ← pageIndex st s.page
    let ls ← linksOf st s.page
    let t1 ← IO.monoNanosNow
    let s1 ← st.get
    let here := match s1.doc with
      | some d => match d.pages[s.page]? with
        | some pg => match (SafePdf.Core.Annot.extractDocPageAnnots limits d pg
            (SafePdf.Core.Filter.Budget.init limits) (oc := s1.oc)).1 with
          | .ok pt => some (Select.fullText (Select.PageIndex.ofText pt).cells)
          | .error _ => none
        | none => none
      | none => none
    let wtext := match ix with | .ok i => some (Select.fullText i.cells) | .error _ => none
    let hereLinks := (s1.doc.map fun d => (Links.pageLinks d limits s.page).size).getD 0
    append s!"text: worker-texts {s1.workerTexts} worker-links {s1.workerLinks} \
      same-text {decide (wtext.isSome && wtext == here)} chars {(wtext.map (·.length)).getD 0} \
      links {ls.size} same-links {decide (ls.size == hereLinks)} \
      ms {(t1 - t0) / 1000000}"
    -- (a) no-block: a 10 ms heartbeat, renders that take 1.5 s longer, a zoom.
    discard <| Shim.eval "proc ::safepdf::hb {} {
  set n [clock milliseconds]
  set d [expr {$n - $::safepdf::hbLast}]
  if {$d > $::safepdf::hbMax} { set ::safepdf::hbMax $d }
  set ::safepdf::hbLast $n
  incr ::safepdf::hbTicks
  after 10 ::safepdf::hb
}"
    discard <| run ["set", "::safepdf::hbTicks", "0"]
    hbReset
    discard <| run ["::safepdf::hb"]
    ses.setEnv #[("SAFEPDF_WORKER_TEST_STALL_MS", some "1500")]
    st.modify fun s => { s with srcSerial := s.srcSerial + 1, syncWaitMs := some 0 }
    discard <| run ["set", "::safepdf::wkT0", toString (← nowMs)]
    let ms ← timed (sendKey "plus")
    append s!"a-event-ms: {ms}"
    setPhase "a"
    next 300
  | "a" =>
    if waiting then next 300; return
    let t0 := ((← run ["set", "::safepdf::wkT0"]).toNat?).getD 0
    append s!"noblock: {photoKind s s.page} elapsed-ms {(← nowMs) - t0} max-gap-ms {← hbMax} \
      ticks {← run ["set", "::safepdf::hbTicks"]} {← stats}"
    append s!"noblock-status: {← status}"
    -- (b) a render that never ends: killed after the deadline.
    ses.setEnv #[("SAFEPDF_WORKER_TEST_STALL_MS", some "600000")]
    st.modify fun s => { s with srcSerial := s.srcSerial + 1 }
    hbReset
    discard <| run ["set", "::safepdf::wkT0", toString (← nowMs)]
    let ms ← timed (sendKey "plus")
    append s!"b-event-ms: {ms}"
    setPhase "b"
    next 300
  | "b" =>
    if waiting then next 300; return
    let t0 := ((← run ["set", "::safepdf::wkT0"]).toNat?).getD 0
    append s!"stalled: {photoKind s s.page} elapsed-ms {(← nowMs) - t0} max-gap-ms {← hbMax} \
      deadline-ms {ses.cfg.deadlineMs} {← stats}"
    append s!"stalled-status: {← status}"
    -- (c) the same document again, in a fresh worker (no stall).
    ses.setEnv #[]
    let ms ← timed (sendKey "plus")
    append s!"c-event-ms: {ms}"
    setPhase "c"
    next 300
  | "c" =>
    if waiting then next 300; return
    append s!"respawn: {photoKind s s.page} {← stats}"
    -- (d) the next file.
    let path := ((dir : System.FilePath) / "next.pdf").toString
    let ms ← timed (openFile st path)
    append s!"d-open-ms: {ms}"
    setPhase "d"
    next 300
  | _ =>
    if waiting then next 300; return
    append s!"next: page {s.page + 1}/{s.pageCount} {photoKind s s.page} outline {s.outline.size} {← stats}"
    append s!"next-status: {← status}"
    append s!"measure-b: {← measureRender st s.page}"
    append s!"cancelled: {s.cancelledRenders} stale {s.staleDropped}"
    finish

/-- Tcl probes of the outline-toggle check of `smokeR4` (task 9.r4): `r4sample WHY` appends
`{WHY canvas-width x y screen-x}` to `::safepdf::r4log`, where x and y are the canvas-window
position of the first page frame and screen-x its x on the screen (`none` without one); it runs at every `<Configure>` of the canvas (after
the viewer's own binding) and every 2 ms while `r4tick` runs. -/
def r4Probe : String := "
set ::safepdf::r4log {}
proc ::safepdf::r4sample {why} {
  set b [.c bbox pageframe]
  if {$b eq {}} { set x none; set y none; set sx none } else {
    set x [expr {round([lindex $b 0] - [.c canvasx 0])}]
    set y [expr {round([lindex $b 1] - [.c canvasy 0])}]
    set sx [expr {[winfo rootx .c] + $x}]
  }
  lappend ::safepdf::r4log [list $why [winfo width .c] $x $y $sx]
}
proc ::safepdf::r4tick {n} {
  ::safepdf::r4sample tick
  if {$n > 0} { after 2 [list ::safepdf::r4tick [expr {$n - 1}]] }
}
bind .c <Configure> {+::safepdf::r4sample conf}
proc ::safepdf::r4toggle {} {
  set ::safepdf::r4log {}
  ::safepdf::r4sample start
  ::safepdf::btnInvoke .bar.sidebar
  ::safepdf::r4tick 200
  set ::safepdf::r4done 0
  after 700 {set ::safepdf::r4done 1}
  vwait ::safepdf::r4done
  ::safepdf::r4sample end
  return $::safepdf::r4log
}
"

/-- Smoke steps of task 9.r4 (`SAFEPDF_VIEWER_SMOKE_MODE=r4`), on the text PDF (bubble) or the
outline PDF (sidebar), started in the default view. Writes `r4.txt`:
* the view-mode drop-down: the default (Vertical Scrolling), each of its four entries
  invoked (scroll and spread variables, the checked entry, the icon), the View menu's Even
  Spreads and the `»` menu's Page Scrolling followed by the drop-down, Two Pages keeping Even
  Spreads; `toolbar.png` / `viewmenu.png` (when `import` is installed);
* with text: a drag over `world` shows the float bubble with its two buttons
  (`bubble.png`); its Add comment adds one note anchored to the selection's quads, opens
  its popup and closes the bubble;
* with an outline: at Page Fit in Single Page and Vertical Scrolling, the outline closed and
  opened, each with the page frame's window position sampled at every canvas `<Configure>`
  and every 2 ms for 700 ms (`r4Probe`); the distinct x positions in order must be just the
  start and the end. -/
def smokeR4 (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let mut out : Array String := #[]
  discard <| run ["update"]
  let shot (name : String) (win : String) : IO Unit := do
    discard <| run ["update"]
    try
      let wid ← if win == "root" then pure "root" else run ["winfo", "id", win]
      discard <| IO.Process.output { cmd := "import", args := #["-window", wid, "-depth", "8", file name] }
    catch _ => pure ()
  let vars : IO String := do
    return s!"{← run ["set", "::safepdf::viewSel"]} {← run ["set", Menu.scrollVar]} {← run ["set", Menu.spreadVar]} icon={← run ["set", "::safepdf::viewShown"]} items={(← run [".bar.vmode", "find", "withtag", "vicon"]).splitOn " " |>.length} on={← run ["set", "::safepdf::viewOn"]}"
  out := out.push s!"view0: {← vars}"
  out := out.push s!"view-entries: {← run [".viewmenu", "entrycget", "0", "-label"]}|{← run [".viewmenu", "entrycget", "1", "-label"]}|{← run [".viewmenu", "entrycget", "2", "-label"]}|{← run [".viewmenu", "entrycget", "3", "-label"]}"
  out := out.push s!"view-left: {← run ["pack", "slaves", ".bar.l"]}"
  out := out.push s!"view-tip: {← run ["set", "::safepdf::btn(tip,.bar.vmode)"]}"
  for c in Toolbar.ViewChoice.all.reverse ++ [.vertical] do
    discard <| run [".viewmenu", "invoke", c.label]
    discard <| run ["update"]
    let s ← st.get
    out := out.push s!"view-{c.key}: {← vars} state={s.scroll.key} {s.spread.key} slots={s.slots.size}"
  let invokeMenu (k : Menu.Cmd) : IO Unit := do
    if let some (m, i) := Menu.locate k then discard <| run [m, "invoke", toString i]
    discard <| run ["update"]
  invokeMenu .spreadEven
  out := out.push s!"menu-even: {← vars}"
  discard <| run [".viewmenu", "invoke", "Two Pages"]
  discard <| run ["update"]
  out := out.push s!"view-two-even: {← vars}"
  discard <| run [Toolbar.morePath, "invoke", "Vertical Scrolling"]
  discard <| run ["update"]
  out := out.push s!"more-vertical: {← vars}"
  invokeMenu .spreadNone
  out := out.push s!"menu-none: {← vars}"
  shot "toolbar.png" "."
  discard <| run [".viewmenu", "post", toString ((← run ["winfo", "rootx", ".bar.vmode"]).toNat?.getD 0),
    toString ((← run ["winfo", "rooty", ".bar.vmode"]).toNat?.getD 0 + 34)]
  shot "viewmenu.png" "root"
  discard <| run [".viewmenu", "unpost"]
  -- (a) The float bubble's Add comment.
  if let .ok ix ← pageIndex st 0 then
    if let some (wa, wb) := (ix.hits (Select.normQuery "world"))[0]? then
      if let (some p0, some p1) := (← cellWindowPos st ix wa, ← cellWindowPos st ix (wb - 1)) then
        sendEvent ".c" "<ButtonPress-1>" ["-x", p0.1, "-y", p0.2]
        sendEvent ".c" "<Motion>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
        sendEvent ".c" "<ButtonRelease-1>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
        discard <| run ["update"]
        let s ← st.get
        let quads : List Box := match s.sel with
          | some (_, a, b) => Select.rangeBoxes ix.cells a b
          | none => []
        match s.bubble with
        | some (k, r) =>
          out := out.push s!"bubble: {repr k} {k.btns.map (·.name)} w={r.x1 - r.x0} items={← tagCount "b:comment"}"
          out := out.push s!"bubble-in-region: {decide (0 ≤ r.x0 ∧ r.x1 ≤ (s.regionW : Rat) ∧ 0 ≤ r.y0 ∧ r.y1 ≤ (s.regionH : Rat))}"
          out := out.push s!"bubble-bind: {← run [".c", "bind", "b:comment", "<Enter>"]}"
          shot "bubble.png" "."
          discard <| run ["::safepdf::bubTipShow", "b:comment", "Add comment"]
          out := out.push s!"bubble-tip: {← run ["winfo", "exists", ".tip"]} {← try run [".tip.l", "cget", "-text"] catch _ => pure ""}"
          shot "bubble-tip.png" "root"
          discard <| run ["::safepdf::bubTipHide"]
          let n0 := s.marks.marks.size
          let some (_, x0, x1) := k.layout.find? (·.1 == .comment) | pure ()
          let vx := (View.parseDecimal (← run [".c", "canvasx", "0"])).getD 0
          let vy := (View.parseDecimal (← run [".c", "canvasy", "0"])).getD 0
          let bx := toString (r.x0 + (x0 + x1) / 2 - vx).floor
          let byy := toString ((r.y0 + r.y1) / 2 - vy).floor
          let t := toString (← IO.monoMsNow)
          sendEvent ".c" "<ButtonPress-1>" ["-x", bx, "-y", byy, "-time", t]
          sendEvent ".c" "<ButtonRelease-1>" ["-x", bx, "-y", byy, "-time", t]
          discard <| run ["update"]
          let s ← st.get
          let added := s.marks.marks.toList.drop n0
          let anchored := added.any fun m => match m.kind with
            | .note _ (.quads qs) => qs == quads && !qs.isEmpty
            | _ => false
          out := out.push s!"comment: added={added.length} note-on-selection={anchored} popup={← run ["winfo", "exists", ".note"]} bubble-after={s.bubble.isSome} sel-after={s.sel.isSome}"
          if let some m := added.head? then
            discard <| run ["::safepdf::noteDone", toString m.id, "save"]
            discard <| run ["update"]
        | none => out := out.push "bubble: none"
  -- (c) The outline toggle at Page Fit.
  if !(← st.get).outline.isEmpty then
    discard <| Shim.eval r4Probe
    for c in [Toolbar.ViewChoice.single, .vertical] do
      discard <| run [".viewmenu", "invoke", c.label]
      discard <| run [".zoommenu", "invoke", "Page Fit"]
      discard <| run ["update"]
      if !(← st.get).outlineShown then
        discard <| run ["::safepdf::btnInvoke", ".bar.sidebar"]
        discard <| run ["after", "300", "set ::safepdf::r4w 1"]
        discard <| run ["vwait", "::safepdf::r4w"]
      for what in ["close", "open"] do
        let log ← run ["::safepdf::r4toggle"]
        out := out.push s!"outline-{what}-{c.key}: shown={(← st.get).outlineShown} {log}"
  out := out.push "done"
  IO.FS.writeFile (file "r4.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- The fixtures of the open-settings smoke step (task 9.r8), opened one after another from
the directory of the file the viewer started with (`scripts/viewer-smoke.sh` case 1s writes
them). -/
def openSettingsFixtures : List String :=
  ["layout-SinglePage", "layout-OneColumn", "layout-TwoColumnLeft", "layout-TwoColumnRight",
   "layout-TwoPageLeft", "layout-TwoPageRight", "mode-UseOutlines", "mode-UseNone",
   "mode-UseThumbs", "xyz", "fit", "named", "js", "uri", "prefs", "r2l", "full", "window",
   "none"]

/-- Smoke steps of task 9.r8 (`SAFEPDF_VIEWER_SMOKE_MODE=opensettings`): opens each of
`openSettingsFixtures` with `openFile` (the File → Open path after its dialog) and writes one
line per file to `opensettings.txt`: view mode (state and the View menu's variables), right to
left, zoom choice, page, outline shown, full screen (state and `wm attributes`), toolbar /
menubar / scroll bar shown, window title, the view top's offset from the current page's top,
the page frames' x in a spread, and the status line. Escape is pressed after `prefs` (the
hidden toolbar comes back) and after `full` (full screen ends, the outline opens for
`/NonFullScreenPageMode /UseOutlines`); `xyz` is reopened with `keepView` after the user
changed the view (the reopen after Save keeps it); the last file has no settings (nothing
carries over). -/
def smokeOpenSettings (st : IO.Ref State) (dir : String) : IO Unit := do
  let base := dirOf ((← st.get).path.getD "")
  let mut out : Array String := #[]
  let row (name : String) : IO String := do
    discard <| run ["update"]
    let s ← st.get
    let off ← match slotOf s s.page, ← viewBand s with
      | some sl, some (top, _, _, _) => pure s!"{(top : Int) - (sl.place.y : Int)}"
      | _, _ => pure "-"
    let xs := s.slots.toList.take 2 |>.map (fun sl => s!"{sl.place.page}@{sl.place.x}")
    return s!"{name}: view={s.scroll.key},{s.spread.key} vars={← run ["set", Menu.scrollVar]},\
      {← run ["set", Menu.spreadVar]} rtl={s.rtl} zoom={s.zoomSel.label} page={s.page + 1} \
      outline={s.outlineShown} panel={s.panel.info.key} full={s.fullScreen},{← run ["wm", "attributes", ".", "-fullscreen"]} \
      bar={← run ["winfo", "ismapped", ".bar"]} menu={← run [".", "cget", "-menu"]} \
      ys={← run ["winfo", "ismapped", ".ys"]} geom={← run ["wm", "geometry", "."]} off={off} xs={",".intercalate xs} \
      title={← run ["wm", "title", "."]} status={← run [".status", "cget", "-text"]}"
  out := out.push (← row "start")
  for f in openSettingsFixtures do
    openFile st s!"{base}/{f}.pdf"
    settle st
    out := out.push (← row f)
    if f == "prefs" || f == "full" then
      -- Tk Aqua ignores leaving full screen while the window is still entering it: wait for
      -- the transition, as a user would (task 10.11).
      if f == "full" && (← isAqua) then
        discard <| run ["after", "1000"]
        discard <| run ["update"]
      sendEvent ".c" "<Key-Escape>"
      settle st
      out := out.push (← row s!"{f}-escape")
    if f == "xyz" then
      -- The user's changes win until the next open; the reopen after Save keeps them.
      setViewMode st "view" "two"
      zoom st "actual" none
      settle st
      out := out.push (← row "xyz-user")
      openFile st s!"{base}/{f}.pdf" (keepView := true)
      settle st
      out := out.push (← row "xyz-keep")
  out := out.push "done"
  IO.FS.writeFile ((dir : System.FilePath) / "opensettings.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke step of the platform keys and the icon (`SAFEPDF_VIEWER_SMOKE_MODE=keys`, task
9.r3), on the text PDF; with `SAFEPDF_VIEWER_PLATFORM=aqua` the aqua mapping is installed
on X11 (where Tk's `Command` modifier is Meta). Writes `keys.txt`: the platform, menu and
context-menu accelerators, the bindings of Ctrl/Command+S and Ctrl/Command+Shift+S, the
quit binding of the find bar and `primaryBind`, `::tk::mac::Quit`, the Save tooltip, the
status after the primary-modifier Select all key (generated as a Tk event), the icon images'
sizes and, when `xprop` is installed, the start of the window's `_NET_WM_ICON`. Task 10.9
adds (after the 9.r3 lines) the accelerators of Go to page, First page, Forward, Sidebar and
Rotate left, the bindings of the macOS conventions on `.` and in the find bar, and
`::safepdf::cancelBind`. -/
def smokeKeys (_st : IO.Ref State) (dir : String) : IO Unit := do
  let plat ← platformRef.get
  let mut out : Array String := #[]
  out := out.push s!"platform: {repr plat}"
  let accel (c : Menu.Cmd) : IO String := do
    let some (m, i) := Menu.locate c | return "?"
    run [m, "entrycget", toString i, "-accelerator"]
  out := out.push s!"accel-open: {← accel .openFile}"
  out := out.push s!"accel-save: {← accel .save}"
  out := out.push s!"accel-saveas: {← accel .saveAs}"
  out := out.push s!"accel-quit: {← accel .quit}"
  out := out.push s!"accel-zoomin: {← accel .zoomIn}"
  out := out.push s!"accel-back: {← accel .back}"
  out := out.push s!"accel-pop-copy: {← run [Menu.popPath, "entrycget", "Copy", "-accelerator"]}"
  out := out.push s!"accel-pop-delete: {← run [Menu.popPath, "entrycget", "Delete mark", "-accelerator"]}"
  for seq in ["<Control-Key-s>", "<Command-Key-s>", "<Control-Key-S>", "<Command-Key-S>",
      "<Shift-Command-Key-s>", "<Command-Key-q>", "<Command-Key-plus>"] do
    out := out.push s!"bind {seq}: [{← run ["bind", ".", seq]}]"
  out := out.push s!"bind-find: [{← run ["bind", ".find.e", "<Command-Key-q>"]}]"
  out := out.push s!"primaryBind: [{← run ["info", "body", "::safepdf::primaryBind"]}]"
  out := out.push s!"mac-quit: [{← run ["info", "procs", "::tk::mac::Quit"]}] [{←
    try run ["info", "body", "::tk::mac::Quit"] catch _ => pure ""}]"
  out := out.push s!"save-tip: {← run ["set", "::safepdf::btn(tip,.bar.save)"]}"
  -- Task 10.9: the macOS conventions (labels, bindings, ⌘. in dialogs).
  out := out.push s!"accel-goto: {← accel .gotoPage}"
  out := out.push s!"accel-first: {← accel .firstPage}"
  out := out.push s!"accel-forward: {← accel .forward}"
  out := out.push s!"accel-outline: {← accel .outline}"
  out := out.push s!"accel-rotccw: {← accel .rotateCcw}"
  for seq in ["<Command-Key-g>", "<Command-Key-G>", "<Option-Command-Key-g>", "<Control-Key-g>",
      "<Command-Key-bracketleft>", "<Command-Key-Up>", "<Control-Command-Key-s>",
      "<Command-Key-l>", "<Command-Key-9>"] do
    out := out.push s!"bind {seq}: [{← run ["bind", ".", seq]}]"
  out := out.push s!"bind-find-next: [{← run ["bind", ".find.e", "<Command-Key-g>"]}]"
  out := out.push s!"cancelBind: [{← run ["info", "body", "::safepdf::cancelBind"]}]"
  let mods := if plat == .aqua then "Command" else "Control"
  sendEvent ".c" s!"<{mods}-Key-a>"
  discard <| run ["update"]
  out := out.push s!"status-selectall: {← run [".status", "cget", "-text"]}"
  for (n, _) in Icons.all do
    let img := s!"::safepdf::icon{n}"
    out := out.push s!"icon{n}: {← run ["image", "width", img]}x{← run ["image", "height", img]}"
  discard <| run ["update"]
  -- Tk sets the property on the toplevel's wrapper, the X parent of `winfo id .` (without a
  -- window manager `wm frame .` is the window itself).
  if (← run ["auto_execok", "xprop"]) != "" && (← run ["auto_execok", "xwininfo"]) != "" then
    let r ← try Shim.eval "if {[regexp {Parent window id: (0x[0-9a-f]+)} \
        [exec xwininfo -children -id [winfo id .] 2>/dev/null] -> p]} \
        {exec xprop -id $p -f _NET_WM_ICON 32c -len 64 _NET_WM_ICON 2>/dev/null} else {set p {no wrapper}}"
      catch e => pure s!"error {e}"
    out := out.push s!"net-wm-icon: {r}"
  out := out.push "done"
  IO.FS.writeFile ((dir : System.FilePath) / "keys.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of the save-dialog audit (`SAFEPDF_VIEWER_SMOKE_MODE=savedlg`, task 9.r6) on a
copy of the text PDF alone in its folder `D` (substitute fonts off; files are answered with
`::safepdf::autoPath`, questions with `::safepdf::autoAnswer`):
* the three-way prompt (`::safepdf::choose`, real dialog): Return on the focused default
  gives it, Tab-focus on Cancel + Return gives Cancel (was: the default), Escape Cancel,
  Space on Save As… gives it; the focus goes back to `.c` each time;
* Save As… with a note: the dialog options (`-filetypes` only off aqua) and its folder `D`;
  a 244-character name is written (the temporary name is cut); a dotted name without `.pdf`
  gets `.pdf`; one that then names an existing file asks (answered No: untouched); a
  read-only file, a folder and a file in a read-only folder are refused with their reason,
  the title keeps `* ` and Save stays enabled; a name with spaces, Tcl metacharacters,
  quotes and non-ASCII is written and shown in the title;
* Export annotations…: the opened PDF chosen writes `NAME.pdf.xfdf` beside it (the PDF
  unchanged; was: the PDF replaced by XML), a name without `.xfdf` gets it;
* the opened file deleted behind the viewer's back: Save asks with the "no longer there"
  question (Cancel) and creates nothing.
Results in `savedlg.txt`; the shell checks them and that no temporary file is left. -/
def smokeSaveDialogs (st : IO.Ref State) (dir : String) : IO Unit := do
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let orig := (← st.get).path.getD ""
  let d := dirOf orig
  let file (name : String) : String := ((d : System.FilePath) / name).toString
  discard <| run ["set", "::safepdf::autoAnswer", ""]
  -- 1. The three-way prompt from the keyboard.
  let chooseWith (keys : String) : IO String := do
    discard <| run ["focus", "-force", ".c"]
    discard <| run ["update"]
    -- Generated keys go to the focus (forced: no window manager); a dialog that ignores them
    -- answers `timeout` after 3 s instead of hanging the run.
    discard <| run ["after", "400", keys]
    discard <| run ["after", "3000", "set ::safepdf::chooseAnswer timeout"]
    let a ← run ["::safepdf::choose", "Save", "Save 1 mark?", "overwrite", "cancel",
      "overwrite", "Overwrite", "saveas", "Save As…", "cancel", "Cancel"]
    discard <| run ["update"]
    discard <| run ["after", "cancel", "set ::safepdf::chooseAnswer timeout"]
    return s!"{a} {← run ["focus"]}"
  let b := ".choose.f.b"
  out := out.push s!"choose-return: {← chooseWith s!"focus -force {b}.overwrite; update; event generate {b}.overwrite <Key-Return>"}"
  out := out.push s!"choose-tab-cancel: {← chooseWith s!"focus -force {b}.cancel; update; event generate {b}.cancel <Key-Return>"}"
  out := out.push s!"choose-escape: {← chooseWith s!"focus -force {b}.overwrite; update; event generate {b}.overwrite <Key-Escape>"}"
  out := out.push s!"choose-space: {← chooseWith s!"focus -force {b}.saveas; update; event generate {b}.saveas <Key-space>"}"
  -- 2. Save As… cases.
  smokeNoteAt st 300 400 "dialog audit"
  let saveAsTo (p : String) : IO String := do
    discard <| run ["set", "::safepdf::autoPath", p]
    discard <| run ["set", "::safepdf::lastAsk", ""]
    discard <| run [".menubar.file", "invoke", Menu.Cmd.saveAs.label]
    discard <| run ["set", "::safepdf::autoPath", ""]
    k.status
  let long := String.ofList (List.replicate 240 'L') ++ ".pdf"
  let st1 ← saveAsTo (file long)
  let dlg ← run ["set", "::safepdf::lastDialog"]
  out := out.push s!"dialog-dir: {(← run ["lindex", dlg, "0"]) == d} {← run ["lindex", dlg, "1"]}"
  out := out.push s!"dialog-filetypes: {(dlg.splitOn "-filetypes").length == 2} {(← onAqua)} {(dlg.splitOn "-defaultextension .pdf").length == 2}"
  out := out.push s!"long-name: {st1.startsWith "saved"} {decide ((← k.size (file long)) > 0)}"
  smokeNoteAt st 300 400 "dialog audit 2"
  let st2 ← saveAsTo (file "3453483.3454032-final")
  out := out.push s!"dotted-name: {st2.startsWith "saved"} {decide ((← k.size (file "3453483.3454032-final.pdf")) > 0)} {(← k.size (file "3453483.3454032-final")) == 0}"
  smokeNoteAt st 300 400 "dialog audit 3"
  IO.FS.writeFile (file "exists.pdf") "keep me\n"
  discard <| run ["set", "::safepdf::autoAnswer", "no"]
  let st3 ← saveAsTo (file "exists")
  discard <| run ["set", "::safepdf::autoAnswer", ""]
  out := out.push s!"ext-exists: {st3 == "save cancelled"} {(← k.lastAsk) == Save.replaceQuestion "exists.pdf"} {(← IO.FS.readFile (file "exists.pdf")) == "keep me\n"}"
  IO.FS.writeFile (file "ro.pdf") "read-only\n"
  discard <| run ["file", "attributes", file "ro.pdf", "-permissions", "0444"]
  let st4 ← saveAsTo (file "ro.pdf")
  out := out.push s!"read-only: {st4.startsWith "cannot save: ro.pdf is read-only"} {(← IO.FS.readFile (file "ro.pdf")) == "read-only\n"}"
  IO.FS.createDirAll (file "folder.pdf")
  let st5 ← saveAsTo (file "folder.pdf")
  out := out.push s!"folder: {st5.startsWith "cannot save: folder.pdf is a folder"}"
  IO.FS.createDirAll (file "rodir")
  discard <| run ["file", "attributes", file "rodir", "-permissions", "0555"]
  let st6 ← saveAsTo (file "rodir/x.pdf")
  discard <| run ["file", "attributes", file "rodir", "-permissions", "0755"]
  out := out.push s!"ro-folder: {st6.startsWith "cannot save: the folder of x.pdf is not writable"} {(← k.size (file "rodir/x.pdf")) == 0}"
  out := out.push s!"refused-state: {(← st.get).marks.dirty} {← k.star} {← k.menuState .save}"
  let weird := "we ird $x [exit 3] {b} \"q\" ü ✓.pdf"
  let st7 ← saveAsTo (file weird)
  out := out.push s!"weird-name: {st7.startsWith "saved"} {decide ((← k.size (file weird)) > 0)} {(← run ["wm", "title", "."]).startsWith weird} {(← st.get).marks.dirty}"
  -- 3. Export annotations….
  let pdf := (← st.get).path.getD ""
  let pdfBytes ← IO.FS.readBinFile pdf
  discard <| run ["set", "::safepdf::autoPath", pdf]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.exportXfdf.label]
  out := out.push s!"export-onto-pdf: {(← k.status).startsWith "exported"} {(← IO.FS.readBinFile pdf).data == pdfBytes.data} {decide ((← k.size (pdf ++ ".xfdf")) > 0)}"
  discard <| run ["set", "::safepdf::autoPath", file "notes"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.exportXfdf.label]
  discard <| run ["set", "::safepdf::autoPath", ""]
  let xd ← run ["set", "::safepdf::lastDialog"]
  out := out.push s!"export-ext: {(← k.status).startsWith "exported"} {decide ((← k.size (file "notes.xfdf")) > 0)} {(xd.splitOn "-filetypes").length == 2} {(← run ["lindex", xd, "1"])}"
  -- 4. The opened file vanished: Save asks, nothing is created.
  smokeNoteAt st 300 400 "vanished"
  IO.FS.removeFile pdf
  discard <| run ["set", "::safepdf::autoAnswer", "cancel"]
  discard <| run ["set", "::safepdf::lastAsk", ""]
  sendEvent ".c" "<Control-Key-s>"
  out := out.push s!"vanished: {(← k.lastAsk).startsWith s!"{weird} is no longer there"} {!(← System.FilePath.pathExists pdf)} {(← st.get).marks.dirty}"
  out := out.push "done"
  IO.FS.writeFile ((dir : System.FilePath) / "savedlg.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["set", "::safepdf::autoAnswer", "dontsave"]
  discard <| run ["destroy", "."]

/-- Smoke steps of the Tcl lockdown (`SAFEPDF_VIEWER_SMOKE_MODE=lockdown`, task 8.7), run by
`scripts/viewer-smoke.sh` with `HOME` holding a hostile `~/.Xdefaults` (script-valued
resources that would create the file `pwned`) and, on the same display, a second Tk
interpreter that tries `send` into the viewer. Step 0 records whether the `send` command
exists, the registered interpreters and the options the resources target (on the page field,
the overflow menu, the main window and freshly created probe widgets), exercises them
(typing into the page field, posting the menu, keyboard traversal) and writes `up`; the next
steps wait (at most 20 s) for the other interpreter's `attacked` file, then write
`lockdown.txt` and close the window. With `SAFEPDF_VIEWER_DRIVE=1` step 0 also renames the
application to a unique name and records it (`appname`, task 10.19). -/
def smokeLockdown (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : System.FilePath := (dir : System.FilePath) / name
  let s ← st.get
  st.modify ({ · with smokeStep := s.smokeStep + 1 })
  if s.smokeStep == 0 then
    discard <| run ["update"]
    let get (w o : String) : IO String := do
      try return s!"[{← run [w, "cget", o]}]" catch e => return s!"error {e}"
    -- Task 10.19: with the drive hook the viewer takes a unique application name and reports
    -- it, so the control run targets exactly this viewer, not a guessed `tk` (on Aqua
    -- `winfo interps` also lists stale and foreign interpreters). Without the hook nothing
    -- registers: `tk appname NAME` would undo `sendOffScript`.
    let mut out : Array String := #[]
    if (← IO.getEnv "SAFEPDF_VIEWER_DRIVE") == some "1" then
      discard <| run ["tk", "appname", s!"safepdf-lock-{← IO.Process.getPID}"]
      out := out.push s!"appname: {← run ["tk", "appname"]}"
    out := out.push s!"send-command: [{← run ["info", "commands", "::send"]}]"
    out := out.push s!"interps: [{← try run ["winfo", "interps"] catch e => pure s!"error {e}"}]"
    out := out.push s!"pg-validate: {← get ".bar.pg.e" "-validate"} {← get ".bar.pg.e" "-validatecommand"}"
    out := out.push s!"more-postcommand: {← get ".more" "-postcommand"}"
    out := out.push s!"root-takefocus: {← get "." "-takefocus"}"
    discard <| run ["entry", ".lockE"]
    discard <| run ["menu", ".lockM"]
    discard <| run ["toplevel", ".lockT"]
    out := out.push s!"probe-entry: {← get ".lockE" "-validate"} {← get ".lockE" "-validatecommand"} {← get ".lockE" "-textvariable"} {← get ".lockE" "-takefocus"}"
    out := out.push s!"probe-menu: {← get ".lockM" "-postcommand"} {← get ".lockM" "-tearoffcommand"}"
    out := out.push s!"probe-toplevel: {← get ".lockT" "-use"} {← get ".lockT" "-screen"} {← get ".lockT" "-container"}"
    -- Exercise what the resources would hook: validation, posting, traversal.
    discard <| run [".bar.pg.e", "insert", "end", "1"]
    discard <| run [".lockE", "insert", "end", "1"]
    discard <| run [".lockM", "post", "0", "0"]
    discard <| run [".lockM", "unpost"]
    discard <| run ["tk_focusNext", "."]
    discard <| run ["tk_focusNext", ".lockE"]
    discard <| run ["destroy", ".lockE", ".lockM", ".lockT"]
    discard <| run ["update"]
    IO.FS.writeFile (file "lockdown.txt") ("\n".intercalate out.toList ++ "\n")
    IO.FS.writeFile (file "up") ""
    discard <| run ["after", "250", "::safepdf::emit smoke"]
  else if (← (file "attacked").pathExists) || s.smokeStep > 80 then
    let old ← IO.FS.readFile (file "lockdown.txt")
    IO.FS.writeFile (file "lockdown.txt") (old ++ s!"attacked-file: {← (file "attacked").pathExists}\ndone\n")
    discard <| run ["destroy", "."]
  else
    discard <| run ["after", "250", "::safepdf::emit smoke"]

/-- Smoke steps of bib-lean's reader mode (`SAFEPDF_VIEWER_SMOKE_MODE=biblean`, task 10.1b;
run by `Tests/biblean/window-test.sh` and `annots-test.sh` under `viewer --biblean`), in three
event-loop turns 1.5 s apart so the library sync (400 ms debounce) runs in between:
step 0 records the window (title, page, marks, Save's label and tooltip, whether the document
is in memory) and writes `up` (the test looks at the process while the window is up), then
highlights the first word of the shown page (`highlight`, nothing saved); step 1 adds a note
next to it (context menu) and presses Ctrl+S at once (Save to library), recording the state
after; step 2 writes `biblean.txt` and closes the window. -/
def smokeBiblean (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : System.FilePath := (dir : System.FilePath) / name
  let s ← st.get
  st.modify ({ · with smokeStep := s.smokeStep + 1 })
  let next : IO Unit := discard <| run ["after", "1500", "::safepdf::emit smoke"]
  let marksLine (s : State) : String :=
    s!"{s.marks.marks.size} saved {s.marks.saved.length} dirty {s.marks.dirty}"
  let append (l : String) : IO Unit := do
    let old ← try IO.FS.readFile (file "biblean.txt") catch _ => pure ""
    IO.FS.writeFile (file "biblean.txt") (old ++ l ++ "\n")
  match s.smokeStep with
  | 0 =>
    discard <| run ["update"]
    let lbl ← match Menu.locate .save with
      | some (m, i) => run [m, "entrycget", toString i, "-label"]
      | none => pure "?"
    append s!"title: {← run ["wm", "title", "."]}"
    append s!"page: {s.page + 1}/{s.pageCount}"
    append s!"in-memory: {s.inMemory} library: {s.library.isSome}"
    append s!"marks0: {marksLine s}"
    append s!"save-label: {lbl} | {← run ["set", "::safepdf::btn(tip,.bar.save)"]}"
    IO.FS.writeFile (file "up") ""
    let .ok ix ← pageIndex st s.page | throw (IO.userError "no text index")
    let (a, b) := Select.wordAt ix.cells 0
    st.modify ({ · with sel := some (s.page, a, b) })
    highlight st none
    let s1 ← st.get
    append s!"highlighted: {Select.rangeText ix.cells a b} {marksLine s1}"
    next
  | 1 =>
    let some m := s.markSel.bind s.marks.find? | throw (IO.userError "no selected highlight")
    let some q := m.quads.head? | throw (IO.userError "highlight without quads")
    smokeNoteAt st (q.urx + 40) ((q.lly + q.ury) / 2) "library note"
    append s!"noted: {marksLine (← st.get)}"
    sendEvent ".c" "<Control-Key-s>"
    let s2 ← st.get
    append s!"after-save: {marksLine s2} title {s2.title}"
    append s!"after-save-path: {s2.path.getD "-"} in-memory {s2.inMemory} library {s2.library.isSome} page {s2.page + 1}"
    append s!"status: {← run [".status", "cget", "-text"]}"
    next
  | _ =>
    append "done"
    discard <| run ["destroy", "."]

/-- Free text or ink of a mark as `key: value` text for the smoke files (task 9.9). -/
def editorDesc (m : Option Marks.Mark) : String :=
  match (m.map (·.kind) : Option Marks.Kind) with
  | some (.freeText t p z c) => s!"text {t} {num p.x} {num p.y} {z} {Marks.rgbHex c}"
  | some (.ink ss w o c) => s!"ink {ss.length} {ss.map List.length} {w} {o} {Marks.rgbHex c}"
  | _ => "none"

/-- Smoke steps of Add text and Draw (`SAFEPDF_VIEWER_SMOKE_MODE=editors`, task 9.9) on a copy
of the text PDF (substitute fonts on, so the saved free text is painted): the toolbar's Add
text turns the mode on with its pop-over; a click at (100, 400) opens a text box, typed text
and Escape make a free-text mark (canvas text items); a double click edits it (a click
elsewhere commits); the pop-over's red swatch and size slider (20) change it; Draw: blue,
thickness 4, two strokes form one drawing (two canvas lines); Ctrl+S (Overwrite) writes into
the opened file and reopens it (both read back, the text box's pixels dark, the stroke blue, drawn by the
renderer); dragging the text box moves it by 50 units (saved, read back moved); Delete removes
the text box and the drawing's bubble Delete the drawing; Ctrl+S leaves none in the file and
white paper. Results in `editors.txt` (boxes for the external `mutool` check of
`editors1.pdf`, the file with both). -/
def smokeEditors (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let winAt (x y : Rat) : IO (String × String) := do
    let some pos ← boxWindowPos st ⟨x, y, x, y⟩ | throw (IO.userError "page not shown")
    return pos
  let press (w : String × String) : IO Unit :=
    sendEvent ".c" "<ButtonPress-1>" ["-x", w.1, "-y", w.2]
  let release (w : String × String) : IO Unit :=
    sendEvent ".c" "<ButtonRelease-1>" ["-x", w.1, "-y", w.2]
  let motion (w : String × String) : IO Unit :=
    sendEvent ".c" "<Motion>" ["-x", w.1, "-y", w.2, "-state", "256"]
  let btn (w : String) : IO Unit := do
    sendEvent w "<ButtonPress-1>" ["-x", "16", "-y", "16"]
    sendEvent w "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
  let edAt (x y : Rat) : IO Unit := do
    sendEvent ".edbar" "<ButtonPress-1>" ["-x", toString x.floor, "-y", toString y.floor]
    sendEvent ".edbar" "<ButtonRelease-1>" ["-x", toString x.floor, "-y", toString y.floor]
  let firstOf (pred : Marks.Mark → Bool) : IO (Option Marks.Mark) := do
    return (← st.get).marks.marks.toList.find? pred
  -- Non-white pixels among 9 × 3 points inside a box (page space).
  let inked (b : Box) : IO Nat := do
    let mut n := 0
    for i in [1:10] do
      for j in [1:4] do
        let q : Pt := ⟨b.llx + (b.urx - b.llx) * i / 10, b.lly + (b.ury - b.lly) * j / 4⟩
        let cs := ((← k.px q).splitOn " ").filterMap String.toNat?
        if cs.length == 3 && cs.any (· < 200) then n := n + 1
    return n
  -- 1. Add text: mode, pop-over, a text box.
  btn ".bar.text"
  discard <| run ["update"]
  out := out.push s!"text-mode: {(← st.get).ui.editor == .text} {← run ["winfo", "ismapped", ".edbar"]} {← run ["::safepdf::btnState", ".bar.text"]}"
  let p1 ← winAt 100 400
  press p1; release p1
  out := out.push s!"editor-open: {← run ["winfo", "exists", ".c.ft"]} {(← st.get).ftEdit.isSome}"
  discard <| run [".c.ft", "insert", "end", "Hello text"]
  discard <| run ["update"]
  sendEvent ".c.ft" "<Key-Escape>"
  let ft ← firstOf isFt
  out := out.push s!"text-added: {(← st.get).marks.marks.size} {editorDesc ft} {← tagCount "ft"} {← run ["winfo", "exists", ".c.ft"]}"
  let some ftm := ft | throw (IO.userError s!"no text box; {out}; status: {← k.status}")
  let some fbox := ftm.box | throw (IO.userError "no text box box")
  -- 2. A double click edits it; a click elsewhere commits.
  discard <| run ["after", "600"]
  let inside ← winAt (fbox.llx + 6) ((fbox.lly + fbox.ury) / 2)
  press inside; release inside; press inside; release inside
  discard <| run ["update"]
  let shown ← try run [".c.ft", "get", "1.0", "end - 1 chars"] catch _ => pure "<none>"
  out := out.push s!"edit-open: {shown == "Hello text"}"
  if shown != "Hello text" then
    throw (IO.userError s!"no editor; {out}; status: {← k.status}")
  discard <| run [".c.ft", "delete", "1.0", "end"]
  discard <| run [".c.ft", "insert", "end", "Edited text ✓"]
  let away ← winAt 400 150
  press away; release away
  out := out.push s!"text-edited: {editorDesc (← firstOf isFt)} {(← st.get).markSel == some ftm.id}"
  -- 3. Colour and size from the pop-over (applied to the selected text box).
  edAt (Bubble.EdPop.swatchX 1) (Bubble.EdPop.ctrlY 0)
  edAt (Bubble.EdPop.fontSize.thumbX 20) (Bubble.EdPop.ctrlY 1)
  out := out.push s!"text-styled: {editorDesc (← firstOf isFt)} {(← st.get).ui.ftSize}"
  -- 4. Draw: blue, thickness 4, two strokes = one drawing.
  btn ".bar.draw"
  out := out.push s!"draw-mode: {(← st.get).ui.editor == .draw} {← run ["winfo", "ismapped", ".edbar"]} {← run ["::safepdf::btnState", ".bar.text"]}"
  edAt (Bubble.EdPop.swatchX 2) (Bubble.EdPop.ctrlY 0)
  edAt (Bubble.EdPop.thickness.thumbX 4) (Bubble.EdPop.ctrlY 1)
  for (y, xs) in [((300 : Rat), [(300 : Rat), 330, 360, 390, 420]), (250, [300, 340, 380, 420])] do
    let ws ← xs.mapM fun x => winAt x (y + (x - 300) / 4)
    if let some w0 := ws.head? then press w0
    for w in ws.drop 1 do motion w
    if let some wl := ws.getLast? then release wl
  let ink ← firstOf isInk
  out := out.push s!"drawn: {(← st.get).marks.marks.size} {editorDesc ink} {← tagCount "ink"}"
  sendKey "Escape"
  btn ".bar.draw"
  out := out.push s!"modes-off: {(← st.get).ui.editor == .none} {← run ["winfo", "ismapped", ".edbar"]}"
  -- 5. Save (into the opened file, answered Overwrite; reopened): both read back, painted by
  -- the renderer.
  discard <| run ["set", "::safepdf::autoAnswer", "overwrite"]
  sendEvent ".c" "<Control-Key-s>"
  let s1 ← st.get
  let path := s1.path.getD ""
  out := out.push s!"saved: {s1.marks.marks.size} {s1.marks.saved.length} {s1.marks.dirty} {← fileMarks path}"
  let ft1 ← firstOf isFt
  let ink1 ← firstOf isInk
  out := out.push s!"after-save-text: {editorDesc ft1}"
  out := out.push s!"after-save-ink: {editorDesc ink1}"
  out := out.push s!"canvas-after-save: {← tagCount "ft"} {← tagCount "ink"}"
  let some tb := ft1.bind (·.box) | throw (IO.userError "text box lost")
  out := out.push s!"text-box: {num tb.llx} {num tb.lly} {num tb.urx} {num tb.ury}"
  out := out.push s!"text-pixels: {decide ((← inked tb) > 3)}"
  let mid : Pt := ⟨345, 300 + 45 / 4⟩
  out := out.push s!"ink-mid: {num mid.x} {num mid.y}"
  out := out.push s!"ink-px: {← k.px mid}"
  out := out.push s!"subst: {(← SafePdf.Shell.Fonts.findFiles).any (·.1 == .helvetica)}"
  IO.FS.writeBinFile (file "editors1.pdf") (← IO.FS.readBinFile path)
  -- 6. Move the text box 50 units right by dragging it; save; read back moved.
  discard <| run ["after", "600"]
  let a ← winAt (tb.llx + 6) ((tb.lly + tb.ury) / 2)
  let b ← winAt (tb.llx + 31) ((tb.lly + tb.ury) / 2)
  let c ← winAt (tb.llx + 56) ((tb.lly + tb.ury) / 2)
  press a; motion b; motion c; release c
  let ftMoved ← firstOf isFt
  let dx := match ft1.map (·.kind), ftMoved.map (·.kind) with
    | some (.freeText _ p _ _), some (.freeText _ q _ _) => q.x - p.x
    | _, _ => 0
  out := out.push s!"moved: {decide (dx > 48 && dx < 52)} {(← st.get).marks.dirty}"
  sendEvent ".c" "<Control-Key-s>"
  let ftSaved ← firstOf isFt
  let dx2 := match ft1.map (·.kind), ftSaved.map (·.kind) with
    | some (.freeText _ p _ _), some (.freeText _ q _ _) => q.x - p.x
    | _, _ => 0
  out := out.push s!"moved-saved: {decide (dx2 > 48 && dx2 < 52)} {(← st.get).marks.dirty} {← fileMarks path}"
  -- 7. Delete each: the text box with Delete, the drawing with its bubble's Delete.
  discard <| run ["after", "600"]
  let some tb2 := ftSaved.bind (·.box) | throw (IO.userError "moved text box lost")
  let t2 ← winAt (tb2.llx + 6) ((tb2.lly + tb2.ury) / 2)
  press t2; release t2
  out := out.push s!"text-selected: {(← st.get).markSel == ftSaved.map (·.id)} {(← st.get).bubble.map (·.1 == .editor)}"
  sendKey "Delete"
  discard <| run ["after", "600"]
  let m2 ← winAt mid.x mid.y
  press m2; release m2
  let bub := (← st.get).bubble
  out := out.push s!"ink-selected: {(← st.get).markSel == ink1.map (·.id)} {bub.map (·.1 == .editor)}"
  if let some (kd, r) := bub then
    if let some (_, x0, x1) := kd.layout.find? (·.1 == .delete) then
      let vx := (View.parseDecimal (← run [".c", "canvasx", "0"])).getD 0
      let vy := (View.parseDecimal (← run [".c", "canvasy", "0"])).getD 0
      let w := (toString (r.x0 + (x0 + x1) / 2 - vx).floor, toString ((r.y0 + r.y1) / 2 - vy).floor)
      press w; release w
      discard <| run ["update"]
  out := out.push s!"deleted: {(← st.get).marks.marks.size} {(← st.get).marks.dirty} {(← st.get).view.isSome}"
  sendEvent ".c" "<Control-Key-s>"
  out := out.push s!"deleted-saved: {(← st.get).marks.marks.size} {(← st.get).marks.dirty} {← fileMarks path}"
  out := out.push s!"after-delete-pixels: {← inked tb2} {← k.px mid}"
  IO.FS.writeFile (file "editors.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- The screenshot set-up of task 9.9 (`SAFEPDF_VIEWER_SMOKE_MODE=editors-shot`): a red text
box and a blue drawing on the page, the Draw mode on with its pop-over open; writes
`ready.txt` and stays up for 20 s (the caller takes the screenshot), then closes. -/
def smokeEditorsShot (st : IO.Ref State) (dir : String) : IO Unit := do
  discard <| run ["update"]
  let winAt (x y : Rat) : IO (String × String) := do
    let some pos ← boxWindowPos st ⟨x, y, x, y⟩ | throw (IO.userError "page not shown")
    return pos
  let ev (w : String) (pat : String) (p : String × String) (more : List String := []) : IO Unit :=
    sendEvent w pat (["-x", p.1, "-y", p.2] ++ more)
  let btn (w : String) : IO Unit := do
    ev w "<ButtonPress-1>" ("16", "16"); ev w "<ButtonRelease-1>" ("16", "16")
  let edAt (x y : Rat) : IO Unit := do
    let p := (toString x.floor, toString y.floor)
    ev ".edbar" "<ButtonPress-1>" p; ev ".edbar" "<ButtonRelease-1>" p
  btn ".bar.text"
  discard <| run ["update"]
  edAt (Bubble.EdPop.swatchX 1) (Bubble.EdPop.ctrlY 0)
  edAt (Bubble.EdPop.fontSize.thumbX 16) (Bubble.EdPop.ctrlY 1)
  let p ← winAt 150 786
  ev ".c" "<ButtonPress-1>" p; ev ".c" "<ButtonRelease-1>" p
  discard <| run [".c.ft", "insert", "end", "Add text: a FreeText box"]
  discard <| run ["update"]
  sendEvent ".c.ft" "<Key-Escape>"
  btn ".bar.draw"
  discard <| run ["update"]
  edAt (Bubble.EdPop.swatchX 2) (Bubble.EdPop.ctrlY 0)
  edAt (Bubble.EdPop.thickness.thumbX 3) (Bubble.EdPop.ctrlY 1)
  let curve (cx cy : Rat) : List (Rat × Rat) :=
    (List.range 25).map fun (i : Nat) =>
      let t : Rat := (i : Rat) / 24
      (cx + 70 * t, cy + 40 * (4 * t * (1 - t)) - 20 * t)
  for (cx, cy) in [((515 : Rat), (520 : Rat)), (515, 495)] do
    let ws ← (curve cx cy).mapM fun (x, y) => winAt x y
    if let some w0 := ws.head? then ev ".c" "<ButtonPress-1>" w0
    for w in ws.drop 1 do ev ".c" "<Motion>" w ["-state", "256"]
    if let some wl := ws.getLast? then ev ".c" "<ButtonRelease-1>" wl
  discard <| run ["update"]
  IO.FS.writeFile ((dir : System.FilePath) / "ready.txt") "ready\n"
  discard <| run ["after", "20000", "destroy ."]

/-! ### The consolidated Phase 9 / M9 smoke run (task 9.6) -/

/-- `R G B` text as numbers. -/
def m9Rgb (s : String) : Option (Nat × Nat × Nat) :=
  match (s.splitOn " ").filterMap String.toNat? with
  | [r, g, b] => some (r, g, b)
  | _ => none

/-- A highlight's or note's yellow (`#FFFF98` multiplied over paper, or the note's fill). -/
def m9Yellow (c : Nat × Nat × Nat) : Bool := c.1 > 200 && c.2.1 > 200 && c.2.2 < 200

/-- The red of the M9 free text (`#D70022`). -/
def m9Red (c : Nat × Nat × Nat) : Bool := c.1 > 150 && c.2.1 < 90 && c.2.2 < 110

/-- The blue of the M9 drawing (`#0000FF`-ish, PDF.js blue). -/
def m9Blue (c : Nat × Nat × Nat) : Bool := c.2.2 > 150 && c.1 < 100

/-- How many of the points `ps` (page space, shown page) have a pixel satisfying `pred`. -/
def m9CountAt (k : SaveKit) (ps : List Pt) (pred : Nat × Nat × Nat → Bool) : IO Nat := do
  let mut n := 0
  for q in ps do
    if let some c := m9Rgb (← k.px q) then
      if pred c then n := n + 1
  return n

/-- A 12 × 6 grid of points inside a box. -/
def m9Grid (b : Box) : List Pt :=
  (List.range 12).flatMap fun (i : Nat) => (List.range 6).map fun (j : Nat) =>
    (⟨b.llx + (b.urx - b.llx) * ((i : Rat) + 1) / 13,
      b.lly + (b.ury - b.lly) * ((j : Rat) + 1) / 7⟩ : Pt)

/-- The coloured pixels of each of the marks `ms` on the shown page, summed per kind:
`hl=… note=… text=… ink=…` (highlights and notes yellow, the free text red, the drawing blue). -/
def m9Pixels (st : IO.Ref State) (ms : List Marks.Mark) : IO String := do
  let k := saveKit st
  let s ← st.get
  let some bx := shownBox s | return "no page"
  let mut hl := 0
  let mut note := 0
  let mut text := 0
  let mut ink := 0
  for m in ms do
    match m.kind with
    | .highlight qs =>
      hl := hl + (← m9CountAt k (qs.flatMap m9Grid) m9Yellow)
    | .note .. =>
      if let some ib := m.iconBox bx then note := note + (← m9CountAt k (m9Grid ib) m9Yellow)
    | .freeText .. =>
      if let some b := m.box then text := text + (← m9CountAt k (m9Grid b) m9Red)
    | .ink ss .. =>
      ink := ink + (← m9CountAt k ss.flatten m9Blue)
  return s!"hl={hl} note={note} text={text} ink={ink}"

/-- A mark as a rounded, order-free description (kind, colour, text, rounded geometry), to
compare marks across save, reopen and an XFDF round trip. -/
def m9Desc (m : Marks.Mark) : String :=
  let r (x : Rat) : String := toString x.floor
  match m.kind with
  | .highlight qs => s!"highlight {m.page} {m.color.name} {qs.length}"
  | .note t _ => s!"note {m.page} {m.color.name} {t}"
  | .freeText t p z c => s!"text {m.page} {t} {r p.x} {r p.y} {z} {Marks.rgbHex c}"
  | .ink ss w o c => s!"ink {m.page} {ss.length} {ss.map List.length} {w} {o} {Marks.rgbHex c}"

/-- Every mark of the store, described (`m9Desc`), sorted, joined by ` | `. -/
def m9Marks (st : IO.Ref State) : IO String := do
  let ds := (← st.get).marks.marks.toList.map m9Desc
  return " | ".intercalate (ds.toArray.qsort (· < ·)).toList

/-- Page-space boxes of the marks for the script's `mutool` check: one `kind llx lly urx ury`
per mark (a note's icon box; a drawing's bounding box). -/
def m9Boxes (st : IO.Ref State) : IO String := do
  let s ← st.get
  let some bx := shownBox s | return ""
  let f (b : Box) : String := s!"{num b.llx} {num b.lly} {num b.urx} {num b.ury}"
  let parts := s.marks.marks.toList.filterMap fun m =>
    match m.kind with
    | .highlight qs => qs.head?.map fun b => s!"hl {f b}"
    | .note .. => (m.iconBox bx).map fun b => s!"note {f b}"
    | .freeText .. => m.box.map fun b => s!"text {f b}"
    | .ink .. => m.box.map fun b => s!"ink {f b}"
  return ";".intercalate parts

/-- Scrolls the whole document from its first page with generated wheel notches only, in the
current view mode, until the view shows the bottom of the last spread (task 9.6, M9 "a paper
reads end to end with the wheel"). Returns a `key: value` line: the 1-based spreads the current
page passed through, the spread count, notches, whether (spread, view top) never went back,
the page field and whether it names a page of the last spread, the final `yview`. -/
def m9WheelThrough (st : IO.Ref State) (label : String) : IO String := do
  sendKey "Home"
  settle st
  let s0 ← st.get
  let n := s0.pageCount
  let sp := s0.spread
  let lastK := View.spreadOf sp (n - 1)
  let top : IO Rat := do return ((viewFracs (← run [".c", "yview"])).map (·.1)).getD 0
  let bottomOk : IO Bool := do return ((viewFracs (← run [".c", "yview"])).map (fun f => decide (f.2 ≥ 1))).getD false
  let mut seen : Array Nat := #[View.spreadOf sp s0.page]
  let mut notches := 0
  let mut monotone := true
  let mut stuck := 0
  let mut k0 := View.spreadOf sp s0.page
  let mut t0 ← top
  for _ in [0:80 * n + 100] do
    if k0 == lastK && (← bottomOk) then break
    sendEvent ".c" "<MouseWheel>" ["-delta", "-120", "-x", "300", "-y", "300"]
    notches := notches + 1
    settle st
    let k1 := View.spreadOf sp (← st.get).page
    let t1 ← top
    if k1 < k0 || (k1 == k0 && t1 < t0) || (s0.scroll == .vertical && t1 < t0) then
      monotone := false
    if k1 == k0 && t1 == t0 then stuck := stuck + 1 else stuck := 0
    if stuck ≥ 3 then break
    if seen.back? != some k1 then seen := seen.push k1
    k0 := k1
    t0 := t1
  let s ← st.get
  let field ← run ["set", "::safepdf::pageText"]
  let fieldOk := field == Toolbar.entryText s.labels s.page &&
    (View.spreadPages sp n lastK).contains s.page
  return s!"wheel-{label}: seen={",".intercalate (seen.toList.map (toString ∘ (· + 1)))} \
    spreads={View.spreadCount sp n} notches={notches} monotone={monotone} field={field} \
    last={fieldOk} bottom={← bottomOk}"

/-- **The consolidated Phase 9 smoke run** (`SAFEPDF_VIEWER_SMOKE_MODE=m9`, task 9.6), on any
document with text on page 1 (the generated fixtures and real corpus papers): the menubar
(every command at its place with its label); the toolbar page box (Enter on the last page,
text reverts, back to 1), its arrows and the zoom drop-down (Page Width, Page Fit, Automatic
Zoom); the wheel alone through the whole document in each of the four view modes (single page,
continuous, facing, continuous facing; `m9WheelThrough`); then, at Page Fit on page 1: a drag
over the first word of five letters or more, the float bubble's Highlight; a note in the top
right corner; an Add text box (red, size 16) and a Draw drawing (blue, thickness 4, two strokes)
near the bottom; Ctrl+S (`FILE-annotated.pdf`, reopened), File → Close, reopened from disk
(`openFile`): the four marks restored equal (`m9Desc`) and drawn by the renderer (`m9Pixels`);
File → Export annotations… (`m9.xfdf`), every mark deleted (no coloured pixels left), the file
imported again (the same four marks). Results in `m9.txt`; the window is closed without saving
the import. -/
def smokeM9 (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let s0 ← st.get
  let n := s0.pageCount
  out := out.push s!"pages: {n}"
  out := out.push s!"outline: {!s0.outline.isEmpty} {s0.outlineShown}"
  -- 1. Menubar: attached, four menus, every command at its place with its label.
  out := out.push s!"menubar: {← run [".", "cget", "-menu"]}"
  let mut menus : Array String := #[]
  let mn := (← run [".menubar", "index", "end"]).toNat?.getD 0
  for i in [0:mn + 1] do menus := menus.push (← run [".menubar", "entrycget", toString i, "-label"])
  out := out.push s!"menus: {",".intercalate menus.toList}"
  let mut bad : Array String := #[]
  for c in Menu.Cmd.all do
    match Menu.locate c with
    | some (m, i) =>
      let l ← try run [m, "entrycget", toString i, "-label"] catch _ => pure "?"
      if l != c.label then bad := bad.push c.label
    | none => bad := bad.push c.label
  out := out.push s!"menu-entries: {Menu.Cmd.all.length} bad={",".intercalate bad.toList}"
  -- 2. Toolbar: page box, arrows, zoom drop-down.
  let page : IO Nat := return (← st.get).page + 1
  let field : IO String := run ["set", "::safepdf::pageText"]
  let enter (txt : String) : IO Unit := do
    sendEvent ".bar.pg.e" "<FocusIn>"
    discard <| run ["set", "::safepdf::pageText", txt]
    sendEvent ".bar.pg.e" "<Key-Return>"
    settle st
  let click (w : String) : IO Unit := do
    sendEvent w "<ButtonPress-1>" ["-x", "16", "-y", "16"]
    sendEvent w "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
    settle st
  enter (Toolbar.entryText s0.labels (n - 1))
  out := out.push s!"pagebox-last: {← page} {← field} {← run [".bar.of", "cget", "-text"]}"
  enter "abc"
  out := out.push s!"pagebox-abc: {← page} {← field}"
  enter (Toolbar.entryText s0.labels 0)
  out := out.push s!"pagebox-first: {← page} {← field}"
  click ".bar.next"
  out := out.push s!"arrow-next: {← page}"
  click ".bar.prev"
  out := out.push s!"arrow-prev: {← page}"
  let zoomNow : IO String := do
    let s ← st.get
    return s!"{← run [".bar.zoom", "itemcget", "label", "-text"]}|{View.zoomPct s.shownZoom s.scaling}"
  let choose (lbl : String) : IO Unit := do
    discard <| run [".zoommenu", "invoke", lbl]
    settle st
  choose "Page Width"
  out := out.push s!"zoom-width: {← zoomNow}"
  choose "Page Fit"
  out := out.push s!"zoom-fit: {← zoomNow}"
  choose "Automatic Zoom"
  out := out.push s!"zoom-auto: {← zoomNow}"
  -- 3. The wheel through the whole document in every view mode (View menu entries).
  let invoke (c : Menu.Cmd) : IO Unit := do
    let some (m, _) := Menu.locate c | return
    discard <| run [m, "invoke", c.label]
    settle st
  invoke .scrollPage; invoke .spreadNone
  out := out.push (← m9WheelThrough st "single")
  invoke .scrollVertical
  out := out.push (← m9WheelThrough st "continuous")
  invoke .scrollPage; invoke .spreadOdd
  out := out.push (← m9WheelThrough st "facing")
  invoke .scrollVertical
  out := out.push (← m9WheelThrough st "cfacing")
  invoke .scrollPage; invoke .spreadNone
  invoke .firstPage
  choose "Page Fit"
  out := out.push s!"back-to-single: {← page} {(← st.get).slots.size}"
  -- 4. Selection bubble → highlight on the first word of five letters or more.
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text on page 1")
  let some bx := shownBox (← st.get) | throw (IO.userError "page 1 not shown")
  let word : Option (Nat × Nat) := Id.run do
    for i in [0:ix.cells.size] do
      let (a, b) := Select.wordAt ix.cells i
      if a == i && b ≥ a + 4 &&
          (ix.cells.extract a (b + 1)).all (fun c => c.text.all Char.isAlpha && c.text.length == 1) then
        return some (a, b)
    return none
  let some (wa, wb) := word | throw (IO.userError "no word of five letters on page 1")
  out := out.push s!"word: {String.join ((ix.cells.extract wa (wb + 1)).toList.map (·.text))}"
  if let (some p0, some p1) := (← cellWindowPos st ix wa, ← cellWindowPos st ix wb) then
    sendEvent ".c" "<ButtonPress-1>" ["-x", p0.1, "-y", p0.2]
    sendEvent ".c" "<Motion>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
    sendEvent ".c" "<ButtonRelease-1>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
    discard <| run ["update"]
  let bubbleKind : IO String := return match (← st.get).bubble with
    | some (.float, _) => "float"
    | some (.edit, _) => "edit"
    | some (.editor, _) => "editor"
    | none => "none"
  out := out.push s!"bubble: {← bubbleKind} {(← st.get).sel.isSome}"
  if let some (kd, r) := (← st.get).bubble then
    if let some (_, x0, x1) := kd.layout.find? (·.1 == .highlight) then
      let vx := (View.parseDecimal (← run [".c", "canvasx", "0"])).getD 0
      let vy := (View.parseDecimal (← run [".c", "canvasy", "0"])).getD 0
      let w := (toString (r.x0 + (x0 + x1) / 2 - vx).floor, toString ((r.y0 + r.y1) / 2 - vy).floor)
      let t := toString (← IO.monoMsNow)
      sendEvent ".c" "<ButtonPress-1>" ["-x", w.1, "-y", w.2, "-time", t]
      sendEvent ".c" "<ButtonRelease-1>" ["-x", w.1, "-y", w.2, "-time", t]
      discard <| run ["update"]
  out := out.push s!"bubble-highlight: {(← st.get).marks.marks.size} {← bubbleKind}"
  sendKey "Escape"
  -- 5. A note in the top right corner.
  smokeNoteAt st (bx.urx - 45) (bx.ury - 45) "M9 note ✓ [x]"
  discard <| run ["destroy", ".note"]
  out := out.push s!"note: {(← st.get).marks.marks.size}"
  -- 6. Add text (red, 16) near the bottom left; Draw (blue, 4) near the bottom right.
  let winAt (x y : Rat) : IO (String × String) := do
    let some pos ← boxWindowPos st ⟨x, y, x, y⟩ | throw (IO.userError "page not shown")
    return pos
  let edAt (x y : Rat) : IO Unit := do
    sendEvent ".edbar" "<ButtonPress-1>" ["-x", toString x.floor, "-y", toString y.floor]
    sendEvent ".edbar" "<ButtonRelease-1>" ["-x", toString x.floor, "-y", toString y.floor]
  click ".bar.text"
  discard <| run ["update"]
  edAt (Bubble.EdPop.swatchX 1) (Bubble.EdPop.ctrlY 0)
  edAt (Bubble.EdPop.fontSize.thumbX 16) (Bubble.EdPop.ctrlY 1)
  let tp ← winAt (bx.llx + 60) (bx.lly + 60)
  sendEvent ".c" "<ButtonPress-1>" ["-x", tp.1, "-y", tp.2]
  sendEvent ".c" "<ButtonRelease-1>" ["-x", tp.1, "-y", tp.2]
  discard <| run ["update"]
  discard <| run [".c.ft", "insert", "end", "M9 text"]
  discard <| run ["update"]
  sendEvent ".c.ft" "<Key-Escape>"
  out := out.push s!"text: {(← st.get).marks.marks.size} {editorDesc ((← st.get).marks.marks.toList.find? isFt)}"
  click ".bar.draw"
  discard <| run ["update"]
  edAt (Bubble.EdPop.swatchX 2) (Bubble.EdPop.ctrlY 0)
  edAt (Bubble.EdPop.thickness.thumbX 4) (Bubble.EdPop.ctrlY 1)
  for y in [(bx.lly + 70 : Rat), bx.lly + 50] do
    let ws ← [(0 : Rat), 20, 40, 60, 80].mapM fun dx => winAt (bx.urx - 170 + dx) (y + dx / 8)
    if let some w0 := ws.head? then
      sendEvent ".c" "<ButtonPress-1>" ["-x", w0.1, "-y", w0.2]
    for w in ws.drop 1 do sendEvent ".c" "<Motion>" ["-x", w.1, "-y", w.2, "-state", "256"]
    if let some wl := ws.getLast? then
      sendEvent ".c" "<ButtonRelease-1>" ["-x", wl.1, "-y", wl.2, "-state", "256"]
  sendKey "Escape"
  click ".bar.draw"
  out := out.push s!"draw: {(← st.get).marks.marks.size} {editorDesc ((← st.get).marks.marks.toList.find? isInk)} {(← st.get).ui.editor == .none}"
  let before ← m9Marks st
  out := out.push s!"marks-before: {before}"
  -- 7. Save (Ctrl+S), close, reopen from disk.
  let target := (← st.get).path.getD ""
  discard <| run ["set", "::safepdf::autoAnswer", "overwrite"]
  sendEvent ".c" "<Control-Key-s>"
  discard <| run ["set", "::safepdf::autoAnswer", ""]
  settle st
  out := out.push s!"saved: {(← st.get).path == some target} {(← st.get).marks.dirty} {← fileMarks target}"
  out := out.push s!"saved-status: {← k.status}"
  discard <| run [".menubar.file", "invoke", Menu.Cmd.close.label]
  out := out.push s!"closed: {(← st.get).doc.isNone} {(← st.get).marks.marks.size} {← run ["wm", "title", "."]}"
  openFile st target
  choose "Page Fit"
  let s1 ← st.get
  out := out.push s!"reopened: {s1.path == some target} {s1.marks.marks.size} {s1.marks.saved.length} {s1.marks.dirty} {← k.star}"
  out := out.push s!"marks-reopened: {← m9Marks st}"
  out := out.push s!"canvas-items: {← tagCount "note"} {← tagCount "ft"} {← tagCount "ink"}"
  let saved := s1.marks.marks.toList
  out := out.push s!"pixels-reopened: {← m9Pixels st saved}"
  out := out.push s!"boxes: {← m9Boxes st}"
  out := out.push s!"cropbox: {match shownBox s1 with
    | some b => s!"{num b.llx} {num b.lly} {num b.urx} {num b.ury}" | none => "none"}"
  -- 8. XFDF: export, delete every mark, import.
  discard <| run ["set", "::safepdf::autoPath", file "m9.xfdf"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.exportXfdf.label]
  discard <| run ["set", "::safepdf::autoPath", ""]
  out := out.push s!"export: {← k.status}"
  for m in saved do deleteMark st m.id
  settle st
  out := out.push s!"removed: {(← st.get).marks.marks.size} {← m9Pixels st saved}"
  discard <| run ["set", "::safepdf::autoPath", file "m9.xfdf"]
  discard <| run [".menubar.file", "invoke", Menu.Cmd.importXfdf.label]
  discard <| run ["set", "::safepdf::autoPath", ""]
  settle st
  out := out.push s!"import: {← k.status}"
  out := out.push s!"marks-imported: {← m9Marks st}"
  out := out.push s!"imported-hl: {← m9Pixels st ((← st.get).marks.marks.toList.filter (!·.isNote))}"
  out := out.push s!"imported-canvas: {← tagCount "note"} {← tagCount "ft"} {← tagCount "ink"}"
  IO.FS.writeFile (file "m9.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- The RGB triple at `(x, y)` of a binary PPM (`P6`, maxval 255, single-space/newline
header as ImageMagick writes it). -/
def ppmAt (d : ByteArray) (x y : Nat) : Option (Nat × Nat × Nat) := Id.run do
  -- header: 4 whitespace-separated tokens, then one whitespace byte
  let mut toks : Array String := #[]
  let mut cur := ""
  let mut i := 0
  while toks.size < 4 && i < d.size && i < 64 do
    let c := Char.ofNat (d.get! i).toNat
    if c.isWhitespace then
      if !cur.isEmpty then toks := toks.push cur; cur := ""
    else cur := cur.push c
    i := i + 1
  let (some w, some _) := ((toks[1]?.bind String.toNat?), (toks[2]?.bind String.toNat?)) |
    return none
  if toks[0]? != some "P6" || toks[3]? != some "255" || x ≥ w then return none
  let o := i + 3 * (y * w + x)
  if o + 2 < d.size then some ((d.get! o).toNat, (d.get! (o + 1)).toNat, (d.get! (o + 2)).toNat)
  else none

/-- **What the screen shows** of the free texts `ms` (task 9.r5): an X screenshot of the
canvas (`import -window ID -depth 8 ppm:…`, ImageMagick; without `-depth 8` it writes 16-bit) — the rendered page and the canvas items
together, as the user sees them — and the number of red pixels (`m9Red`) on a grid in each
text box; `none` when `import` is missing or fails. -/
def screenFtRed (st : IO.Ref State) (dir : String) (ms : List Marks.Mark) : IO (Option Nat) := do
  discard <| run ["update"]
  let s ← st.get
  let some bx := shownBox s | return none
  let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
    View.parseDecimal (← run [".c", "canvasy", "0"])) | return none
  let wid ← run ["winfo", "id", ".c"]
  let shot := (dir : System.FilePath) / "screen.ppm"
  let ok ← try
      let r ← IO.Process.output { cmd := "import", args := #["-window", wid, "-depth", "8", s!"ppm:{shot}"] }
      pure (r.exitCode == 0)
    catch _ => pure false
  if !ok then return none
  let d ← IO.FS.readBinFile shot
  let mut n := 0
  for m in ms do
    if let some b := m.box then
      for q in m9Grid b do
        let (x0, y0, _, _) := canvasRect s bx ⟨q.x, q.y, q.x, q.y⟩
        let (px, py) := ((x0 - vx).floor, (y0 - vy).floor)
        if px ≥ 0 && py ≥ 0 then
          if let some c := ppmAt d px.toNat py.toNat then
            if m9Red c then n := n + 1
  return some n

/-- The second half of the M9 run (`SAFEPDF_VIEWER_SMOKE_MODE=m9-reopen`, task 9.6): a fresh
viewer process on the file `smokeM9` saved into (task 9.r2: the opened file) restores the four marks (equal
descriptions) and the renderer draws them (pixels), at Page Fit; the free text is visible on
screen before any click (`screenFtRed`, task 9.r5: `screen-text: N subst=… ft-items=…`).
Results in `m9-reopen.txt`. -/
def smokeM9Reopen (st : IO.Ref State) (dir : String) : IO Unit := do
  discard <| run ["update"]
  discard <| run [".zoommenu", "invoke", "Page Fit"]
  settle st
  let s ← st.get
  let mut out : Array String := #[]
  out := out.push s!"restored: {s.marks.marks.size} {s.marks.saved.length} {s.marks.dirty}"
  out := out.push s!"marks: {← m9Marks st}"
  out := out.push s!"pixels: {← m9Pixels st s.marks.marks.toList}"
  -- task 9.r5: the reopened free text is visible without any click, on screen (page photo
  -- plus canvas items), with or without a substitute Helvetica
  let fts := s.marks.marks.toList.filter (·.isFreeText)
  let red := match ← screenFtRed st dir fts with
    | some n => toString n | none => "skipped"
  out := out.push s!"screen-text: {red} subst={s.paintsHelvetica} ft-items={← tagCount "ft"}"
  -- … and stays visible after a zoom change, a page change and back, a rotation and back,
  -- and in continuous vertical scrolling
  let shot (what : String) : IO String := do
    settle st
    let n := match ← screenFtRed st dir fts with | some n => toString n | none => "skipped"
    let ms := (← st.get).marks.marks.toList
    return s!"{what}={n}/{← m9Pixels st ms}"
  let mut after : Array String := #[]
  discard <| run [".zoommenu", "invoke", "Page Width"]
  after := after.push (← shot "zoom")
  discard <| run [".menubar.go", "invoke", Menu.Cmd.nextPage.label]
  settle st
  discard <| run [".menubar.go", "invoke", Menu.Cmd.prevPage.label]
  after := after.push (← shot "page")
  discard <| run [".zoommenu", "invoke", "Page Fit"]
  rotate st true
  after := after.push (← shot "rot90")
  rotate st false
  after := after.push (← shot "rot0")
  setViewMode st "scroll" "vertical"
  after := after.push (← shot "vertical")
  setViewMode st "scroll" "page"
  after := after.push (← shot "single")
  out := out.push s!"screen-after: {" ".intercalate after.toList}"
  out := out.push s!"status: {← run [".status", "cget", "-text"]}"
  IO.FS.writeFile ((dir : System.FilePath) / "m9-reopen.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- The M9 look-check set-up (`SAFEPDF_VIEWER_SMOKE_MODE=m9-shot`, task 9.10), in the state of
the human's PDF.js reference screenshot (`docs/viewer-reference/pdfjs-firefox.png`): page 1 at
Automatic Zoom with the outline sidebar as opened on load, the toolbar's Highlight pop-over open
(tool on, yellow), the first sentence of the abstract (`SAFEPDF_VIEWER_SHOT_FROM` …
`SAFEPDF_VIEWER_SHOT_TO`, default the first sentence of arxiv-1706.03762's abstract) dragged
over in the tool mode, so it is highlighted in yellow and shows its edit bubble. Writes
`ready.txt` (or `error: …`) and stays up 20 s for the screenshot, then closes. -/
def smokeM9Shot (st : IO.Ref State) (dir : String) : IO Unit := do
  discard <| run ["update"]
  settle st
  let fromQ := (← IO.getEnv "SAFEPDF_VIEWER_SHOT_FROM").getD "The dominant sequence"
  let toQ := (← IO.getEnv "SAFEPDF_VIEWER_SHOT_TO").getD "and a decoder."
  sendEvent ".bar.highlight" "<ButtonPress-1>" ["-x", "16", "-y", "16"]
  sendEvent ".bar.highlight" "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
  discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text on page 1")
  let some (a, _) := (ix.hits (Select.normQuery fromQ))[0]? | throw (IO.userError s!"{fromQ} not found")
  let some (_, b) := (ix.hits (Select.normQuery toQ))[0]? | throw (IO.userError s!"{toQ} not found")
  let (some p0, some p1) := (← cellWindowPos st ix a, ← cellWindowPos st ix b) |
    throw (IO.userError "sentence not shown")
  sendEvent ".c" "<ButtonPress-1>" ["-x", p0.1, "-y", p0.2]
  sendEvent ".c" "<Motion>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
  sendEvent ".c" "<ButtonRelease-1>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
  discard <| run ["update"]
  settle st
  discard <| run ["update"]
  let s ← st.get
  let kind := match s.bubble with
    | some (.float, _) => "float" | some (.edit, _) => "edit" | some (.editor, _) => "editor"
    | none => "none"
  IO.FS.writeFile ((dir : System.FilePath) / "ready.txt")
    s!"ready\nmarks: {s.marks.marks.size}\nbubble: {kind}\npopover: {← run ["winfo", "ismapped", ".hlbar"]}\n\
      field: {← run ["set", "::safepdf::pageText"]} {← run [".bar.of", "cget", "-text"]}\n\
      zoom: {← run [".bar.zoom", "itemcget", "label", "-text"]}\nsidebar: {s.outlineShown}\n"
  discard <| run ["after", "20000", "destroy ."]

/-- Smoke steps of closing a note popup without Save (`SAFEPDF_VIEWER_SMOKE_MODE=noteclose`,
task 9.r12, script case 1t) on the text PDF of `smokeText`. Each line of `noteclose.txt` gives
the notes left (`notes=`), whether a note icon is on the canvas (`icons=`), whether the popup
is open (`popup=`) and the case's note text or state:
`menu-esc` (Edit → Add note…, Escape in the text widget: removed, no icon),
`typed-esc` (context menu, typed text, Escape: kept with the text), `saved-clear-esc` (that
note made saved, reopened by a click on its icon, cleared, Escape: kept, still saved),
`saved-empty-esc` (an empty saved note, reopened by a click: removed, the title gets `*`),
`comment-esc` (Edit → Add note… on a selected highlight, Escape: the comment goes, the
highlight stays), `selection-blank-esc` (a note on the selection with white space only:
removed), `cancel-empty` / `cancel-typed` (the Cancel button), `wm-empty` / `wm-typed` (the
window's close button, its `WM_DELETE_WINDOW` script), `switch` (Add note… while an empty
note's popup is open removes that note), `deleted-open` (the note deleted while its popup is
open: the popup goes; a stale `noteClose` is ignored). -/
def smokeNoteClose (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text index")
  let notes : IO (List Marks.Mark) := return (← st.get).marks.marks.toList.filter (·.isNote)
  let popup : IO String := run ["winfo", "exists", ".note"]
  let state (what : String) : IO String := do
    discard <| run ["update"]
    let ns ← notes
    return s!"notes={ns.length} icons={decide ((← tagCount "note") > 0)} popup={← popup} {what}"
  let esc : IO Unit := do
    sendEvent ".note.t" "<Key-Escape>"
    discard <| run ["update"]
  let typeText (t : String) : IO Unit := do
    discard <| run [".note.t", "insert", "end", t]
  let menuNote : IO Unit := do
    discard <| run [".menubar.edit", "invoke", Menu.Cmd.addNote.label]
    discard <| run ["update", "idletasks"]
  let ctxNote (x y : Rat) : IO Unit := do
    let some npos ← boxWindowPos st ⟨x, y, x, y⟩ | return
    sendEvent ".c" "<ButtonPress-3>" ["-x", npos.1, "-y", npos.2]
    discard <| run [Menu.popPath, "invoke", Menu.Cmd.addNote.label]
    discard <| run ["update", "idletasks"]
  let clickNote (id : Nat) : IO Unit := do
    let s ← st.get
    let some bx := shownBox s | return
    let some m := s.marks.find? id | return
    let some ib := m.iconBox bx | return
    let some pos ← boxWindowPos st ib | return
    k.clickAt pos
    discard <| run ["update", "idletasks"]
  let markSaved : IO Unit := do
    st.modify fun s => { s with marks := Marks.Store.load s.marks.marks.toList }
    repaint st
    syncMenus st
  let dragSel (q : String) : IO Unit := do
    let some (wa, wb) := (ix.hits (Select.normQuery q))[0]? | return
    let (some p0, some p1) := (← cellWindowPos st ix wa, ← cellWindowPos st ix (wb - 1)) | return
    sendEvent ".c" "<ButtonPress-1>" ["-x", p0.1, "-y", p0.2]
    sendEvent ".c" "<Motion>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
    sendEvent ".c" "<ButtonRelease-1>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
    discard <| run ["update"]
  let textOf (id : Option Nat) : IO String := do
    return (((← st.get).marks.find? (id.getD 0)).map (·.text)).getD "<gone>"
  let newest : IO (Option Nat) := return ((← notes).getLast?.map (·.id))
  -- 1. A new note (Edit → Add note…, nothing selected) + Escape in the text widget.
  menuNote
  out := out.push s!"menu-open: {← state ""} focus={← run ["focus"]}"
  esc
  out := out.push s!"menu-esc: {← state ""}"
  -- 2. A new note (context menu) with typed text + Escape: the text is saved.
  ctxNote 300 400
  typeText "typed text"
  esc
  let typed ← newest
  out := out.push s!"typed-esc: {← state (← textOf typed)}"
  -- 3. That note saved in the file; reopened by a click on its icon, cleared, Escape.
  markSaved
  clickNote (typed.getD 0)
  let shown ← try run [".note.t", "get", "1.0", "end - 1 chars"] catch _ => pure "<none>"
  discard <| run [".note.t", "delete", "1.0", "end"]
  esc
  out := out.push s!"saved-clear-esc: {← state (← textOf typed)} shown={shown} dirty={(← st.get).marks.dirty} star={← k.star}"
  -- 4. An empty saved note (Save with no text, then saved in the file), reopened, Escape.
  ctxNote 100 100
  discard <| run [".note.b.save", "invoke"]
  let empty ← newest
  markSaved
  out := out.push s!"saved-empty-before: {← state (← textOf empty)} star={← k.star}"
  clickNote (empty.getD 0)
  out := out.push s!"saved-empty-open: {← popup}"
  esc
  out := out.push s!"saved-empty-esc: {← state (← textOf empty)} dirty={(← st.get).marks.dirty} star={← k.star}"
  -- 5. The comment of a highlight: highlight `world`, Add note… on it, Escape.
  dragSel "world"
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.highlight.label]
  let hl := (← st.get).markSel
  menuNote
  let cmt ← newest
  let anchored := ((← st.get).marks.find? (cmt.getD 0)).map (·.quads) ==
    ((← st.get).marks.find? (hl.getD 0)).map (·.quads)
  out := out.push s!"comment-open: {← popup} anchored={anchored}"
  esc
  out := out.push s!"comment-esc: {← state (← textOf cmt)} highlight={((← st.get).marks.find? (hl.getD 0)).isSome}"
  -- 6. A note on the selection (as the bubble's Add comment) with white space only.
  dragSel "safe"
  menuNote
  let onSel ← newest
  typeText "  \n\t "
  esc
  out := out.push s!"selection-blank-esc: {← state (← textOf onSel)}"
  -- 7. The Cancel button.
  menuNote
  let c1 ← newest
  discard <| run [".note.b.cancel", "invoke"]
  out := out.push s!"cancel-empty: {← state (← textOf c1)}"
  menuNote
  let c2 ← newest
  typeText "via cancel"
  discard <| run [".note.b.cancel", "invoke"]
  out := out.push s!"cancel-typed: {← state (← textOf c2)}"
  -- 8. The window's close button.
  let wmClose : IO Unit := do
    discard <| run ["uplevel", "#0", ← run ["wm", "protocol", ".note", "WM_DELETE_WINDOW"]]
    discard <| run ["update"]
  menuNote
  let w1 ← newest
  wmClose
  out := out.push s!"wm-empty: {← state (← textOf w1)}"
  menuNote
  let w2 ← newest
  typeText "via close"
  wmClose
  out := out.push s!"wm-typed: {← state (← textOf w2)}"
  -- 9. Add note… while an empty note's popup is open: the first note goes.
  ctxNote 200 200
  let a ← newest
  menuNote
  let b ← newest
  out := out.push s!"switch: {← state (← textOf a)} other={a != b} for={(← run ["set", "::safepdf::noteId"]) == toString (b.getD 0)}"
  esc
  out := out.push s!"switch-esc: {← state (← textOf b)}"
  -- 10. The note deleted while its popup is open; then a stale close.
  menuNote
  let d ← newest
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.deleteMark.label]
  out := out.push s!"deleted-open: {← state (← textOf d)}"
  discard <| run ["::safepdf::emit", "noteClose", toString (d.getD 0), ""]
  discard <| run ["::safepdf::emit", "noteClose", "999", "x"]
  out := out.push s!"stale-close: {← state ""}"
  out := out.push s!"texts: {(← notes).map (·.text)}"
  out := out.push "done"
  IO.FS.writeFile (file "noteclose.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of the dismissal rule (`SAFEPDF_VIEWER_SMOKE_MODE=dismiss`, task 10.6,
`Toolbar.Transient`) on the text PDF of `smokeText`. Each line of `dismiss.txt` gives what is
open after a step (`1`/`0`: the bar or pop-over is packed / placed): the find bar closes on a
drag on the page (and the drag still selects: the click is not consumed) and on Escape with
the focus on the page; Ctrl+F closes the go-to bar; the go-to bar stays on a press inside it
and closes on a press on the status line; the Highlight pop-over stays on a press inside it
and on the page, closes on a press elsewhere (the tool stays on) and on Escape; the Add text
pop-over likewise (the mode stays on); the edit bubble's colour picker closes on a press
outside the page; a note popup with typed text closes on a press on the page (the text is
kept, task 9.r12), an empty new one on Escape in the main window (the note goes). -/
def smokeDismiss (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let mut out : Array String := #[]
  discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text index")
  let upd : IO Unit := discard <| run ["update"]
  let packed (w : String) : IO String := do
    return if (← run ["winfo", "manager", w]).isEmpty then "0" else "1"
  let placed (w : String) : IO String := run ["winfo", "ismapped", w]
  let note : IO String := run ["winfo", "exists", ".note"]
  let press (w : String) (x y : String := "2") : IO Unit := do
    sendEvent w "<ButtonPress-1>" ["-x", x, "-y", y, "-time", toString (← IO.monoMsNow)]
    sendEvent w "<ButtonRelease-1>" ["-x", x, "-y", y, "-time", toString (← IO.monoMsNow)]
    upd
  let btn (w : String) : IO Unit := press w "16" "16"
  let dragSel (q : String) : IO Unit := do
    let some (wa, wb) := (ix.hits (Select.normQuery q))[0]? | return
    let (some p0, some p1) := (← cellWindowPos st ix wa, ← cellWindowPos st ix (wb - 1)) | return
    sendEvent ".c" "<ButtonPress-1>" ["-x", p0.1, "-y", p0.2]
    sendEvent ".c" "<Motion>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
    sendEvent ".c" "<ButtonRelease-1>" ["-x", p1.1, "-y", p1.2, "-state", "256"]
    upd
  let some blank ← boxWindowPos st ⟨40, 760, 40, 760⟩ | throw (IO.userError "page not shown")
  let pause : IO Unit := discard <| run ["after", "600"]
  -- 1. The find bar: a drag on the page closes it and still selects; Escape closes it.
  sendEvent ".c" "<Control-Key-f>"
  upd
  out := out.push s!"find-open: {← packed ".find"} focus={← run ["focus"]}"
  dragSel "world"
  out := out.push s!"find-drag: {← packed ".find"} sel={(← st.get).sel.isSome} focus={← run ["focus"]}"
  sendEvent ".c" "<Control-Key-f>"
  upd
  sendKey "Escape"
  upd
  out := out.push s!"find-esc: {← packed ".find"}"
  -- 2. The go-to bar: Ctrl+F closes it (rivals); a press inside keeps it, one outside closes it.
  sendEvent ".c" "<Control-Key-g>"
  upd
  out := out.push s!"goto-open: {← packed ".goto"}"
  sendEvent ".c" "<Control-Key-f>"
  upd
  out := out.push s!"goto-rival: goto={← packed ".goto"} find={← packed ".find"}"
  sendEvent ".find.e" "<Key-Escape>"
  sendEvent ".c" "<Control-Key-g>"
  upd
  press ".goto.e"
  out := out.push s!"goto-inside: {← packed ".goto"}"
  press ".status"
  out := out.push s!"goto-away: {← packed ".goto"}"
  -- 3. The Highlight pop-over.
  pause
  btn ".bar.highlight"
  out := out.push s!"hl-open: {← placed ".hlbar"} tool={(← st.get).ui.tool}"
  press ".hlbar"
  out := out.push s!"hl-inside: {← placed ".hlbar"}"
  press ".c" blank.1 blank.2
  out := out.push s!"hl-page: {← placed ".hlbar"}"
  press ".status"
  out := out.push s!"hl-away: {← placed ".hlbar"} tool={(← st.get).ui.tool}"
  pause
  btn ".bar.highlight"
  pause
  btn ".bar.highlight"
  out := out.push s!"hl-reopen: {← placed ".hlbar"} tool={(← st.get).ui.tool}"
  sendKey "Escape"
  upd
  out := out.push s!"hl-esc: {← placed ".hlbar"} tool={(← st.get).ui.tool}"
  pause
  btn ".bar.highlight"
  out := out.push s!"hl-off: {(← st.get).ui.tool}"
  -- 4. The Add text pop-over.
  pause
  btn ".bar.text"
  out := out.push s!"ed-open: {← placed ".edbar"} text={(← st.get).ui.editor == .text}"
  press ".status"
  out := out.push s!"ed-away: {← placed ".edbar"} text={(← st.get).ui.editor == .text}"
  pause
  btn ".bar.text"
  pause
  btn ".bar.text"
  sendKey "Escape"
  upd
  out := out.push s!"ed-esc: {← placed ".edbar"} text={(← st.get).ui.editor == .text}"
  pause
  btn ".bar.text"
  -- 5. The edit bubble's colour picker.
  dragSel "safe"
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.highlight.label]
  upd
  if let some (k, r) := (← st.get).bubble then
    if let some (_, x0, x1) := k.layout.find? (·.1 == .color) then
      let vx := (View.parseDecimal (← run [".c", "canvasx", "0"])).getD 0
      let vy := (View.parseDecimal (← run [".c", "canvasy", "0"])).getD 0
      pause
      press ".c" (toString (r.x0 + (x0 + x1) / 2 - vx).floor) (toString ((r.y0 + r.y1) / 2 - vy).floor)
  out := out.push s!"picker-open: {(← st.get).pickerAt.isSome}"
  press ".status"
  out := out.push s!"picker-away: {(← st.get).pickerAt.isSome} {(← st.get).ui.picker}"
  sendKey "Escape"
  upd
  -- 6. The note popup: a press on the page closes it the 9.r12 way (typed text kept).
  let notes : IO (List Marks.Mark) := return (← st.get).marks.marks.toList.filter (·.isNote)
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.addNote.label]
  upd
  discard <| run [".note.t", "insert", "end", "kept by a click away"]
  press ".note.t"
  out := out.push s!"note-inside: {← note}"
  pause
  press ".c" blank.1 blank.2
  out := out.push s!"note-away: popup={← note} notes={(← notes).length} text={((← notes).getLast?.map (·.text)).getD "<none>"}"
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.addNote.label]
  upd
  out := out.push s!"note-open: popup={← note} notes={(← notes).length}"
  sendKey "Escape"
  upd
  out := out.push s!"note-esc: popup={← note} notes={(← notes).length}"
  out := out.push "done"
  IO.FS.writeFile (file "dismiss.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of the select-text tool and the cursor (task 10.8,
`SAFEPDF_VIEWER_SMOKE_MODE=tools`) on a page with the text `Hello safe world` and a link
annotation over blank paper: Select text is active and pressed at start; the canvas cursor
over the word `safe`, the link and blank paper (`Toolbar.cursorFor`); Draw takes over (Select
text unpressed, crosshair at once and over the text) and its button again gives Select text
back; Highlight takes over, Escape keeps it (task 10.6), the Select text button ends it; Add
text shows the I-beam over the link. Clicks are spaced 2.5 s apart in event time (Aqua counts
closer ones as double clicks). -/
def smokeTools (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let mut out : Array String := #[]
  discard <| run ["update"]
  let upd : IO Unit := discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text index")
  let some (wa, _) := (ix.hits (Select.normQuery "safe"))[0]? | throw (IO.userError "no safe")
  let some onText ← cellWindowPos st ix (wa + 1) | throw (IO.userError "page not shown")
  let some l := (← linksOf st 0)[0]? | throw (IO.userError "no link")
  let some onLink ← boxWindowPos st l.box | throw (IO.userError "link not shown")
  let some blank ← boxWindowPos st ⟨40, 760, 40, 760⟩ | throw (IO.userError "page not shown")
  let t ← IO.mkRef ((← IO.monoMsNow) % 1000000000)
  let btn (w : String) : IO Unit := do
    t.modify (· + 2500)
    let tm := toString (← t.get)
    sendEvent w "<ButtonPress-1>" ["-x", "16", "-y", "16", "-time", tm]
    sendEvent w "<ButtonRelease-1>" ["-x", "16", "-y", "16", "-time", tm]
    upd
  let moveTo (pos : String × String) : IO Unit := do
    sendEvent ".c" "<Motion>" ["-x", pos.1, "-y", pos.2]
    upd
  let cursor : IO String := return s!"[{← run [".c", "cget", "-cursor"]}]"
  let modeName : Toolbar.Mode → String
    | .select => "select" | .highlight => "highlight" | .text => "text" | .draw => "draw"
  let tog (w : String) : IO String := run ["set", s!"::safepdf::btn(tog,{w})"]
  let tools : IO String := do
    return s!"{modeName (Toolbar.Mode.of (← st.get).ui)} select={← tog ".bar.select"} \
      highlight={← tog ".bar.highlight"} text={← tog ".bar.text"} draw={← tog ".bar.draw"}"
  out := out.push s!"tool0: {← tools}"
  out := out.push s!"select-state: {← run ["::safepdf::btnState", ".bar.select"]}"
  moveTo onText
  out := out.push s!"cursor-text: {← cursor}"
  moveTo onLink
  out := out.push s!"cursor-link: {← cursor}"
  moveTo blank
  out := out.push s!"cursor-empty: {← cursor}"
  -- Draw: crosshair at once (no motion) and over the text; its button again gives Select back.
  btn ".bar.draw"
  out := out.push s!"draw-on: {← tools}"
  out := out.push s!"cursor-draw-still: {← cursor}"
  moveTo onText
  out := out.push s!"cursor-draw-text: {← cursor}"
  btn ".bar.draw"
  out := out.push s!"draw-off: {← tools}"
  out := out.push s!"cursor-after-draw: {← cursor}"
  -- Highlight: Escape keeps the tool, Select text ends it.
  btn ".bar.highlight"
  out := out.push s!"hl-on: {← tools} popover={(← st.get).ui.popover}"
  sendKey "Escape"
  upd
  out := out.push s!"hl-esc: {← tools} popover={(← st.get).ui.popover}"
  btn ".bar.select"
  out := out.push s!"select-btn: {← tools} popover={(← st.get).ui.popover}"
  btn ".bar.select"
  out := out.push s!"select-again: {← tools}"
  -- Add text: the I-beam also over the link (a click places a text box there).
  btn ".bar.text"
  moveTo onLink
  out := out.push s!"text-on: {← tools}"
  out := out.push s!"cursor-text-link: {← cursor}"
  btn ".bar.select"
  out := out.push s!"cursor-select-link: {← cursor}"
  out := out.push "done"
  IO.FS.writeFile (file "tools.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Waits until the thumbnails panel has rendered every thumbnail it wants (task 9.r9 smoke
tests): processes Tk events, starts renders (`thumbView`), waits for them (`thumbPoll`). -/
def thumbSettle (st : IO.Ref State) : IO Unit := do
  for _ in [0:400] do
    discard <| run ["update"]
    thumbView st
    let js := (← st.get).thJobs
    if js.isEmpty then break
    for j in js do discard <| IO.wait j.task
    thumbPoll st
  discard <| run ["update"]

/-- `VmRSS` and `VmHWM` of this process in KiB (Linux `/proc/self/status`; `0` elsewhere). -/
def memKiB : IO (Nat × Nat) := do
  let txt ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
  let field (k : String) : Nat :=
    match (txt.splitOn "\n").find? (·.startsWith k) with
    | some l => (((l.drop k.length).toString.trimAscii.toString.splitOn " ").head?.bind (·.toNat?)).getD 0
    | none => 0
  return (field "VmRSS:", field "VmHWM:")

/-- One line describing the sidebar for the thumbnails smoke test: shown, panel, the panel
buttons mapped, the toggle mapped, the heading, thumbnails laid out / rendered / kept, the
highlighted and selected page, the current page. -/
def thumbRow (st : IO.Ref State) (name : String) : IO String := do
  discard <| run ["update"]
  let s ← st.get
  let mut btns : List String := []
  for i in Sidebar.panels do
    if (← run ["winfo", "ismapped", i.button]) == "1" then btns := btns ++ [i.key]
  let vis := match ← thumbBand s with
    | some (top, bot) => Sidebar.thumbsIn s.thSlots top bot
    | none => []
  return s!"{name}: shown={s.outlineShown} panel={s.panel.info.key} \
    buttons={",".intercalate btns} toggle={← run ["winfo", "ismapped", ".bar.sidebar"]} \
    head={← run [".ol.h", "cget", "-text"]} slots={s.thSlots.size} rendered={s.thRendered} \
    have={s.thHave.length} visible={vis.length} first-visible={(vis.head?.map (· + 1)).getD 0} \
    marked={(s.thMarked.map (· + 1)).getD 0} sel={(s.thSel.map (· + 1)).getD 0} \
    page={s.page + 1} photos={(← run ["image", "names"]).splitOn " " |>.filter (·.startsWith "::safepdf::th") |>.length} \
    status={← run [".status", "cget", "-text"]}"

/-- Window y in `.ol.th` of the middle of page `p`'s thumbnail, scrolled into view first. -/
def thumbWinY (st : IO.Ref State) (p : Nat) : IO (Option String) := do
  let s ← st.get
  let some t := s.thSlots[p]? | return none
  thumbSee st t
  discard <| run ["update"]
  let some (top, _) ← thumbBand (← st.get) | return none
  return some (toString ((t.y + t.h / 2 : Nat) - (top : Int)))

/-- Smoke steps of task 9.r9 (`SAFEPDF_VIEWER_SMOKE_MODE=thumbs`), started on
`th-outline.pdf` (60 pages with an outline, page 5 `/Rotate 90`) next to `th-thumbs.pdf` (60
pages, `/PageMode /UseThumbs`, no outline) and `th-plain.pdf` (3 pages, nothing). Writes one
`thumbRow` per step to `thumbs.txt`: opened with the outline and both buttons; the Thumbnails
button (lazy: only the visible thumbnails and the margin rendered); the rotated page's slot;
a click on thumbnail 3; the main view at page 40 (highlight follows, scrolled into view);
Down, Down, Return in the panel; the panel scrolled to the end (at most
`Sidebar.thumbBudget` kept); a rotation (laid out again); the UseThumbs file (opens with
thumbnails, no outline button, no note); the plain file (closed, toggle shown) and its
toggle (thumbnails). -/
def smokeThumbs (st : IO.Ref State) (dir : String) : IO Unit := do
  let base := dirOf ((← st.get).path.getD "")
  let mut out : Array String := #[]
  settle st
  out := out.push (← thumbRow st "outline-open")
  discard <| run ["::safepdf::btnInvoke", ".ol.sw.thumbnails"]
  thumbSettle st
  out := out.push (← thumbRow st "thumbs-open")
  let s ← st.get
  out := out.push s!"rot-slot: {(s.thSlots[4]?.map fun t => s!"{t.w}x{t.h}").getD "-"} \
    {(s.thSlots[0]?.map fun t => s!"{t.w}x{t.h}").getD "-"}"
  -- Click on thumbnail 3.
  if let some y ← thumbWinY st 2 then
    sendEvent ".ol.th" "<ButtonRelease-1>" ["-x", "100", "-y", y]
  settle st
  thumbSettle st
  out := out.push (← thumbRow st "click-3")
  -- The main view goes to page 40: the highlight follows and is scrolled into view.
  discard <| run ["::safepdf::emit", "goto", "40"]
  settle st
  thumbSettle st
  out := out.push (← thumbRow st "main-40")
  -- Keyboard: Down, Down, Return.
  sendEvent ".ol.th" "<Key-Down>"
  sendEvent ".ol.th" "<Key-Down>"
  out := out.push (← thumbRow st "keys-down2")
  sendEvent ".ol.th" "<Key-Return>"
  settle st
  thumbSettle st
  out := out.push (← thumbRow st "keys-return")
  -- Scroll the panel through the whole document: at most the budget is kept.
  let mut maxHave := 0
  for k in [0:11] do
    discard <| run [".ol.th", "yview", "moveto", fmtFrac ((k : Rat) / 10)]
    thumbSettle st
    maxHave := max maxHave (← st.get).thHave.length
  out := out.push s!"{← thumbRow st "scrolled-end"} max-have={maxHave} budget={Sidebar.thumbBudget}"
  -- Rotation: laid out again with the rotated sizes.
  discard <| run ["::safepdf::emit", "rotate", "cw"]
  settle st
  thumbSettle st
  let s ← st.get
  out := out.push (← thumbRow st "rotated")
  out := out.push s!"rotated-slots: slot1={(s.thSlots[0]?.map fun t => s!"{t.w}x{t.h}").getD "-"} \
    slot5={(s.thSlots[4]?.map fun t => s!"{t.w}x{t.h}").getD "-"}"
  -- A UseThumbs file without an outline opens with the thumbnails.
  openFile st s!"{base}/th-thumbs.pdf"
  settle st
  thumbSettle st
  out := out.push (← thumbRow st "usethumbs")
  -- A file with neither: closed, but the toggle shows and opens the thumbnails.
  openFile st s!"{base}/th-plain.pdf"
  settle st
  out := out.push (← thumbRow st "plain")
  discard <| run ["::safepdf::btnInvoke", ".bar.sidebar"]
  thumbSettle st
  out := out.push (← thumbRow st "plain-toggle")
  discard <| run ["::safepdf::btnInvoke", ".bar.sidebar"]
  out := out.push (← thumbRow st "plain-toggle2")
  out := out.push "done"
  IO.FS.writeFile ((dir : System.FilePath) / "thumbs.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Thumbnail performance (task 9.r9, `SAFEPDF_VIEWER_SMOKE_MODE=thumbperf` on any file):
reopens the start-up file with the thumbnails panel (as the event loop runs it: Tk events and
`poll` until the visible thumbnails are shown) and writes `thumbperf.txt`: time to open, to
the first thumbnail and to every visible one; the longest main-view page change (Next)
while thumbnails render; then the panel scrolled through the whole document in steps of one
panel height: total time, most thumbnails kept, thumbnails rendered; memory (VmRSS before,
after the first screen, VmHWM at the end, KiB). -/
def smokeThumbPerf (st : IO.Ref State) (dir : String) : IO Unit := do
  let path := (← st.get).path.getD ""
  let (rss0, _) ← memKiB
  let t0 ← IO.monoNanosNow
  st.modify ({ · with panel := .thumbnails })
  openFile st path
  if !(← st.get).outlineShown then showSidebar st (some .thumbnails)
  if (← st.get).panel != .thumbnails then showPanel st .thumbnails
  let tOpen ← IO.monoNanosNow
  -- The event loop: until every visible thumbnail is shown (at most 60 s).
  let mut tAll := 0
  for _ in [0:30000] do
    discard <| run ["update"]
    let s ← st.get
    if let some (top, bot) ← thumbBand s then
      let vis := Sidebar.thumbsIn s.thSlots top bot
      if !vis.isEmpty && vis.all s.thHave.contains then
        tAll := (← IO.monoNanosNow) - t0
        break
    IO.sleep 2
  let (rss1, _) ← memKiB
  -- Page changes of the main view while thumbnails render.
  let mut worst := 0
  discard <| run [".ol.th", "yview", "moveto", "0.5"]
  for _ in [0:5] do
    let a ← IO.monoNanosNow
    discard <| run ["::safepdf::emit", "next"]
    let b ← IO.monoNanosNow
    worst := max worst (b - a)
    discard <| run ["update"]
  -- Scroll the panel through the document.
  let t1 ← IO.monoNanosNow
  let s ← st.get
  let hgt := ((← run ["winfo", "height", ".ol.th"]).toNat?).getD 1
  let steps := s.thHeight / (max hgt 1) + 1
  let mut maxHave := 0
  for k in [0:steps + 1] do
    discard <| run [".ol.th", "yview", "moveto", fmtFracFine ((k : Rat) / (steps : Rat))]
    thumbSettle st
    maxHave := max maxHave (← st.get).thHave.length
  let t2 ← IO.monoNanosNow
  let (rss2, hwm) ← memKiB
  let s ← st.get
  IO.FS.writeFile ((dir : System.FilePath) / "thumbperf.txt")
    s!"file: {path}\npages: {s.pageCount}\nopen-ms: {formatMs (tOpen - t0)}\n\
      first-thumb-ms: {(s.thFirstNs.map formatMs).getD "-"}\nvisible-thumbs-ms: {formatMs tAll}\n\
      worst-next-ms: {formatMs worst}\nscroll-all-ms: {formatMs (t2 - t1)}\nscroll-steps: {steps + 1}\n\
      max-kept: {maxHave}\nbudget: {Sidebar.thumbBudget}\nrendered: {s.thRendered}\n\
      rss0-kib: {rss0}\nrss-first-screen-kib: {rss1}\nrss-end-kib: {rss2}\nhwm-kib: {hwm}\n"
  discard <| run ["destroy", "."]

/-- Task 12.3b: the live photos without a reservation plus the reservations without a live
photo (expected 0): page photos with an image and kept thumbnails against `photoTix`, and
each reservation against its Tk image's present size (`Budget.photoBytes`). -/
def photoMismatch (st : IO.Ref State) : IO Nat := do
  let s ← st.get
  let live := (s.photos.toList.filterMap fun (p, r) => match r with
    | .ok _ => some (photoOf p) | .error _ => none) ++ s.thHave.map thumbPhoto
  let mut bad := (live.filter fun n => !s.photoTix.any (·.1 == n)).length
  for (n, t) in s.photoTix do
    if !live.contains n then bad := bad + 1; continue
    let w := (← run ["image", "width", n]).toNat?.getD 0
    let h := (← run ["image", "height", n]).toNat?.getD 0
    if Budget.photoBytes w h != t.bytes then bad := bad + 1
  if s.photoPool.used != s.photoTix.foldl (fun a (_, t) => a + t.bytes) 0 then bad := bad + 1
  return bad

/-- **The interleave scenario** (task 12.3, `SAFEPDF_VIEWER_SMOKE_MODE=interleave`, driven by
`scripts/interleave.sh`, which samples the resident memory of this process and of its workers
meanwhile): reopens the start-up file with the thumbnails panel and runs `rounds` rounds of
zoom in `zoomSteps` steps (from 75 % to 200 %), two searches (a frequent word and one that is nowhere, which indexes every page under
one work allowance), the thumbnails panel scrolled on, two page changes and zoom out as many steps
— each
step followed by 250 ms of the event loop, so renders, thumbnails and text requests overlap.
Task 12.3b adds the deep zoom phase: 600 % and then 800 %, each scrolled through the whole
document in 12 steps of 400 ms (the zoom is limited to `Budget.Ceilings.pagePixels` per page;
the resident memory after each step is logged). Then waits for everything in flight and writes
`interleave.txt`: the pool's peak and what it holds at the end (must be nothing: no
reservation leaks), waits, lowered thumbnails, refusals, unreserved text requests, stopped
searches, renders and worker statistics; the photo pool's peak, evictions, refusals and
`photoMismatch` (expected 0), the deep zoom steps, status line and peak. -/
def smokeInterleave (st : IO.Ref State) (dir : String) (rounds : Nat := 8) (zoomSteps : Nat := 4) :
    IO Unit := do
  let mut deepSteps := 0
  let path := (← st.get).path.getD ""
  let t0 ← IO.monoNanosNow
  st.modify ({ · with panel := .thumbnails })
  openFile st path
  if !(← st.get).outlineShown then showSidebar st (some .thumbnails)
  if (← st.get).panel != .thumbnails then showPanel st .thumbnails
  let pump (ms : Nat) : IO Unit := do
    let t ← IO.monoMsNow
    let stop := t + ms
    while (← IO.monoMsNow) < stop do
      discard <| run ["update"]
      IO.sleep 5
  let rssNow : IO Nat := do
    let (r, _) ← memKiB
    if r > 0 then return r
    try
      let o ← IO.Process.output { cmd := "ps", args := #["-o", "rss=", "-p", toString (← IO.Process.getPID)] }
      return o.stdout.trimAscii.toString.toNat?.getD 0
    catch _ => return 0
  let mut log : Array String := #[]
  pump 500
  for r in [0:rounds] do
    for _ in [0:zoomSteps] do
      discard <| run ["::safepdf::emit", "zoom", "in"]
      pump 250
    find st ["next", "the"]
    pump 250
    find st ["next", "zqxjkvw"]
    pump 250
    discard <| run [".ol.th", "yview", "moveto", fmtFracFine ((r : Rat) / (rounds : Rat))]
    discard <| run ["::safepdf::emit", "thView"]
    pump 250
    discard <| run ["::safepdf::emit", "next"]
    pump 250
    discard <| run ["::safepdf::emit", "next"]
    pump 250
    for _ in [0:zoomSteps] do
      discard <| run ["::safepdf::emit", "zoom", "out"]
      pump 250
    let s ← st.get
    log := log.push s!"round {r}: page {s.page + 1} pool-used {s.pool.used} held {s.pool.held.length} jobs {s.jobs.size} thumbs {s.thJobs.size} rss-kib {← rssNow} photo-pool {s.photoPool.used} cache {s.cache.bytes} status {← run [".status", "cget", "-text"]}"
  -- Task 12.3b: the deep zoom phase — 600 % and 800 %, scrolled through the document.
  let mut rssPeak := 0
  for pct in ["600", "800"] do
    zoomChoose st pct
    pump 600
    for k in [0:12] do
      discard <| run [".c", "yview", "moveto", fmtFracFine ((k : Rat) / 12)]
      viewChanged st
      pump 400
      let s ← st.get
      let rss ← rssNow
      deepSteps := deepSteps + 1
      rssPeak := max rssPeak rss
      let px := s.photos.foldl (fun n (_, r) => match r with | .ok i => n + i.w * i.h | _ => n) 0
      log := log.push s!"zoom {pct} step {k}: page {s.page + 1} photos {s.photos.size} photo-px {px} photo-pool {s.photoPool.used} cache {s.cache.bytes} pool-used {s.pool.used} jobs {s.jobs.size} rss-kib {rss}"
  log := log.push s!"zoom-status: {← run [".status", "cget", "-text"]}"
  zoomChoose st "auto"
  pump 500
  log := log.push s!"zoom-rss-peak-kib: {rssPeak}"
  -- Everything in flight finishes; then the pool must be empty.
  settle st
  thumbSettle st
  for j in (← st.get).textJobs ++ (← st.get).linkJobs do discard <| IO.wait j.task
  sweepSide st
  let t1 ← IO.monoNanosNow
  let s ← st.get
  let spawns ← match s.worker with
    | some ses => pure (← ses.state.get).spawns
    | none => pure 0
  let timeouts ← match s.worker with
    | some ses => pure (← ses.state.get).timeouts
    | none => pure 0
  let kills ← match s.worker with
    | some ses => pure (← ses.state.get).kills
    | none => pure 0
  let fields : List String := [s!"file: {path}", s!"pages: {s.pageCount}", s!"rounds: {rounds}",
    s!"elapsed-ms: {formatMs (t1 - t0)}", s!"pool-ceiling: {s.pool.ceiling}",
    s!"pool-peak: {s.poolPeak}", s!"pool-used-end: {s.pool.used}",
    s!"pool-held-end: {s.pool.held.length}", s!"waits: {s.budgetWaits}",
    s!"degraded: {s.budgetDegraded}", s!"refused: {s.budgetRefused}",
    s!"unreserved: {s.budgetUnreserved}", s!"search-stops: {s.searchStops}",
    s!"renders: {s.renders}", s!"worker-renders: {s.workerRenders}",
    s!"worker-texts: {s.workerTexts}", s!"thumbs-rendered: {s.thRendered}",
    s!"spawns: {spawns}", s!"timeouts: {timeouts}", s!"kills: {kills}",
    s!"worker: {s.worker.isSome}", s!"photo-ceiling: {s.photoPool.ceiling}",
    s!"photo-peak: {s.photoPeak}", s!"photo-used-end: {s.photoPool.used}",
    s!"photo-evicted: {s.photoEvicted}", s!"photo-refused: {s.photoRefused}",
    s!"photo-mismatch: {← photoMismatch st}", s!"deep-zoom-steps: {deepSteps}", "done"]
  IO.FS.writeFile ((dir : System.FilePath) / "interleave.txt")
    ("\n".intercalate (log.toList ++ fields) ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of the attachments panel (`SAFEPDF_VIEWER_SMOKE_MODE=attach`, task 9.r10), on
the generated `att.pdf` (`/PageMode /UseAttachments`, an outline, two files in the
`/EmbeddedFiles` tree, one external file specification, a file attachment annotation on page
2) with `outline.pdf` and `noatt.pdf` beside it. Writes `attach.txt`: the panel as opened
(sidebar, panel, switcher buttons, toggle), the rows before any decoding (name and size
column) and two tooltips (one probed, `attProbe`); Save attachment as… of every row to
`save-N.bin` in `DIR` (the dialog answered by `::safepdf::autoPath`; the dialog's proposed
name); the refused targets (the opened PDF, a read-only file, a read-only folder, a folder);
the switcher buttons; the sidebar toggle; a click on the annotation's icon (sidebar closed on
the outline panel before) selects its row; the other two files (no attachments button). -/
def smokeAttach (st : IO.Ref State) (dir : String) : IO Unit := do
  let base := dirOf ((← st.get).path.getD "")
  let mut out : Array String := #[]
  let panelRow (name : String) : IO String := do
    discard <| run ["update"]
    let s ← st.get
    return s!"{name}: shown={s.outlineShown} panel={s.panel.info.key} \
      outlineBtn={← run ["winfo", "ismapped", ".ol.sw.outline"]} \
      attBtn={← run ["winfo", "ismapped", ".ol.sw.attachments"]} \
      list={← run ["winfo", "ismapped", ".ol.at"]} \
      toggle={← run ["winfo", "ismapped", ".bar.sidebar"]} atts={s.attList.size}"
  let status : IO String := run [".status", "cget", "-text"]
  let rowsNow : IO String := do
    let items := (← run [".ol.at", "children", ""]).splitOn " " |>.filter (!·.isEmpty)
    let mut rows : Array String := #[]
    for i in items do
      rows := rows.push s!"{← run [".ol.at", "item", i, "-text"]}|{← run [".ol.at", "set", i, "size"]}"
    return ";".intercalate rows.toList
  out := out.push (← panelRow "start")
  out := out.push s!"rows: {← rowsNow}"
  let tip (i : Nat) : IO String := do
    return (← run ["set", s!"::safepdf::attTip(a{i})"]).replace "\n" " / "
  out := out.push s!"tip0: {← tip 0}"
  out := out.push s!"tip1: {← tip 1}"
  -- The tooltip's probe decodes data.bin (its size is not in the file).
  discard <| run ["::safepdf::emit", "attProbe", "0"]
  out := out.push s!"probed: {← rowsNow} tip0={← tip 0}"
  -- Save attachment as… for every row.
  let n := (← st.get).attList.size
  for k in [0:n] do
    discard <| run ["set", "::safepdf::lastDialog", ""]
    discard <| run ["set", "::safepdf::autoPath", s!"{dir}/save-{k}.bin"]
    discard <| run ["::safepdf::emit", "attSave", toString k]
    let dlg ← run ["lindex", ← run ["set", "::safepdf::lastDialog"], "1"]
    out := out.push s!"save-{k}: proposed={dlg} status={← status}"
  -- Refused targets: the opened PDF, a read-only file, a read-only folder, a folder.
  let some pdf := (← st.get).path | return
  IO.FS.writeFile s!"{dir}/ro.bin" "read-only\n"
  discard <| run ["file", "attributes", s!"{dir}/ro.bin", "-permissions", "0444"]
  IO.FS.createDirAll s!"{dir}/rodir"
  discard <| run ["file", "attributes", s!"{dir}/rodir", "-permissions", "0555"]
  for (nm, target) in [("pdf", pdf), ("ro", s!"{dir}/ro.bin"), ("rodir", s!"{dir}/rodir/x.bin"),
      ("folder", dir)] do
    discard <| run ["set", "::safepdf::autoPath", target]
    discard <| run ["::safepdf::emit", "attSave", "0"]
    out := out.push s!"refused-{nm}: {← status}"
  discard <| run ["file", "attributes", s!"{dir}/rodir", "-permissions", "0755"]
  discard <| run ["set", "::safepdf::autoPath", ""]
  -- The selection's status line and the context menu's entry.
  discard <| run [".ol.at", "selection", "set", "a1"]
  discard <| run ["update"]
  out := out.push s!"select-a1: {← status}"
  out := out.push s!"menu: {← run [".attmenu", "entrycget", "0", "-label"]}"
  -- The switcher and the toggle.
  discard <| run ["::safepdf::btnInvoke", ".ol.sw.outline"]
  out := out.push (← panelRow "switch-outline")
  discard <| run ["::safepdf::btnInvoke", ".ol.sw.attachments"]
  out := out.push (← panelRow "switch-attachments")
  discard <| run ["::safepdf::btnInvoke", ".bar.sidebar"]
  out := out.push (← panelRow "toggle-off")
  discard <| run ["::safepdf::btnInvoke", ".bar.sidebar"]
  out := out.push (← panelRow "toggle-on")
  -- The annotation's icon on page 2: with the sidebar closed on the outline panel, a click on
  -- it opens the attachments panel and selects its row.
  showPanel st .outline
  showSidebar st none
  let s ← st.get
  if let some ic := s.attIcons.head? then
    goTo st ic.page
    settle st
    let s ← st.get
    if let some sl := slotOf s ic.page then
      let (x0, y0, x1, y1) := sl.rect (Box.ofRect ic.rect)
      let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
        View.parseDecimal (← run [".c", "canvasy", "0"])) | return
      let wx := toString ((x0 + x1) / 2 - vx).floor
      let wy := toString ((y0 + y1) / 2 - vy).floor
      sendEvent ".c" "<ButtonPress-1>" ["-x", wx, "-y", wy]
      sendEvent ".c" "<ButtonRelease-1>" ["-x", wx, "-y", wy]
      discard <| run ["update"]
      out := out.push s!"{← panelRow "icon"} sel={← run [".ol.at", "selection"]} \
        entry={ic.entry} status={← status}"
  -- A file with an outline and no attachments; a file with neither.
  for f in ["outline", "noatt"] do
    openFile st s!"{base}/{f}.pdf"
    settle st
    out := out.push (← panelRow f)
  out := out.push "done"
  IO.FS.writeFile ((dir : System.FilePath) / "attach.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of the layers panel (`SAFEPDF_VIEWER_SMOKE_MODE=layers`, task 9.r11b), on the
generated `oc.pdf` (`/PageMode /UseOC`; one page whose squares and words belong to the groups
Base (ON), Extra (OFF), Notes (ON), the radio pair English (ON) / French (OFF) under the
heading "Languages", Locked (locked, ON, nested under Notes), Orphan (ON, not in `/Order`: under
"Additional Layers", collapsed at first) and an OCMD AllOn(Base, Extra)) with `oc-nomode.pdf`, `oc-noorder.pdf` and `plain.pdf` beside it.
Writes `layers.txt`: the panel as opened and its rows (as Tk shows them); the page's pixels
at each square and the search hits of each word; a thumbnail pixel before and after; toggling
Extra (its square, the OCMD square and its word appear); French (English goes off); the locked
group (no change); Additional Layers opened and Orphan toggled off and on; collapsing the
heading; a note saved into the file (Ctrl+S, Overwrite) and
the reopen after the save (state kept); opening the file again (defaults); the other files.
The smoke script runs it on a copy of `oc.pdf` (`saved.pdf`), so the original stays. -/
def smokeLayers (st : IO.Ref State) (dir : String) : IO Unit := do
  let base := dirOf ((← st.get).path.getD "")
  let mut out : Array String := #[]
  let status : IO String := run [".status", "cget", "-text"]
  let panelRow (name : String) : IO String := do
    discard <| run ["update"]
    let s ← st.get
    return s!"{name}: shown={s.outlineShown} panel={s.panel.info.key} \
      layersBtn={decide ((← run ["winfo", "manager", ".ol.sw.layers"]) == "pack")} \
      list={← run ["winfo", "ismapped", ".ol.ly"]} rows={s.lyRows.length} \
      title={← run [".ol.h", "cget", "-text"]}"
  let tagText (tag : String) : IO String := do
    match (← run [".ol.ly", "tag", "ranges", tag]).splitOn " " with
    | [a, b] => run [".ol.ly", "get", a, b]
    | _ => pure "?"
  -- The rows as Tk shows them: depth, label, kind, checkbox value, disabled, mapped.
  let rowsNow : IO String := do
    discard <| run ["update"]
    let s ← st.get
    let mut parts : Array String := #[]
    let mut i := 0
    for r in s.lyRows do
      let w := s!".ol.ly.c{i}"
      if r.group.isSome then
        let v ← run ["set", s!"::safepdf::ly({i})"]
        parts := parts.push s!"{r.depth}:{← tagText s!"g{i}"}:{v}\
          {if (← run [w, "instate", "disabled"]) == "1" then ":locked" else ""}\
          {if (← run ["winfo", "ismapped", w]) == "1" then "" else ":hidden"}"
      else
        parts := parts.push s!"{r.depth}:[{← tagText s!"h{i}"}]"
      i := i + 1
    return ";".intercalate parts.toList
  let rowOf (label : String) : IO Nat := do
    return ((← st.get).lyRows.findIdx? (·.label == label)).getD 9999
  let invoke (label : String) : IO Unit := do
    discard <| run [s!".ol.ly.c{← rowOf label}", "invoke"]
    settle st
  -- Square centres (page points) and the pixel colour there.
  let squares : List (String × Pt) := [("base", ⟨100, 650⟩), ("extra", ⟨250, 650⟩),
    ("ocmd", ⟨400, 650⟩), ("en", ⟨100, 450⟩), ("fr", ⟨250, 450⟩), ("locked", ⟨400, 450⟩),
    ("orphan", ⟨100, 250⟩)]
  let pixels : IO String := do
    discard <| run ["update"]
    let mut parts : Array String := #[]
    for (n, q) in squares do parts := parts.push s!"{n}=({← photoPixel st 0 q})"
    return " ".intercalate parts.toList
  let hits : IO String := do
    match ← pageIndex st 0 with
    | .ok ix =>
      let mut parts : Array String := #[]
      for w in ["alpha", "bravo", "english", "french", "always"] do
        parts := parts.push s!"{w}={(ix.hits (Select.normQuery w)).size}"
      return " ".intercalate parts.toList
    | .error e => return s!"error {e}"
  -- The thumbnail of page 1 at the Extra square (thumbnail pixels: page point × zoom).
  let thumbPx : IO String := do
    discard <| run ["::safepdf::btnInvoke", ".ol.sw.thumbnails"]
    thumbSettle st
    let s ← st.get
    let some doc := s.doc | return "-"
    let z := thumbZoom s doc 0
    let x := ((250 : Rat) * z).floor
    let y := (((792 : Rat) - 650) * z).floor
    let px ← try run [thumbPhoto 0, "get", toString x, toString y] catch _ => pure "<none>"
    discard <| run ["::safepdf::btnInvoke", ".ol.sw.layers"]
    return s!"have={s.thHave.contains 0} px=({px})"
  settle st
  out := out.push s!"{← panelRow "start"} status={← status}"
  out := out.push s!"rows: {← rowsNow}"
  out := out.push s!"px-start: {← pixels}"
  out := out.push s!"text-start: {← hits}"
  out := out.push s!"thumb-start: {← thumbPx}"
  out := out.push (← panelRow "back")
  -- Extra on: its square and word, and the OCMD square (AllOn Base, Extra).
  invoke "Extra"
  out := out.push s!"extra-on: {← rowsNow}"
  out := out.push s!"px-extra: {← pixels}"
  out := out.push s!"text-extra: {← hits}"
  -- The radio pair: French on turns English off.
  invoke "French"
  out := out.push s!"french-on: {← rowsNow}"
  out := out.push s!"px-french: {← pixels}"
  out := out.push s!"text-french: {← hits}"
  -- The locked group: its disabled checkbox does nothing, nor does the event itself.
  invoke "Locked"
  discard <| run ["::safepdf::emit", "layer", toString (← rowOf "Locked")]
  settle st
  out := out.push s!"locked: {← rowsNow} status={← status}"
  out := out.push s!"px-locked: {← pixels}"
  -- Additional Layers (the groups not in /Order) starts collapsed; opened, Orphan toggles.
  let aRow := ((← st.get).lyRows.findIdx? (·.italic)).getD 9999
  discard <| run ["::safepdf::emit", "lyToggle", toString aRow]
  out := out.push s!"additional-open: {← rowsNow}"
  invoke "Orphan"
  out := out.push s!"orphan-off: {← rowsNow}"
  out := out.push s!"px-orphan: {← pixels}"
  invoke "Orphan"
  out := out.push s!"px-orphan-on: {← pixels}"
  -- Collapsing the heading hides its checkboxes; opening shows them again.
  let hRow := ((← st.get).lyRows.findIdx? (·.group.isNone)).getD 9999
  discard <| run ["::safepdf::emit", "lyToggle", toString hRow]
  out := out.push s!"collapsed: {← rowsNow}"
  discard <| run ["::safepdf::emit", "lyToggle", toString hRow]
  out := out.push s!"expanded: {← rowsNow}"
  out := out.push s!"thumb-after: {← thumbPx}"
  -- A note saved into the file: the reopen after the save keeps the layers' state.
  smokeNoteAt st 500 100 "layers"
  discard <| run ["set", "::safepdf::autoAnswer", "overwrite"]
  sendEvent ".c" "<Control-Key-s>"
  settle st
  out := out.push s!"{← panelRow "saved"} dirty={(← st.get).marks.dirty} status={← status}"
  out := out.push s!"saved-rows: {← rowsNow}"
  out := out.push s!"px-saved: {← pixels}"
  -- Opened again: the document's default state.
  openFile st ((← st.get).path.getD "")
  settle st
  out := out.push (← panelRow "reopened")
  out := out.push s!"reopened-rows: {← rowsNow}"
  out := out.push s!"px-reopened: {← pixels}"
  out := out.push s!"text-reopened: {← hits}"
  for f in ["oc-nomode", "oc-noorder", "plain"] do
    openFile st s!"{base}/{f}.pdf"
    settle st
    out := out.push s!"{← panelRow f} status={← status}"
    out := out.push s!"{f}-rows: {← rowsNow}"
  out := out.push "done"
  IO.FS.writeFile ((dir : System.FilePath) / "layers.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- Smoke steps of delete and undo/redo on marks (`SAFEPDF_VIEWER_SMOKE_MODE=undo`, task 10.7)
on a copy of the text PDF of `smokeText` (substitute fonts off: the page is white where the
words are). `world` is highlighted (Edit → Highlight selection), selected by a click and
removed with Backspace (white again); Ctrl+Z brings it back (tinted pixels), Ctrl+Shift+Z
removes it again; two more Ctrl+Z go back to before the highlight (clean, Undo disabled), a
Ctrl+Shift+Z redoes it. A note at a blank point gets the text `first`, then `second`; Ctrl+Z
gives back `first`, then the empty new note, then no note; Ctrl+Shift+Z twice gives `first`
again. Ctrl+S (answered Overwrite) saves the highlight and the note and reopens the file (the
history is cleared). The saved highlight is selected and deleted with Delete (dirty, white);
Ctrl+Z restores it (clean again, the saved mark shown from the file: tinted, Save disabled);
it is recoloured green and Ctrl+S writes that: the reopened file holds both marks, the
highlight green with its id. With the highlight selected, Backspace and Delete typed into the
find entry and into the note's popup edit their text (marks, selection and page unchanged).
Each click takes `world`'s position from the current view and carries its own `-time` (task
10.14: untimed clicks were double clicks on Aqua; the word they selected anchored the note to
the highlight's quads, making it the comment that Delete removes with the highlight). Results
in `undo.txt`. -/
def smokeUndo (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let k := saveKit st
  let mut out : Array String := #[]
  discard <| run ["update"]
  let .ok ix ← pageIndex st 0 | throw (IO.userError "no text index")
  let boxOf (q : String) : Option Box := do
    let (a, b) ← (ix.hits (Select.normQuery q))[0]?
    (Select.rangeBoxes ix.cells a b).head?
  let some world := boxOf "world" | throw (IO.userError "word not found")
  -- Tinted (coloured) pixels among 7 × 3 points inside a box: 0 without a highlight.
  let tinted (b : Box) : IO Nat := do
    let mut n := 0
    for i in [1:8] do
      for j in [1:4] do
        let q : Pt := ⟨b.llx + (b.urx - b.llx) * i / 8, b.lly + (b.ury - b.lly) * j / 4⟩
        let cs := ((← k.px q).splitOn " ").filterMap String.toNat?
        if cs.length == 3 && (cs.foldl max 0) - (cs.foldl min 255) > 40 then n := n + 1
    return n
  let shade : IO String := return if (← tinted world) > 0 then "tinted" else "white"
  let count : IO Nat := return (← st.get).marks.marks.size
  let undoKey : IO Unit := sendEvent ".c" "<Control-Key-z>"
  let redoKey : IO Unit := sendEvent ".c" "<Control-Key-Z>"
  let states : IO String := return s!"{← k.menuState .undo} {← k.menuState .redo}"
  let path := (← st.get).path.getD ""
  -- Task 10.14: `world`'s window position is taken from the current view before each click
  -- (Save reopens the file, which can scroll), scrolled into the window first when it is
  -- outside; every click carries an explicit `-time` 2 s after the previous one (Tk Aqua counts
  -- generated clicks without `-time` as double clicks, which select the word under them).
  let wposNow : IO (String × String) := do
    settle st
    let s ← st.get
    let some bx := shownBox s | throw (IO.userError "world not shown")
    let (x0, y0, x1, y1) := canvasRect s bx world
    let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
      View.parseDecimal (← run [".c", "canvasy", "0"])) | throw (IO.userError "no view")
    if y0 < vy || vy + (s.canvasH : Rat) < y1 then
      discard <| run [".c", "yview", "moveto",
        fmtFrac (((y0 + y1) / 2 - (s.canvasH : Rat) / 2) / (s.regionH : Rat))]
    if x0 < vx || vx + (s.canvasW : Rat) < x1 then
      discard <| run [".c", "xview", "moveto",
        fmtFrac (((x0 + x1) / 2 - (s.canvasW : Rat) / 2) / (s.regionW : Rat))]
    settle st
    let some p ← boxWindowPos st world | throw (IO.userError "world not shown")
    return p
  let clock ← IO.mkRef ((← IO.monoMsNow) % 1000000000)
  -- `n` press/release pairs 1 ms apart (2: a double click), 2 s after the last click.
  let clicks (n : Nat) : IO Unit := do
    let pos ← wposNow
    clock.modify (· + 2000)
    for i in [0:n] do
      let t := toString ((← clock.get) + i)
      sendEvent ".c" "<ButtonPress-1>" ["-x", pos.1, "-y", pos.2, "-time", t]
      sendEvent ".c" "<ButtonRelease-1>" ["-x", pos.1, "-y", pos.2, "-time", t]
    discard <| run ["update", "idletasks"]
  -- The click's selection: (a mark selected, a text selection).
  let selState : IO String := do
    let s ← st.get
    return s!"{s.markSel.isSome} {s.sel.isSome}"
  out := out.push s!"start: {← count} {← shade} {← states}"
  -- 1. Highlight `world`, select it, Backspace removes it.
  clicks 2
  discard <| run [".menubar.edit", "invoke", Menu.Cmd.highlight.label]
  syncMenus st
  out := out.push s!"highlighted: {← count} {← shade} {(← st.get).marks.dirty} {← states}"
  clicks 1
  let hid := (← st.get).markSel
  out := out.push s!"select-click: {← selState}"
  sendKey "BackSpace"
  syncMenus st
  out := out.push s!"backspace: {hid.isSome} {← count} {← shade} {← states}"
  -- 2. Undo brings it back, redo removes it again.
  undoKey
  syncMenus st
  out := out.push s!"undo-delete: {← count} {← shade} {((← st.get).marks.marks.toList.map (·.id)) == hid.toList} {← states}"
  redoKey
  syncMenus st
  out := out.push s!"redo-delete: {← count} {← shade} {← states}"
  -- 3. Back to before the highlight: clean, nothing more to undo; redo highlights again.
  undoKey
  undoKey
  syncMenus st
  out := out.push s!"undo-all: {← count} {← shade} {(← st.get).marks.dirty} {← k.star} {← states}"
  undoKey
  out := out.push s!"undo-empty: {← count} {← k.status}"
  redoKey
  syncMenus st
  out := out.push s!"redo-highlight: {← count} {← shade} {← states}"
  -- 4. A note: `first`, then `second`; undo steps back through its texts and its creation.
  smokeNoteAt st 300 400 "first"
  discard <| run ["destroy", ".note"]
  let noteText : IO String := do
    let s ← st.get
    return ((s.marks.marks.toList.find? (·.isNote)).map (·.text)).getD "<none>"
  let nid := ((← st.get).marks.marks.toList.find? (·.isNote)).map (·.id)
  out := out.push s!"note: {nid.isSome} {← noteText} {← states}"
  -- Anchored at its point, not to a (stale) word selection: that would make it the
  -- highlight's comment, which Delete on the highlight removes with it (9.5g).
  let anchorKind (m : Marks.Mark) : String := if m.quads.isEmpty then "point" else "quads"
  out := out.push s!"note-anchor: {((← st.get).marks.marks.toList.find? (·.isNote)).map anchorKind}"
  if let some n := nid then noteSave st (toString n) "second"
  out := out.push s!"note-edited: {← noteText}"
  undoKey
  out := out.push s!"note-undo1: {← noteText}"
  undoKey
  out := out.push s!"note-undo2: [{← noteText}]"
  undoKey
  out := out.push s!"note-undo3: {← noteText} {← count}"
  redoKey
  redoKey
  syncMenus st
  out := out.push s!"note-redo: {← noteText} {← count} {← states}"
  -- 5. Save (Overwrite): the history starts again with the reopened file.
  discard <| run ["set", "::safepdf::autoAnswer", "overwrite"]
  sendEvent ".c" "<Control-Key-s>"
  syncMenus st
  let s1 ← st.get
  out := out.push s!"saved: {s1.path == some path} {s1.marks.marks.size} {s1.marks.dirty} {← k.star} {← shade} {← states}"
  -- 6. The saved highlight: Delete, undo (clean again, drawn from the file).
  clicks 1
  out := out.push s!"saved-select: {← selState}"
  let sid := (← st.get).markSel
  let savedSel := sid.any (← st.get).marks.isSaved
  sendKey "Delete"
  syncMenus st
  out := out.push s!"saved-delete: {savedSel} {← count} {(← st.get).marks.dirty} {← k.star} {← shade} {← k.menuState .save}"
  undoKey
  syncMenus st
  let s2 ← st.get
  out := out.push s!"saved-undo: {← count} {s2.marks.dirty} {← k.star} {← shade} {← k.menuState .save} {(sid.bind s2.marks.find?).isSome} {s2.view.isNone}"
  -- 7. Recoloured green and saved: the file holds both marks, the highlight green.
  clicks 1
  discard <| run [".menubar.edit.hl", "invoke", Marks.Color.green.label]
  sendEvent ".c" "<Control-Key-s>"
  syncMenus st
  let s3 ← st.get
  out := out.push s!"resaved: {s3.marks.marks.size} {s3.marks.dirty} {((sid.bind s3.marks.find?).map (·.color.name))} {← k.px ⟨(world.llx + world.urx) / 2, (world.lly + world.ury) / 2⟩} {← states}"
  out := out.push s!"file-marks: {← fileMarks path}"
  -- 8. With the highlight selected, Backspace and Delete typed into the find bar's entry and
  -- into a note popup's text edit the text there; the marks and the page stay.
  clicks 1
  let pg0 := (← st.get).page
  sendEvent ".c" "<Control-Key-f>"
  discard <| run ["update"]
  discard <| run [".find.e", "delete", "0", "end"]
  discard <| run [".find.e", "insert", "end", "abcd"]
  discard <| run [".find.e", "icursor", "2"]
  sendEvent ".find.e" "<Key-BackSpace>"
  sendEvent ".find.e" "<Key-Delete>"
  out := out.push s!"find-keys: {← run [".find.e", "get"]} {← count} {← selState} {(← st.get).page == pg0}"
  sendEvent ".find.e" "<Key-Escape>"
  if let some n := (← st.get).marks.marks.toList.find? (·.isNote) then
    openNote st n.id
    discard <| run ["update"]
    discard <| run [".note.t", "mark", "set", "insert", "1.2"]
    sendEvent ".note.t" "<Key-BackSpace>"
    sendEvent ".note.t" "<Key-Delete>"
    out := out.push s!"note-keys: {← run [".note.t", "get", "1.0", "end-1c"]} {← count} {(← st.get).page == pg0}"
    discard <| run ["destroy", ".note"]
  -- 9. Right-click → Add note… (task 10.17, `addNote st (some pos)`): far from a word
  -- selection it is a point note; inside the selection it is a comment on it (quads).
  let noteKind : IO String := do
    let s ← st.get
    return ((s.markSel.bind s.marks.find?).map anchorKind).getD "<none>"
  clicks 2
  let selected := (← st.get).sel.isSome
  let pos ← wposNow
  let (some px0, some py0) := (pos.1.toInt?, pos.2.toInt?) | throw (IO.userError "bad position")
  addNote st (some (px0, py0 + 150))
  out := out.push s!"note-far: {selected} {← noteKind} {(← st.get).sel.isSome}"
  discard <| run ["destroy", ".note"]
  clicks 2
  let pos1 ← wposNow
  let (some px1, some py1) := (pos1.1.toInt?, pos1.2.toInt?) | throw (IO.userError "bad position")
  addNote st (some (px1, py1))
  out := out.push s!"note-inside: {← noteKind} {(← st.get).sel.isSome}"
  discard <| run ["destroy", ".note"]
  IO.FS.writeFile (file "undo.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- The tint photos that exist (`::safepdf::tint`, task 10.10). -/
def tintImages : IO Nat := do
  let l ← run ["lsearch", "-all", "-inline", ← run ["image", "names"], "::safepdf::tint_*"]
  return (l.splitOn " ").filter (!·.isEmpty) |>.length

/-- Milliseconds (two decimals) of `k` runs of `act`, averaged. -/
def timeMs (k : Nat) (act : IO Unit) : IO String := do
  let t0 ← IO.monoNanosNow
  for _ in [0:k] do act
  let t1 ← IO.monoNanosNow
  let us := (t1 - t0) / (1000 * max 1 k)
  let frac := (us % 1000) / 10
  return s!"{us / 1000}.{if frac < 10 then "0" else ""}{frac}"

/-- Smoke steps of the highlight fills (`SAFEPDF_VIEWER_SMOKE_MODE=tint`, task 10.10) on a page
whose first line is `Hello safe world` over a black marker under `safe` (as 1d) and whose
other lines repeat `safe` (hundreds of search hits; non-embedded Helvetica unpainted). Writes
`tint.txt`: the item kind of the selection (Ctrl+A) and of the hits (search `safe`), item and
tint photo counts, and probes — at a canvas point, the items there bottom to top as
`tag=kind`, image items with their pixel `(R G B A)` — over the marker (ink) and over white
paper, for the selection, the current hit and another hit; drawing times of the overlays
(average of 5 `drawOverlay` + `update idletasks`) as tint photos and as stippled rectangles,
and the cost of filling one page-sized photo (option (b), a full overlay image, for
comparison). Background mode cannot capture the composited window, so the smoke test
composites the probed page and fill pixels itself. -/
def smokeTint (st : IO.Ref State) (dir : String) : IO Unit := do
  let file (name : String) : String := ((dir : System.FilePath) / name).toString
  let mut out : Array String := #[]
  settle st
  discard <| run ["update"]
  out := out.push s!"aqua: {!(← st.get).stipple}"
  out := out.push s!"tk: {← run ["package", "provide", "Tk"]} rgba-put={← run ["set", "::safepdf::tintRgba"]} get-alpha={← run ["set", "::safepdf::getAlpha"]}"
  let .ok ix ← pageIndex st (← st.get).page | do
    IO.FS.writeFile (file "tint.txt") "error: no text index\n"
    discard <| run ["destroy", "."]
  let hits := ix.hits (Select.normQuery "safe")
  let boxOf (k : Nat) : Option Box := do
    let (a, b) ← hits[k]?
    (Select.rangeBoxes ix.cells a b).head?
  let (some safe, some other, some hello) := (boxOf 0, boxOf 1, (ix.cells[0]?).map (·.box)) | do
    IO.FS.writeFile (file "tint.txt") "error: words not found\n"
    discard <| run ["destroy", "."]
  let centre (b : Box) : Pt := ⟨(b.llx + b.urx) / 2, (b.lly + b.ury) / 2⟩
  -- Inside the black marker (y 700–712.6) under `safe`.
  let inkPt : Pt := ⟨(safe.llx + safe.urx) / 2, 706⟩
  let probe (p : Pt) : IO String := do
    let s ← st.get
    let some bx := shownBox s | return "<no page>"
    let (cx, cy, _, _) := canvasRect s bx ⟨p.x, p.y, p.x, p.y⟩
    let (x, y) := (cx.floor, cy.floor)
    let ids := ((← run [".c", "find", "overlapping", toString x, toString y, toString x,
      toString y]).splitOn " ").filter (!·.isEmpty)
    let mut parts : Array String := #[]
    for id in ids do
      let tag := ((← run [".c", "gettags", id]).splitOn " ").headD ""
      let kind ← run [".c", "type", id]
      if kind == "image" then
        let img ← run [".c", "itemcget", id, "-image"]
        let px ← match ((← run [".c", "coords", id]).splitOn " ").filterMap View.parseDecimal with
          | [ix0, iy0] =>
            try run ["::safepdf::pixel", img, toString (x - ix0.floor), toString (y - iy0.floor)]
            catch _ => pure "outside"
          | _ => pure "?"
        parts := parts.push s!"{tag}={kind}({px})"
      else parts := parts.push s!"{tag}={kind}"
    return ";".intercalate parts.toList
  let kindOf (tag : String) : IO String := do
    match ((← run [".c", "find", "withtag", tag]).splitOn " ").head? with
    | some id => if id.isEmpty then pure "none" else run [".c", "type", id]
    | none => pure "none"
  let redraw : IO Unit := do drawOverlay st; discard <| run ["update", "idletasks"]
  -- 1. Select the page.
  sendEvent ".c" "<Control-Key-a>"
  discard <| run ["update"]
  out := out.push s!"sel: kind={← kindOf "sel"} items={← tagCount "sel"} photos={← tintImages}"
  out := out.push s!"sel-ink: {← probe inkPt}"
  out := out.push s!"sel-paper: {← probe (centre hello)}"
  out := out.push s!"ms-sel: {← timeMs 5 redraw}"
  -- 1b. Selection bands (task 10.18): the `sel` items' bounding boxes in drawing order, each
  -- full line's extent (rounded as `drawOverlay`), then a selection from the middle of line 3
  -- to the middle of line 5 (runs 2–4 after the heading) with the canvas x of its start and
  -- end glyphs and a probe in the paper between lines 3 and 4.
  let px (v : Rat) : String := toString (v + 1 / 2).floor
  let bandsNow : IO String := do
    let ids := ((← run [".c", "find", "withtag", "sel"]).splitOn " ").filter (!·.isEmpty)
    let mut bs : Array String := #[]
    for id in ids do bs := bs.push (",".intercalate ((← run [".c", "bbox", id]).splitOn " "))
    return ";".intercalate bs.toList
  let runs := (Select.lineRuns ix.cells 0 (ix.cells.size - 1)).toArray
  let s1 ← st.get
  if let some sl := slotOf s1 s1.page then
    let lineX := runs.toList.map fun (_, _, b) =>
      let (x0, _, x1, _) := sl.rect b
      s!"{px x0},{px x1}"
    out := out.push s!"sel-bands: {← bandsNow}"
    out := out.push s!"sel-lines: {";".intercalate lineX}"
    if let (some (_, i2, b2), some (_, _, b3), some (_, i4, _)) := (runs[2]?, runs[3]?, runs[4]?) then
      let (a, b) := (i2 + 22, i4 + 22)
      st.modify ({ · with sel := some (s1.page, a, b) })
      redraw
      let cx (i : Nat) (hi : Bool) : String := match ix.cells[i]? with
        | some c => let (x0, _, x1, _) := sl.rect c.box; px (if hi then x1 else x0)
        | none => "?"
      out := out.push s!"sel3-bands: {← bandsNow}"
      out := out.push s!"sel3-ends: {cx a false},{cx b true}"
      -- In the paper gap above line 3, a quarter of the way down from line 2's glyph boxes.
      out := out.push s!"sel3-gap: {← probe ⟨(b3.llx + b3.urx) / 2, b3.ury + (b2.lly - b3.ury) / 4⟩}"
      out := out.push s!"sel3-text: {(Select.rangeText ix.cells a b).length}"
  -- 2. Search `safe`: the first hit (current, orange) lies over the marker.
  st.modify ({ · with sel := none })
  sendEvent ".c" "<Control-Key-f>"
  discard <| run ["update", "idletasks"]
  discard <| run ["set", "::safepdf::query", "safe"]
  sendEvent ".find.e" "<Key-Return>"
  discard <| run ["update"]
  out := out.push s!"hit: kind={← kindOf "hit"} items={← tagCount "hit"} photos={← tintImages} status={← run [".status", "cget", "-text"]}"
  out := out.push s!"hit-ink: {← probe inkPt}"
  out := out.push s!"hit-paper: {← probe (centre other)}"
  out := out.push s!"ms-hits: {← timeMs 5 redraw}"
  -- 3. Everything at once, then the same as stippled rectangles (the X11 drawing).
  sendEvent ".c" "<Control-Key-a>"
  discard <| run ["update"]
  out := out.push s!"ms-all: {← timeMs 5 redraw} items={(← tagCount "sel") + (← tagCount "hit")}"
  let stip := (← st.get).stipple
  st.modify ({ · with stipple := !stip })
  out := out.push s!"ms-all-other: {← timeMs 5 redraw} stipple={!stip}"
  st.modify ({ · with stipple := stip })
  redraw
  -- 4. One page-sized overlay photo filled with a translucent colour (option (b)'s floor).
  let pg := photoOf (← st.get).page
  let (w, h) := (← run ["image", "width", pg], ← run ["image", "height", pg])
  let fill : IO Unit := do
    discard <| run ["image", "create", "photo", "::safepdf::tintProbe", "-width", w, "-height", h]
    discard <| run ["::safepdf::tintFill", "::safepdf::tintProbe", Tint.sel.rgb, Tint.sel.alphaHex, w, h]
    discard <| run ["image", "delete", "::safepdf::tintProbe"]
  out := out.push s!"ms-fullpage-photo: {← timeMs 5 fill} size={w}x{h}"
  -- 5. Closing the search and dropping the selection leaves no fill and no photo.
  sendEvent ".find.e" "<Key-Escape>"
  st.modify ({ · with sel := none })
  redraw
  out := out.push s!"closed: items={(← tagCount "sel") + (← tagCount "hit")} photos={← tintImages}"
  out := out.push "done"
  IO.FS.writeFile (file "tint.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- The smoke test of task 12.5 (`SAFEPDF_VIEWER_SMOKE_MODE=honest`, honest UI for hidden
content). The viewer opens `ocr.pdf` (a visible line and a `Tr 3` line); `full.pdf`
(`/PageMode /FullScreen`) and `prefs.pdf` (`/HideToolbar`) lie next to it. Writes `honest.txt`:
* `copy`: select all + copy: the status (it counts the invisible characters) and whether the
  clipboard holds the invisible text;
* `full` / `full-escape`, `prefs` / `prefs-escape`, `plain`: whether the identity line `.ident`
  is packed, its text, and the status (the full-screen note stays, task 10.13);
* `save1`: a highlight saved into `ocr.pdf` (no deleted mark: no notice); `save2`: that saved
  highlight deleted and saved again: the revision-retention notice. -/
def smokeHonest (st : IO.Ref State) (dir : String) : IO Unit := do
  let base := dirOf ((← st.get).path.getD "")
  let mut out : Array String := #[]
  let status : IO String := run [".status", "cget", "-text"]
  let ident : IO String := do
    discard <| run ["update"]
    return s!"ident={← run ["winfo", "manager", ".ident"]} full={(← st.get).fullScreen} \
      text={← run [".ident", "cget", "-text"]}"
  settle st
  -- 1. Copy with invisible text.
  selectAll st
  copySel st
  let clip ← try run ["clipboard", "get"] catch _ => pure "<empty>"
  out := out.push s!"copy: hidden-in-clipboard={decide ((clip.splitOn "hidden words").length > 1)} \
    status={← status}"
  out := out.push s!"plain: {← ident}"
  -- 2. The identity line in document full screen and with hidden chrome.
  let ocr := (← st.get).path.getD ""
  for f in ["full", "prefs"] do
    openFile st s!"{base}/{f}.pdf"
    settle st
    out := out.push s!"{f}: {← ident} status={← status}"
    if f == "full" && (← isAqua) then
      discard <| run ["after", "1000"]
      discard <| run ["update"]
    discard <| escapeWindow st
    settle st
    out := out.push s!"{f}-escape: {← ident}"
  -- 3. Delete a saved mark, save: the revision-retention notice.
  discard <| run ["set", "::safepdf::autoAnswer", "overwrite"]
  openFile st ocr
  settle st
  selectAll st
  highlight st none
  discard <| save st (confirmed := true)
  out := out.push s!"save1: marks={(← st.get).marks.marks.size} saved={(← st.get).marks.saved.length} \
    status={← status}"
  match (← st.get).marks.marks[0]? with
  | some m =>
    st.modify fun s => { s with marks := s.marks.remove m.id }
    marksChanged st
  | none => pure ()
  out := out.push s!"deleted: dirty={(← st.get).marks.dirty} \
    deletedSaved={(← st.get).marks.deletedSaved.length}"
  discard <| save st (confirmed := true)
  out := out.push s!"save2: marks={(← st.get).marks.marks.size} status={← status}"
  out := out.push "done"
  IO.FS.writeFile ((dir : System.FilePath) / "honest.txt") ("\n".intercalate out.toList ++ "\n")
  discard <| run ["destroy", "."]

/-- One step of the smoke test. Every step but the last schedules the next one 300 ms later
(the prefetch runs 100 ms after a page is shown). Files written into the smoke directory:
* step 0: `f` (fit page; the viewer opens in Automatic Zoom);
* step 1: `page-1.ppm` (fit page), then `Next`;
* step 2: `page-2.ppm`, `state.txt` (title, status, page; the status says whether page 2
  came from the prefetched cache); then `Home`, `0` (100 %);
* step 3: `zoom-100.ppm`, then `+`; step 4: `zoom-in.ppm` (125 %), then `-` `-`;
* step 5: `zoom-out.ppm` (75 %), then `r`; step 6: `rot.ppm` (75 %, 90°), then `R` and
  `+` ×4 (200 %), and the scroll test: `Down`, `Next` must scroll within page 1; `Next`
  repeated must reach page 2; `Prior` at the top of page 2 must reach the bottom of page 1;
  results in `view.txt`.
A document that failed to open ends after step 2. -/
def smoke (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some dir := s.smokeDir | return
  if s.smokeMode == "text" then smokeText st dir; return
  if s.smokeMode == "worker" then
    try smokeWorker st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "worker.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "nav" then smokeNav st dir; return
  if s.smokeMode == "menu" then smokeMenu st dir; return
  if s.smokeMode == "toolbar" then smokeToolbar st dir; return
  if s.smokeMode == "bubble" then
    try smokeBubble st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "bubble.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "save" || s.smokeMode == "reopen" || s.smokeMode == "encrypted" ||
      s.smokeMode == "edit" then
    let name := s!"{s.smokeMode}.txt"
    try
      if s.smokeMode == "save" then smokeSave st dir
      else if s.smokeMode == "reopen" then smokeReopen st dir
      else if s.smokeMode == "edit" then smokeEdit st dir
      else smokeEncrypted st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / name) s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "undo" then
    try smokeUndo st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "undo.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "xfdf" then
    try smokeXfdf st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "xfdf.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "modes" || s.smokeMode == "scroll" then
    let name := s!"{s.smokeMode}.txt"
    try
      if s.smokeMode == "modes" then smokeModes st dir else smokeScroll st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / name) s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "wheelflow" then
    try smokeWheelFlow st dir
    catch e =>
      -- Task 10.c2: appended, after the lines already written.
      appendLine ((dir : System.FilePath) / "wheelflow.txt") s!"error: {e}"
      progressLine s!"wheelflow-progress: error: {e}"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "async" then
    try smokeAsync st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "async.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "keys" then
    try smokeKeys st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "keys.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "r4" then
    try smokeR4 st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "r4.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "honest" then
    try smokeHonest st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "honest.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "opensettings" then
    try smokeOpenSettings st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "opensettings.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "thumbs" || s.smokeMode == "thumbperf" then
    try
      if s.smokeMode == "thumbs" then smokeThumbs st dir else smokeThumbPerf st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / s!"{s.smokeMode}.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "interleave" then
    try smokeInterleave st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "interleave.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "attach" then
    try smokeAttach st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "attach.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "layers" then
    try smokeLayers st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "layers.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "noteclose" then
    try smokeNoteClose st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "noteclose.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "tint" then
    try smokeTint st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "tint.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "dismiss" then
    try smokeDismiss st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "dismiss.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "tools" then
    try smokeTools st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "tools.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "savedlg" then
    try smokeSaveDialogs st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "savedlg.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "lockdown" then
    try smokeLockdown st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "lockdown.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "biblean" then
    try smokeBiblean st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "biblean.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "editors" || s.smokeMode == "editors-shot" then
    try
      if s.smokeMode == "editors" then smokeEditors st dir else smokeEditorsShot st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "editors.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "m9" || s.smokeMode == "m9-reopen" || s.smokeMode == "m9-shot" then
    let name := s!"{s.smokeMode}.txt"
    try
      if s.smokeMode == "m9" then smokeM9 st dir
      else if s.smokeMode == "m9-shot" then smokeM9Shot st dir
      else smokeM9Reopen st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / name) s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  if s.smokeMode == "marks" then
    try smokeMarks st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "marks.txt") s!"error: {e}\n"
      discard <| run ["destroy", "."]
    return
  st.modify ({ · with smokeStep := s.smokeStep + 1 })
  -- Writing an empty photo fails in Tk; that only means there is nothing to write.
  let write (name : String) : IO Unit :=
    try discard <| run [photoOf (← st.get).page, "write", ((dir : System.FilePath) / name).toString,
      "-format", "ppm"]
    catch _ => pure ()
  let next : IO Unit := discard <| run ["after", "300", "::safepdf::emit smoke"]
  let yview : IO String := run [".c", "yview"]
  match s.smokeStep with
  | 0 =>
    -- Fit page first (the default is Automatic Zoom, task 9.7), so that Next turns the page
    -- and the prefetch of page 2 happens before step 1 looks at it.
    sendKey "f"
    next
  | 1 =>
    write "page-1.ppm"
    if s.pageCount ≥ 2 then sendKey "Next"
    next
  | 2 =>
    if s.pageCount ≥ 2 then write "page-2.ppm"
    let title ← run ["wm", "title", "."]
    let status ← run [".status", "cget", "-text"]
    IO.FS.writeFile ((dir : System.FilePath) / "state.txt")
      s!"title: {title}\nstatus: {status}\npage: {(← st.get).page + 1}/{s.pageCount}\n"
    if s.pageCount ≥ 2 then
      sendKey "Home"; sendKey "0"; next
    else discard <| run ["destroy", "."]
  | 3 => write "zoom-100.ppm"; sendKey "plus"; next
  | 4 => write "zoom-in.ppm"; sendKey "minus"; sendKey "minus"; next
  | 5 => write "zoom-out.ppm"; sendKey "r"; next
  | 6 =>
    write "rot.ppm"
    sendKey "R"
    for _ in [0:4] do sendKey "plus"
    let x0 ← run [".c", "xview"]
    let y0 ← yview
    sendKey "Down"
    let y1 ← yview
    sendKey "Next"
    let y2 ← yview
    let p2 := (← st.get).page + 1
    let mut n := 0
    while (← st.get).page == 0 && n < 30 do
      sendKey "Next"; n := n + 1
    let p3 := (← st.get).page + 1
    let y3 ← yview
    sendKey "Prior"
    let p4 := (← st.get).page + 1
    let y4 ← yview
    let s' ← st.get
    IO.FS.writeFile ((dir : System.FilePath) / "view.txt")
      s!"scaling-milli: {(s'.scaling * 1000).floor}\nzoom: {View.zoomPct s'.shownZoom s'.scaling}\n\
        x0: {x0}\ny0: {y0}\ny-down: {y1}\ny-pagedown: {y2}\npage-after-pagedown: {p2}\n\
        pagedowns: {n}\npage-after-pagedowns: {p3}\ny-page2: {y3}\n\
        page-after-prior: {p4}\ny-prior: {y4}\ncache-entries: {s'.cache.entries.size}\n\
        status: {← run [".status", "cget", "-text"]}\n"
    discard <| run ["destroy", "."]
  | _ => discard <| run ["destroy", "."]

/-! ## Events -/

/-- Parses an optional `X Y` window position. -/
def posOf : List String → Option (Nat × Nat)
  | [x, y] => match x.toInt?, y.toInt? with
    | some x, some y => some (x.toNat, y.toNat)
    | _, _ => none
  | _ => none

/-- Parses a window position `X Y` (integers, possibly negative while dragging outside). -/
def intPos (x y : String) : Option (Int × Int) :=
  match x.toInt?, y.toInt? with
  | some x, some y => some (x, y)
  | _, _ => none

/-- Handles one `::safepdf::emit` call. -/
def handle (st : IO.Ref State) (args : Array String) : IO Unit := do
  let s ← st.get
  match args.toList with
  | ["next"] => goTo st (View.nextPage s.spread s.pageCount s.page)
  | ["prev"] => goTo st (View.prevPage s.spread s.page)
  | ["prevEnd"] => goTo st (View.prevPage s.spread s.page) .bottom
  | ["viewChanged"] => viewChanged st
  | ["renderMore"] => renderMore st
  | ["poll"] => poll st
  | ["viewMode", what, key] => setViewMode st what key
  | ["first"] => goTo st 0
  | ["last"] => goTo st (s.pageCount - 1)
  | ["open"] => openDialog st
  | ["smoke"] => smoke st
  | ["prefetch"] => prefetch st
  | ["zoom", "choose", key] => zoomChoose st key
  | "zoom" :: what :: pos => zoom st what (posOf pos)
  | ["rotate", "cw"] => rotate st true
  | ["rotate", "ccw"] => rotate st false
  | ["press", x, y] => if let some (x, y) := intPos x y then press st x y
  | ["drag", x, y] => if let some (x, y) := intPos x y then dragTo st x y false
  | ["release", x, y] => if let some (x, y) := intPos x y then dragTo st x y true
  | ["word", x, y] => if let some (x, y) := intPos x y then selectWord st x y
  | ["selectall"] => selectAll st
  | ["copy"] => copySel st
  | "find" :: rest => find st rest
  | ["hover", x, y] => hover st (intPos x y)
  | ["back"] => histMove st true
  | ["forward"] => histMove st false
  | ["outlineToggle"] =>
    if s.doc.isSome then showSidebar st (Sidebar.afterToggle s.outlineShown s.panel (contentOf s))
    else showOutline st false
  | ["panel", k] => panelClick st k
  | ["attSave", k] => if let some i := k.toNat? then saveAttachment st i
  | ["attProbe", k] => if let some i := k.toNat? then attProbe st i
  | ["attSelect", k] =>
    if let some i := k.toNat? then if let some t := attText s i then setStatus t
  | ["thView"] => thumbView st
  | ["thClick", y] => thumbClick st y
  | ["thKey", k] => thumbKey st k
  | ["thBlur"] =>
    st.modify ({ · with thSel := none })
    discard <| run [".ol.th", "delete", "thfocus"]
  | ["olToggle", k] => olToggle st k
  | ["layer", k] => layerClick st k
  | ["lyToggle", k] => lyToggle st k
  | ["pageEntry", txt] => pageEntry st txt
  | ["pageRevert"] => if s.doc.isSome && s.pageCount > 0 then showPageField s
  | ["tool", name] => tool st name
  | ["highlight"] => highlight st none
  | ["highlight", c] => highlight st (some c)
  | ["note"] => addNote st none
  | ["note", x, y] => addNote st (intPos x y)
  | ["noteSave", id, text] => noteSave st id text
  | ["noteDelete", id] => if let some id := id.toNat? then deleteMark st id
  | ["noteClose", id, text] => noteClose st id text
  | ["markDelete"] => markDelete st
  | ["backspace"] =>
    if s.doc.isSome && s.markSel.isSome then markDelete st
    else discard <| run ["::safepdf::step", "y", "-1", "pages"]
  | ["undo"] => undoRedo st true
  | ["redo"] => undoRedo st false
  | ["hlTool"] => hlToolToggle st
  | ["showAll"] => toggleShowAll st
  | ["escape"] => escape st
  | ["clickAway", w] => clickAway st w
  | ["opening", name] => opening st name
  | ["popClick", x, y] => popClick st x y
  | ["edClick", x, y] => edClick st x y
  | ["edDrag", x, y] => edDrag st x y
  | ["ftCommit"] => discard <| commitFt st
  | ["popDrag", x, y] => popDrag st x y
  | ["popup", x, y, rx, ry] => popup st x y rx ry
  | ["wheel", axis, kind, d] => wheel st axis kind d
  | ["close"] =>
    discard <| commitFt st
    if ← confirmDiscard st "closing" then closeFile st
  | ["save"] => discard <| commitFt st; discard <| save st
  | ["saveAs"] => discard <| commitFt st; discard <| saveAs st
  | ["importXfdf"] => importXfdf st
  | ["exportXfdf"] => exportXfdf st
  | ["quit"] =>
    discard <| commitFt st
    if ← confirmDiscard st "quitting" then discard <| run ["after", "0", "destroy ."]
  | ["outline", id] => outlineClick st id
  | ["goto", txt] => gotoText st txt
  | ["resize", w, h] =>
    match w.toNat?, h.toNat? with
    | some w, some h =>
      if w ≥ 2 && h ≥ 2 && (w, h) != (s.canvasW, s.canvasH) then
        st.modify ({ · with canvasW := w, canvasH := h })
        refresh st
        if (← st.get).ui.popover then syncTool st
    | _, _ => pure ()
  | _ => setStatus s!"internal: unknown event {args}"

/-- Runs `act`, showing an exception in the status line instead of letting it escape into
Tk (stderr when even the status line fails). -/
def guarded (act : IO Unit) : IO Unit := do
  try act
  catch e =>
    try setStatus s!"error: {e}" catch _ => IO.eprintln s!"viewer: {e}"

/-- `handle`, with every exception shown in the status line instead of escaping into Tk;
then the menubar and toolbar enabled states are brought up to date (`syncMenus`). -/
def safeHandle (st : IO.Ref State) (args : Array String) : IO Unit := do
  guarded (handle st args)
  guarded (syncMenus st)

/-- The document worker executable (task 12.2c): `worker` next to the viewer's executable
(`.lake/build/bin/worker` after `lake build`). -/
def workerExe : IO System.FilePath := do
  return (← IO.appDir) / "worker"

/-- The worker's font search, from this process's environment (task 12.2d): the worker reads
no environment, so `SAFEPDF_SUBST_FONTS=0`, `$HOME` (for `~/Library/Fonts`) and
`$SAFEPDF_FONT_DIR` become its flags `--no-subst`, `--home=`, `--font-dir=` — the search
`Fonts.loadSubstFonts` makes here, so both render with the same substitute fonts. -/
def workerStart : IO Worker.Protocol.StartConfig := do
  let noSubst := (← IO.getEnv "SAFEPDF_SUBST_FONTS") == some "0"
  let home := (← IO.getEnv "HOME").filter (!·.isEmpty)
  return { limits, noSubst, home, fontDirs := ← Fonts.userDirs,
           memLimitMiB := Budget.ceilings.workerMemMiB, cpuLimitS := Budget.ceilings.workerCpuS }

/-- Starts the document worker session (task 12.2c), or says why pages render in this process:
`SAFEPDF_VIEWER_WORKER=0`, or no worker executable (a development build of only the viewer;
the viewer keeps working, with the reason in the status line). In smoke mode
`SAFEPDF_WORKER_DEADLINE_MS` sets the deadline (`smokeWorker` sets the test hook's variable of
the workers it starts, `Worker.TestHooks`). -/
def startWorker (smoke : Bool) : IO (Option Worker.Session × String) := do
  if (← IO.getEnv "SAFEPDF_VIEWER_WORKER") == some "0" then
    return (none, "pages render in this process (SAFEPDF_VIEWER_WORKER=0)")
  let exe ← workerExe
  if !(← exe.pathExists) then
    return (none, s!"no document worker at {exe}: pages render in this process")
  let deadlineMs ← if smoke then
      pure (((← IO.getEnv "SAFEPDF_WORKER_DEADLINE_MS").bind String.toNat?).getD workerDeadlineMs)
    else pure workerDeadlineMs
  let ses ← Worker.Session.start { exe, limits, deadlineMs, start := ← workerStart }
  return (some ses, "")

/-- Parses a window size `WxH` (`SAFEPDF_VIEWER_GEOMETRY`), each side 200–10000 pixels. -/
def parseGeometry (g : String) : Option (Nat × Nat) :=
  match g.splitOn "x" with
  | [w, h] => do
    let w ← w.toNat?
    let h ← h.toNat?
    if 200 ≤ w ∧ w ≤ 10000 ∧ 200 ≤ h ∧ h ≤ 10000 then some (w, h) else none
  | _ => none

#guard parseGeometry "1900x940" == some (1900, 940)
#guard parseGeometry "1900x" == none && parseGeometry "10x10" == none &&
  parseGeometry "1x2x3" == none

/-- Usage text. -/
def usage : String :=
  "usage: viewer [FILE.pdf]
Opens FILE (or asks for one) in a window.
Keys: Next/space, Prior/BackSpace scroll by a window (then next/previous page);
Down/Up/Right/Left scroll; Home/End first/last page; + - zoom in/out; 0 actual size;
f fit page; w fit width; r/R rotate right/left; Ctrl+wheel zoom; Ctrl+O open; Ctrl+W close;
View menu: Page/Vertical Scrolling, No/Odd/Even Spreads (continuous and facing pages);
Ctrl+Q quit (on macOS every Ctrl key is also Command). The menubar (File, Edit, View, Go) has every command.
Mouse drag selects text, double-click a word; Ctrl+A select page; Ctrl+C copy;
Ctrl+F find (Enter/F3 next, Shift+F3 previous, Escape close).
Add text: click to place a text box (Escape or a click elsewhere ends it, double-click
edits); Draw: drag to draw strokes; drag a text box or drawing to move it.
h or the Highlight button highlights the selection (the button without one: Highlight
tool and its pop-over); a selection shows a Highlight bubble, a selected highlight its
colour/comment/delete bubble; Escape dismisses them; right button: Highlight colours,
Add note...; click a mark to select it (a note opens its text), Delete or Backspace
removes it; Ctrl+Z undoes a mark edit, Ctrl+Shift+Z redoes it (Edit > Undo / Redo).
Ctrl+S saves the marks into FILE-annotated.pdf (an incremental update: the original bytes
stay unchanged at its start); Ctrl+Shift+S saves to a chosen file; marks saved in a file are
restored when it is opened; saved marks can be recoloured, deleted and edited (9.5g). Closing or quitting asks about unsaved marks.
File > Import annotations... / Export annotations... read and write XFDF (STEM.xfdf by default).
Files open as their /PageLayout, /PageMode, /OpenAction (destinations only; JavaScript and
other actions are never run) and viewer preferences say; Escape leaves full screen and shows
a toolbar, menubar or scroll bars the document hid.
F9 outline panel; click a link to follow it (external addresses are only shown and, if
confirmed, copied); Alt+Left/Alt+Right back/forward; Ctrl+G go to a page number or label.
SAFEPDF_VIEWER_SMOKE=DIR: scripted smoke test writing images and state into DIR, then exit
(SAFEPDF_VIEWER_SMOKE_MODE=text: the selection/copy/search steps instead;
SAFEPDF_VIEWER_SMOKE_MODE=nav: the outline/link/history/go-to steps;
SAFEPDF_VIEWER_SMOKE_MODE=menu: the menubar steps;
SAFEPDF_VIEWER_SMOKE_MODE=toolbar: the toolbar and sidebar steps;
SAFEPDF_VIEWER_SMOKE_MODE=marks: the highlight and note steps;
SAFEPDF_VIEWER_SMOKE_MODE=bubble: the selection bubble and Highlight pop-over steps;
SAFEPDF_VIEWER_SMOKE_MODE=save / reopen / encrypted: the save flow, reopening the saved file,
saving an encrypted file).
SAFEPDF_VIEWER_SMOKE_MODE=xfdf: XFDF export and import (task 9.11);
SAFEPDF_VIEWER_SMOKE_MODE=editors: Add text and Draw, save, move, delete (task 9.9);
=editors-shot: a text box, a drawing and the Draw pop-over, kept up 20 s for a screenshot;
SAFEPDF_VIEWER_SMOKE_MODE=biblean: under viewer --biblean, a highlight, a note and Save to
library (task 10.1b);
SAFEPDF_VIEWER_SMOKE_MODE=modes: the view-mode steps; =scroll: scroll the document through in
the vertical mode and write timings (a benchmark).
SAFEPDF_VIEWER_SMOKE_MODE=lockdown: Tk send and hostile X resources (task 8.7).
SAFEPDF_VIEWER_SMOKE_MODE=async: rendering on worker threads, placeholders, stale results
(task 8.8).
SAFEPDF_VIEWER_DRIVE=1: test hook keeping Tk's send command (scripts/viewer-corpus.sh drives
the viewer through it); without it other X clients cannot send Tcl to the viewer.
SAFEPDF_VIEWER_GEOMETRY=WxH: initial window size (default 1200x960).
SAFEPDF_VIEWER_VIEW=single|continuous|facing|continuous-facing: view mode of files without
/PageLayout (facing: odd spreads; View menu: Page/Vertical Scrolling, No/Odd/Even Spreads).
SAFEPDF_VIEWER_SMOKE_MODE=opensettings: the document open settings steps (task 9.r8)."

/-- Runs the viewer with `init` run once the window is built (task 10.1b: `viewer --biblean`
opens its document from memory there, `openBytes`), after the file named in `args`, if any.
When neither opened anything, the window asks for a file (`tk_getOpenFile`, not in smoke
mode). Exit codes: 0 after the window closes; 2 usage error; 3 Tk failed to start (no
display, missing Tk). -/
def mainWith (args : List String) (init : IO.Ref State → IO Unit) : IO UInt32 := do
  let file ← match args with
    | [] => pure none
    | ["--help"] | ["-h"] => IO.println usage; return 0
    | [f] => pure (some f)
    | _ => IO.eprintln usage; return 2
  try
    Shim.init
    -- Task 8.7: no Tcl from other X clients through `send`, unless the corpus driver
    -- (`scripts/viewer-corpus.sh`) asks to drive the viewer that way. Before anything else:
    -- Tk handles incoming sends only in the event loop, which has not run yet.
    if (← IO.getEnv "SAFEPDF_VIEWER_DRIVE") != some "1" then
      discard <| Shim.eval sendOffScript
  catch e =>
    IO.eprintln s!"viewer: cannot start Tk: {e}"
    return 3
  let smokeDir ← IO.getEnv "SAFEPDF_VIEWER_SMOKE"
  let smokeMode := (← IO.getEnv "SAFEPDF_VIEWER_SMOKE_MODE").getD ""
  let subst ← Fonts.loadSubstFonts limits
  -- Task 8.8: an event waits at most 100 ms for the renders of the pages it shows; in smoke
  -- mode until they are done (the steps look at the pages at once), except in the `async` test.
  let syncWaitMs := if smokeDir.isNone || smokeMode == "async" then
    some (if smokeMode == "async" then 0 else 100) else none
  let (worker, workerNote) ← startWorker smokeDir.isSome
  let st ← IO.mkRef ({ smokeDir, smokeMode, subst, syncWaitMs, worker, workerNote } : State)
  Shim.setEmitHandler (safeHandle st)
  try
    discard <| Shim.eval setupScript
    -- Task 9.r3: keys and labels for the platform (Command on macOS), then the icon. The
    -- smoke run can ask for the aqua mapping on X11 (`SAFEPDF_VIEWER_PLATFORM=aqua`).
    let forced := smokeDir.isSome && (← IO.getEnv "SAFEPDF_VIEWER_PLATFORM") == some "aqua"
    let ws ← Shim.eval "tk windowingsystem"
    let plat := if forced then .aqua else Menu.Platform.ofWindowingSystem ws
    platformRef.set plat
    setIcon
    buildMenus
    buildToolbar
    discard <| Shim.eval (Menu.platformScript plat)
    if let some g ← IO.getEnv "SAFEPDF_VIEWER_GEOMETRY" then
      if let some (w, h) := parseGeometry g then
        discard <| run ["wm", "geometry", ".", s!"{w}x{h}"]
    if smokeDir.isSome then discard <| run ["set", "::safepdf::autoConfirm", "1"]
    -- The initial view mode (task 9.3).
    if let some v ← IO.getEnv "SAFEPDF_VIEWER_VIEW" then
      if let some (sc, sp) := View.viewModeOf v then
        st.modify ({ · with scroll := sc, spread := sp, defaultView := (sc, sp) })
        discard <| run ["set", Menu.scrollVar, sc.key]
        discard <| run ["set", Menu.spreadVar, sp.key]
        discard <| run ["set", "::safepdf::continuous", if sc == .vertical then "1" else "0"]
    showViewChoice (← st.get) false
    if (← Shim.eval "tk windowingsystem") == "aqua" then st.modify ({ · with stipple := false })
    -- Screen scale (pixels per point), kept in [1/2, 8].
    if let some sc := View.parseDecimal (← Shim.eval "tk scaling") then
      st.modify ({ · with scaling := max (1 / 2) (min 8 sc) })
    -- Lay the window out so that the first render uses the real canvas size.
    discard <| Shim.eval "update"
    let w ← Shim.eval "winfo width .c"
    let h ← Shim.eval "winfo height .c"
    if let (some w, some h) := (w.toNat?, h.toNat?) then
      if w ≥ 2 && h ≥ 2 then st.modify ({ · with canvasW := w, canvasH := h })
  catch e =>
    IO.eprintln s!"viewer: cannot build the window: {e}"
    return 3
  if let some f := file then guarded (openFile st f)
  guarded (init st)
  if (← st.get).path.isNone then
    setStatus (← keyText "No file. Press Ctrl+O or Open... to choose a PDF.")
    if smokeDir.isNone then discard <| run ["after", "idle", "::safepdf::emit open"]
  guarded (syncMenus st)
  if smokeDir.isSome then discard <| run ["after", "300", "::safepdf::emit smoke"]
  Shim.mainLoop
  -- Task 12.2c: the worker is killed with the window (waited for at most 2 s).
  if let some w := (← st.get).worker then w.shutdown
  return 0

/-- Runs the viewer (`mainWith` without an `init`): opens the file named in `args`, else asks
for one. Exits the process as soon as the window is closed (task 8.8): a page render still
running on a worker thread cannot be interrupted, and the Lean runtime would wait for it. -/
def main (args : List String) : IO UInt32 := do
  let code ← mainWith args fun _ => pure ()
  IO.Process.exit (if code > 255 then 1 else code.toUInt8)

end SafePdf.Shell.App.Viewer
