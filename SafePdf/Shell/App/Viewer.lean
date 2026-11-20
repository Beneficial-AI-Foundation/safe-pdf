import SafePdf.Shell.App.Shim
import SafePdf.Shell.App.Tcl
import SafePdf.Shell.App.View
import SafePdf.Shell.App.Select
import SafePdf.Shell.App.Links
import SafePdf.Shell.App.Menu
import SafePdf.Shell.App.Toolbar
import SafePdf.Shell.App.Sidebar
import SafePdf.Shell.App.Marks
import SafePdf.Shell.App.Bubble
import SafePdf.Core.Annot
import SafePdf.Shell.Inspect
import SafePdf.Shell.Views.Pages
import SafePdf.Shell.Fonts

/-!
# Native viewer (tasks 8.2a–8.2d, 9.1, 9.2, 9.4, 9.7, 9.8; Plan.md §6 Phases 8–9, §8 native app, §10 `SafePdf/Shell/`)

The unverified, replaceable shell of the viewer (Plan.md §8): one Tk window with a menubar
(File / Edit / View / Go, built from the Tk-free model `Menu.menubar`, entries enabled by
`Menu.Cmd.enabled` and kept in step after every event by `syncMenus`; task 9.1), a toolbar and
an outline sidebar imitating PDF.js, Firefox's viewer (task 9.7; built from the Tk-free models
`Toolbar.layout` and `Sidebar.rows`: sidebar toggle, page arrows, page field, zoom −/+ and
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
  `rotAdd`). Zoom is capped at `View.maxViewPixels` pixels per page image (status line says
  so); a side above `Limits.maxPageSide` is cropped by the renderer (status line says so).
  Non-embedded fonts are painted with the substitute programs `Shell.Fonts.loadSubstFonts`
  finds at start-up (task 7.7, `docs/raster.md`; `State.subst`).
* **Page cache** (`View.Cache`): render results keyed by (document generation, page, zoom,
  rotation), LRU, at most `View.cacheBytes` (256 MiB) of images. After a page is shown the
  next page is prefetched 100 ms later (same event loop, no threads) when it is at most
  `prefetchPixels` pixels.
* **Scrolling.** The canvas has scroll bars; its scroll region is the page image plus a margin.
  Keys (Tcl proc `::safepdf::step`): `Down`/`Up` and `Right`/`Left` scroll by a tenth of the window,
  `Next`/`space` and `Prior`/`BackSpace`/`Shift+space` by a window. Past the bottom (right) edge
  they move to the top of the next page; past the top they move to the bottom of the previous
  page (page-at-a-time). The mouse wheel does the same (task 9.2, `wheel`, logic in
  `View.wheelStep`: small deltas accumulate, the page turns only after the view reached the
  edge and the wheel pushes on past it); Shift+wheel scrolls horizontally without turning
  pages; Ctrl+wheel zooms about the mouse pointer.
* **Anchoring (C2).** Before a zoom or rotation change the viewer reads the canvas point under
  the mouse (Ctrl+wheel) or at the window centre, maps it to page space with `Geom.toPage`;
  after the new image is shown it maps that page point back with `Geom.toScreen`
  (`View.reanchor`) and scrolls so it lies under the same window position.
* **Selection and copy** (task 8.2c, pure logic in `Select`). A page's text is extracted on
  first use (`Annot.extractDocPageAnnots`, fresh budget, as the text view) and cached per page
  as a `Select.PageIndex` (glyph cells in reading order with page-space boxes, plus the
  normalised search text). A mouse press/drag/release maps the window positions to page space
  with `Geom.toPage` and selects the glyphs between the nearest glyphs in reading order;
  double-click selects a word; Ctrl+A the page. The selection is drawn as stippled canvas
  rectangles over the page image (tag `sel`; the image is not re-rendered). Ctrl+C or the
  context menu (right button) copies `Select.rangeText` to the clipboard (`clipboard append`,
  the text passed as one quoted word).
* **Search** (Ctrl+F opens the find bar; Enter/F3 next, Shift+Enter/Shift+F3 previous, Escape
  closes): case-insensitive, whitespace-normalised (`Select.normQuery`), page by page from the
  current hit, wrapping around the document; pages are extracted lazily. All hits of the
  current page are highlighted (tag `hit`, the current one in orange) and the current hit is
  scrolled into view; the status line says `"q": hit k/n on page p` (k of the n hits of that
  page) or `"q": not found`.
* **Navigation** (task 8.2d, pure logic in `Links`). The outline (`Nav.outline`) fills a
  tree (a text widget, task 9.7) in the left pane of a paned window (shown when the document has an outline;
  F9, the Outline button or the context menu toggle it); clicking an item jumps to its
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
* **Marks** (task 9.4, pure model in `Marks`): highlights of the selection in PDF.js's five
  colours (toolbar Highlight button, `h`, Edit menu, context-menu colour cascade) and notes
  (Add note… on the selection or at the right-clicked point; a popup edits the text), kept in
  memory per document in page space (`Marks.Store`, stable ids). Highlights are multiplied
  into the shown page image (`Marks.composite`, PDF.js's `mix-blend-mode: multiply`); note
  icons, note anchors and the selected-mark outline are canvas items (tag `mark`). A click on
  a mark selects it (a note also opens its popup); Delete or Edit → Delete mark removes it,
  a colour entry recolours it.
* **Selection bubble and Highlight pop-over** (task 9.8, pure logic in `Bubble`): after a
  text selection a floating Highlight button at the selection's end; on a selected highlight
  the edit bubble (colour swatch with a picker, Comment, Delete), canvas items placed again on
  every redraw (`drawBubble`); the toolbar's Highlight button without a selection toggles the
  Highlight tool and its pop-over `.hlbar` (swatches, thickness slider, "Show all"; `syncTool`,
  `drawPopover`); with the tool on a mouse-up that selects text highlights it at once; Escape
  closes the pop-over and dismisses the bubble.
* **Errors** (unreadable file, parse error, render error, Tcl error) are shown in the status
  line; the window stays usable. Every event handler catches its own exceptions.
* **No data in script text.** Every Tcl command that carries data (file names, error messages,
  numbers) is built with `Tcl.cmd`/`Script.render`, whose literal words go through the proved
  `Tcl.quote` (`Tcl.parseScript_render`); the only raw script text is the constant UI setup.
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
  /-- Keep the page point `p` under the window position `(wx, wy)` (C2 anchoring). -/
  | anchor (wx wy : Nat) (p : Pt)
  /-- Show the page point (`left`, `top`) at the window's top-left corner (a destination's
  position; a missing coordinate is the page's left or top edge). -/
  | dest (left top : Option Rat)
  /-- Restore the scroll fractions `(x, y)` (history). -/
  | frac (x y : Rat)

/-- The viewer's state, kept in one `IO.Ref`. -/
structure State where
  /-- Path of the open file, if any. -/
  path : Option String := none
  /-- The opened document (`none`: no file, or it failed to open). -/
  doc : Option Doc := none
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
  /-- Rendered pages. -/
  cache : View.Cache := {}
  /-- Substitute programs for non-embedded fonts (task 7.7, `Shell.Fonts`), found at start-up
  and parsed on first use. -/
  subst : SafePdf.Core.Raster.Subst.SubstFonts := {}
  /-- Key of what is on screen (successful or failed render). -/
  shown : Option View.Key := none
  /-- Canvas position and size of the shown image, zoom and total rotation it was drawn
  with (for anchoring). -/
  imgX : Nat := View.margin
  /-- See `imgX`. -/
  imgY : Nat := View.margin
  /-- See `imgX`. -/
  shownZoom : Rat := 1
  /-- See `imgX`. -/
  shownRot : SafePdf.Core.Doc.Rotation := .r0
  /-- Scroll to apply after the next image is shown. -/
  pending : Option ScrollTo := none
  /-- Scroll region size of the shown page (pixels). -/
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
  /-- Highlights are stippled fills (`false` on Aqua, which has no stipples: outlines). -/
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
  /-- Whether the outline panel is shown. -/
  outlineShown : Bool := false
  /-- Links per page (`none`: not read yet). -/
  links : Array (Option (Array Links.Link)) := #[]
  /-- Index of the link under the mouse pointer on the shown page. -/
  hover : Option Nat := none
  /-- The status line text from before the pointer entered a link (restored on leaving). -/
  savedStatus : String := ""
  /-- Back/forward history of jumps. -/
  history : Links.History := {}
  /-- Enabled states last applied to the menubar entries and toolbar buttons
  (`Menu.entryStates` order; empty: not applied yet). -/
  menuStates : List Bool := []
  /-- Wheel state: sub-pixel remainder and push past the page edge (task 9.2). -/
  wheel : View.Wheel := {}
  /-- Rows of the outline tree (task 9.7, `Sidebar.rows`). -/
  olRows : List Sidebar.Row := []
  /-- Which outline rows are open (`Sidebar.toggle`). -/
  olOpen : Array Bool := #[]
  /-- Whether the sidebar toggle is shown (`none`: not applied yet). -/
  toggleShown : Option Bool := none
  /-- The user's highlights and notes of the open document (task 9.4). -/
  marks : Marks.Store := {}
  /-- The selected mark (its id). -/
  markSel : Option Nat := none
  /-- The current highlight colour (`::safepdf::hlColor`). -/
  hlColor : Marks.Color := .yellow
  /-- The page image on screen before the highlights are multiplied in (`Marks.composite`). -/
  shownImg : Option Clip.Image := none
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

/-- The limits the viewer parses and renders with. -/
def limits : Limits := Limits.default

/-- Name of the Tk photo image that shows the page. -/
def photoName : String := "::safepdf::page"

/-- Pages up to this many pixels are prefetched (2²² ≈ 4 Mpx, e.g. Letter at 250 %). -/
def prefetchPixels : Nat := 1 <<< 22

/-! ## Pure helpers -/

/-- Number of pages of the open document (0 when none). -/
def State.pageCount (s : State) : Nat :=
  match s.doc with
  | some d => d.pages.size
  | none => 0

/-- How page `p` is displayed: zoom, total rotation (`/Rotate` + user rotation), page box,
whether the zoom was capped and whether the image is cropped. -/
structure ViewParams where
  /-- Zoom in pixels per page unit. -/
  zoom : Rat
  /-- Total rotation. -/
  rot : SafePdf.Core.Doc.Rotation
  /-- CropBox. -/
  box : Box
  /-- The zoom was lowered to `View.maxViewPixels`. -/
  capped : Bool
  /-- The image is cropped to `Limits.maxPageSide`. -/
  cropped : Bool

/-- View parameters of page `p` of `doc` in state `s`. -/
def viewParams (s : State) (doc : Doc) (p : Nat) : Option ViewParams :=
  doc.pages[p]?.map fun page =>
    let r := rotAdd page.rotate s.rot
    let bx := Box.ofRect page.cropBox
    let (pw, ph) := View.boxSize r bx
    let z0 := s.zoomSel.zoom s.canvasW s.canvasH s.scaling pw ph
    let (z, capped) := View.capZoom View.maxViewPixels z0 r bx
    ⟨z, r, bx, capped, View.cropped limits.maxPageSide z r bx⟩

/-- Last path component of a file name (for the window title). -/
def baseName (path : String) : String :=
  (System.FilePath.mk path).fileName.getD path

/-- Window title: `safe-pdf`, or `NAME - page k/n - safe-pdf`. -/
def State.title (s : State) : String :=
  match s.path, s.doc with
  | some p, some _ => s!"{baseName p} - {Links.pageText s.labels s.page s.pageCount} - safe-pdf"
  | some p, none => s!"{baseName p} - safe-pdf"
  | none, _ => "safe-pdf"

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
#guard fmtFrac 2 = "1.000000"
#guard fmtFrac (-1) = "0.000000"

/-- Name of a zoom choice for the status line. -/
def modeName (c : Toolbar.ZoomChoice) : String := c.statusName

/-! ## Tcl -/

/-- Evaluates a command built from literal words (every word quoted by `Tcl.quote`). -/
def run (words : List String) : IO String :=
  Shim.eval (Tcl.Script.render ⟨[Tcl.cmd words]⟩)

/-- Shows `msg` in the status line. -/
def setStatus (msg : String) : IO Unit := do
  discard <| run [".status", "configure", "-text", msg]

/-- The constant UI setup script (no data in it). Widgets: the toolbar `.bar` after PDF.js
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
namespace eval ::safepdf { variable resizeId {}; variable query {}; variable outlineOn 0 }
namespace eval ::safepdf::icon {}
wm title . safe-pdf
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
proc ::safepdf::icon::more {c} {
  $c create line 10 11 15 16 10 21 -width 1.6 -capstyle round -joinstyle round -tags inkf
  $c create line 17 11 22 16 17 21 -width 1.6 -capstyle round -joinstyle round -tags inkf
}
# Toolbar buttons: a 32 px canvas with a round background (hover, pressed, toggled as in
# PDF.js) and an icon; disabled buttons draw the icon dimmed and ignore clicks. State in
# ::safepdf::btn(KEY,PATH).
set ::safepdf::tipId {}
proc ::safepdf::iconButton {w icon tip cmd} {
  canvas $w -width 32 -height 32 -background $::safepdf::col(bar) -highlightthickness 0 \\
    -borderwidth 0 -takefocus 0
  $w create oval 1 1 31 31 -fill $::safepdf::col(bar) -outline {} -tags bg
  ::safepdf::icon::$icon $w
  foreach {k v} [list st normal tog 0 in 0 down 0 cmd $cmd tip $tip] { set ::safepdf::btn($k,$w) $v }
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
    set bg $c(hover) } elseif {$b(tog,$w)} { set bg $c(toggled) } else { set bg $c(bar) }
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
  bind .bar.pg.e <Control-q> {destroy .}
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
# Overflow menu (PDF.js's secondary toolbar), posted under the right edge of the » button.
menu .more -tearoff 0 -background white -activebackground $::safepdf::col(hover) \\
  -activeforeground $::safepdf::col(text) -foreground $::safepdf::col(text) \\
  -font ::safepdf::fBar -relief solid -borderwidth 1 -activeborderwidth 0
proc ::safepdf::postMore {} {
  set x [expr {[winfo rootx .bar.more] + [winfo width .bar.more] - [winfo reqwidth .more]}]
  tk_popup .more $x [expr {[winfo rooty .bar.more] + [winfo height .bar.more] + 2}]
}
# The sidebar toggle is shown only when the document has an outline.
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
  if {$a <= 0.0 && $b >= 1.0} { grid remove .ol.s } else { grid .ol.s }
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
canvas .c -background $::safepdf::col(body) -highlightthickness 0 -takefocus 1 -confine 1 \\
  -xscrollcommand {.xs set} -yscrollcommand {.ys set}
ttk::scrollbar .ys -orient vertical -command {.c yview}
ttk::scrollbar .xs -orient horizontal -command {.c xview}
grid .c -in .v -row 0 -column 0 -sticky nsew
grid .ys -in .v -row 0 -column 1 -sticky ns
grid .xs -in .v -row 1 -column 0 -sticky ew
grid rowconfigure .v 0 -weight 1
grid columnconfigure .v 0 -weight 1
image create photo ::safepdf::page
.c create rectangle 0 0 0 0 -outline #c8c8d0 -width 1 -state hidden -tags pageframe
.c create image 8 8 -anchor nw -image ::safepdf::page -tags page
label .status -text {} -anchor w -background $::safepdf::col(bar) \\
  -foreground $::safepdf::col(dim) -font ::safepdf::fBar -padx 6 -pady 2 -borderwidth 0
frame .statusline -height 1 -background $::safepdf::col(line)
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
bind . <Key-BackSpace> {::safepdf::step y -1 pages}
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
bind . <Control-q> {destroy .}
bind .c <Configure> {
  after cancel $::safepdf::resizeId
  set ::safepdf::resizeId [after 100 {::safepdf::emit resize [winfo width .c] [winfo height .c]}]
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
  if {![winfo ismapped .find]} { pack .find -side top -fill x -after .barline }
  focus .find.e
  .find.e selection range 0 end
  .find.e icursor end
}
proc ::safepdf::hideFind {} { pack forget .find; focus .c; ::safepdf::emit find close }
bind .find.e <Return> {::safepdf::emit find next $::safepdf::query; break}
bind .find.e <KP_Enter> {::safepdf::emit find next $::safepdf::query; break}
bind .find.e <Shift-Return> {::safepdf::emit find prev $::safepdf::query; break}
bind .find.e <F3> {::safepdf::emit find next $::safepdf::query; break}
bind .find.e <Shift-F3> {::safepdf::emit find prev $::safepdf::query; break}
bind .find.e <Escape> {::safepdf::hideFind; break}
bind .find.e <Control-q> {destroy .}
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
.pop add command -label {Outline} -accelerator F9 -command {::safepdf::emit outlineToggle}
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
  if {![winfo ismapped .goto]} { pack .goto -side top -fill x -after .barline }
  focus .goto.e
  .goto.e selection range 0 end
  .goto.e icursor end
}
proc ::safepdf::hideGoto {} { pack forget .goto; focus .c }
bind .goto.e <Return> {::safepdf::emit goto $::safepdf::gotoText; break}
bind .goto.e <KP_Enter> {::safepdf::emit goto $::safepdf::gotoText; break}
bind .goto.e <Escape> {::safepdf::hideGoto; break}
bind .goto.e <Control-q> {destroy .}
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
document, to the address below. safe-pdf never opens it; it can copy the address to the \\
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
# Marks (9.4): current highlight colour, the right-clicked point, keys, the note icon and the note popup.
set ::safepdf::hlColor yellow
set ::safepdf::popX {}
set ::safepdf::popY {}
bind . <Key-h> {::safepdf::emit highlight}
bind . <Key-Delete> {::safepdf::emit markDelete}
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
# note, Cancel/Escape closes.
proc ::safepdf::noteEdit {id text x y} {
  set w .note
  destroy $w
  toplevel $w -background $::safepdf::col(panel)
  wm title $w Note
  wm transient $w .
  wm geometry $w +$x+$y
  text $w.t -wrap word -width 36 -height 6 -font ::safepdf::fOl -relief solid -borderwidth 1 \
    -undo 1 -background #ffffe8 -foreground $::safepdf::col(text) -padx 6 -pady 4
  $w.t insert end $text
  ttk::frame $w.b
  ttk::button $w.b.save -text Save -command [list ::safepdf::noteDone $id save]
  ttk::button $w.b.del -text Delete -command [list ::safepdf::noteDone $id delete]
  ttk::button $w.b.cancel -text Cancel -command [list destroy $w]
  pack $w.b.cancel $w.b.save -side right -padx 4 -pady 4
  pack $w.b.del -side left -padx 4 -pady 4
  pack $w.b -side bottom -fill x
  pack $w.t -side top -fill both -expand 1 -padx 6 -pady {6 0}
  bind $w <Escape> [list destroy $w]
  bind $w.t <Control-Return> [list ::safepdf::noteDone $id save]
  focus $w.t
}
proc ::safepdf::noteDone {id what} {
  if {![winfo exists .note]} return
  set t [.note.t get 1.0 {end - 1 chars}]
  destroy .note
  if {$what eq {save}} { ::safepdf::emit noteSave $id $t } else { ::safepdf::emit noteDelete $id }
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
bind . <Key-Escape> {::safepdf::emit escape}
focus .c
"

/-! ## Text index and highlights (task 8.2c) -/

/-- The text index of page `p`: extracted on first use (`Annot.extractDocPageAnnots` with a
fresh budget, as the text view and the renderer) and cached for the open document. -/
def pageIndex (st : IO.Ref State) (p : Nat) : IO (Except String Select.PageIndex) := do
  let s ← st.get
  let some doc := s.doc | return .error "no document"
  match s.texts[p]? with
  | some (some r) => return r
  | _ =>
    let some page := doc.pages[p]? | return .error "page index out of range"
    let r ← IO.lazyPure fun _ =>
      match (SafePdf.Core.Annot.extractDocPageAnnots limits doc page
          (SafePdf.Core.Filter.Budget.init limits)).1 with
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

/-- The page point under window position `(wx, wy)` of the canvas (`Geom.toPage`, C2). -/
def pagePoint (st : IO.Ref State) (wx wy : Int) : IO (Option Pt) := do
  let s ← st.get
  let some bx := shownBox s | return none
  let cx ← run [".c", "canvasx", toString wx]
  let cy ← run [".c", "canvasy", toString wy]
  let (some cx, some cy) := (View.parseDecimal cx, View.parseDecimal cy) | return none
  return some (toPage s.shownZoom s.shownRot bx ⟨cx - (s.imgX : Rat), cy - (s.imgY : Rat)⟩)

/-- The marks of the shown page that are drawn: all of them, or only the notes while "Show
all" is off (task 9.8). -/
def visibleMarks (s : State) : List Marks.Mark :=
  let ms := s.marks.onPage s.page
  if s.ui.showAll then ms else ms.filter (·.isNote)

/-- `canvasRect` as a `Bubble.Rect`. -/
def canvasR (s : State) (bx b : Box) : Bubble.Rect :=
  let (x0, y0, x1, y1) := canvasRect s bx b
  ⟨x0, y0, x1, y1⟩

/-- Canvas coordinates of window position `(wx, wy)`. -/
def canvasPos (wx wy : Int) : IO (Option (Rat × Rat)) := do
  let cx ← run [".c", "canvasx", toString wx]
  let cy ← run [".c", "canvasy", toString wy]
  return match View.parseDecimal cx, View.parseDecimal cy with
    | some x, some y => some (x, y)
    | _, _ => none

/-- Draws the canvas items of the shown page's marks (tag `mark`, task 9.4): note icons
(`::safepdf::noteIcon`, tag `note` and `mID`), the dashed quads a note is anchored to, and the
outline of the selected mark (tag `marksel`). Highlight fills are pixels (`showImage`). -/
def drawMarks (s : State) (bx : Box) : IO Unit := do
  for m in visibleMarks s do
    let tags := s!"mark m{m.id}"
    if m.isNote then
      for q in m.quads do
        let (x0, y0, x1, y1) := canvasRect s bx q
        discard <| run [".c", "create", "rectangle", toString x0.floor, toString y0.floor,
          toString x1.ceil, toString y1.ceil, "-outline", "#c99a00", "-dash", "4 2",
          "-width", "1", "-tags", tags]
      if let some ib := m.iconBox bx then
        let (x0, y0, x1, y1) := canvasRect s bx ib
        discard <| run ["::safepdf::noteIcon", ".c", toString x0.floor, toString y0.floor,
          toString x1.ceil, toString y1.ceil, m.color.hex, s!"{tags} note"]
    if s.markSel == some m.id then
      let boxes := if m.isNote then (m.iconBox bx).toList else m.quads
      for q in boxes do
        let (x0, y0, x1, y1) := canvasRect s bx q
        discard <| run [".c", "create", "rectangle", toString (x0.floor - 2),
          toString (y0.floor - 2), toString (x1.ceil + 2), toString (y1.ceil + 2),
          "-outline", "#0060df", "-width", "2", "-tags", s!"{tags} marksel"]

/-- Draws the bubble of the shown page (canvas items tagged `bub`, task 9.8; `Bubble`): after
a text selection (not while dragging) the float bubble with the Highlight button, on a selected
highlight the edit bubble (colour swatch and chevron, Comment, Delete) and, when open, its
colour picker. Placed by `Bubble.place` in canvas coordinates inside the scroll region, so it
scrolls with the page; every redraw (zoom, rotation, page change) places it again. Records
what is drawn in `State.bubble` / `State.pickerAt` for the clicks. -/
def drawBubble (st : IO.Ref State) (bx : Box) : IO Unit := do
  let s ← st.get
  let selRects ← match s.sel with
    | some (p, a, b) =>
      if p == s.page && s.pressPt.isNone then
        match ← pageIndex st p with
        | .ok ix => pure ((Select.rangeBoxes ix.cells a b).map (canvasR s bx))
        | .error _ => pure []
      else pure []
    | none => pure []
  let mark := (s.markSel.bind s.marks.find?).filter fun m => m.page == s.page && !m.isNote
  let markRects := (mark.map fun m => m.quads.map (canvasR s bx)).getD []
  let area : Bubble.Rect := ⟨0, 0, (s.regionW : Rat), (s.regionH : Rat)⟩
  let placed := (Bubble.kindFor (!selRects.isEmpty) (!markRects.isEmpty) s.ui).bind fun k =>
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

/-- Redraws the overlays of the shown page: the marks' canvas items (`drawMarks`), all search
hits (tag `hit`, the current one in orange), the selection (tag `sel`) and the bubble (tag
`bub`, `drawBubble`), in that stacking order. -/
def drawOverlay (st : IO.Ref State) : IO Unit := do
  discard <| run [".c", "delete", "sel", "hit", "mark", "bub"]
  st.modify ({ · with bubble := none, pickerAt := none })
  let s ← st.get
  let some bx := shownBox s | return
  drawMarks s bx
  let rect (b : Box) (color tag : String) : IO Unit := do
    let (x0, y0, x1, y1) := canvasRect s bx b
    let style := if s.stipple then ["-fill", color, "-stipple", "gray50", "-outline", ""]
      else ["-fill", "", "-outline", color, "-width", "2"]
    discard <| run ([".c", "create", "rectangle", toString x0.floor, toString y0.floor,
      toString x1.ceil, toString y1.ceil] ++ style ++ ["-tags", tag])
  if !s.query.isEmpty then
    if let .ok ix ← pageIndex st s.page then
      let hits := ix.hits s.query
      for i in [0:hits.size] do
        if let some (a, b) := hits[i]? then
          let color := if s.hit == some (s.page, i) then "orange" else "yellow"
          for b in Select.rangeBoxes ix.cells a b do rect b color "hit"
  if let some (p, a, b) := s.sel then
    if p == s.page then
      if let .ok ix ← pageIndex st p then
        for b in Select.rangeBoxes ix.cells a b do rect b "#3874f2" "sel"
  drawBubble st bx

/-! ## Rendering -/

/-- Renders page `p` of `doc` at `zoom` and user rotation `rot` with a fresh budget (the
inspector's `raster` view does the same). -/
def renderPage (doc : Doc) (p : Nat) (zoom : Rat) (rot : SafePdf.Core.Doc.Rotation)
    (subst : SafePdf.Core.Raster.Subst.SubstFonts := {}) :
    IO (Except Error Clip.Image) := do
  match doc.pages[p]? with
  | some page =>
    IO.lazyPure fun _ =>
      (SafePdf.Core.Raster.Glyph.renderDocPage limits doc page zoom rot
        (SafePdf.Core.Filter.Budget.init limits) (subst := subst)).1
  | none => return .error (.malformed 0 "page index out of range")

/-- The render result for `key` from the cache, or rendered now and cached. Returns the
result and the render time in nanoseconds (`none`: from the cache). -/
def fetch (st : IO.Ref State) (doc : Doc) (key : View.Key) :
    IO (Except Error Clip.Image × Option Nat) := do
  let (hit, cache) := (← st.get).cache.find? key
  st.modify ({ · with cache })
  match hit with
  | some r => return (r, none)
  | none =>
    let t0 ← IO.monoNanosNow
    let r ← renderPage doc key.page key.zoom key.rot (← st.get).subst
    let t1 ← IO.monoNanosNow
    st.modify fun s => { s with cache := s.cache.insert key r }
    return (r, some (t1 - t0))

/-- Applies the pending scroll for an image of `w × h` pixels at canvas `(ix, iy)` in a
scroll region `rw × rh`, drawn with view parameters `vp`. -/
def applyScroll (s : State) (vp : ViewParams) (ix iy rw rh : Nat) : IO Unit := do
  match s.pending with
  | some .top => discard <| run [".c", "yview", "moveto", "0"]
  | some .bottom => discard <| run [".c", "yview", "moveto", "1"]
  | some (.anchor wx wy p) =>
    if 0 < vp.zoom then
      let q := toScreen vp.zoom vp.rot vp.box p
      let left : Rat := q.x + (ix : Rat) - (wx : Rat)
      let top : Rat := q.y + (iy : Rat) - (wy : Rat)
      discard <| run [".c", "xview", "moveto", fmtFrac (left / (max rw 1 : Nat))]
      discard <| run [".c", "yview", "moveto", fmtFrac (top / (max rh 1 : Nat))]
  | some (.dest left top) =>
    if 0 < vp.zoom then
      let q := toScreen vp.zoom vp.rot vp.box ⟨left.getD vp.box.llx, top.getD vp.box.ury⟩
      discard <| run [".c", "xview", "moveto", fmtFrac ((q.x + (ix : Rat)) / (max rw 1 : Nat))]
      discard <| run [".c", "yview", "moveto", fmtFrac ((q.y + (iy : Rat)) / (max rh 1 : Nat))]
  | some (.frac x y) =>
    discard <| run [".c", "xview", "moveto", fmtFrac x]
    discard <| run [".c", "yview", "moveto", fmtFrac y]
  | none => pure ()

/-- Shows the current page in the toolbar's page field (`Toolbar.entryText`: the number, or
the label when the document has labels) and the "of N" label next to it (task 9.7). -/
def showPageField (s : State) : IO Unit := do
  discard <| run ["::safepdf::setPage", Toolbar.entryText s.labels s.page,
    Toolbar.ofText s.labels s.page s.pageCount, "1"]

/-- Updates title, labels and (when the page, document, zoom or rotation changed, or a scroll
is pending) the page image. -/
def refresh (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  discard <| run ["wm", "title", ".", s.title]
  match s.path, s.doc with
  | some path, some doc =>
    showPageField s
    discard <| run ["::safepdf::zoomShow", s.zoomSel.label, s.zoomSel.selected, "1"]
    let some vp := viewParams s doc s.page | return
    let pct := match s.zoomSel.mode with
      | some (.scale p) => if vp.capped then View.zoomPct vp.zoom s.scaling else p
      | _ => View.zoomPct vp.zoom s.scaling
    let key : View.Key := ⟨s.gen, s.page, vp.zoom, s.rot⟩
    if s.shown == some key && s.pending.isNone then return
    st.modify ({ · with shown := some key })
    let (res, time) ← fetch st doc key
    let s ← st.get
    match res with
    | .ok img =>
      st.modify ({ · with shownImg := some img })
      Shim.photoPut photoName img.w.toUInt32 img.h.toUInt32
        (Marks.composite vp.zoom vp.rot vp.box img.w img.h img.data (visibleMarks s))
      -- Centre the page when it is smaller than the canvas; the scroll region is the page
      -- plus the margin (at least the canvas).
      let m := View.margin
      let ix := max m ((s.canvasW - img.w) / 2)
      let iy := max m ((s.canvasH - img.h) / 2)
      let rw := max s.canvasW (img.w + 2 * m)
      let rh := max s.canvasH (img.h + 2 * m)
      discard <| run [".c", "coords", "page", toString ix, toString iy]
      discard <| run [".c", "coords", "pageframe", toString (ix - 1), toString (iy - 1),
        toString (ix + img.w), toString (iy + img.h)]
      discard <| run [".c", "itemconfigure", "pageframe", "-state", "normal"]
      discard <| run [".c", "configure", "-scrollregion", s!"0 0 {rw} {rh}"]
      applyScroll s vp ix iy rw rh
      st.modify ({ · with imgX := ix, imgY := iy, shownZoom := vp.zoom, shownRot := vp.rot,
                          pending := none, regionW := rw, regionH := rh })
      drawOverlay st
      let how := match time with
        | some t => s!"rendered in {formatMs t} ms"
        | none => "from cache"
      let notes := (if vp.capped then
          s!"; zoom limited to {View.maxViewPixels / 1048576} Mpx per page" else "") ++
        (if vp.cropped then s!"; cropped to {limits.maxPageSide} px per side" else "")
      setStatus s!"{path}: {Links.pageText s.labels s.page s.pageCount}, {pct}% ({modeName s.zoomSel}), \
        rotation {View.rotDeg s.rot}, {img.w}x{img.h} px, {how}{notes}"
      if s.page + 1 < s.pageCount then
        discard <| run ["after", "100", "::safepdf::emit prefetch"]
    | .error e =>
      st.modify ({ · with pending := none, shownImg := none })
      discard <| run [".c", "delete", "sel", "hit", "mark", "bub"]
      st.modify ({ · with bubble := none, pickerAt := none })
      discard <| run [".c", "itemconfigure", "pageframe", "-state", "hidden"]
      discard <| run [photoName, "blank"]
      setStatus s!"{path}: {Links.pageText s.labels s.page s.pageCount}: cannot render: {renderError e}"
  | _, _ =>
    discard <| run ["::safepdf::setPage", "", "", "0"]
    discard <| run ["::safepdf::zoomShow", s.zoomSel.label, s.zoomSel.selected, "0"]
    discard <| run [".c", "delete", "sel", "hit", "mark", "bub"]
    st.modify ({ · with bubble := none, pickerAt := none })
    discard <| run [".c", "itemconfigure", "pageframe", "-state", "hidden"]
    discard <| run [photoName, "blank"]

/-- Shows the current page image again with the marks of the page multiplied in, and redraws
the overlays (after a mark was added, removed or recoloured; task 9.4). -/
def repaint (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  if let (some img, some bx) := (s.shownImg, shownBox s) then
    Shim.photoPut photoName img.w.toUInt32 img.h.toUInt32
      (Marks.composite s.shownZoom s.shownRot bx img.w img.h img.data (visibleMarks s))
  drawOverlay st

/-- Renders the page after the current one into the cache when it is small enough
(`prefetchPixels`) and not cached yet. -/
def prefetch (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some doc := s.doc | return
  let p := s.page + 1
  let some vp := viewParams s doc p | return
  let key : View.Key := ⟨s.gen, p, vp.zoom, s.rot⟩
  if s.cache.contains key then return
  let (w, h) := View.pixelSize vp.zoom vp.rot vp.box
  if w * h > prefetchPixels then return
  discard <| fetch st doc key

/-! ## Outline panel (task 8.2d) -/

/-- Shows or hides the outline sidebar (the left pane of `.pw`); the sidebar toggle button
looks pressed while it is shown (PDF.js's `toggled`). -/
def showOutline (st : IO.Ref State) (on : Bool) : IO Unit := do
  let s ← st.get
  -- The View → Outline check entry toggles its variable before it runs the command; set it
  -- back to the panel's real state whatever happens below.
  discard <| run ["set", Menu.outlineVar, if s.outlineShown then "1" else "0"]
  if on == s.outlineShown then return
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

/-- Opens `path`: reads and parses it, builds the page tree, shows page 1. Every failure
ends up in the status line with an empty page. -/
def openFile (st : IO.Ref State) (path : String) : IO Unit := do
  st.modify fun s => { s with path := some path, doc := none, page := 0, shown := none }
  st.modify fun s => { s with gen := s.gen + 1, cache := ({} : View.Cache), pending := some .top,
                              texts := #[], sel := none, pressPt := none, hit := none,
                              labels := #[], outline := #[], links := #[], hover := none,
                              history := {}, marks := {}, markSel := none, shownImg := none }
  discard <| run ["destroy", ".note"]
  fillOutline st
  showOutline st false
  st.modify ({ · with toggleShown := none })
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
      st.modify ({ · with doc := some doc, texts := Array.replicate doc.pages.size none })
      let (labels, outline) ← IO.lazyPure fun _ =>
        (Links.labels doc limits, (Links.outlineEntries doc limits).toArray)
      st.modify ({ · with labels, outline, links := Array.replicate doc.pages.size none })
      fillOutline st
      showOutline st (Sidebar.shownOnLoad (!outline.isEmpty))
      -- Lay the window out again so that the first render uses the canvas size beside the
      -- outline panel.
      discard <| run ["update", "idletasks"]
      if let (some w, some h) := ((← run ["winfo", "width", ".c"]).toNat?,
          (← run ["winfo", "height", ".c"]).toNat?) then
        if w ≥ 2 && h ≥ 2 then st.modify ({ · with canvasW := w, canvasH := h })
      if doc.pages.size == 0 then
        refresh st
        setStatus s!"{path}: the document has no pages"
      else refresh st

/-- Moves to page `p` (clamped to the document), scrolled to `where`, and refreshes. -/
def goTo (st : IO.Ref State) (p : Nat) (whereTo : ScrollTo := .top) : IO Unit := do
  let s ← st.get
  if s.pageCount == 0 then return
  let p := min p (s.pageCount - 1)
  if p != s.page then
    st.modify ({ · with page := p, pending := some whereTo, sel := none, pressPt := none,
                        hover := none, wheel := {}, markSel := none })
    discard <| run [".c", "configure", "-cursor", ""]
    refresh st

/-- Remembers the page point at window position `(wx, wy)` of the canvas, so that the next
refresh keeps it there (C2 anchoring). Nothing when no page is shown. -/
def anchorAt (st : IO.Ref State) (wx wy : Nat) : IO Unit := do
  let s ← st.get
  let some doc := s.doc | return
  let some page := doc.pages[s.page]? | return
  if s.shown.isNone || !(0 < s.shownZoom) then return
  let cx ← run [".c", "canvasx", toString wx]
  let cy ← run [".c", "canvasy", toString wy]
  let (some cx, some cy) := (View.parseDecimal cx, View.parseDecimal cy) | return
  let q : Pt := ⟨cx - (s.imgX : Rat), cy - (s.imgY : Rat)⟩
  let p := toPage s.shownZoom s.shownRot (Box.ofRect page.cropBox) q
  st.modify ({ · with pending := some (.anchor wx wy p) })

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
  -- The current percentage: the fixed one, or the one a fit mode came out at (rounded).
  let cur := match s.zoomSel.mode with
    | some (.scale p) => p
    | _ => View.zoomPct s.shownZoom s.scaling
  match what with
  | "in" => setMode st (.pct (View.stepIn cur)) pos
  | "out" => setMode st (.pct (View.stepOut cur)) pos
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

/-- The two numbers of an `xview`/`yview` result. -/
def viewFracs (s : String) : Option (Rat × Rat) :=
  match (s.splitOn " ").filter (!·.isEmpty) with
  | [a, b] => do return (← View.parseDecimal a, ← View.parseDecimal b)
  | _ => none

/-- Handles `wheel AXIS KIND D` (task 9.2): a wheel or trackpad delta `D` of kind `KIND`
(`notch`, `line`, `pixel`; `View.WheelKind`) on axis `x` or `y`. `View.wheelStep` decides:
scroll within the page (small deltas accumulate), or, on the vertical axis after reaching the
edge and pushing on past it by `View.wheelThreshold`, turn to the top of the next page or the
bottom of the previous one, as the keys do. -/
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
  let (w, act) := View.wheelStep s.wheel now (View.wheelPixels kind d view) (kind == .pixel) isY
    top view region (View.wheelThreshold kind view)
  match act with
  | .none => st.modify ({ · with wheel := w })
  | .scrollTo p =>
    st.modify ({ · with wheel := w })
    -- Tk rounds `moveto` to the nearest pixel, so the fraction p / region lands on p.
    discard <| run [".c", if isY then "yview" else "xview", "moveto",
      fmtFrac ((p : Rat) / (max region 1 : Nat))]
  | .next =>
    if s.page + 1 < s.pageCount then goTo st (s.page + 1) .top
    st.modify ({ · with wheel := w })
  | .prev =>
    if s.page > 0 then goTo st (s.page - 1) .bottom
    st.modify ({ · with wheel := w })

/-- Rotates the view by a quarter turn (`cw` or `ccw`), keeping the window centre's page
point at the centre. -/
def rotate (st : IO.Ref State) (cw : Bool) : IO Unit := do
  let s ← st.get
  if s.doc.isNone then return
  let (wx, wy) := anchorPos s none
  anchorAt st wx wy
  st.modify fun s => { s with rot := if cw then View.rotCw s.rot else View.rotCcw s.rot }
  refresh st

/-- The `tk_getOpenFile` dialog; opens the chosen file (nothing when cancelled). -/
def openDialog (st : IO.Ref State) : IO Unit := do
  let path ← run ["tk_getOpenFile", "-parent", ".", "-title", "Open PDF", "-filetypes",
    "{{PDF files} {.pdf .PDF}} {{All files} *}"]
  if !path.isEmpty then openFile st path

/-! ## Menubar (task 9.1) -/

/-- Closes the document (File → Close, Ctrl+W): the window stays, empty, as after starting
without a file. -/
def closeFile (st : IO.Ref State) : IO Unit := do
  st.modify fun s => { s with path := none, doc := none, page := 0, shown := none,
                              gen := s.gen + 1, cache := ({} : View.Cache), pending := none,
                              texts := #[], sel := none, pressPt := none, query := #[],
                              hit := none, labels := #[], outline := #[], links := #[],
                              hover := none, history := {}, toggleShown := none,
                              marks := {}, markSel := none, shownImg := none,
                              ui := { s.ui with tool := false, popover := false,
                                                picker := false },
                              bubble := none, pickerAt := none, bubblePress := false }
  discard <| run ["pack", "forget", ".find", ".goto"]
  discard <| run ["destroy", ".note"]
  discard <| run ["::safepdf::popHide"]
  discard <| run ["::safepdf::btnToggled", ".bar.highlight", "0"]
  discard <| run ["set", Menu.hlToolVar, "0"]
  fillOutline st
  showOutline st false
  discard <| run [".c", "configure", "-cursor", ""]
  refresh st
  setStatus "No file. Press Ctrl+O or Open... to choose a PDF."

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

/-- Builds the menubar `.menubar` from `Menu.menubar` (every word a literal through
`Tcl.quote`; the `-command` scripts are the model's constants) and attaches it to the main
window; then the mark entries of the context menu (`Menu.popupMarks`, task 9.4). -/
def buildMenus : IO Unit := do
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
        discard <| run [m.path, "add", "command", "-label", c.label, "-accelerator", c.accel,
          "-underline", toString c.underline, "-command", c.script]
      | .check c var =>
        discard <| run [m.path, "add", "checkbutton", "-label", c.label, "-accelerator", c.accel,
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
        "-accelerator", c.accel, "-command", c.popScript]

/-- Builds the toolbar from `Toolbar.layout` (task 9.7): icon buttons (`::safepdf::iconButton`
with the model's constant icon name, tooltip and script), separators, the page field and the
zoom drop-down (its menu `.zoommenu` lists `ZoomChoice.presets` as radio entries on
`::safepdf::zoomSel`), and the overflow menu `.more` (`Toolbar.overflow`). -/
def buildToolbar : IO Unit := do
  for (g, items) in Toolbar.layout do
    for it in items do
      match it with
      | .button b =>
        discard <| run ["::safepdf::iconButton", b.path, b.icon, b.tip, b.script]
        discard <| run ["::safepdf::barPack", b.path, g, "-padx", "2", "-pady", "4"]
      | .sep w =>
        discard <| run ["::safepdf::vsep", w]
        discard <| run ["::safepdf::barPack", w, g, "-padx", "2"]
      | .pageField => discard <| run ["::safepdf::pageField"]
      | .zoomBox => discard <| run ["::safepdf::zoomBox"]
  for c in Toolbar.ZoomChoice.presets do
    discard <| run [".zoommenu", "add", "radiobutton", "-label", c.label, "-value", c.key,
      "-variable", "::safepdf::zoomSel",
      "-command", "::safepdf::emit zoom choose $::safepdf::zoomSel"]
  for e in Toolbar.overflow do
    match e with
    | none => discard <| run [Toolbar.morePath, "add", "separator"]
    | some c =>
      discard <| run [Toolbar.morePath, "add", "command", "-label", c.label, "-accelerator",
        c.accel, "-command", c.script]

/-- The part of the state the enabled rules look at. -/
def menuCtx (s : State) : Menu.Ctx :=
  { hasDoc := s.doc.isSome && s.pageCount > 0, page := s.page, pages := s.pageCount,
    hasSel := s.sel.isSome, hasMark := s.markSel.isSome, hasOutline := !s.outline.isEmpty,
    canBack := !s.history.back.isEmpty, canForward := !s.history.fwd.isEmpty }

/-- Sets the `-state` of every menubar entry, overflow-menu entry and toolbar button whose
enabled state (`Toolbar.states`) changed since the last call, and shows or hides the sidebar
toggle (`Sidebar.toggleVisible`). Runs after every event. -/
def syncMenus (st : IO.Ref State) : IO Unit := do
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
  let vis := Sidebar.toggleVisible (c.hasDoc && c.hasOutline)
  if s.toggleShown != some vis then
    discard <| run ["::safepdf::showToggle", if vis then "1" else "0"]
  st.modify ({ · with menuStates := now, toggleShown := some vis })

/-! ## Links, jumps, history, go to page (task 8.2d) -/

/-- The links of page `p`, read on first use (`Links.pageLinks`) and cached. -/
def linksOf (st : IO.Ref State) (p : Nat) : IO (Array Links.Link) := do
  let s ← st.get
  let some doc := s.doc | return #[]
  match s.links[p]? with
  | some (some ls) => return ls
  | _ =>
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
                              sel := if p == s.page then s.sel else none, wheel := {} }
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

/-- The link of the shown page under window position `(wx, wy)`, if any. -/
def linkUnder (st : IO.Ref State) (wx wy : Int) : IO (Option (Nat × Links.Link)) := do
  let some p ← pagePoint st wx wy | return none
  return Links.linkAt (← linksOf st (← st.get).page) p

/-- Pointer motion: over a link the cursor becomes a hand and the status line shows the
target (the full address of a URI); leaving it restores the status line. -/
def hover (st : IO.Ref State) (pos : Option (Int × Int)) : IO Unit := do
  let s ← st.get
  if s.pressPt.isSome then return
  let l ← match pos with
    | some (x, y) => linkUnder st x y
    | none => pure none
  let idx := l.map (·.1)
  if idx == s.hover then return
  if s.hover.isNone then
    let cur ← run [".status", "cget", "-text"]
    st.modify ({ · with savedStatus := cur })
  st.modify ({ · with hover := idx })
  match l with
  | some (_, k) =>
    discard <| run [".c", "configure", "-cursor", "hand2"]
    setStatus (Links.describe s.labels s.pageCount k.action)
  | none =>
    discard <| run [".c", "configure", "-cursor", ""]
    setStatus (← st.get).savedStatus

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
  if m.isNote then "note" else s!"{m.color.name} highlight"

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

/-- Brings the Tk side in step with the Highlight tool state (task 9.8): the Edit menu's check
variables, the toolbar button's toggled look, and the pop-over (drawn and placed under the
Highlight button, right-aligned with it, `Bubble.Popover.left`; hidden when closed). -/
def syncTool (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let b (v : Bool) : String := if v then "1" else "0"
  discard <| run ["set", Menu.hlToolVar, b s.ui.tool]
  discard <| run ["set", Menu.showAllVar, b s.ui.showAll]
  discard <| run ["::safepdf::btnToggled", ".bar.highlight", b s.ui.tool]
  if s.ui.popover && s.doc.isSome then
    drawPopover s
    let num? (w : List String) : IO Rat := return (View.parseDecimal (← run w)).getD 0
    let bx := (← num? ["winfo", "rootx", ".bar.highlight"]) - (← num? ["winfo", "rootx", "."])
    let bw ← num? ["winfo", "width", ".bar.highlight"]
    let ww ← num? ["winfo", "width", "."]
    discard <| run ["::safepdf::popShow", toString (Bubble.Popover.left bx bw ww).floor]
  else discard <| run ["::safepdf::popHide"]

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
      repaint st
      setStatus s!"page {p + 1}: highlighted {(Select.rangeText ix.cells a b).length} \
        characters in {c.name} (click it to select it; Delete removes it)"
    | none => setStatus "nothing to highlight"
  | none =>
    match s.markSel, chosen with
    | some id, some c =>
      st.modify ({ · with marks := s.marks.recolor id c })
      repaint st
      setStatus s!"mark recoloured: {c.name}"
    | _, some c => setStatus s!"highlight colour: {c.name} (select text, then Highlight)"
    | _, none => setStatus "select text first (drag over it or double-click a word), then Highlight"

/-- Opens the popup of note `id` next to its icon. -/
def openNote (st : IO.Ref State) (id : Nat) : IO Unit := do
  let s ← st.get
  let some m := s.marks.find? id | return
  let some bx := shownBox s | return
  let some ib := m.iconBox bx | return
  let (_, y0, x1, _) := canvasRect s bx ib
  let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
    View.parseDecimal (← run [".c", "canvasy", "0"])) | return
  let (some rx, some ry) := ((← run ["winfo", "rootx", ".c"]).toInt?,
    (← run ["winfo", "rooty", ".c"]).toInt?) | return
  let x := rx + (x1 - vx).ceil + 8
  let y := ry + (y0 - vy).floor
  discard <| run ["::safepdf::noteEdit", toString id, m.text, toString (max 0 x),
    toString (max 0 y)]

/-- Handles `note [X Y]` (Edit → Add note…, the edit bubble's Comment, or the context menu at
window position `(X, Y)`): adds a note anchored to the selection on the shown page; else,
without a position and with a highlight selected, opens that highlight's comment (the note
anchored to its quads, `Marks.Store.noteOn`) or adds one in its colour (task 9.8); else a note
at the page point under `(X, Y)`, else at the window centre; selects it and opens its popup. -/
def addNote (st : IO.Ref State) (pos : Option (Int × Int)) : IO Unit := do
  let s ← st.get
  if s.doc.isNone || (shownBox s).isNone then return
  let mut anchor : Option Marks.Anchor := none
  if let some (p, a, b) := s.sel then
    if p == s.page then
      if let .ok ix ← pageIndex st p then
        let qs := Select.rangeBoxes ix.cells a b
        if !qs.isEmpty then anchor := some (.quads qs)
  -- The comment of the selected highlight (the edit bubble's Comment, task 9.8): its note,
  -- or a new note anchored to its quads in its colour.
  let mut color := Marks.Color.yellow
  if anchor.isNone && pos.isNone then
    if let some m := s.markSel.bind s.marks.find? then
      if m.page == s.page && !m.isNote && !m.quads.isEmpty then
        if let some id := s.marks.noteOn s.page m.quads then
          setStatus s!"page {s.page + 1}: comment of the {m.color.name} highlight"
          openNote st id
          return
        anchor := some (.quads m.quads)
        color := m.color
  if anchor.isNone then
    let (wx, wy) := pos.getD (((s.canvasW / 2 : Nat) : Int), ((s.canvasH / 2 : Nat) : Int))
    anchor := (← pagePoint st wx wy).map .point
  let some anc := anchor | return
  let (marks, id) := s.marks.addNote s.page color "" anc
  st.modify ({ · with marks, markSel := some id, sel := none })
  repaint st
  setStatus s!"page {s.page + 1}: note added (type its text, then Save)"
  openNote st id

/-- Handles `noteSave ID TEXT` from the note popup. -/
def noteSave (st : IO.Ref State) (idS text : String) : IO Unit := do
  let some id := idS.toNat? | return
  let s ← st.get
  if (s.marks.find? id).isNone then return
  st.modify ({ · with marks := s.marks.setText id text })
  drawOverlay st
  setStatus s!"note saved ({text.length} characters)"

/-- Removes mark `id` (Delete, Edit → Delete mark, the note popup's Delete). -/
def deleteMark (st : IO.Ref State) (id : Nat) : IO Unit := do
  let s ← st.get
  let some m := s.marks.find? id | return
  st.modify ({ · with marks := s.marks.remove id,
                      markSel := if s.markSel == some id then none else s.markSel })
  repaint st
  setStatus s!"{markName m} deleted"

/-- Handles `markDelete`: removes the selected mark. -/
def markDelete (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  match s.markSel with
  | some id => deleteMark st id
  | none => if s.doc.isSome then setStatus "no mark selected (click a highlight or note)"

/-- Selects the mark under page point `p` of the shown page, if any (a note also opens its
popup when `openIt` is set). Returns whether there was one. -/
def selectMarkAt (st : IO.Ref State) (p : Pt) (openIt : Bool) : IO Bool := do
  let s ← st.get
  let some bx := shownBox s | return false
  let store := if s.ui.showAll then s.marks
    else { s.marks with marks := s.marks.marks.filter (·.isNote) }
  match store.hitAt bx s.page p with
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
    if let some p ← pagePoint st wx wy then
      if !(← selectMarkAt st p false) && (← st.get).markSel.isSome then
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
    let keep := on || ((s.markSel.bind s.marks.find?).map (·.isNote)).getD true
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
      if !m.isNote then
        st.modify ({ · with marks := s.marks.recolor m.id c })
        repaint st
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

/-- Escape (task 9.8): closes the colour picker and the pop-over and dismisses the bubble (the
text selection and the selected mark are cleared; the tool stays on). -/
def escape (st : IO.Ref State) : IO Unit := do
  st.modify fun s => { s with ui := s.ui.escape, sel := none, markSel := none, pressPt := none }
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
      match Bubble.hit k r cx cy with
      | some .color =>
        st.modify fun s => { s with ui := { s.ui with picker := !s.ui.picker } }
        drawOverlay st
      | some b =>
        if let some c := b.cmd? then discard <| run ["after", "idle", c.script]
      | none => pure ()
      return true
  return false

/-- Handles `tool NAME` (an annotation tool, Print or Save): Highlight works (task 9.4); the
others are not available yet. -/
def tool (st : IO.Ref State) (name : String) : IO Unit := do
  match Toolbar.toolOf name with
  | some .highlight => toolHighlight st
  | some t => setStatus s!"{t.tip}: not available yet ({t.task})"
  | none => setStatus s!"internal: unknown tool {name}"

/-! ## Selection, copy and search (task 8.2c) -/

/-- Status line after a selection change. -/
def selStatus (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some (p, a, b) := s.sel | return
  if let .ok ix ← pageIndex st p then
    setStatus s!"page {p + 1}: selected {(Select.rangeText ix.cells a b).length} characters \
      (Ctrl+C copies)"

/-- Mouse press at window position `(wx, wy)`: clears the selection and remembers the page
point where a drag starts. -/
def press (st : IO.Ref State) (wx wy : Int) : IO Unit := do
  st.modify ({ · with bubblePress := false })
  if ← bubbleClick st wx wy then return
  st.modify fun s => { s with sel := none, pressPt := none, markSel := none,
                              ui := { s.ui with picker := false } }
  if let some p ← pagePoint st wx wy then st.modify ({ · with pressPt := some p })
  drawOverlay st

/-- Mouse drag (`final`: release) to `(wx, wy)`: selects the glyphs from the one nearest to
the press point to the one nearest to this point, in reading order. A release where the press
was (a click) selects nothing. -/
def dragTo (st : IO.Ref State) (wx wy : Int) (final : Bool) : IO Unit := do
  let s ← st.get
  if s.bubblePress then
    if final then st.modify ({ · with bubblePress := false })
    return
  let some p0 := s.pressPt | return
  if final then st.modify ({ · with pressPt := none })
  let some p1 ← pagePoint st wx wy | return
  if final && p0 == p1 then
    -- A click in place: select the mark under it (task 9.4; marks lie above links), else
    -- activate the link under it (task 8.2d).
    if ← selectMarkAt st p1 true then return
    if let some (_, l) := Links.linkAt (← linksOf st s.page) p1 then activate st l.action
    return
  match ← pageIndex st s.page with
  | .ok ix =>
    if let some (a, b) := Select.dragRange ix.cells p0 p1 then
      st.modify ({ · with sel := some (s.page, a, b) })
      drawOverlay st
      if final then
        selStatus st
        -- With the Highlight tool on, the mouse-up highlights at once (PDF.js, task 9.8).
        if (← st.get).ui.highlightOnRelease true then highlight st none
  | .error e => setStatus s!"page {s.page + 1}: no text: {e}"

/-- Double click at `(wx, wy)`: selects the word of the nearest glyph (`Select.wordAt`). -/
def selectWord (st : IO.Ref State) (wx wy : Int) : IO Unit := do
  st.modify ({ · with pressPt := none })
  let s ← st.get
  -- The second click of a double click on the bubble is not a word selection (task 9.8).
  if let some (cx, cy) ← canvasPos wx wy then
    if (s.bubble.any fun (_, r) => r.contains cx cy) || (s.pickerAt.any (·.contains cx cy)) then
      return
  let some p ← pagePoint st wx wy | return
  match ← pageIndex st s.page with
  | .ok ix =>
    if let some i := Select.nearest ix.cells p then
      let (a, b) := Select.wordAt ix.cells i
      st.modify ({ · with sel := some (s.page, a, b) })
      drawOverlay st
      selStatus st
      if (← st.get).ui.highlightOnRelease true then highlight st none
  | .error e => setStatus s!"page {s.page + 1}: no text: {e}"

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

/-- Copies the selected text to the clipboard (Ctrl+C); the text is one quoted Tcl word. -/
def copySel (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  match s.sel with
  | some (p, a, b) =>
    if let .ok ix ← pageIndex st p then
      let t := Select.rangeText ix.cells a b
      discard <| run ["clipboard", "clear"]
      discard <| run ["clipboard", "append", "--", t]
      setStatus s!"copied {t.length} characters"
  | none => setStatus "nothing selected (drag over text, double-click a word, or Ctrl+A)"

/-- Scrolls the current search hit into view (centred on an axis where it is not visible). -/
def scrollToHit (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some (p, k) := s.hit | return
  if p != s.page then return
  let some bx := shownBox s | return
  let .ok ix ← pageIndex st p | return
  let some (a, b) := (ix.hits s.query)[k]? | return
  let some u := (Select.rangeBoxes ix.cells a b).foldl (fun acc b =>
    some (match acc with | some u => Select.Box.union u b | none => b)) none | return
  let (x0, y0, x1, y1) := canvasRect s bx u
  let (some vx, some vy) := (View.parseDecimal (← run [".c", "canvasx", "0"]),
    View.parseDecimal (← run [".c", "canvasy", "0"])) | return
  let cw : Rat := s.canvasW
  let ch : Rat := s.canvasH
  if x0 < vx || vx + cw < x1 then
    discard <| run [".c", "xview", "moveto", fmtFrac (((x0 + x1) / 2 - cw / 2) / (s.regionW : Rat))]
  if y0 < vy || vy + ch < y1 then
    discard <| run [".c", "yview", "moveto", fmtFrac (((y0 + y1) / 2 - ch / 2) / (s.regionH : Rat))]

/-- The next (`forward`) or previous search hit after the current one, as (page, index on
the page, hits on the page, wrapped around). Searches the current page, then the following
(preceding) pages, wrapping around to the current page. -/
def nextHit (st : IO.Ref State) (forward : Bool) : IO (Option (Nat × Nat × Nat × Bool)) := do
  let s ← st.get
  let n := s.pageCount
  let q := s.query
  let cur := match s.hit with
    | some (p, k) => if p == s.page then some k else none
    | none => none
  if let .ok ix ← pageIndex st s.page then
    let c := (ix.hits q).size
    let cand := if forward then some ((cur.map (· + 1)).getD 0)
      else match cur with
        | some k => if k > 0 then some (k - 1) else none
        | none => if c > 0 then some (c - 1) else none
    if let some k := cand then
      if k < c then return some (s.page, k, c, false)
  for i in [1:n + 1] do
    let p := if forward then (s.page + i) % n else (s.page + n - i % n) % n
    if let .ok ix ← pageIndex st p then
      let c := (ix.hits q).size
      if c > 0 then
        let wrapped := if forward then p ≤ s.page else p ≥ s.page
        return some (p, if forward then 0 else c - 1, c, wrapped)
  return none

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
    | none =>
      st.modify ({ · with hit := none })
      drawOverlay st
      setStatus s!"\"{qs}\": not found"
    | some (p, k, c, wrapped) =>
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
            s!"{← run [".c", "coords", "sel"]}\n{s'.imgX} {s'.imgY}\n"
          try discard <| run [photoName, "write", file "text-page-1.ppm", "-format", "ppm"]
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
document of at least two pages: the toolbar layout, the sidebar (shown with its toggle only
when the document has an outline; collapsing/expanding a row with children through its
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
  out := out.push s!"tools: {← btnStates [".bar.highlight", ".bar.comment", ".bar.text", ".bar.draw", ".bar.image", ".bar.print", ".bar.save"]}"
  -- A disabled tool ignores clicks.
  let click (w : String) : IO Unit := do
    sendEvent w "<ButtonPress-1>" ["-x", "16", "-y", "16"]
    sendEvent w "<ButtonRelease-1>" ["-x", "16", "-y", "16"]
  let st0 ← run [".status", "cget", "-text"]
  click ".bar.comment"
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
    try run [photoName, "get", toString q.x.floor, toString q.y.floor]
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
    try run [photoName, "get", toString q.x.floor, toString q.y.floor]
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
  if s.smokeMode == "nav" then smokeNav st dir; return
  if s.smokeMode == "menu" then smokeMenu st dir; return
  if s.smokeMode == "toolbar" then smokeToolbar st dir; return
  if s.smokeMode == "bubble" then
    try smokeBubble st dir
    catch e =>
      IO.FS.writeFile ((dir : System.FilePath) / "bubble.txt") s!"error: {e}\n"
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
    try discard <| run [photoName, "write", ((dir : System.FilePath) / name).toString,
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
  | ["next"] => goTo st (s.page + 1)
  | ["prev"] => if s.page > 0 then goTo st (s.page - 1)
  | ["prevEnd"] => if s.page > 0 then goTo st (s.page - 1) .bottom
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
  | ["outlineToggle"] => showOutline st (Sidebar.afterToggle s.outlineShown (!s.outline.isEmpty))
  | ["olToggle", k] => olToggle st k
  | ["pageEntry", txt] => pageEntry st txt
  | ["pageRevert"] => if s.doc.isSome && s.pageCount > 0 then showPageField s
  | ["tool", name] => tool st name
  | ["highlight"] => highlight st none
  | ["highlight", c] => highlight st (some c)
  | ["note"] => addNote st none
  | ["note", x, y] => addNote st (intPos x y)
  | ["noteSave", id, text] => noteSave st id text
  | ["noteDelete", id] => if let some id := id.toNat? then deleteMark st id
  | ["markDelete"] => markDelete st
  | ["hlTool"] => hlToolToggle st
  | ["showAll"] => toggleShowAll st
  | ["escape"] => escape st
  | ["popClick", x, y] => popClick st x y
  | ["popDrag", x, y] => popDrag st x y
  | ["popup", x, y, rx, ry] => popup st x y rx ry
  | ["wheel", axis, kind, d] => wheel st axis kind d
  | ["close"] => closeFile st
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
Ctrl+Q quit. The menubar (File, Edit, View, Go) has every command.
Mouse drag selects text, double-click a word; Ctrl+A select page; Ctrl+C copy;
Ctrl+F find (Enter/F3 next, Shift+F3 previous, Escape close).
h or the Highlight button highlights the selection (the button without one: Highlight
tool and its pop-over); a selection shows a Highlight bubble, a selected highlight its
colour/comment/delete bubble; Escape dismisses them; right button: Highlight colours,
Add note...; click a mark to select it (a note opens its text), Delete removes it.
F9 outline panel; click a link to follow it (external addresses are only shown and, if
confirmed, copied); Alt+Left/Alt+Right back/forward; Ctrl+G go to a page number or label.
SAFEPDF_VIEWER_SMOKE=DIR: scripted smoke test writing images and state into DIR, then exit
(SAFEPDF_VIEWER_SMOKE_MODE=text: the selection/copy/search steps instead;
SAFEPDF_VIEWER_SMOKE_MODE=nav: the outline/link/history/go-to steps;
SAFEPDF_VIEWER_SMOKE_MODE=menu: the menubar steps;
SAFEPDF_VIEWER_SMOKE_MODE=toolbar: the toolbar and sidebar steps;
SAFEPDF_VIEWER_SMOKE_MODE=marks: the highlight and note steps;
SAFEPDF_VIEWER_SMOKE_MODE=bubble: the selection bubble and Highlight pop-over steps).
SAFEPDF_VIEWER_GEOMETRY=WxH: initial window size (default 1200x960)."

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
  let smokeMode := (← IO.getEnv "SAFEPDF_VIEWER_SMOKE_MODE").getD ""
  let subst ← Fonts.loadSubstFonts limits
  let st ← IO.mkRef ({ smokeDir, smokeMode, subst } : State)
  Shim.setEmitHandler (safeHandle st)
  try
    discard <| Shim.eval setupScript
    buildMenus
    buildToolbar
    if let some g ← IO.getEnv "SAFEPDF_VIEWER_GEOMETRY" then
      if let some (w, h) := parseGeometry g then
        discard <| run ["wm", "geometry", ".", s!"{w}x{h}"]
    if smokeDir.isSome then discard <| run ["set", "::safepdf::autoConfirm", "1"]
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
  match file with
  | some f => guarded (openFile st f)
  | none =>
    setStatus "No file. Press Ctrl+O or Open... to choose a PDF."
    if smokeDir.isNone then discard <| run ["after", "idle", "::safepdf::emit open"]
  guarded (syncMenus st)
  if smokeDir.isSome then discard <| run ["after", "300", "::safepdf::emit smoke"]
  Shim.mainLoop
  return 0

end SafePdf.Shell.App.Viewer
