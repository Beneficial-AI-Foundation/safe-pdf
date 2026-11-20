import SafePdf.Shell.App.Shim
import SafePdf.Shell.App.Tcl
import SafePdf.Shell.App.View
import SafePdf.Shell.App.Select
import SafePdf.Core.Annot
import SafePdf.Shell.Inspect
import SafePdf.Shell.Views.Pages

/-!
# Native viewer (tasks 8.2a, 8.2b, 8.2c; Plan.md §6 Phase 8, §8 native app, §10 `SafePdf/Shell/`)

The unverified, replaceable shell of the viewer (Plan.md §8): one Tk window with a toolbar
(Open…, Prev, Next, zoom out/in, 100 %, fit page, fit width, rotate left/right, page k/n,
zoom %), a scrollable canvas showing the current page as a Tk photo image, and a status line.
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
* **Page cache** (`View.Cache`): render results keyed by (document generation, page, zoom,
  rotation), LRU, at most `View.cacheBytes` (256 MiB) of images. After a page is shown the
  next page is prefetched 100 ms later (same event loop, no threads) when it is at most
  `prefetchPixels` pixels.
* **Scrolling.** The canvas has scroll bars; its scroll region is the page image plus a margin.
  Keys (Tcl proc `::safepdf::step`): `Down`/`Up` and `Right`/`Left` scroll by a tenth of the window,
  `Next`/`space` and `Prior`/`BackSpace`/`Shift+space` by a window. Past the bottom (right) edge
  they move to the top of the next page; past the top they move to the bottom of the previous
  page (page-at-a-time). The mouse wheel scrolls (Shift: horizontally), Ctrl+wheel zooms
  about the mouse pointer.
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
  /-- Zoom mode. -/
  mode : View.Mode := .fitPage
  /-- User rotation (added to each page's `/Rotate`). -/
  rot : SafePdf.Core.Doc.Rotation := .r0
  /-- Screen scale: pixels per point (`tk scaling`). -/
  scaling : Rat := 4 / 3
  /-- Rendered pages. -/
  cache : View.Cache := {}
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
    let z0 := View.modeZoom s.mode s.canvasW s.canvasH s.scaling pw ph
    let (z, capped) := View.capZoom View.maxViewPixels z0 r bx
    ⟨z, r, bx, capped, View.cropped limits.maxPageSide z r bx⟩

/-- Last path component of a file name (for the window title). -/
def baseName (path : String) : String :=
  (System.FilePath.mk path).fileName.getD path

/-- Window title: `safe-pdf`, or `NAME - page k/n - safe-pdf`. -/
def State.title (s : State) : String :=
  match s.path, s.doc with
  | some p, some _ => s!"{baseName p} - page {s.page + 1}/{s.pageCount} - safe-pdf"
  | some p, none => s!"{baseName p} - safe-pdf"
  | none, _ => "safe-pdf"

/-- A fraction in `[0, 1]` as a decimal with six digits (for `xview`/`yview moveto`). -/
def fmtFrac (r : Rat) : String :=
  let r := max 0 (min 1 r)
  let n := (r * 1000000).floor.toNat
  s!"{n / 1000000}.{padLeft 6 '0' (toString (n % 1000000))}"

#guard fmtFrac (1 / 4) = "0.250000"
#guard fmtFrac 2 = "1.000000"
#guard fmtFrac (-1) = "0.000000"

/-- Name of a zoom mode for the status line. -/
def modeName : View.Mode → String
  | .fitPage => "fit page"
  | .fitWidth => "fit width"
  | .scale _ => "fixed"

/-! ## Tcl -/

/-- Evaluates a command built from literal words (every word quoted by `Tcl.quote`). -/
def run (words : List String) : IO String :=
  Shim.eval (Tcl.Script.render ⟨[Tcl.cmd words]⟩)

/-- Shows `msg` in the status line. -/
def setStatus (msg : String) : IO Unit := do
  discard <| run [".status", "configure", "-text", msg]

/-- The constant UI setup script (no data in it). Widgets: toolbar `.bar` (buttons, page
label `.bar.page`, zoom label `.bar.zoom`), canvas `.c` with scroll bars `.xs`/`.ys` gridded
in frame `.v`, the photo image `::safepdf::page` on canvas item tag `page`, status line
`.status`. Key bindings on the toplevel's bind tag `.`; canvas resizes are debounced and
reported as `emit resize W H`. -/
def setupScript : String := "
namespace eval ::safepdf { variable resizeId {}; variable query {} }
wm title . safe-pdf
wm geometry . 860x1040
wm minsize . 320 200
ttk::frame .bar
ttk::button .bar.open -text {Open...} -command {::safepdf::emit open}
ttk::button .bar.prev -text {< Prev} -command {::safepdf::emit prev}
ttk::button .bar.next -text {Next >} -command {::safepdf::emit next}
ttk::button .bar.zout -text {-} -width 2 -command {::safepdf::emit zoom out}
ttk::button .bar.zin -text {+} -width 2 -command {::safepdf::emit zoom in}
ttk::button .bar.actual -text {100%} -command {::safepdf::emit zoom actual}
ttk::button .bar.fitp -text {Fit page} -command {::safepdf::emit zoom fitpage}
ttk::button .bar.fitw -text {Fit width} -command {::safepdf::emit zoom fitwidth}
ttk::button .bar.rccw -text {Rotate left} -command {::safepdf::emit rotate ccw}
ttk::button .bar.rcw -text {Rotate right} -command {::safepdf::emit rotate cw}
ttk::label .bar.page -text {} -anchor w
ttk::label .bar.zoom -text {} -anchor w
pack .bar.open .bar.prev .bar.next .bar.zout .bar.zin .bar.actual .bar.fitp .bar.fitw \\
  .bar.rccw .bar.rcw -side left -padx 2 -pady 2
pack .bar.page .bar.zoom -side left -padx 8
ttk::frame .v
canvas .c -background gray60 -highlightthickness 0 -takefocus 1 -confine 1 \\
  -xscrollcommand {.xs set} -yscrollcommand {.ys set}
ttk::scrollbar .ys -orient vertical -command {.c yview}
ttk::scrollbar .xs -orient horizontal -command {.c xview}
grid .c -in .v -row 0 -column 0 -sticky nsew
grid .ys -in .v -row 0 -column 1 -sticky ns
grid .xs -in .v -row 1 -column 0 -sticky ew
grid rowconfigure .v 0 -weight 1
grid columnconfigure .v 0 -weight 1
image create photo ::safepdf::page
.c create image 8 8 -anchor nw -image ::safepdf::page -tags page
ttk::label .status -text {} -anchor w -relief sunken -padding {4 2}
pack .bar -side top -fill x
pack .status -side bottom -fill x
pack .v -side top -fill both -expand 1
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
proc ::safepdf::wheel {axis d} {
  if {$d > 0} { .c ${axis}view scroll -1 units } elseif {$d < 0} { .c ${axis}view scroll 1 units }
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
bind .c <MouseWheel> {::safepdf::wheel y %D; break}
bind .c <Shift-MouseWheel> {::safepdf::wheel x %D; break}
bind .c <Control-MouseWheel> {::safepdf::wheelZoom %D %x %y; break}
bind .c <Button-4> {::safepdf::wheel y 1; break}
bind .c <Button-5> {::safepdf::wheel y -1; break}
bind .c <Shift-Button-4> {::safepdf::wheel x 1; break}
bind .c <Shift-Button-5> {::safepdf::wheel x -1; break}
bind .c <Control-Button-4> {::safepdf::wheelZoom 1 %x %y; break}
bind .c <Control-Button-5> {::safepdf::wheelZoom -1 %x %y; break}
bind . <Control-o> {::safepdf::emit open}
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
bind .c <Button-3> {tk_popup .pop %X %Y}
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
  if {![winfo ismapped .find]} { pack .find -side top -fill x -after .bar }
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

/-- Redraws the highlight rectangles of the shown page: all search hits (tag `hit`, the
current one in orange) and the selection (tag `sel`). -/
def drawOverlay (st : IO.Ref State) : IO Unit := do
  discard <| run [".c", "delete", "sel", "hit"]
  let s ← st.get
  let some bx := shownBox s | return
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

/-! ## Rendering -/

/-- Renders page `p` of `doc` at `zoom` and user rotation `rot` with a fresh budget (the
inspector's `raster` view does the same). -/
def renderPage (doc : Doc) (p : Nat) (zoom : Rat) (rot : SafePdf.Core.Doc.Rotation) :
    IO (Except Error Clip.Image) := do
  match doc.pages[p]? with
  | some page =>
    IO.lazyPure fun _ =>
      (SafePdf.Core.Raster.Glyph.renderDocPage limits doc page zoom rot
        (SafePdf.Core.Filter.Budget.init limits)).1
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
    let r ← renderPage doc key.page key.zoom key.rot
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
  | none => pure ()

/-- Updates title, labels and (when the page, document, zoom or rotation changed, or a scroll
is pending) the page image. -/
def refresh (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  discard <| run ["wm", "title", ".", s.title]
  match s.path, s.doc with
  | some path, some doc =>
    discard <| run [".bar.page", "configure", "-text", s!"page {s.page + 1} of {s.pageCount}"]
    let some vp := viewParams s doc s.page | return
    let pct := match s.mode with
      | .scale p => if vp.capped then View.zoomPct vp.zoom s.scaling else p
      | _ => View.zoomPct vp.zoom s.scaling
    discard <| run [".bar.zoom", "configure", "-text", s!"{pct}%"]
    let key : View.Key := ⟨s.gen, s.page, vp.zoom, s.rot⟩
    if s.shown == some key && s.pending.isNone then return
    st.modify ({ · with shown := some key })
    let (res, time) ← fetch st doc key
    let s ← st.get
    match res with
    | .ok img =>
      Shim.photoPut photoName img.w.toUInt32 img.h.toUInt32 img.data
      -- Centre the page when it is smaller than the canvas; the scroll region is the page
      -- plus the margin (at least the canvas).
      let m := View.margin
      let ix := max m ((s.canvasW - img.w) / 2)
      let iy := max m ((s.canvasH - img.h) / 2)
      let rw := max s.canvasW (img.w + 2 * m)
      let rh := max s.canvasH (img.h + 2 * m)
      discard <| run [".c", "coords", "page", toString ix, toString iy]
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
      setStatus s!"{path}: page {s.page + 1}/{s.pageCount}, {pct}% ({modeName s.mode}), \
        rotation {View.rotDeg s.rot}, {img.w}x{img.h} px, {how}{notes}"
      if s.page + 1 < s.pageCount then
        discard <| run ["after", "100", "::safepdf::emit prefetch"]
    | .error e =>
      st.modify ({ · with pending := none })
      discard <| run [".c", "delete", "sel", "hit"]
      discard <| run [photoName, "blank"]
      setStatus s!"{path}: page {s.page + 1}: cannot render: {renderError e}"
  | _, _ =>
    discard <| run [".bar.page", "configure", "-text", ""]
    discard <| run [".bar.zoom", "configure", "-text", ""]
    discard <| run [".c", "delete", "sel", "hit"]
    discard <| run [photoName, "blank"]

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

/-- Opens `path`: reads and parses it, builds the page tree, shows page 1. Every failure
ends up in the status line with an empty page. -/
def openFile (st : IO.Ref State) (path : String) : IO Unit := do
  st.modify fun s => { s with path := some path, doc := none, page := 0, shown := none }
  st.modify fun s => { s with gen := s.gen + 1, cache := ({} : View.Cache), pending := some .top,
                              texts := #[], sel := none, pressPt := none, hit := none }
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
    st.modify ({ · with page := p, pending := some whereTo, sel := none, pressPt := none })
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
def setMode (st : IO.Ref State) (mode : View.Mode) (pos : Option (Nat × Nat)) : IO Unit := do
  let s ← st.get
  if s.doc.isNone then return
  let (wx, wy) := anchorPos s pos
  anchorAt st wx wy
  st.modify ({ · with mode })
  refresh st

/-- Handles `zoom in|out|actual|fitpage|fitwidth ?X Y?`. -/
def zoom (st : IO.Ref State) (what : String) (pos : Option (Nat × Nat)) : IO Unit := do
  let s ← st.get
  -- The current percentage: the fixed one, or the one a fit mode came out at (rounded).
  let cur := match s.mode with
    | .scale p => p
    | _ => View.zoomPct s.shownZoom s.scaling
  match what with
  | "in" => setMode st (.scale (View.stepIn cur)) pos
  | "out" => setMode st (.scale (View.stepOut cur)) pos
  | "actual" => setMode st (.scale 100) pos
  | "fitpage" => setMode st .fitPage pos
  | "fitwidth" => setMode st .fitWidth pos
  | _ => setStatus s!"internal: unknown zoom {what}"

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
  st.modify ({ · with sel := none, pressPt := none })
  if let some p ← pagePoint st wx wy then st.modify ({ · with pressPt := some p })
  drawOverlay st

/-- Mouse drag (`final`: release) to `(wx, wy)`: selects the glyphs from the one nearest to
the press point to the one nearest to this point, in reading order. A release where the press
was (a click) selects nothing. -/
def dragTo (st : IO.Ref State) (wx wy : Int) (final : Bool) : IO Unit := do
  let s ← st.get
  let some p0 := s.pressPt | return
  if final then st.modify ({ · with pressPt := none })
  let some p1 ← pagePoint st wx wy | return
  if final && p0 == p1 then return
  match ← pageIndex st s.page with
  | .ok ix =>
    if let some (a, b) := Select.dragRange ix.cells p0 p1 then
      st.modify ({ · with sel := some (s.page, a, b) })
      drawOverlay st
      if final then selStatus st
  | .error e => setStatus s!"page {s.page + 1}: no text: {e}"

/-- Double click at `(wx, wy)`: selects the word of the nearest glyph (`Select.wordAt`). -/
def selectWord (st : IO.Ref State) (wx wy : Int) : IO Unit := do
  st.modify ({ · with pressPt := none })
  let s ← st.get
  let some p ← pagePoint st wx wy | return
  match ← pageIndex st s.page with
  | .ok ix =>
    if let some i := Select.nearest ix.cells p then
      let (a, b) := Select.wordAt ix.cells i
      st.modify ({ · with sel := some (s.page, a, b) })
      drawOverlay st
      selStatus st
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

/-- One step of the smoke test. Every step but the last schedules the next one 300 ms later
(the prefetch runs 100 ms after a page is shown). Files written into the smoke directory:
* step 0: `page-1.ppm` (fit page), then `Next`;
* step 1: `page-2.ppm`, `state.txt` (title, status, page; the status says whether page 2
  came from the prefetched cache); then `Home`, `0` (100 %);
* step 2: `zoom-100.ppm`, then `+`; step 3: `zoom-in.ppm` (125 %), then `-` `-`;
* step 4: `zoom-out.ppm` (75 %), then `r`; step 5: `rot.ppm` (75 %, 90°), then `R` and
  `+` ×4 (200 %), and the scroll test: `Down`, `Next` must scroll within page 1; `Next`
  repeated must reach page 2; `Prior` at the top of page 2 must reach the bottom of page 1;
  results in `view.txt`.
A document that failed to open ends after step 1. -/
def smoke (st : IO.Ref State) : IO Unit := do
  let s ← st.get
  let some dir := s.smokeDir | return
  if s.smokeMode == "text" then smokeText st dir; return
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
    write "page-1.ppm"
    if s.pageCount ≥ 2 then sendKey "Next"
    next
  | 1 =>
    if s.pageCount ≥ 2 then write "page-2.ppm"
    let title ← run ["wm", "title", "."]
    let status ← run [".status", "cget", "-text"]
    IO.FS.writeFile ((dir : System.FilePath) / "state.txt")
      s!"title: {title}\nstatus: {status}\npage: {(← st.get).page + 1}/{s.pageCount}\n"
    if s.pageCount ≥ 2 then
      sendKey "Home"; sendKey "0"; next
    else discard <| run ["destroy", "."]
  | 2 => write "zoom-100.ppm"; sendKey "plus"; next
  | 3 => write "zoom-in.ppm"; sendKey "minus"; sendKey "minus"; next
  | 4 => write "zoom-out.ppm"; sendKey "r"; next
  | 5 =>
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
  | ["resize", w, h] =>
    match w.toNat?, h.toNat? with
    | some w, some h =>
      if w ≥ 2 && h ≥ 2 && (w, h) != (s.canvasW, s.canvasH) then
        st.modify ({ · with canvasW := w, canvasH := h })
        refresh st
    | _, _ => pure ()
  | _ => setStatus s!"internal: unknown event {args}"

/-- Runs `act`, showing an exception in the status line instead of letting it escape into
Tk (stderr when even the status line fails). -/
def guarded (act : IO Unit) : IO Unit := do
  try act
  catch e =>
    try setStatus s!"error: {e}" catch _ => IO.eprintln s!"viewer: {e}"

/-- `handle`, with every exception shown in the status line instead of escaping into Tk. -/
def safeHandle (st : IO.Ref State) (args : Array String) : IO Unit :=
  guarded (handle st args)

/-- Usage text. -/
def usage : String :=
  "usage: viewer [FILE.pdf]
Opens FILE (or asks for one) in a window.
Keys: Next/space, Prior/BackSpace scroll by a window (then next/previous page);
Down/Up/Right/Left scroll; Home/End first/last page; + - zoom in/out; 0 actual size;
f fit page; w fit width; r/R rotate right/left; Ctrl+wheel zoom; Ctrl+O open; Ctrl+Q quit.
Mouse drag selects text, double-click a word; Ctrl+A select page; Ctrl+C copy;
Ctrl+F find (Enter/F3 next, Shift+F3 previous, Escape close).
SAFEPDF_VIEWER_SMOKE=DIR: scripted smoke test writing images and state into DIR, then exit
(SAFEPDF_VIEWER_SMOKE_MODE=text: the selection/copy/search steps instead)."

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
  let st ← IO.mkRef ({ smokeDir, smokeMode } : State)
  Shim.setEmitHandler (safeHandle st)
  try
    discard <| Shim.eval setupScript
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
  if smokeDir.isSome then discard <| run ["after", "300", "::safepdf::emit smoke"]
  Shim.mainLoop
  return 0

end SafePdf.Shell.App.Viewer
