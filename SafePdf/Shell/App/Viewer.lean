import SafePdf.Shell.App.Shim
import SafePdf.Shell.App.Tcl
import SafePdf.Shell.App.View
import SafePdf.Shell.Inspect
import SafePdf.Shell.Views.Pages

/-!
# Native viewer (tasks 8.2a, 8.2b; Plan.md §6 Phase 8, §8 native app, §10 `SafePdf/Shell/`)

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
  /-- Smoke-test output directory (`SAFEPDF_VIEWER_SMOKE`). -/
  smokeDir : Option String := none
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
namespace eval ::safepdf { variable resizeId {} }
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
focus .c
"

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
                          pending := none })
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
      discard <| run [photoName, "blank"]
      setStatus s!"{path}: page {s.page + 1}: cannot render: {renderError e}"
  | _, _ =>
    discard <| run [".bar.page", "configure", "-text", ""]
    discard <| run [".bar.zoom", "configure", "-text", ""]
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
  st.modify fun s => { s with gen := s.gen + 1, cache := ({} : View.Cache), pending := some .top }
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
      st.modify ({ · with doc := some doc })
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
    st.modify ({ · with page := p, pending := some whereTo })
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

/-! ## Smoke mode -/

/-- Sends the key `k` to the canvas through Tk (as a user would type it). -/
def sendKey (k : String) : IO Unit := do
  try
    discard <| run ["focus", "-force", ".c"]
    discard <| run ["event", "generate", ".c", s!"<Key-{k}>"]
  catch _ => pure ()

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
SAFEPDF_VIEWER_SMOKE=DIR: scripted smoke test writing images and state into DIR, then exit."

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
  let st ← IO.mkRef ({ smokeDir } : State)
  Shim.setEmitHandler (safeHandle st)
  try
    discard <| Shim.eval setupScript
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
