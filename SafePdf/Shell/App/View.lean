import SafePdf.Core.Raster.Geom
import SafePdf.Core.Raster.Clip
import SafePdf.Core.Limits

/-!
# Viewer geometry, wheel, view modes and page cache (tasks 8.2b, 9.2, 9.3; Plan.md §6 Phases 8–9, §8 native app, §10 `SafePdf/Shell/`)

The pure, Tk-free part of the viewer's viewing logic (unverified shell code, but total and
checked by `#guard`s): zoom modes and steps, the zoom cap, the C2 re-anchoring that keeps a
point fixed on screen across a zoom or rotation change, decimal parsing of Tcl numbers, and the
LRU cache of rendered pages bounded by total bytes.

* **Zoom.** `Mode.fitPage`, `Mode.fitWidth` or `Mode.scale pct` (percent; 100 % = 72 dpi ×
  the screen's scale factor, Tk's `tk scaling` in pixels per point). The effective zoom
  (pixels per page unit) is rounded down to a multiple of 1/64 (`quant`) so the renderer's
  rational arithmetic stays cheap. Steps: `zoomSteps` (25 % … 800 %).
* **Zoom cap.** A page larger than `maxViewPixels` pixels at the requested zoom gets a smaller
  zoom (`capZoom`); a side above `Limits.maxPageSide` is cropped by the renderer
  (`Clip.pageSize`), which `cropped` detects so the viewer can say so.
* **Anchoring (C2).** `reanchor z r z' r' bx q = toScreen z' r' bx (toPage z r bx q)`: the
  screen position, in the new view, of the page point that was at `q` in the old one. By
  `Geom.toPage_toScreen`/`toScreen_toPage` this is the identity when nothing changed.
* **Wheel across pages** (task 9.2). `wheelStep` turns one wheel/trackpad event into a scroll
  within the page or a page turn: deltas in notches, lines or pixels (`wheelPixels`), sub-pixel
  remainders accumulated, the page turned only after the view is at the edge and the user
  pushes on past it by `wheelThreshold`; trackpad momentum after a turn is swallowed until a
  pause (`wheelGapMs`).
* **View modes** (task 9.3, Plan.md §6 Phase 9 "View modes"; PDF.js's scroll and spread
  modes). `ScrollMode` (page, vertical) × `SpreadMode` (none, odd, even): `spreads` pairs the
  pages (`mem_spreadPages`: every page lies in exactly one spread), `nextPage`/`prevPage` move
  by a spread (`nextPage_spread`), `layoutRows` places the rows of pages in the scroll region
  (`stack_pairwise`: stacked extents never overlap), `visiblePages`/`wantedPages` give the pages
  in a view band (plus one each side, kept rendered), `pageAt` the page at a point,
  `topFor`/`bottomFor` the scroll positions of a page, `fitBox` the box the fit zooms use.
* **Cache.** `Cache` keyed by (document generation, page, zoom, rotation); `Cache.insert`
  evicts least-recently-used entries until the total image bytes are at most the budget
  (`cacheBytes`, 256 MiB) and there are at most `cacheEntries` entries.
-/

namespace SafePdf.Shell.App.View

open SafePdf.Core
open SafePdf.Core.Raster.Geom

/-! ## Zoom -/

/-- How the zoom is chosen. -/
inductive Mode where
  /-- The whole page fits into the window. -/
  | fitPage
  /-- The page width fits into the window. -/
  | fitWidth
  /-- A fixed scale in percent of actual size (100 % = 72 dpi × screen scale factor). -/
  | scale (pct : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Zoom steps in percent for zoom in/out. -/
def zoomSteps : List Nat := [25, 33, 50, 67, 75, 100, 125, 150, 200, 300, 400, 600, 800]

/-- Smallest zoom step (percent). -/
def minPct : Nat := 25

/-- Largest zoom step (percent). -/
def maxPct : Nat := 800

/-- The next zoom step above `cur` percent (`maxPct` at the top). -/
def stepIn (cur : Nat) : Nat :=
  (zoomSteps.find? (· > cur)).getD maxPct

/-- The next zoom step below `cur` percent (`minPct` at the bottom). -/
def stepOut (cur : Nat) : Nat :=
  (zoomSteps.reverse.find? (· < cur)).getD minPct

#guard stepIn 100 = 125
#guard stepIn 97 = 100
#guard stepIn 800 = 800
#guard stepOut 100 = 75
#guard stepOut 26 = 25
#guard stepOut 25 = 25

/-- Rounds a zoom down to a multiple of 1/64, at least 1/64. -/
def quant (z : Rat) : Rat :=
  max (1 / 64) (((z * 64).floor : Rat) / 64)

#guard quant (4 / 3) = 85 / 64
#guard quant 0 = 1 / 64

/-- Margin in pixels around the page inside the canvas (each side). -/
def margin : Nat := 8

/-- Width and height (page units) of the displayed box `bx` under rotation `r`. -/
def boxSize (r : Doc.Rotation) (bx : Box) : Rat × Rat :=
  screenSize 1 r bx

/-- The zoom that fits a `pw × ph` box into a `cw × ch` canvas less `margin` on every side
(only the width when `widthOnly`), quantised and kept in `[1/16, 8]`. A degenerate box gets
zoom 1. -/
def fitZoom (widthOnly : Bool) (cw ch : Nat) (pw ph : Rat) : Rat :=
  if pw ≤ 0 || ph ≤ 0 then 1
  else
    let aw : Rat := ((cw - 2 * margin : Nat) : Rat)
    let ah : Rat := ((ch - 2 * margin : Nat) : Rat)
    let z := if widthOnly then aw / pw else min (aw / pw) (ah / ph)
    max (1 / 16) (min 8 (quant z))

#guard fitZoom false 1000 1000 0 100 = 1
#guard fitZoom false 100 100 10000 10000 = 1 / 16
#guard fitZoom false 2000 2000 100 100 = 8
#guard fitZoom false 216 216 100 200 = 1
#guard fitZoom true 216 216 100 200 = 2

/-- The zoom (pixels per page unit) of a percentage at screen scale `scaling` (pixels per
point). -/
def pctZoom (pct : Nat) (scaling : Rat) : Rat :=
  quant ((pct : Rat) * scaling / 100)

#guard pctZoom 100 1 = 1
#guard pctZoom 100 (4 / 3) = 85 / 64

/-- The percentage shown for zoom `z` at screen scale `scaling`, rounded to the nearest
integer. -/
def zoomPct (z scaling : Rat) : Nat :=
  if scaling ≤ 0 then 100 else (z * 100 / scaling + 1 / 2).floor.toNat

#guard zoomPct (85 / 64) (4 / 3) = 100
#guard zoomPct 2 1 = 200

/-- The effective zoom of `mode` for a canvas `cw × ch`, screen scale `scaling` and a box of
displayed size `pw × ph` (page units). -/
def modeZoom (mode : Mode) (cw ch : Nat) (scaling : Rat) (pw ph : Rat) : Rat :=
  match mode with
  | .fitPage => fitZoom false cw ch pw ph
  | .fitWidth => fitZoom true cw ch pw ph
  | .scale pct => pctZoom pct scaling

/-- Largest page image the viewer renders, in pixels (2²⁶: 256 MiB of RGBA). Larger
requests get a smaller zoom (`capZoom`). -/
def maxViewPixels : Nat := 1 <<< 26

/-- Pixel size of the displayed box at zoom `z` (no side cap). -/
def pixelSize (z : Rat) (r : Doc.Rotation) (bx : Box) : Nat × Nat :=
  let s := screenSize z r bx
  (s.1.ceil.toNat, s.2.ceil.toNat)

/-- Caps the zoom so that the page image has at most `maxPx` pixels: returns the zoom and
whether it was lowered. The lowered zoom is `quant (z · √(maxPx / (w·h)) · 99/100)`, which
leaves room for the rounding up of the pixel size. -/
def capZoom (maxPx : Nat) (z : Rat) (r : Doc.Rotation) (bx : Box) : Rat × Bool :=
  let (w, h) := pixelSize z r bx
  if w * h ≤ maxPx then (z, false)
  else
    -- √(maxPx / (w h)) to 10 binary digits.
    let s : Rat := ((Nat.sqrt (maxPx * (1 <<< 20) / (w * h)) : Nat) : Rat) / 1024
    (quant (z * s * 99 / 100), true)

#guard capZoom 10000 1 .r0 ⟨0, 0, 100, 100⟩ = (1, false)
#guard (capZoom 2500 1 .r0 ⟨0, 0, 100, 100⟩).2 = true
#guard let z := (capZoom 2500 1 .r0 ⟨0, 0, 100, 100⟩).1
  let (w, h) := pixelSize z .r0 ⟨0, 0, 100, 100⟩; w * h ≤ 2500 && w * h ≥ 2000

/-- `true` when the renderer crops the page at zoom `z` (a side above `side`,
`Limits.maxPageSide`; see `Clip.pageSize`). -/
def cropped (side : Nat) (z : Rat) (r : Doc.Rotation) (bx : Box) : Bool :=
  let (w, h) := pixelSize z r bx
  w > side || h > side

#guard cropped 16384 1 .r0 ⟨0, 0, 100, 20000⟩ = true
#guard cropped 16384 1 .r90 ⟨0, 0, 100, 200⟩ = false

/-! ## Rotation -/

/-- A quarter turn clockwise more (`r` key). -/
def rotCw (r : Doc.Rotation) : Doc.Rotation := rotAdd r .r90

/-- A quarter turn counter-clockwise more (`R` key). -/
def rotCcw (r : Doc.Rotation) : Doc.Rotation := rotAdd r .r270

#guard rotCcw (rotCw .r90) = .r90
#guard rotCw .r270 = .r0

/-- Degrees of a rotation (for the status line). -/
def rotDeg (r : Doc.Rotation) : Nat := (rotDegrees r).toNat

/-! ## Anchoring (C2) -/

/-- The screen position in the view `(z', r')` of the page point shown at `q` in the view
`(z, r)` (same page box): `toScreen z' r' bx (toPage z r bx q)`. -/
def reanchor (z : Rat) (r : Doc.Rotation) (z' : Rat) (r' : Doc.Rotation) (bx : Box) (q : Pt) :
    Pt :=
  toScreen z' r' bx (toPage z r bx q)

/-- With nothing changed the anchor stays put (C2, `toScreen_toPage`). -/
theorem reanchor_self {z : Rat} (hz : 0 < z) (r : Doc.Rotation) (bx : Box) (q : Pt) :
    reanchor z r z r bx q = q :=
  toScreen_toPage hz r bx q

-- The centre of a Letter page stays the centre when zooming 1 → 2 and rotating 0 → 90°.
#guard reanchor 1 .r0 2 .r90 ⟨0, 0, 612, 792⟩ ⟨306, 396⟩ = ⟨792, 612⟩
-- Zoom about a point: the page point under (100, 50) at zoom 1 is under (200, 100) at zoom 2.
#guard reanchor 1 .r0 2 .r0 ⟨0, 0, 612, 792⟩ ⟨100, 50⟩ = ⟨200, 100⟩

/-! ## Tcl numbers -/

/-- Parses a decimal digit string to its value and digit count. -/
def digits (s : List Char) : Option (Nat × Nat) :=
  if s.all Char.isDigit then
    some (s.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0, s.length)
  else none

/-- Parses a Tcl floating-point result such as `12`, `-3.5`, `0.25` or `1e-05` (as returned
by `canvasx`, `xview`). `none` for anything else. -/
def parseDecimal (s : String) : Option Rat :=
  let s := s.trimAscii.toString
  let (neg, body) := match s.toList with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let (mant, ex) := match body.splitOn 'e' with
    | [m] => (m, some (0 : Int))
    | [m, e] => (m, match e with
        | '-' :: d => (digits d).bind fun (v, n) => if n == 0 then none else some (-(v : Int))
        | '+' :: d => (digits d).bind fun (v, n) => if n == 0 then none else some (v : Int)
        | d => (digits d).bind fun (v, n) => if n == 0 then none else some (v : Int))
    | _ => (body, none)
  match ex, mant.splitOn '.' with
  | some e, [i] =>
    (digits i).bind fun (iv, n) =>
      if n == 0 || e.natAbs > 30 then none else
        let v : Rat := if e ≥ 0 then (iv * 10 ^ e.toNat : Nat) else (iv : Rat) / (10 ^ e.natAbs : Nat)
        some (if neg then -v else v)
  | some e, [i, f] =>
    (digits i).bind fun (iv, ni) => (digits f).bind fun (fv, nf) =>
      if ni + nf == 0 || e.natAbs > 30 then none else
        let m : Rat := (iv : Rat) + (fv : Rat) / (10 ^ nf : Nat)
        let v : Rat := if e ≥ 0 then m * (10 ^ e.toNat : Nat) else m / (10 ^ e.natAbs : Nat)
        some (if neg then -v else v)
  | _, _ => none

#guard parseDecimal "12" = some 12
#guard parseDecimal "-3.5" = some (-7 / 2)
#guard parseDecimal "0.25 " = some (1 / 4)
#guard parseDecimal "1e-05" = some (1 / 100000)
#guard parseDecimal "2.5e+2" = some 250
#guard parseDecimal "abc" = none
#guard parseDecimal "" = none
#guard parseDecimal "." = none

/-! ## Wheel scrolling across pages (task 9.2) -/

/-- Kind of a wheel event's delta. -/
inductive WheelKind where
  /-- `<MouseWheel>` `%D` in 1/120 notches (Tk ≥ 8.7 everywhere, Windows; X11 Button-4/5
  are sent as ±120). High-resolution wheels and trackpads give smaller deltas. -/
  | notch
  /-- `<MouseWheel>` `%D` in whole lines (Tk 8.6 on macOS: ±1 per notch, small values from a
  trackpad). -/
  | line
  /-- Pixels (`<TouchpadScroll>` through `tk::PreciseScrollDeltas`, Tk ≥ 9 on macOS). -/
  | pixel
  deriving DecidableEq, Repr, Inhabited

/-- Wheel state between events: unapplied sub-pixel remainder, how far the user has pushed
past the page edge, when the last event came, and whether trackpad momentum after a page turn
is being swallowed. -/
structure Wheel where
  /-- Pixels not yet scrolled (|acc| < 1; positive = forward, down/right). -/
  acc : Rat := 0
  /-- Pixels pushed past the edge in the current direction (positive: past the end). -/
  push : Rat := 0
  /-- Time of the last event (ms, monotonic). -/
  last : Nat := 0
  /-- A trackpad event turned the page; further trackpad events are ignored until a pause. -/
  latched : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- What a wheel event does. -/
inductive WheelAct where
  /-- Nothing (sub-pixel movement, a push not yet past the threshold, swallowed momentum). -/
  | none
  /-- Scroll so that the view's top (left) edge is at this pixel of the scroll region. -/
  | scrollTo (pos : Nat)
  /-- Turn to the top of the next page. -/
  | next
  /-- Turn to the bottom of the previous page. -/
  | prev
  deriving DecidableEq, Repr, Inhabited

/-- A pause longer than this (ms) between wheel events forgets the push and the latch. -/
def wheelGapMs : Nat := 400

/-- Pixels a wheel delta `d` of kind `k` moves, forward positive (Tk's `%D` is positive for
"up"), where one notch moves a tenth of the view (`view` pixels), as Tk's `scroll 1 units`
does with the default scroll increment. -/
def wheelPixels (k : WheelKind) (d : Int) (view : Nat) : Rat :=
  match k with
  | .notch => -(d : Rat) * (view : Rat) / 1200
  | .line => -(d : Rat) * (view : Rat) / 10
  | .pixel => -(d : Rat)

/-- How far (pixels) the user must keep pushing at a page edge before the page turns: one
notch for wheels (a tenth of the view), a quarter of the view for trackpads, whose small
deltas and momentum would otherwise turn pages by accident. -/
def wheelThreshold (k : WheelKind) (view : Nat) : Rat :=
  match k with
  | .pixel => (view : Rat) / 4
  | _ => (view : Rat) / 10

/-- Integer part towards zero. -/
def truncRat (r : Rat) : Int := if r < 0 then r.ceil else r.floor

/-- One wheel event of `px` pixels (forward positive) at time `now` (ms) on an axis whose
scroll region is `region` pixels, the view `view` pixels, its top (left) edge at `top`.
Fractional pixels accumulate (`acc`); a direction change drops the remainder and the push.
Within the page the view scrolls, stopping exactly at the edge. Only once it is at the edge
do further events add their exact deltas to a push (a pause or a direction change resets it);
when the push reaches `threshold` and `cross` holds (vertical axis), the page turns (`next` / `prev`). A `precise` (trackpad) event that turns the
page latches: trackpad events are swallowed until a pause of `wheelGapMs`, so momentum
does not turn several pages. -/
def wheelStep (w : Wheel) (now : Nat) (px : Rat) (precise cross : Bool) (top view region : Nat)
    (threshold : Rat) : Wheel × WheelAct :=
  let idle := now - w.last > wheelGapMs
  let w := if idle then { w with push := 0, latched := false, acc := 0 } else w
  let w := { w with last := now }
  if w.latched && precise then (w, .none)
  else
    let w := { w with latched := false }
    -- A direction change drops the remainder and the push.
    let w := if px * w.acc < 0 || px * w.push < 0 then { w with acc := 0, push := 0 } else w
    let maxTop := region - view
    let atEdge := if px > 0 then top ≥ maxTop else top = 0
    if px == 0 then (w, .none)
    else if atEdge then
      -- At the edge: the exact deltas add up to the push (no rounding), and only a push of
      -- `threshold` turns the page.
      if !cross then ({ w with acc := 0, push := 0 }, .none)
      else
        let push := w.push + px
        if push ≥ threshold then ({ w with acc := 0, push := 0, latched := precise }, .next)
        else if -push ≥ threshold then ({ w with acc := 0, push := 0, latched := precise }, .prev)
        else ({ w with acc := 0, push }, .none)
    else
      let acc := w.acc + px
      let m := truncRat acc
      let w := { w with acc := acc - m, push := 0 }
      if m == 0 then (w, .none)
      else if m > 0 then (w, .scrollTo (min (top + m.toNat) maxTop))
      else (w, .scrollTo (top - min m.natAbs top))

/-- Runs `wheelStep` over a list of `(time, pixels)` events with fixed geometry, scrolling
the top as the actions say (for the `#guard`s). Returns the actions. -/
def wheelRun (evs : List (Nat × Rat)) (precise : Bool) (top view region : Nat)
    (threshold : Rat) : List WheelAct :=
  (evs.foldl (fun (acc : Wheel × Nat × List WheelAct) (t, px) =>
    let (w, top, out) := acc
    let (w', a) := wheelStep w t px precise true top view region threshold
    let top' := match a with
      | .scrollTo p => p
      | .next => 0
      | .prev => region - view
      | .none => top
    (w', top', out ++ [a])) ({}, top, [])).2.2

-- Wheel notches (view 100 px, region 250 px: max top 150; a notch is 10 px).
#guard wheelPixels .notch (-120) 100 = 10
#guard wheelPixels .notch 120 100 = -10
#guard wheelPixels .line (-1) 100 = 10
#guard wheelPixels .pixel 7 100 = -7
-- Scrolling within the page stops exactly at the edge; one more notch turns the page.
#guard wheelRun [(0, 100), (10, 100)] false 0 100 250 10 = [.scrollTo 100, .scrollTo 150]
#guard wheelRun [(0, 10), (10, 10)] false 145 100 250 10 = [.scrollTo 150, .next]
-- At the edge already: the first notch past it turns the page.
#guard wheelRun [(0, 10)] false 150 100 250 10 = [.next]
-- Upwards at the top: the previous page (shown at its bottom).
#guard wheelRun [(0, -10)] false 0 100 250 10 = [.prev]
-- A page that fits the view (fit page): every notch turns a page.
#guard wheelRun [(0, 10), (10, 10), (20, -10)] false 0 100 100 10 = [.next, .next, .prev]
-- Small deltas accumulate: twelve 1/12 notches are one notch, and a tiny overscroll does not
-- turn the page (eleven of them stay below the threshold).
#guard (wheelRun ((List.range 11).map fun i => (i, (10 : Rat) / 12)) false 150 100 250 10).all
  (· == .none)
#guard (wheelRun ((List.range 12).map fun i => (i, (10 : Rat) / 12)) false 150 100 250 10).getLast?
  = some .next
-- Fractional pixels scroll once they add up to a whole pixel.
#guard wheelRun [(0, 1 / 2), (1, 1 / 2), (2, 1 / 2)] false 0 100 250 10 =
  [.none, .scrollTo 1, .none]
-- A pause forgets a partial push.
#guard wheelRun [(0, 6), (1000, 6)] false 150 100 250 10 = [.none, .none]
-- A direction change forgets the push.
#guard wheelRun [(0, 6), (1, -1 / 2), (2, 6)] false 150 100 250 10 = [.none, .none, .none]
#guard wheelRun [(0, 6), (2, 6)] false 150 100 250 10 = [.none, .next]
-- Horizontal (no crossing): the edge just stops.
#guard (wheelStep {} 0 10 false false 150 100 250 10).2 = .none
-- Trackpad momentum after a page turn is swallowed until a pause; a wheel event is not.
#guard wheelRun [(0, 30), (16, 30), (32, 30), (600, 30)] true 0 100 100 25 =
  [.next, .none, .none, .next]
#guard
  let (w, a) := wheelStep {} 0 30 true true 0 100 100 25
  a == .next && (wheelStep w 16 10 false true 0 100 100 10).2 == .next

/-! ## View modes and page layout (task 9.3)

PDF.js's *Scroll mode* (Page, Vertical; Wrapped and Horizontal are not offered) and *Spread
mode* (None, Odd, Even). Single page = (page, none), continuous = (vertical, none), facing =
(page, odd/even), continuous facing = (vertical, odd/even). A spread is the row of pages shown
side by side; `layoutRows` places the rows of the scroll region. -/

/-- How pages follow each other (PDF.js "Scroll mode"). -/
inductive ScrollMode where
  /-- One page (or spread) at a time; scrolling past its edge turns the page. -/
  | page
  /-- All pages (spreads) stacked vertically with gaps; the wheel scrolls the whole document. -/
  | vertical
  deriving DecidableEq, Repr, Inhabited

/-- How pages are paired side by side (PDF.js "Spread mode"). -/
inductive SpreadMode where
  /-- No spreads: one page per row. -/
  | none
  /-- Odd spreads: pages 1|2, 3|4, … (1-based numbers). -/
  | odd
  /-- Even spreads: page 1 alone, then 2|3, 4|5, … -/
  | even
  deriving DecidableEq, Repr, Inhabited

/-- Name of a scroll mode (Tcl radio value). -/
def ScrollMode.key : ScrollMode → String
  | .page => "page"
  | .vertical => "vertical"

/-- The scroll mode named `s`. -/
def ScrollMode.ofKey : String → Option ScrollMode
  | "page" => some .page
  | "vertical" => some .vertical
  | _ => none

/-- Name of a spread mode (Tcl radio value). -/
def SpreadMode.key : SpreadMode → String
  | .none => "none"
  | .odd => "odd"
  | .even => "even"

/-- The spread mode named `s`. -/
def SpreadMode.ofKey : String → Option SpreadMode
  | "none" => some .none
  | "odd" => some .odd
  | "even" => some .even
  | _ => none

#guard [ScrollMode.page, .vertical].all fun m => ScrollMode.ofKey m.key == some m
#guard [SpreadMode.none, .odd, .even].all fun m => SpreadMode.ofKey m.key == some m

/-- The spread (0-based) holding page `p` (0-based). -/
def spreadOf : SpreadMode → Nat → Nat
  | .none, p => p
  | .odd, p => p / 2
  | .even, p => (p + 1) / 2

/-- The first page of spread `k` (for `.even`, spread 0 is page 0 alone). -/
def spreadFirst : SpreadMode → Nat → Nat
  | .none, k => k
  | .odd, k => 2 * k
  | .even, k => 2 * k - 1

/-- Whether spread `k` has room for two pages. -/
def spreadTwo : SpreadMode → Nat → Bool
  | .none, _ => false
  | .odd, _ => true
  | .even, k => k != 0

/-- The pages of spread `k` of a document of `n` pages, left to right. -/
def spreadPages (sp : SpreadMode) (n k : Nat) : List Nat :=
  let q := spreadFirst sp k
  (if spreadTwo sp k then [q, q + 1] else [q]).filter (· < n)

/-- Number of spreads of a document of `n` pages. -/
def spreadCount (sp : SpreadMode) (n : Nat) : Nat :=
  if n = 0 then 0 else spreadOf sp (n - 1) + 1

/-- All spreads of a document of `n` pages, in order. -/
def spreads (sp : SpreadMode) (n : Nat) : List (List Nat) :=
  (List.range (spreadCount sp n)).map (spreadPages sp n)

/-- Page `p` is in spread `k` exactly when `k` is its spread: every page appears in exactly
one spread. -/
theorem mem_spreadPages {sp : SpreadMode} {n k p : Nat} :
    p ∈ spreadPages sp n k ↔ p < n ∧ spreadOf sp p = k := by
  cases sp with
  | none => simp [spreadPages, spreadFirst, spreadTwo, spreadOf, List.mem_filter]; omega
  | odd => simp [spreadPages, spreadFirst, spreadTwo, spreadOf, List.mem_filter]; omega
  | even =>
    by_cases hk : k = 0
    · subst hk; simp [spreadPages, spreadFirst, spreadTwo, spreadOf, List.mem_filter]; omega
    · simp [spreadPages, spreadFirst, spreadTwo, spreadOf, List.mem_filter, hk]; omega

/-- The spread of a page of the document is one of its spreads. -/
theorem spreadOf_lt_count {sp : SpreadMode} {n p : Nat} (h : p < n) :
    spreadOf sp p < spreadCount sp n := by
  unfold spreadCount
  cases sp <;> simp only [spreadOf] <;> split <;> omega

/-- The first page of spread `k` lies in spread `k`. -/
theorem spreadOf_spreadFirst (sp : SpreadMode) (k : Nat) : spreadOf sp (spreadFirst sp k) = k := by
  cases sp <;> simp only [spreadOf, spreadFirst] <;> omega

#guard spreads .none 3 == [[0], [1], [2]]
#guard spreads .odd 5 == [[0, 1], [2, 3], [4]]
#guard spreads .even 5 == [[0], [1, 2], [3, 4]]
#guard spreads .even 4 == [[0], [1, 2], [3]]
#guard spreads .odd 0 == [] && spreads .even 1 == [[0]]
-- Every page is in exactly one spread (the theorem, checked on examples).
#guard [SpreadMode.none, .odd, .even].all fun sp =>
  (List.range 9).all fun n => ((spreads sp n).flatten == List.range n)

/-- The page "Next" goes to: the first page of the next spread (two pages on in the facing
modes), or `p` itself at the end. -/
def nextPage (sp : SpreadMode) (n p : Nat) : Nat :=
  let q := spreadFirst sp (spreadOf sp p + 1)
  if q < n then q else p

/-- The page "Previous" goes to: the first page of the previous spread, or `p` itself in the
first spread. -/
def prevPage (sp : SpreadMode) (p : Nat) : Nat :=
  match spreadOf sp p with
  | 0 => p
  | k + 1 => spreadFirst sp k

/-- "Next" moves exactly one spread on (or stays at the end). -/
theorem nextPage_spread (sp : SpreadMode) (n p : Nat) :
    nextPage sp n p = p ∨ spreadOf sp (nextPage sp n p) = spreadOf sp p + 1 := by
  simp only [nextPage]
  split
  · exact .inr (spreadOf_spreadFirst sp _)
  · exact .inl rfl

#guard (List.range 5).map (nextPage .none 5) == [1, 2, 3, 4, 4]
#guard (List.range 5).map (nextPage .odd 5) == [2, 2, 4, 4, 4]
#guard (List.range 5).map (nextPage .even 5) == [1, 3, 3, 3, 4]
#guard (List.range 5).map (prevPage .odd) == [0, 1, 0, 0, 2]
#guard (List.range 5).map (prevPage .even) == [0, 0, 0, 1, 1]

/-- Gap in pixels between pages: between the rows of the vertical modes and between the two
pages of a spread (PDF.js leaves a similar margin). -/
def pageGap : Nat := 10

/-- Places extents `ss` one after another from `pos`, `g` apart: `(start, extent)` each. -/
def stack (pos g : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | s :: ss => (pos, s) :: stack (pos + s + g) g ss

/-- Everything stacked from `pos` starts at or after `pos`. -/
theorem stack_ge : ∀ {pos g : Nat} {ss : List Nat} {a : Nat × Nat}, a ∈ stack pos g ss → pos ≤ a.1
  | _, _, [], _, h => by simp [stack] at h
  | pos, g, s :: ss, a, h => by
    simp only [stack, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact Nat.le_refl _
    · have := stack_ge h; omega

/-- Stacked items never overlap: each ends at least `g` before every later one starts. -/
theorem stack_pairwise : ∀ (pos g : Nat) (ss : List Nat),
    (stack pos g ss).Pairwise (fun a b => a.1 + a.2 + g ≤ b.1)
  | _, _, [] => List.Pairwise.nil
  | pos, g, s :: ss => by
    simp only [stack]
    refine List.Pairwise.cons (fun b hb => ?_) (stack_pairwise _ g ss)
    have := stack_ge hb
    simp only at this ⊢
    omega

/-- Total extent of `ss` stacked `g` apart. -/
def span (g : Nat) : List Nat → Nat
  | [] => 0
  | [s] => s
  | s :: ss => s + g + span g ss

#guard stack 8 10 [100, 50, 70] == [(8, 100), (118, 50), (178, 70)]
#guard span 10 [100, 50, 70] == 240 && span 10 [] == 0 && span 10 [7] == 7

/-- Where a page image lies in the scroll region (canvas pixels, top-left corner and size). -/
structure Place where
  /-- Page index (0-based). -/
  page : Nat
  /-- Left edge. -/
  x : Nat
  /-- Top edge. -/
  y : Nat
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Places the rows `rows` (spreads: page lists, left to right) of pages of pixel sizes
`sizes` (indexed by page) in a canvas of `cw × ch`: rows stacked `pageGap` apart from the top
margin (or centred vertically when `centreY` and they fit, as the single-page view does), each
row centred horizontally with its pages `pageGap` apart and centred vertically within the row
(PDF.js's `vertical-align: middle`). Returns the places in page order and the scroll region's
width and height (at least the canvas, at least the content plus `margin` on each side). -/
def layoutRows (sizes : Array (Nat × Nat)) (rows : List (List Nat)) (cw ch : Nat)
    (centreY : Bool) : Array Place × Nat × Nat :=
  let sz (p : Nat) : Nat × Nat := sizes[p]?.getD (0, 0)
  let rowW (r : List Nat) : Nat := span pageGap (r.map fun p => (sz p).1)
  let rowH (r : List Nat) : Nat := (r.map fun p => (sz p).2).foldl max 0
  let regionW := max cw ((rows.map rowW).foldl max 0 + 2 * margin)
  let content := span pageGap (rows.map rowH)
  let regionH := max ch (content + 2 * margin)
  let y0 := if centreY then max margin ((ch - content) / 2) else margin
  let places := ((stack y0 pageGap (rows.map rowH)).zip rows).flatMap fun ((ry, rh), r) =>
    ((stack ((regionW - rowW r) / 2) pageGap (r.map fun p => (sz p).1)).zip r).map
      fun ((x, w), p) => ({ page := p, x, y := ry + (rh - (sz p).2) / 2, w, h := (sz p).2 } : Place)
  (places.toArray, regionW, regionH)

/-- Two places overlap (their rectangles share an interior point). -/
def Place.overlaps (a b : Place) : Bool :=
  a.x < b.x + b.w && b.x < a.x + a.w && a.y < b.y + b.h && b.y < a.y + a.h

/-- No two places overlap. -/
def disjoint (ps : Array Place) : Bool :=
  (List.range ps.size).all fun i => (List.range ps.size).all fun j =>
    i == j || match ps[i]?, ps[j]? with
      | some a, some b => !a.overlaps b
      | _, _ => true

/-- Whether place `pl` shares rows of pixels with the band `[top, bot)`. -/
def Place.meets (pl : Place) (top bot : Nat) : Bool :=
  pl.y < bot && top < pl.y + pl.h

/-- The pages whose places meet the view band `[top, bot)` (scroll region pixels). -/
def visiblePages (ps : Array Place) (top bot : Nat) : List Nat :=
  (ps.toList.filter (·.meets top bot)).map (·.page)

/-- The pages to keep rendered for the view band `[top, bot)`: the visible ones and one more
place before and after them (in page order), so the next page is ready before it scrolls in. -/
def wantedPages (ps : Array Place) (top bot : Nat) : List Nat :=
  let idx := (List.range ps.size).filter fun i => (ps[i]?.map (·.meets top bot)).getD false
  match idx.head?, idx.getLast? with
  | some lo, some hi =>
    ((List.range ps.size).filter fun i => lo ≤ i + 1 && i ≤ hi + 1).filterMap
      fun i => ps[i]?.map (·.page)
  | _, _ => []

/-- Distance from `a` to the interval `[lo, lo + len)` (0 inside). -/
def gapTo (a lo len : Nat) : Nat :=
  if a < lo then lo - a else if a < lo + len then 0 else a + 1 - (lo + len)

/-- The page at scroll-region point `(x, y)`: the place containing it, else the nearest one
(by the sum of the horizontal and vertical distances; the first in page order on a tie). -/
def pageAt (ps : Array Place) (x y : Nat) : Option Nat :=
  (ps.foldl (fun (best : Option (Nat × Nat)) pl =>
    let d := gapTo x pl.x pl.w + gapTo y pl.y pl.h
    match best with
    | some (_, bd) => if d < bd then some (pl.page, d) else best
    | none => some (pl.page, d)) none).map (·.1)

/-- The place of page `p`. -/
def placeOf (ps : Array Place) (p : Nat) : Option Place :=
  ps.find? (·.page == p)

/-- The scroll position (top of the view) that shows place `pl` from its top, with the margin
above it. -/
def topFor (pl : Place) : Nat := pl.y - margin

/-- The scroll position that shows place `pl` down to its bottom, with the margin below it,
in a view `view` pixels high. -/
def bottomFor (pl : Place) (view : Nat) : Nat := pl.y + pl.h + margin - view

-- One page in a large canvas is centred (the single-page view: same as before task 9.3).
#guard layoutRows #[(100, 200)] [[0]] 300 400 true == (#[⟨0, 100, 100, 100, 200⟩], 300, 400)
-- A page larger than the canvas: margins, scroll region grows.
#guard layoutRows #[(500, 600)] [[0]] 300 400 true == (#[⟨0, 8, 8, 500, 600⟩], 516, 616)
-- Vertical: three pages stacked 10 px apart from the top margin, centred horizontally.
#guard layoutRows #[(100, 200), (100, 200), (120, 100)] [[0], [1], [2]] 300 300 false ==
  (#[⟨0, 100, 8, 100, 200⟩, ⟨1, 100, 218, 100, 200⟩, ⟨2, 90, 428, 120, 100⟩], 300, 536)
-- A spread: two pages side by side, the shorter one centred vertically in the row.
#guard layoutRows #[(100, 200), (100, 100)] [[0, 1]] 300 300 true ==
  (#[⟨0, 45, 50, 100, 200⟩, ⟨1, 155, 100, 100, 100⟩], 300, 300)
-- Continuous facing (even spreads): page 1 alone, then 2|3; nothing overlaps.
#guard
  let (ps, _, _) := layoutRows #[(100, 200), (100, 200), (100, 200), (100, 200)]
    (spreads .even 4) 300 300 false
  disjoint ps && ps.map (·.page) == #[0, 1, 2, 3] && ps.map (·.y) == #[8, 218, 218, 428]
#guard [SpreadMode.none, .odd, .even].all fun sp =>
  let sizes := (Array.range 7).map fun i => (60 + 13 * i, 90 + 7 * (i % 3))
  disjoint (layoutRows sizes (spreads sp 7) 200 150 false).1
-- Visible pages, the pages kept rendered (one more on each side), the page at a point.
#guard
  let (ps, _, _) := layoutRows #[(100, 200), (100, 200), (100, 200), (100, 200)]
    [[0], [1], [2], [3]] 300 300 false
  visiblePages ps 0 300 == [0, 1] && wantedPages ps 0 300 == [0, 1, 2] &&
  visiblePages ps 400 600 == [1, 2] && wantedPages ps 400 600 == [0, 1, 2, 3] &&
  wantedPages ps 5000 5300 == [] &&
  pageAt ps 150 150 == some 0 && pageAt ps 150 300 == some 1 && pageAt ps 150 210 == some 0 &&
  pageAt ps 0 9999 == some 3 && pageAt #[] 0 0 == none &&
  (placeOf ps 2).map topFor == some 420 && (placeOf ps 2).map (bottomFor · 300) == some 336

/-- The view mode named by `SAFEPDF_VIEWER_VIEW`: `single`, `continuous`, `facing` (odd
spreads, as a printed book's two-page view starting with page 1 on the left) or
`continuous-facing`. -/
def viewModeOf : String → Option (ScrollMode × SpreadMode)
  | "single" => some (.page, .none)
  | "continuous" => some (.vertical, .none)
  | "facing" => some (.page, .odd)
  | "continuous-facing" => some (.vertical, .odd)
  | _ => none

#guard viewModeOf "continuous" == some (.vertical, .none) && viewModeOf "x" == none

/-- The page size (page units) that the fit zooms use in spread mode `sp`: a page alone, or
twice its width in the facing modes, as PDF.js (`#pageWidthScaleFactor` 2), so that every
spread of a document of equal pages shows at the same zoom. -/
def fitBox (sp : SpreadMode) (pw ph : Rat) : Rat × Rat :=
  if sp == .none then (pw, ph) else (2 * pw, ph)

/-- The canvas width the fit zooms use in spread mode `sp`: less the gap between the two pages
of a spread. -/
def fitCanvasW (sp : SpreadMode) (cw : Nat) : Nat :=
  if sp == .none then cw else cw - pageGap

#guard fitBox .none 612 792 == (612, 792) && fitBox .odd 612 792 == (1224, 792)
#guard fitZoom true (fitCanvasW .odd 1250) 900 1224 792 == fitZoom true 1240 900 1224 792

/-! ## Page cache -/

/-- Cache key: document generation (bumped on every open), page index, zoom, user rotation. -/
structure Key where
  /-- Document generation. -/
  gen : Nat
  /-- Page index (0-based). -/
  page : Nat
  /-- Zoom (pixels per page unit). -/
  zoom : Rat
  /-- User rotation (added to the page's `/Rotate`). -/
  rot : Doc.Rotation
  deriving DecidableEq, Repr, Inhabited

/-- A cached render result. -/
structure Entry where
  /-- Its key. -/
  key : Key
  /-- The rendered page, or the error. -/
  result : Except Error Raster.Clip.Image
  /-- Bytes held (`0` for an error). -/
  bytes : Nat
  /-- Tick of the last use (LRU order). -/
  used : Nat

/-- Total image bytes the cache may hold (256 MiB). -/
def cacheBytes : Nat := 256 * 1024 * 1024

/-- Most entries the cache may hold (bounds cached errors, which hold no image bytes). -/
def cacheEntries : Nat := 64

/-- LRU cache of rendered pages, bounded by total bytes and entry count. -/
structure Cache where
  /-- The entries, in no particular order. -/
  entries : Array Entry := #[]
  /-- Sum of the entries' `bytes`. -/
  bytes : Nat := 0
  /-- Use counter. -/
  tick : Nat := 0
  /-- Byte budget. -/
  budget : Nat := cacheBytes
  /-- Entry budget. -/
  maxEntries : Nat := cacheEntries

/-- Bytes of a render result. -/
def resultBytes : Except Error Raster.Clip.Image → Nat
  | .ok img => img.data.size
  | .error _ => 0

/-- Looks `k` up and, on a hit, marks the entry as most recently used. -/
def Cache.find? (c : Cache) (k : Key) : Option (Except Error Raster.Clip.Image) × Cache :=
  match c.entries.findIdx? (·.key == k) with
  | some i =>
    match c.entries[i]? with
    | some e =>
      (some e.result, { c with entries := c.entries.modify i ({ · with used := c.tick + 1 }),
                               tick := c.tick + 1 })
    | none => (none, c)
  | none => (none, c)

/-- `true` when `k` is cached (no LRU update). -/
def Cache.contains (c : Cache) (k : Key) : Bool :=
  c.entries.any (·.key == k)

/-- Removes the least recently used entry. -/
def Cache.evictOne (c : Cache) : Cache :=
  match c.entries[0]? with
  | none => c
  | some e0 =>
    let (_, best) := c.entries.foldl (fun (acc : Nat × Nat) e =>
      let (i, b) := acc
      (i + 1, if e.used < (c.entries[b]?.map (·.used)).getD 0 then i else b)) (0, 0)
    let victim := (c.entries[best]?).getD e0
    { c with entries := c.entries.eraseIdxIfInBounds best, bytes := c.bytes - victim.bytes }

/-- Evicts LRU entries (at most `fuel`) while over either budget. -/
def Cache.trim (c : Cache) : Nat → Cache
  | 0 => c
  | fuel + 1 =>
    if c.bytes > c.budget || c.entries.size > c.maxEntries then (c.evictOne).trim fuel else c

/-- Inserts (or replaces) `k ↦ r` as the most recently used entry, then evicts LRU entries
until both budgets hold. A result larger than half the byte budget is not cached. -/
def Cache.insert (c : Cache) (k : Key) (r : Except Error Raster.Clip.Image) : Cache :=
  let b := resultBytes r
  if 2 * b > c.budget then c
  else
    let old := c.entries.filter (·.key == k)
    let c := { c with entries := c.entries.filter (·.key != k),
                      bytes := c.bytes - (old.foldl (fun n (e : Entry) => n + e.bytes) 0) }
    let c := { c with entries := c.entries.push ⟨k, r, b, c.tick + 1⟩, bytes := c.bytes + b,
                      tick := c.tick + 1 }
    c.trim c.entries.size

private def img (n : Nat) : Except Error Raster.Clip.Image :=
  .ok ⟨n, 1, ByteArray.mk (Array.replicate (4 * n) 255)⟩

private def key (p : Nat) : Key := ⟨0, p, 1, .r0⟩

-- Budget 100 bytes: pages of 40 bytes each; the third insertion evicts the LRU one.
#guard
  let c : Cache := { budget := 100 }
  let c := (c.insert (key 0) (img 10)).insert (key 1) (img 10)
  let (_, c) := c.find? (key 0)            -- page 0 is now more recent than page 1
  let c := c.insert (key 2) (img 10)
  c.contains (key 0) && !c.contains (key 1) && c.contains (key 2) && c.bytes == 80
-- Re-inserting a key replaces it; too-large results are not cached.
#guard
  let c : Cache := { budget := 100 }
  let c := (c.insert (key 0) (img 10)).insert (key 0) (img 5)
  let c := c.insert (key 1) (img 20)
  c.entries.size == 1 && c.bytes == 20
-- The entry budget bounds cached errors.
#guard
  let c : Cache := { maxEntries := 2 }
  let c := [0, 1, 2, 3].foldl (fun c p => c.insert (key p) (.error (.malformed 0 "x"))) c
  c.entries.size == 2 && c.contains (key 3) && c.contains (key 2)

end SafePdf.Shell.App.View
