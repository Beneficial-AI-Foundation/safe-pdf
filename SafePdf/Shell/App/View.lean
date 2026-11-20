import SafePdf.Core.Raster.Geom
import SafePdf.Core.Raster.Clip
import SafePdf.Core.Limits

/-!
# Viewer geometry and page cache (task 8.2b; Plan.md §6 Phase 8, §8 native app, §10 `SafePdf/Shell/`)

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
