import SafePdf.Shell.App.Toolbar
import SafePdf.Shell.App.Budget
import SafePdf.Core.Raster.Clip

/-!
# C API v2: view and chrome logic (task 11.3a2; Plan.md §6 Phase 11, §8 native app)

The pure viewing and chrome rules of the Tk viewer, exported for the native macOS shell
(`docs/macos-design.md` §3, decision 1: whatever has a theorem or a `#guard` stays in Lean and
crosses as a pure function, state in → state out + display data). Every export here **calls**
the existing functions of `App.View`, `App.Toolbar` and `App.Menu`; nothing with a theorem or a
`#guard` is re-implemented. The only composition is `layout`, which follows the Tk viewer's
`Viewer.computeLayout`/`baseZoom`/`viewParamsAt` (that module links Tk, so it cannot be
imported here) step by step.

This module is unverified shell code. It is **not** the public C API: `macos/safepdf_view.c`
wraps it into plain C (`macos/safepdf_view.h`: flat structs, `safepdf_free_*`).

**Internal wire format.** Numbers cross as a `ByteArray` of little-endian 64-bit two's
complement integers (`enc`, `getI64`): a rational is two of them, numerator and denominator
(`ratW`; an unrepresentable one is sent as `0/0`, which the C side reports as an error), a
`Bool` is `0`/`1`, an `Option Nat` is a flag and the value. Tables cross as a `Table`: the
integers of every row in one `ByteArray` and the strings of every row in one `Array String`,
with a fixed number of each per row (documented at each table). Exports consume their
arguments (Lean v4.36 `@[export]` takes no `@&`), and every result is owned by the caller.

**Enumerations** cross as their index in a fixed list (`Menu.Cmd.all`, `toolAll`, …), mirrored
by C enums in the header and checked by name in `macos/tests/view_test.c` (`cmdName`).
-/

namespace SafePdf.Shell.FfiView

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Shell.App

/-! ## Wire encoding -/

/-- Largest 64-bit signed integer. -/
def i64Max : Int := 2 ^ 63 - 1

/-- Smallest 64-bit signed integer. -/
def i64Min : Int := -(2 ^ 63)

/-- Whether `v` fits a 64-bit signed integer. -/
def fitsI64 (v : Int) : Bool := decide (i64Min ≤ v) && decide (v ≤ i64Max)

/-- Appends `v` as 8 little-endian bytes (two's complement, wrapping outside the range). -/
def putI64 (b : ByteArray) (v : Int) : ByteArray :=
  let u := v.toInt64.toUInt64
  (List.range 8).foldl (fun b i => b.push (u >>> (8 * i).toUInt64).toUInt8) b

/-- The integers `xs` in the wire format. -/
def enc (xs : List Int) : ByteArray := xs.foldl putI64 ByteArray.empty

/-- Integer `i` (0-based) of a wire array; `0` past its end. -/
def getI64 (b : ByteArray) (i : Nat) : Int :=
  let u : Nat := (List.range 8).foldl
    (fun acc k => acc + (b[8 * i + k]?.getD 0).toNat * 256 ^ k) 0
  if u ≥ 2 ^ 63 then (u : Int) - 2 ^ 64 else u

/-- Integer `i` as a natural number (negative values become `0`). -/
def getNat (b : ByteArray) (i : Nat) : Nat := (getI64 b i).toNat

/-- Integer `i` as a flag (non-zero is `true`). -/
def getBool (b : ByteArray) (i : Nat) : Bool := getI64 b i != 0

/-- The rational `n / d`; `0` when `d ≤ 0` (the C side rejects such input before the call). -/
def ratOf (n d : Int) : Rat := if d ≤ 0 then 0 else (n : Rat) / (d : Rat)

/-- The rational held in integers `i` and `i + 1`. -/
def getRat (b : ByteArray) (i : Nat) : Rat := ratOf (getI64 b i) (getI64 b (i + 1))

/-- A rational on the wire: numerator and (positive) denominator, or `0, 0` when either does
not fit 64 bits. -/
def ratW (q : Rat) : List Int :=
  if fitsI64 q.num && fitsI64 q.den then [q.num, q.den] else [0, 0]

/-- A natural number on the wire, saturated at `i64Max`. -/
def natW (n : Nat) : Int := min (n : Int) i64Max

/-- A flag on the wire. -/
def boolW (x : Bool) : Int := if x then 1 else 0

/-- The page box held in integers `i … i + 7` (`llx lly urx ury`, each a rational). -/
def getBox (b : ByteArray) (i : Nat) : Box :=
  ⟨getRat b i, getRat b (i + 2), getRat b (i + 4), getRat b (i + 6)⟩

/-- A rotation from degrees: `(deg / 90) mod 4` quarter turns (0, 90, 180, 270 exactly;
other values rounded down to a quarter turn). -/
def rotOf (deg : Nat) : Doc.Rotation :=
  match (deg / 90) % 4 with
  | 0 => .r0
  | 1 => .r90
  | 2 => .r180
  | _ => .r270

/-- Degrees of a rotation (`View.rotDeg`). -/
def degW (r : Doc.Rotation) : Int := View.rotDeg r

#guard getI64 (enc [-5, 0, i64Max, i64Min, 300]) 0 == -5
#guard (List.range 5).map (getI64 (enc [-5, 0, i64Max, i64Min, 300])) == [-5, 0, i64Max, i64Min, 300]
#guard ratW (85 / 64) == [85, 64] && ratW (-3 / 2) == [-3, 2] && ratW ((2 : Rat) ^ 70) == [0, 0]
#guard [0, 90, 180, 270, 360, 450].map (degW ∘ rotOf) == [0, 90, 180, 270, 0, 90]

/-- A table crossing to C: `ints` holds a fixed number of integers per row, `strs` a fixed
number of strings per row (per table, documented at its export). -/
structure Table where
  /-- The integers of every row, row after row, in the wire format. -/
  ints : ByteArray
  /-- The strings of every row, row after row. -/
  strs : Array String

/-- A table from its rows (integers and strings of each row). -/
def Table.ofRows (rows : List (List Int × List String)) : Table :=
  ⟨enc (rows.flatMap (·.1)), (rows.flatMap (·.2)).toArray⟩

/-- The last component of a constructor's `repr` (`Menu.Cmd.openFile` → `openFile`). -/
def ctorName {α : Type} [Repr α] (a : α) : String :=
  ((reprStr a).splitOn ".").getLast?.getD ""

/-! ## Enumerations as indices -/

/-- Index of a command in `Menu.Cmd.all` (the C enum `safepdf_cmd`). -/
def cmdIdx (c : Menu.Cmd) : Nat := Menu.Cmd.all.idxOf c

/-- The command of index `i`. -/
def cmdOf (i : Nat) : Option Menu.Cmd := Menu.Cmd.all[i]?

/-- Every toolbar tool, in the order of the C enum `safepdf_tool`. -/
def toolAll : List Toolbar.Tool := [.select, .highlight, .comment, .text, .draw, .image, .print]

/-- Index of a tool in `toolAll`. -/
def toolIdx (t : Toolbar.Tool) : Nat := toolAll.idxOf t

/-- Every active-tool mode, in the order of the C enum `safepdf_tool_mode`. -/
def modeAll : List Toolbar.Mode := [.select, .highlight, .text, .draw]

/-- Every pointer hit, in the order of the C enum `safepdf_hit`. -/
def hitAll : List Toolbar.Hit := [.text, .link, .mark, .empty]

/-- Every key action, in the order of the C enum `safepdf_action` (`Menu.Action.all`). -/
def actionIdx (a : Menu.Action) : Nat := Menu.Action.all.idxOf a

/-- Scroll mode from its index (`page`, `vertical`). -/
def scrollOf (i : Nat) : View.ScrollMode := if i == 1 then .vertical else .page

/-- Index of a scroll mode. -/
def scrollIdx : View.ScrollMode → Nat
  | .page => 0
  | .vertical => 1

/-- Spread mode from its index (`none`, `odd`, `even`). -/
def spreadOf (i : Nat) : View.SpreadMode :=
  match i with
  | 1 => .odd
  | 2 => .even
  | _ => .none

/-- Index of a spread mode. -/
def spreadIdx : View.SpreadMode → Nat
  | .none => 0
  | .odd => 1
  | .even => 2

/-- Zoom choice from its kind (`auto`, `actual`, `pageFit`, `pageWidth`, `pct`) and percent. -/
def zoomOf (kind pct : Nat) : Toolbar.ZoomChoice :=
  match kind with
  | 0 => .auto
  | 1 => .actual
  | 2 => .pageFit
  | 3 => .pageWidth
  | _ => .pct pct

/-- Kind and percent of a zoom choice (percent `0` except for `pct`). -/
def zoomW : Toolbar.ZoomChoice → List Int
  | .auto => [0, 0]
  | .actual => [1, 0]
  | .pageFit => [2, 0]
  | .pageWidth => [3, 0]
  | .pct p => [4, p]

/-- Index of a view-mode choice in `Toolbar.ViewChoice.all`. -/
def viewChoiceIdx (c : Toolbar.ViewChoice) : Nat := Toolbar.ViewChoice.all.idxOf c

-- The index lists are complete and the round trips hold.
#guard Menu.Cmd.all.length == 38 && (List.range 38).all fun i => (cmdOf i).map cmdIdx == some i
#guard toolAll.eraseDups.length == 7 && modeAll.eraseDups.length == 4 && hitAll.eraseDups.length == 4
#guard [Toolbar.ZoomChoice.auto, .actual, .pageFit, .pageWidth, .pct 33].all fun c =>
  match zoomW c with
  | [k, p] => zoomOf k.toNat p.toNat == c
  | _ => false
#guard [View.SpreadMode.none, .odd, .even].all fun s => spreadOf (spreadIdx s) == s
#guard [View.ScrollMode.page, .vertical].all fun s => scrollOf (scrollIdx s) == s
#guard ctorName Menu.Cmd.openFile == "openFile" && ctorName Toolbar.Tool.print == "print"

/-! ## Constants -/

/-- The view constants, in order: `View.margin`, `View.pageGap`, `View.minPct`,
`View.maxPct`, `Toolbar.autoMaxPct`, `Budget.ceilings.pagePixels` (the per-page pixel cap the
Tk viewer passes to `capZoom`), `Limits.maxPageSide` (default limits), `View.maxViewPixels`. -/
@[export safepdf_lean_view_constants]
def constants (_u : Unit) : ByteArray :=
  enc [View.margin, View.pageGap, View.minPct, View.maxPct, Toolbar.autoMaxPct,
    Budget.ceilings.pagePixels, Limits.default.maxPageSide, View.maxViewPixels]

/-- The zoom steps in percent (`View.zoomSteps`). -/
@[export safepdf_lean_view_zoom_steps]
def zoomSteps (_u : Unit) : ByteArray := enc (View.zoomSteps.map Int.ofNat)

/-! ## Zoom (View) -/

/-- `View.quant`. In: `z` (2). Out: rational. -/
@[export safepdf_lean_view_quant]
def quant (a : ByteArray) : ByteArray := enc (ratW (View.quant (getRat a 0)))

/-- `View.pctZoom`. In: `pct`, `scaling` (2). Out: rational. -/
@[export safepdf_lean_view_pct_zoom]
def pctZoom (a : ByteArray) : ByteArray := enc (ratW (View.pctZoom (getNat a 0) (getRat a 1)))

/-- `View.zoomPct`. In: `z` (2), `scaling` (2). Out: percent. -/
@[export safepdf_lean_view_zoom_pct]
def zoomPct (a : ByteArray) : ByteArray := enc [View.zoomPct (getRat a 0) (getRat a 2)]

/-- An `Option Nat` on the wire: flag, value. -/
def optW : Option Nat → List Int
  | some p => [1, p]
  | none => [0, 0]

/-- `View.stepInZ` (Zoom In on the quantised zoom, task 10.12). In: `z` (2), `scaling` (2).
Out: found flag, percent. -/
@[export safepdf_lean_view_step_in]
def stepIn (a : ByteArray) : ByteArray := enc (optW (View.stepInZ (getRat a 0) (getRat a 2)))

/-- `View.stepOutZ`. In and out as `stepIn`. -/
@[export safepdf_lean_view_step_out]
def stepOut (a : ByteArray) : ByteArray := enc (optW (View.stepOutZ (getRat a 0) (getRat a 2)))

/-- `View.fitZoom`. In: `widthOnly`, `cw`, `ch`, `pw` (2), `ph` (2). Out: rational. -/
@[export safepdf_lean_view_fit_zoom]
def fitZoom (a : ByteArray) : ByteArray :=
  enc (ratW (View.fitZoom (getBool a 0) (getNat a 1) (getNat a 2) (getRat a 3) (getRat a 5)))

/-- `View.capZoom`. In: `maxPx`, `z` (2), rotation degrees, box (8). Out: rational, lowered
flag. -/
@[export safepdf_lean_view_cap_zoom]
def capZoom (a : ByteArray) : ByteArray :=
  let (z, low) := View.capZoom (getNat a 0) (getRat a 1) (rotOf (getNat a 3)) (getBox a 4)
  enc (ratW z ++ [boolW low])

/-- `View.pixelSize`, `Clip.pageSize` with side `side`, and `View.cropped side`. In: `side`,
`z` (2), rotation degrees, box (8). Out: uncapped width, height; page image width, height (as
the renderer makes it); cropped flag. -/
@[export safepdf_lean_view_pixel_size]
def pixelSize (a : ByteArray) : ByteArray :=
  let side := getNat a 0
  let z := getRat a 1
  let r := rotOf (getNat a 3)
  let bx := getBox a 4
  let (w, h) := View.pixelSize z r bx
  let (cw, chh) := Raster.Clip.pageSize side z r bx
  enc [w, h, cw, chh, boolW (View.cropped side z r bx)]

/-- `View.rotCw`, `View.rotCcw` and `View.boxSize`. In: rotation degrees, box (8). Out:
degrees after a clockwise and after a counter-clockwise quarter turn, displayed width (2) and
height (2) in page units. -/
@[export safepdf_lean_view_rotate]
def rotate (a : ByteArray) : ByteArray :=
  let r := rotOf (getNat a 0)
  let (w, h) := View.boxSize r (getBox a 1)
  enc ([degW (View.rotCw r), degW (View.rotCcw r)] ++ ratW w ++ ratW h)

/-- `View.reanchor` (C2). In: `z` (2), `r`, `z'` (2), `r'`, box (8), point (4). Out: point
(4). -/
@[export safepdf_lean_view_reanchor]
def reanchor (a : ByteArray) : ByteArray :=
  let q := View.reanchor (getRat a 0) (rotOf (getNat a 2)) (getRat a 3) (rotOf (getNat a 5))
    (getBox a 6) ⟨getRat a 14, getRat a 16⟩
  enc (ratW q.x ++ ratW q.y)

#guard reanchor (enc ([1, 1, 0, 2, 1, 90, 0, 1, 0, 1, 612, 1, 792, 1, 306, 1, 396, 1])) ==
  enc [792, 1, 612, 1]

/-! ## Spreads and page order (View) -/

/-- `View.spreadOf`, `View.spreadCount`, `View.spreadPages` of the page's spread,
`View.nextPage`, `View.prevPage`. In: spread mode, `n`, page. Out: spread, spread count, next
page, previous page, number of pages in the spread, its pages (two slots, unused ones `0`). -/
@[export safepdf_lean_view_spread]
def spread (a : ByteArray) : ByteArray :=
  let sp := spreadOf (getNat a 0)
  let n := getNat a 1
  let p := getNat a 2
  let k := View.spreadOf sp p
  let ps := View.spreadPages sp n k
  enc (([k, View.spreadCount sp n, View.nextPage sp n p, View.prevPage sp p, ps.length,
    ps.getD 0 0, ps.getD 1 0] : List Nat).map Int.ofNat)

#guard (List.range 5).map (fun p => getNat (spread (enc [1, 5, Int.ofNat p])) 2) == [2, 2, 4, 4, 4]
#guard (List.range 5).map (fun p => getNat (spread (enc [2, 5, Int.ofNat p])) 3) == [0, 0, 0, 1, 1]

/-! ## Layout (View, composed as `Viewer.computeLayout`) -/

/-- Per-page view parameters of a layout: zoom (capped per page), rotation (page `/Rotate`
plus the user's), box, whether the zoom was lowered by the pixel cap, whether the renderer
crops the page. -/
structure PageView where
  /-- Zoom of the page (pixels per page unit). -/
  zoom : Rat
  /-- Rotation (page `/Rotate` + user rotation). -/
  rot : Doc.Rotation
  /-- The page box. -/
  box : Box
  /-- `View.capZoom` lowered the zoom. -/
  capped : Bool
  /-- `View.cropped` at `Limits.maxPageSide`. -/
  cropped : Bool

/-- The layout of a document whose pages have boxes and `/Rotate` values `pages`, as the Tk
viewer computes it (`Viewer.layoutRowsOf`, `baseZoom`, `viewParamsAt`, `computeLayout`): the
rows are the current spread in the page scroll mode, every spread in the vertical one; the
zoom is `ZoomChoice.zoomWith` for the current page (its size, or the `View.fitBox` spread box
in a canvas `View.fitCanvasW` wide); each laid-out page gets that zoom capped by
`View.capZoom` at `Budget.ceilings.pagePixels`, image size `Clip.pageSize` at
`Limits.maxPageSide`; `View.layoutRows` places them (centred vertically in the page scroll
mode) and right-to-left documents mirror the spreads (`View.mirrorPlace`). Returns the base
zoom, the places with their page parameters (page order) and the scroll region's size. -/
def layout (pages : Array (Box × Doc.Rotation)) (scroll : View.ScrollMode)
    (spreadM : View.SpreadMode) (userRot : Doc.Rotation) (zc : Toolbar.ZoomChoice)
    (scaling : Rat) (cw ch page : Nat) (rtl : Bool) :
    Rat × Array (View.Place × PageView) × Nat × Nat :=
  let n := pages.size
  let side := Limits.default.maxPageSide
  let rows := match scroll with
    | .page => [View.spreadPages spreadM n (View.spreadOf spreadM page)]
    | .vertical => View.spreads spreadM n
  let z0 := match pages[page]? with
    | some (bx, pr) =>
      let r := rotAdd pr userRot
      let (pw, ph) := View.boxSize r bx
      let (fw, fh) := View.fitBox spreadM pw ph
      zc.zoomWith (View.fitCanvasW spreadM cw) ch scaling fw fh (decide (pw ≤ ph))
    | none => 1
  let vps : Array (Option PageView) := (Array.range n).map fun p =>
    if scroll == .vertical || rows.any (·.contains p) then
      pages[p]?.map fun (bx, pr) =>
        let r := rotAdd pr userRot
        let (z, capped) := View.capZoom Budget.ceilings.pagePixels z0 r bx
        ⟨z, r, bx, capped, View.cropped side z r bx⟩
    else none
  let sizes := vps.map fun o => match o with
    | some v => Raster.Clip.pageSize side v.zoom v.rot v.box
    | none => (0, 0)
  let (ps, rw, rh) := View.layoutRows sizes rows cw ch (scroll == .page)
  let ps := if rtl && spreadM != .none then ps.map (View.mirrorPlace rw) else ps
  (z0, ps.filterMap fun pl => (vps[pl.page]?.join).map (pl, ·), rw, rh)

/-- Integers per page in `layoutW`'s input. -/
def pageInts : Nat := 9

/-- Integers per place in `layoutW`'s output. -/
def placeInts : Nat := 10

/-- `layout` on the wire. In: scroll mode, spread mode, user rotation degrees, zoom kind,
zoom percent, `scaling` (2), `cw`, `ch`, current page, right-to-left flag, then per page
(`pageInts`): box (8) and `/Rotate` degrees. Out: base zoom (2), region width, region height,
place count, then per place (`placeInts`): page, `x`, `y`, `w`, `h`, zoom (2), rotation
degrees, capped flag, cropped flag. -/
@[export safepdf_lean_view_layout]
def layoutW (a : ByteArray) : ByteArray :=
  let hdr := 11
  let n := (a.size / 8 - hdr) / pageInts
  let pages := (Array.range n).map fun i =>
    (getBox a (hdr + pageInts * i), rotOf (getNat a (hdr + pageInts * i + 8)))
  let (z0, ps, rw, rh) := layout pages (scrollOf (getNat a 0)) (spreadOf (getNat a 1))
    (rotOf (getNat a 2)) (zoomOf (getNat a 3) (getNat a 4)) (getRat a 5) (getNat a 7)
    (getNat a 8) (getNat a 9) (getBool a 10)
  enc (ratW z0 ++ ([rw, rh, ps.size] : List Nat).map Int.ofNat ++ ps.toList.flatMap fun (pl, v) =>
    ([pl.page, pl.x, pl.y, pl.w, pl.h] : List Nat).map Int.ofNat ++ ratW v.zoom ++ [degW v.rot, boolW v.capped,
      boolW v.cropped])

-- Four 100 × 200 pages at 100 % (scaling 1) stacked in a 300 × 300 canvas: the places of
-- `View.layoutRows`' own `#guard` (y 8, 218, 428, …), region 300 wide.
#guard
  let bx : Box := ⟨0, 0, 100, 200⟩
  let (z, ps, rw, rh) := layout #[(bx, .r0), (bx, .r0), (bx, .r0), (bx, .r0)] .vertical .none
    .r0 (.pct 100) 1 300 300 0 false
  z == 1 && rw == 300 && rh == 846 && ps.map (·.1.y) == #[8, 218, 428, 638] &&
  ps.map (·.1.x) == #[100, 100, 100, 100] && ps.all (!·.2.capped)
-- The page scroll mode lays out the current spread only (odd spreads: pages 2|3 of 5).
#guard
  let bx : Box := ⟨0, 0, 100, 200⟩
  let (_, ps, _, _) := layout (Array.replicate 5 (bx, .r0)) .page .odd .r0 (.pct 100) 1 300 300
    2 false
  ps.map (·.1.page) == #[2, 3]
-- Automatic Zoom on a Letter page in a wide window: 125 % (task 9.7's `#guard`), and the
-- user rotation applies on top of `/Rotate`.
#guard (layout #[(⟨0, 0, 612, 792⟩, .r0)] .vertical .none .r0 .auto (4 / 3) 1900 900 0
  false).1 == View.pctZoom 125 (4 / 3)
#guard ((layout #[(⟨0, 0, 612, 792⟩, .r90)] .vertical .none .r90 (.pct 100) 1 1000 1000 0
  false).2.1.map (·.2.rot)) == #[.r180]
#guard getI64 (layoutW (enc ([1, 0, 0, 4, 100, 1, 1, 300, 300, 0, 0] ++
  [0, 1, 0, 1, 100, 1, 200, 1, 0]))) 4 == 1

/-- Integers per place in the input of `visible`, `wanted` and `pageAtW`. -/
def placeInInts : Nat := 5

/-- The places of a wire array from integer `start` on (page, `x`, `y`, `w`, `h` each). -/
def getPlaces (a : ByteArray) (start : Nat) : Array View.Place :=
  let n := (a.size / 8 - start) / placeInInts
  (Array.range n).map fun i =>
    let o := start + placeInInts * i
    ⟨getNat a o, getNat a (o + 1), getNat a (o + 2), getNat a (o + 3), getNat a (o + 4)⟩

/-- `View.visiblePages` and `View.wantedPages`. In: `top`, `bot`, then places (5 each). Out:
visible count, the visible pages, then the wanted pages (the rest). -/
@[export safepdf_lean_view_pages_in_band]
def pagesInBand (a : ByteArray) : ByteArray :=
  let ps := getPlaces a 2
  let vis := View.visiblePages ps (getNat a 0) (getNat a 1)
  let want := View.wantedPages ps (getNat a 0) (getNat a 1)
  enc ([(vis.length : Int)] ++ vis.map Int.ofNat ++ want.map Int.ofNat)

/-- `View.pageAt`, and `View.topFor` / `View.bottomFor` of that page's place. In: `x`, `y`,
view height, then places (5 each). Out: found flag, page, its top and bottom scroll
positions. -/
@[export safepdf_lean_view_page_at]
def pageAtW (a : ByteArray) : ByteArray :=
  let ps := getPlaces a 3
  match View.pageAt ps (getNat a 0) (getNat a 1) with
  | some p => match View.placeOf ps p with
    | some pl => enc [1, p, View.topFor pl, View.bottomFor pl (getNat a 2)]
    | none => enc [0, 0, 0, 0]
  | none => enc [0, 0, 0, 0]

/-! ## Zoom choices, view choices, page field (Toolbar) -/

/-- The zoom drop-down (`ZoomChoice.presets`). Rows: kind, percent | label, key. -/
@[export safepdf_lean_view_zoom_presets]
def zoomPresets (_u : Unit) : Table :=
  .ofRows (Toolbar.ZoomChoice.presets.map fun c => (zoomW c, [c.label, c.key]))

/-- `ZoomChoice.label` and `ZoomChoice.key` of a choice (kind, percent). -/
@[export safepdf_lean_view_zoom_label]
def zoomLabel (kind pct : UInt32) : Array String :=
  let c := zoomOf kind.toNat pct.toNat
  #[c.label, c.key]

/-- `ZoomChoice.ofKey`. Out: found flag, kind, percent. -/
@[export safepdf_lean_view_zoom_parse]
def zoomParse (key : String) : ByteArray :=
  match Toolbar.ZoomChoice.ofKey key with
  | some c => enc ([1] ++ zoomW c)
  | none => enc [0, 0, 0]

/-- `ZoomChoice.zoomWith`. In: kind, percent, `cw`, `ch`, `scaling` (2), `pw` (2), `ph` (2),
portrait flag. Out: rational. -/
@[export safepdf_lean_view_zoom_with]
def zoomWith (a : ByteArray) : ByteArray :=
  enc (ratW ((zoomOf (getNat a 0) (getNat a 1)).zoomWith (getNat a 2) (getNat a 3) (getRat a 4)
    (getRat a 6) (getRat a 8) (getBool a 10)))

/-- The view-mode drop-down (`ViewChoice.all`). Rows: index, scroll mode, spread mode (from
spread mode none) | label, key. -/
@[export safepdf_lean_view_choices]
def viewChoices (_u : Unit) : Table :=
  .ofRows (Toolbar.ViewChoice.all.map fun c =>
    let (sc, sp) := c.modes .none
    ([viewChoiceIdx c, scrollIdx sc, spreadIdx sp], [c.label, c.key]))

/-- `ViewChoice.ofModes` and `ViewChoice.modes`. In: scroll mode, spread mode, choice index.
Out: the choice the modes show; the scroll and spread modes the choice sets from that spread
mode. -/
@[export safepdf_lean_view_choice_modes]
def viewChoiceModes (a : ByteArray) : ByteArray :=
  let sp := spreadOf (getNat a 1)
  let shown := Toolbar.ViewChoice.ofModes (scrollOf (getNat a 0)) sp
  let c := (Toolbar.ViewChoice.all[getNat a 2]?).getD .single
  let (sc', sp') := c.modes sp
  enc [viewChoiceIdx shown, scrollIdx sc', spreadIdx sp']

/-- `Toolbar.entryText` and `Toolbar.ofText` on page `page` of `n`. -/
@[export safepdf_lean_view_page_field]
def pageField (labels : Array String) (page n : USize) : Array String :=
  #[Toolbar.entryText labels page.toNat, Toolbar.ofText labels page.toNat n.toNat]

/-- `Toolbar.pageEntry`. Out: page, valid flag. -/
@[export safepdf_lean_view_page_entry]
def pageEntry (labels : Array String) (n cur : USize) (input : String) : ByteArray :=
  let (p, ok) := Toolbar.pageEntry labels n.toNat cur.toNat input
  enc [p, boolW ok]

#guard pageEntry #["i", "ii", "1"] 3 0 "II" == enc [1, 1]

/-! ## Toolbar, enabled rules, cursor (Toolbar) -/

/-- A Tk path without the toolbar's `.bar.` prefix (the item's id). -/
def barId (path : String) : String :=
  if path.startsWith ".bar." then (path.drop 5).toString else path

/-- One toolbar item as a row: group (0 left, 1 centre, 2 right), kind (0 button,
1 separator, 2 page field, 3 zoom drop-down, 4 view drop-down), action (0 command, 1 tool,
2 overflow menu; buttons only), command index, tool index | id, icon name, tooltip (with the
macOS key glyphs, `Platform.keyText .aqua`). -/
def itemRow (g : Nat) : Toolbar.Item → List Int × List String
  | .button b =>
    let (act, c, t) : Nat × Int × Int := match b.act with
      | .cmd k => (0, cmdIdx k, -1)
      | .tool t => (1, -1, toolIdx t)
      | .more => (2, -1, -1)
    ([g, 0, act, c, t], [barId b.path, b.icon, Menu.Platform.aqua.keyText b.tip])
  | .sep p => ([g, 1, -1, -1, -1], [barId p, "", ""])
  | .pageField => ([g, 2, -1, -1, -1], ["page", "", ""])
  | .zoomBox => ([g, 3, -1, -1, -1], ["zoom", "", ""])
  | .viewBox => ([g, 4, -1, -1, -1], ["view", "", ""])

/-- Every toolbar item, left to right, with its group. -/
def toolbarItems : List (Nat × Toolbar.Item) :=
  ((List.range Toolbar.layout.length).zip Toolbar.layout).flatMap fun (g, _, items) =>
    items.map (g, ·)

/-- The toolbar (`Toolbar.layout`). Rows: as `itemRow` (5 integers, 3 strings). -/
@[export safepdf_lean_view_toolbar]
def toolbar (_u : Unit) : Table :=
  .ofRows (toolbarItems.map fun (g, it) => itemRow g it)

/-- The enabled rules' context from the wire: flags (bit 0 `hasDoc`, 1 `hasSel`,
2 `hasOutline`, 3 `hasMark`, 4 `canBack`, 5 `canForward`, 6 `dirty`, 7 `canUndo`,
8 `canRedo`, 9 `onFirst`, 10 `onLast`), page, pages. -/
def ctxOf (a : ByteArray) : Menu.Ctx :=
  let f := getNat a 0
  let bit (i : Nat) : Bool := (f >>> i) % 2 == 1
  { hasDoc := bit 0, hasSel := bit 1, hasOutline := bit 2, hasMark := bit 3, canBack := bit 4,
    canForward := bit 5, dirty := bit 6, canUndo := bit 7, canRedo := bit 8, onFirst := bit 9,
    onLast := bit 10, page := getNat a 1, pages := getNat a 2 }

/-- `Cmd.enabled` of every command (`Cmd.all` order), then per toolbar item its enabled and
visible flags (`Button.enabled`, `Button.visible`; items other than buttons `1, 1`). In: the
context (`ctxOf`). -/
@[export safepdf_lean_view_states]
def states (a : ByteArray) : ByteArray :=
  let c := ctxOf a
  enc (Menu.Cmd.all.map (boolW ∘ Menu.Cmd.enabled c) ++ toolbarItems.flatMap fun (_, it) =>
    match it with
    | .button b => [boolW (b.enabled c), boolW (b.visible c)]
    | _ => [1, 1])

-- Without a document only Open, Quit, About and the overflow button work.
#guard
  let s := states (enc [0, 0, 0])
  let ids := (toolbar ()).strs
  (List.range 38).filter (getBool s ·) == [0, 6, 37] &&
  ((List.range toolbarItems.length).filter fun i =>
    getI64 (toolbar ()).ints (5 * i + 1) == 0 && getBool s (38 + 2 * i)).map
    (fun i => ids[3 * i]?) == [some "more"]

/-- Cursor kinds of the C enum `safepdf_cursor`: the Tk cursor names of `Toolbar.cursorFor`
(`""` arrow, `xterm` I-beam, `hand2` pointing hand, `crosshair`). -/
def cursorKind (s : String) : Nat :=
  if s == "xterm" then 1 else if s == "hand2" then 2 else if s == "crosshair" then 3 else 0

/-- `Toolbar.cursorFor` of a mode and a hit (indices in `modeAll`, `hitAll`), as a cursor
kind. -/
@[export safepdf_lean_view_cursor_for]
def cursorFor (mode hit : UInt32) : UInt32 :=
  let m := (modeAll[mode.toNat]?).getD .select
  let h := (hitAll[hit.toNat]?).getD .empty
  (cursorKind (Toolbar.cursorFor m h)).toUInt32

/-- `Toolbar.hitOf` (index in `hitAll`). -/
@[export safepdf_lean_view_hit_of]
def hitOf (mark link text : UInt8) : UInt32 :=
  (hitAll.idxOf (Toolbar.hitOf (mark != 0) (link != 0) (text != 0))).toUInt32

/-- `Toolbar.Mode.tool`: the tool (index in `toolAll`) whose button shows pressed in a mode. -/
@[export safepdf_lean_view_mode_tool]
def modeTool (mode : UInt32) : UInt32 :=
  (toolIdx ((modeAll[mode.toNat]?).getD .select).tool).toUInt32

-- Every cursor of the table is a known kind, and the kinds are those of the Tk names.
#guard modeAll.all fun m => hitAll.all fun h =>
  ["", "xterm", "hand2", "crosshair"].contains (Toolbar.cursorFor m h)
#guard cursorFor 0 0 == 1 && cursorFor 0 1 == 2 && cursorFor 3 0 == 3 && cursorFor 0 3 == 0
#guard hitOf 1 1 1 == 2 && hitOf 0 0 0 == 3 && modeTool 3 == 4

/-! ## Commands, menus and keys (Menu) -/

/-- Modifier mask of the C API: 1 Command, 2 Shift, 4 Option, 8 Control. -/
def modsW (cmd shift opt ctrl : Bool) : Int :=
  boolW cmd + 2 * boolW shift + 4 * boolW opt + 8 * boolW ctrl

/-- A key of the macOS column (`Cmd.keyOn .aqua`, `Cmd.macKeys`, `Action.macKeys`): the
primary modifier is Command, `ctrl` the Control key. -/
def macKeyW (k : Menu.Key) : Int := modsW k.primary k.shift k.alt k.ctrl

/-- A key of the X11 column (`Cmd.key`, `Cmd.primaryKeys`, `Action.x11Keys`): the primary
modifier is Control. -/
def x11KeyW (k : Menu.Key) : Int := modsW false k.shift k.alt (k.primary || k.ctrl)

/-- The macOS accelerator of a command as (modifiers | key sym, shown name); none: `0 | "", ""`. -/
def accelW (c : Menu.Cmd) : List Int × List String :=
  match c.keyOn .aqua with
  | some k => ([macKeyW k], [k.sym, k.shown])
  | none => ([0], ["", ""])

/-- The commands (`Cmd.all`). Rows: index, macOS accelerator modifiers | name (the
constructor, for the C enum check), label, accelerator key sym (Tk keysym), shown key name. -/
@[export safepdf_lean_view_commands]
def commands (_u : Unit) : Table :=
  .ofRows (Menu.Cmd.all.map fun c =>
    let (ki, ks) := accelW c
    ([(cmdIdx c : Int)] ++ ki, [ctorName c, c.label] ++ ks))

/-- The radio group of a command (0 none, 1 scroll mode, 2 spread mode) and its value
(`Cmd.radio?`, the mode's key). -/
def radioW (c : Menu.Cmd) : Int × String :=
  match c.radio? with
  | some (v, val) => (if v == Menu.scrollVar then 1 else 2, val)
  | none => (0, "")

/-- A menu entry as a row: menu index, kind (0 command, 1 check, 2 highlight-colour cascade,
3 separator), command index (`-1` none), accelerator modifiers, radio group | label,
accelerator key sym, shown key name, radio value. -/
def entryRow (m : Nat) : Menu.Entry → List Int × List String
  | .cmd c =>
    let (ki, ks) := accelW c
    let (rg, rv) := radioW c
    ([(m : Int), 0, cmdIdx c] ++ ki ++ [rg], [c.label] ++ ks ++ [rv])
  | .check c _ =>
    let (ki, ks) := accelW c
    ([(m : Int), 1, cmdIdx c] ++ ki ++ [0], [c.label] ++ ks ++ [""])
  | .colors _ => ([(m : Int), 2, -1, 0, 0], [Menu.colorsLabel, "", "", ""])
  | .sep => ([(m : Int), 3, -1, 0, 0], ["", "", "", ""])

/-- The menubar (`Menu.menubar`): the menu labels, then the entries. Out: (labels, entry table
with rows as `entryRow`: 5 integers, 4 strings). -/
@[export safepdf_lean_view_menubar]
def menubar (_u : Unit) : Array String × Table :=
  ((Menu.menubar.map (·.label)).toArray,
    .ofRows (((List.range Menu.menubar.length).zip Menu.menubar).flatMap fun (i, m) =>
      m.entries.map (entryRow i)))

/-- The toolbar's overflow menu (`Toolbar.overflow`) as one menu (index 0) labelled as the
overflow button's tooltip. Out: as `menubar`. -/
@[export safepdf_lean_view_overflow]
def overflow (_u : Unit) : Array String × Table :=
  (((Toolbar.buttons.find? (·.act == .more)).map (·.tip)).toArray,
    .ofRows (Toolbar.overflow.map fun e => match e with
      | some c => entryRow 0 (.cmd c)
      | none => entryRow 0 .sep))

#guard (overflow ()).1 == #["Tools"] && (overflow ()).2.strs.size == 4 * Toolbar.overflow.length

/-- A key binding of the main window: the command or action it runs, the key, and whether it
comes from the X11 column (kept on macOS by the Tk viewer) or the macOS one. -/
structure KeyRow where
  /-- The command (`.inl`) or key action (`.inr`). -/
  target : Menu.Cmd ⊕ Menu.Action
  /-- The key. -/
  key : Menu.Key
  /-- From the X11 column (primary modifier = Control). -/
  x11 : Bool

/-- The script a binding runs (`Cmd.script`, `Action.script`). -/
def KeyRow.script (r : KeyRow) : String :=
  match r.target with
  | .inl c => c.script
  | .inr a => a.script

/-- Every key binding of the main window on macOS, in the order of `Menu.keyTable .aqua`
(which the `#guard` below reproduces from these rows). -/
def keyRows : List KeyRow :=
  (Menu.Cmd.all.flatMap fun c =>
      ((c.key.toList.filter (!·.primary)) ++ c.primaryKeys).map fun k => ⟨.inl c, k, true⟩) ++
  (Menu.Action.all.flatMap fun a => a.x11Keys.map fun k => ⟨.inr a, k, true⟩) ++
  (Menu.Cmd.all.flatMap fun c => c.macKeys.map fun k => ⟨.inl c, k, false⟩) ++
  (Menu.Action.all.flatMap fun a => a.macKeys.map fun k => ⟨.inr a, k, false⟩)

-- The rows are exactly `Menu.keyTable .aqua` (conflict-free by Menu's `#guard`s).
#guard (keyRows.flatMap fun r =>
  (if r.x11 then r.key.x11Seqs else r.key.macSeqs).map (·, r.script)) == Menu.keyTable .aqua

/-- The key table (`keyRows`). Rows: target kind (0 command, 1 action), target index,
modifiers (the column's meaning of the primary modifier applied), X11-column flag | key sym
(Tk keysym; a letter in lower case unless `R` with Shift), shown key name. -/
@[export safepdf_lean_view_keys]
def keys (_u : Unit) : Table :=
  .ofRows (keyRows.map fun r =>
    let (kind, idx) : Int × Int := match r.target with
      | .inl c => (0, cmdIdx c)
      | .inr a => (1, actionIdx a)
    ([kind, idx, if r.x11 then x11KeyW r.key else macKeyW r.key, boolW r.x11],
      [r.key.sym, r.key.shown]))

/-- The key action names (`Action.all`): constructor name, then `Action.name`. -/
@[export safepdf_lean_view_actions]
def actions (_u : Unit) : Array String :=
  (Menu.Action.all.flatMap fun a => [ctorName a, a.name]).toArray

/-- `Menu.appName` and `Menu.aboutDetail`. -/
@[export safepdf_lean_view_app_strings]
def appStrings (_u : Unit) : Array String := #[Menu.appName, Menu.aboutDetail]

#guard (commands ()).strs.size == 4 * 38
#guard (menubar ()).1 == #["File", "Edit", "View", "Go", "Help"]
#guard (menubar ()).2.strs.size == 4 * ((menubar ()).2.ints.size / 40)
#guard accelW .gotoPage == ([5], ["g", "G"]) && accelW .outline == ([9], ["s", "S"]) &&
  accelW .saveAs == ([3], ["s", "S"]) && accelW .prevPage == ([0], ["Prior", "PageUp"])

/-! ## Viewing parity, part 2 (task 11.3c2): wheel, page text, history, page → screen -/

/-- `View.WheelKind` from its index (`notch`, `line`, `pixel`; the C enum
`safepdf_wheel_kind`). -/
def wheelKindOf : Nat → View.WheelKind
  | 0 => .notch
  | 1 => .line
  | _ => .pixel

/-- **One wheel event** as the Tk viewer's `Viewer.wheel` handles it: `View.wheelStep` with the
movement of `View.wheelPixels` and the push of `View.wheelThreshold`. In: wheel state (`acc`
(2), `push` (2), `last`), kind, delta `d` (signed, Tk's `%D`: positive is up/left), `cross`
(the vertical axis in the page scroll mode), `now` (ms), `top`, `view`, `region` (pixels).
Out: action (0 none, 1 scroll to, 2 next page, 3 previous page), position (action 1), the new
state (`acc` (2), `push` (2), `last`). -/
@[export safepdf_lean_view_wheel_step]
def wheelStep (a : ByteArray) : ByteArray :=
  let w : View.Wheel := { acc := getRat a 0, push := getRat a 2, last := getNat a 4 }
  let k := wheelKindOf (getNat a 5)
  let view := getNat a 10
  let region := getNat a 11
  let (w', act) := View.wheelStep w (getNat a 8) (View.wheelPixels k (getI64 a 6) view)
    (getBool a 7) (getNat a 9) view region (View.wheelThreshold k view (region - view))
  let (code, pos) : Nat × Nat := match act with
    | .none => (0, 0)
    | .scrollTo p => (1, p)
    | .next => (2, 0)
    | .prev => (3, 0)
  enc ([Int.ofNat code, natW pos] ++ ratW w'.acc ++ ratW w'.push ++ [natW w'.last])

-- 100 px down from the top scrolls; at the bottom a push of 30 px past the threshold (25 px:
-- a twentieth of the view) turns the page.
#guard (List.range 2).map (getI64 (wheelStep (enc [0, 1, 0, 1, 0, 2, -100, 1, 1000, 0, 500, 1000]))) ==
  [1, 100]
#guard getI64 (wheelStep (enc [0, 1, 0, 1, 0, 2, -30, 1, 1000, 500, 500, 1000])) 0 == 2
#guard getI64 (wheelStep (enc [0, 1, 0, 1, 0, 2, -30, 0, 1000, 500, 500, 1000])) 0 == 0

/-- `Links.pageText`: the page as the window title and status line show it (`page k/n`, or
`page L (k/n)` with page labels). -/
@[export safepdf_lean_view_page_text]
def pageText (labels : Array String) (page n : USize) : String :=
  Links.pageText labels page.toNat n.toNat

#guard pageText #["i", "ii", "iii"] 2 120 == "page iii (3/120)" && pageText #[] 1 2 == "page 2/2"

/-- A history location held in integers `i … i + 4` (page, `x` (2), `y` (2)). -/
def getLoc (b : ByteArray) (i : Nat) : Links.Loc := ⟨getNat b i, getRat b (i + 1), getRat b (i + 3)⟩

/-- A history location on the wire. -/
def locW (l : Links.Loc) : List Int := [natW l.page] ++ ratW l.x ++ ratW l.y

/-- `n` locations from integer `i` on. -/
def getLocs (b : ByteArray) (i n : Nat) : List Links.Loc :=
  (List.range n).map fun k => getLoc b (i + 5 * k)

/-- A history on the wire: the back stack's length and locations, then the forward stack's. -/
def historyW (h : Links.History) : List Int :=
  [(h.back.length : Int)] ++ h.back.flatMap locW ++ [(h.fwd.length : Int)] ++ h.fwd.flatMap locW

/-- **Back/forward history** (`Links.History`, theorem `History.back_push`). In: operation (0
`push` — a jump from `cur`; 1 `goBack`; 2 `goForward`), `cur` (5), the back stack (length,
then 5 integers per location, nearest first), the forward stack (the same). Lengths are capped
by the input's size. Out: found flag (always 1 for `push`), the location to show (`cur` for
`push` and when nothing was found), the new history (`historyW`; unchanged when nothing was
found). -/
@[export safepdf_lean_view_history]
def history (a : ByteArray) : ByteArray :=
  let cap := a.size / 40
  let cur := getLoc a 1
  let nb := min (getNat a 6) cap
  let nf := min (getNat a (7 + 5 * nb)) cap
  let h : Links.History := ⟨getLocs a 7 nb, getLocs a (8 + 5 * nb) nf⟩
  let res : Option (Links.Loc × Links.History) := match getNat a 0 with
    | 0 => some (cur, h.push cur)
    | 1 => h.goBack cur
    | _ => h.goForward cur
  match res with
  | some (l, h') => enc ([1] ++ locW l ++ historyW h')
  | none => enc ([0] ++ locW cur ++ historyW h)

-- Push page 0, then go back from page 5: back to page 0, page 5 on the forward stack.
#guard
  let pushed := history (enc [0, 0, 0, 1, 0, 1, 0, 0])
  let back := history (enc ([1, 5, 0, 1, 1, 2] ++ (List.range 7).map (getI64 pushed ∘ (· + 6))))
  getI64 pushed 0 == 1 && getI64 pushed 5 == 1 && getI64 back 0 == 1 && getI64 back 1 == 0 &&
  getI64 back 6 == 0 && getI64 back 7 == 1 && getI64 back 8 == 5
-- Nothing to go forward to.
#guard getI64 (history (enc [2, 3, 0, 1, 0, 1, 0, 0])) 0 == 0

/-- `Geom.toScreen` (C2): where page point `p` (page units) is shown, in pixels from the page
image's top-left, at zoom `z` and rotation `r` of box `bx` — how the Tk viewer scrolls to a
destination (`Viewer.applyScroll`, `.dest`). In: `z` (2), rotation degrees, box (8), point (4).
Out: point (4). -/
@[export safepdf_lean_view_to_screen]
def toScreenW (a : ByteArray) : ByteArray :=
  let q := toScreen (getRat a 0) (rotOf (getNat a 2)) (getBox a 3) ⟨getRat a 11, getRat a 13⟩
  enc (ratW q.x ++ ratW q.y)

#guard toScreenW (enc [1, 1, 0, 0, 1, 0, 1, 612, 1, 792, 1, 0, 1, 792, 1]) == enc [0, 1, 0, 1]
#guard toScreenW (enc [3, 2, 0, 0, 1, 0, 1, 612, 1, 792, 1, 100, 1, 692, 1]) == enc [150, 1, 150, 1]

end SafePdf.Shell.FfiView
