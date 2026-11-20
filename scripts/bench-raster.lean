import SafePdf.Core.Raster.Clip

/-!
# Raster benchmark (task 7.2d; Plan.md §6 Phase 7 exit criterion M7: median page < 100 ms)

Renders four synthetic scenes on a US-letter page (612 × 792 pt) at zoom 1 (612 × 792 pixels)
with `Clip.renderItems` (fill, stroke, clip, compositing; default `Limits` caps) and prints
the best wall time of `--reps` runs (default 5) per scene (after a baseline: the empty page,
i.e. allocating the white RGBA buffer and summing it):

* `full-fill`: one rectangle covering the whole page;
* `circles-1000`: 1000 separately filled circles of radius 4 pt (glyph-size, 4 cubics each);
* `grid-119`: one stroked path of 119 lines (60 horizontal, 59 vertical), width 0.5 pt;
* `clipped-rects-1000`: 1000 filled 10 × 10 pt rectangles under one circular clip.

Then hotspot splits (no compositing): the full-page fill's coverage mask, the grid's stroke
edges and stroke mask (`Stroke.strokeEdges` / `Stroke.strokePath`), and the 1000 circle fill
masks (task 7.2e: after the compositor rewrite, these dominate the scene times).

Run it compiled, not interpreted (the interpreter is far slower):

    scripts/bench-raster.sh [--reps N]

`bench-raster.sh` builds the library, compiles this file with `lean -c` and links it with
`leanc -O3`, like `bench-flate.sh`; no lakefile target is needed.
-/

open SafePdf SafePdf.Core SafePdf.Core.Raster.Geom SafePdf.Core.Raster.Fill
  SafePdf.Core.Raster.Clip
open SafePdf.Core.Content (FillRule Clip Color Comp DisplayItem DisplayList Path Segment)

/-- A page-space point in thousandths of a point. -/
def ptm (x y : Int) : Content.Point := ⟨Content.Fixed.clamp (x * 1000), Content.Fixed.clamp (y * 1000)⟩

/-- A page-space point in whole points. -/
def pt (x y : Int) : Content.Point := ptm (x * 1000) (y * 1000)

/-- Rectangle `[x0, x1] × [y0, y1]` (points). -/
def rectP (x0 y0 x1 y1 : Int) : Path :=
  ⟨#[.moveTo (pt x0 y0), .lineTo (pt x1 y0), .lineTo (pt x1 y1), .lineTo (pt x0 y1), .closePath]⟩

/-- Circle of centre `(cx, cy)` and radius `r` (thousandths of a point), 4 cubics. -/
def circleM (cx cy r : Int) : Path :=
  let k : Int := r * 5523 / 10000
  ⟨#[.moveTo (ptm (cx + r) cy),
    .curveTo (ptm (cx + r) (cy + k)) (ptm (cx + k) (cy + r)) (ptm cx (cy + r)),
    .curveTo (ptm (cx - k) (cy + r)) (ptm (cx - r) (cy + k)) (ptm (cx - r) cy),
    .curveTo (ptm (cx - r) (cy - k)) (ptm (cx - k) (cy - r)) (ptm cx (cy - r)),
    .curveTo (ptm (cx + k) (cy - r)) (ptm (cx + r) (cy - k)) (ptm (cx + r) cy),
    .closePath]⟩

/-- Opaque black. -/
def black : Content.FillStyle := ⟨.gray Comp.zero, Comp.one⟩

/-- Scene 1: the whole page. -/
def fullFill : DisplayList := #[.fillPath (rectP 0 0 612 792) .nonzero black []]

/-- Scene 2: 1000 glyph-size discs on a 40 × 25 grid. -/
def circles : DisplayList := Id.run do
  let mut out := #[]
  for i in [0:1000] do
    let cx : Int := 20000 + ((i % 40 : Nat) : Int) * 14500 + 1300
    let cy : Int := 30000 + ((i / 40 : Nat) : Int) * 29000 + 700
    out := out.push (.fillPath (circleM cx cy 4000) .nonzero black [])
  return out

/-- Scene 3: a grid of 119 lines in one stroked path. -/
def grid : DisplayList := Id.run do
  let mut segs : Array Segment := #[]
  for i in [0:60] do
    let y : Int := 36 + (i : Int) * 12
    segs := (segs.push (.moveTo (pt 36 y))).push (.lineTo (pt 576 y))
  for i in [0:59] do
    let x : Int := 36 + (i : Int) * 9
    segs := (segs.push (.moveTo (pt x 36))).push (.lineTo (pt x 744))
  let style : Content.StrokeStyle :=
    { color := .gray Comp.zero, alpha := Comp.one,
      line := { width := Content.Fixed.clamp 500000 }, ctm := Content.Matrix.identity }
  return #[.strokePath ⟨segs⟩ style []]

/-- Scene 4: 1000 small rectangles under one circular clip. -/
def clippedRects : DisplayList := Id.run do
  let clip : Clip := [⟨circleM 306000 396000 250000, .nonzero⟩]
  let mut out := #[]
  for i in [0:1000] do
    let x : Int := 20 + ((i % 40 : Nat) : Int) * 14
    let y : Int := 20 + ((i / 40 : Nat) : Int) * 30
    out := out.push (.fillPath (rectP x y (x + 10) (y + 10)) .nonzero black clip)
  return out

/-- Page → device for a 612 × 792 page at zoom 1. -/
def view : Aff := viewMatrix 1 .r0 ⟨0, 0, 612, 792⟩

/-- Render once between two clock readings; returns a checksum (so the work is kept) and ns. -/
@[noinline] def timeOnce (items : DisplayList) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let img := renderItems {} view 612 792 items
  let sum := img.data.foldl (fun s b => s + b.toNat) 0
  let t1 ← IO.monoNanosNow
  pure (sum, t1 - t0)

/-- Hotspot split for `full-fill`: the coverage mask alone (`fillCounted`, no compositing). -/
@[noinline] def timeMask (p : Path) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let m := (fillCounted {} view p .nonzero ⟨0, 0, 612, 792⟩).1
  let sum := m.total
  let t1 ← IO.monoNanosNow
  pure (sum, t1 - t0)

/-- The grid scene's stroke: its path and style. -/
def gridStroke : Path × Content.StrokeStyle :=
  match (grid[0]? : Option DisplayItem) with
  | some (.strokePath p s _) => (p, s)
  | _ => ({}, ⟨.gray Comp.zero, Comp.one, {}, Content.Matrix.identity⟩)

/-- Hotspot split for `grid-119`: the stroke's edges alone (`Stroke.strokeEdges`). -/
@[noinline] def timeStrokeEdges (u : Unit) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let es := Raster.Stroke.strokeEdges view gridStroke.1 gridStroke.2 {}
  let n := es.size + (if u == () then 0 else 1)
  let t1 ← IO.monoNanosNow
  pure (n, t1 - t0)

/-- Hotspot split for `grid-119`: the stroke's coverage mask (`Stroke.strokePath` = edges +
scanline fill, no compositing). -/
@[noinline] def timeStrokeMask (u : Unit) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let m := Raster.Stroke.strokePath view gridStroke.1 gridStroke.2 ⟨0, 0, 612, 792⟩ {}
  let n := m.total + (if u == () then 0 else 1)
  let t1 ← IO.monoNanosNow
  pure (n, t1 - t0)

/-- Hotspot split for `circles-1000`: the 1000 fill masks alone (`fillCounted` over the page,
no compositing; returns the summed coverage). -/
@[noinline] def timeCircleMasks (items : DisplayList) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let n := items.foldl (fun acc it => match it with
    | .fillPath p rule _ _ => acc + (fillCounted {} view p rule ⟨0, 0, 612, 792⟩).1.total
    | _ => acc) 0
  let t1 ← IO.monoNanosNow
  pure (n, t1 - t0)

/-- Best time of `reps` runs of `act`. -/
def bestOf (reps : Nat) (act : Unit → IO (Nat × Nat)) : IO Nat := do
  let mut best := 0
  for i in [0:reps] do
    let r ← act ()
    if i == 0 || r.2 < best then best := r.2
  pure best

/-- Best of `reps` runs. -/
def bench (reps : Nat) (items : DisplayList) : IO (Nat × Nat) := do
  let mut best : Nat × Nat := (0, 0)
  for i in [0:reps] do
    let r ← timeOnce items
    if i == 0 || r.2 < best.2 then best := r
  pure best

/-- Entry point: `[--reps N]`. -/
def main (args : List String) : IO UInt32 := do
  let reps := match args with
    | "--reps" :: n :: _ => n.toNat?.getD 5
    | _ => 5
  let scenes : List (String × DisplayList) :=
    [("empty (white page + checksum)", #[]), ("full-fill", fullFill), ("circles-1000", circles), ("grid-119", grid),
      ("clipped-rects-1000", clippedRects)]
  for (name, items) in scenes do
    let (sum, ns) ← bench reps items
    let ms := ns.toFloat / 1.0e6
    IO.println s!"{name}: {ms} ms (best of {reps}; {items.size} items; checksum {sum})"
  let mut best := 0
  for i in [0:reps] do
    let r ← timeMask (rectP 0 0 612 792)
    if i == 0 || r.2 < best then best := r.2
  IO.println s!"full-fill, coverage mask only: {best.toFloat / 1.0e6} ms (best of {reps})"
  let e ← bestOf reps timeStrokeEdges
  IO.println s!"grid-119, stroke edges only: {e.toFloat / 1.0e6} ms (best of {reps})"
  let sm ← bestOf reps timeStrokeMask
  IO.println s!"grid-119, stroke mask only (edges + scanline): {sm.toFloat / 1.0e6} ms (best of {reps})"
  let cm ← bestOf reps (fun _ => timeCircleMasks circles)
  IO.println s!"circles-1000, fill masks only: {cm.toFloat / 1.0e6} ms (best of {reps})"
  pure 0
