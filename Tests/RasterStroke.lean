import SafePdf.Core.Raster.Stroke

/-!
# Stroking suite (task 7.2b)

Plan.md §6 Phase 7 (stroking: width, caps, joins, miter limit, dashes) and §4 S3. The square
root bound and the edge-count bound are theorems in `SafePdf.Core.Raster.Stroke`; this suite
checks the stroker's behaviour by evaluation:

* a circle (4 cubics) stroked with width 4 and 40 covers the annulus area within 0.5%;
* round caps add a disc (`π·r²` within 3%); round joins lie between bevel and miter;
* dashes: coverage ratio `on/(on + off)`, phase shifts the pattern, odd arrays repeat with
  swapped roles, zero-length dashes with square caps are `w × w` squares, all-zero and
  negative arrays are solid;
* closed subpaths join at the start (square outline area exact), open ones get caps;
* CTMs: rotation by 45° with scale √2 (pen radius scales), reflection (det < 0) gives the same
  joins, a non-uniform scale gives an elliptic pen, a degenerate CTM gives a hairline;
* a page-space `DisplayList` stroke (`strokePath`, CTM + `Geom.viewMatrix`) lands where
  expected;
* pseudo-random polylines (fixed seed): mask buffer shape, mask inside the window, and the
  edge count within `strokeEdges_size_le`'s bound.

Set `SAFEPDF_PGM_DIR=<dir>` to also write a few stroke masks as PGM files there (for
eyeballing; never committed).
-/

namespace SafePdf.Tests.RasterStroke

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill
open SafePdf.Core.Raster.Stroke
open SafePdf.Core.Content (LineCap LineJoin LineStyle)

/-- One step of a 31-bit linear congruential generator. -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- A device point from pixel coordinates (rounded to subpixel units). -/
def fp (x y : Rat) : FPt := ⟨toSub x, toSub y⟩

/-- An open (or closed) polyline through pixel points. -/
def poly (pts : List (Rat × Rat)) (closed : Bool := false) : DPath :=
  match pts with
  | [] => #[]
  | (x, y) :: rest =>
    let a := #[DSeg.moveTo (fp x y)] ++ (rest.map fun (a, b) => DSeg.lineTo (fp a b)).toArray
    if closed then a.push .closePath else a

/-- A circle of radius `r` around `(cx, cy)` from 4 cubics (κ = 0.5523). -/
def circle (cx cy r : Rat) : DPath :=
  let k := r * 5523 / 10000
  #[.moveTo (fp (cx + r) cy),
    .curveTo (fp (cx + r) (cy + k)) (fp (cx + k) (cy + r)) (fp cx (cy + r)),
    .curveTo (fp (cx - k) (cy + r)) (fp (cx - r) (cy + k)) (fp (cx - r) cy),
    .curveTo (fp (cx - r) (cy - k)) (fp (cx - k) (cy - r)) (fp cx (cy - r)),
    .curveTo (fp (cx + k) (cy - r)) (fp (cx + r) (cy - k)) (fp (cx + r) cy),
    .closePath]

/-- A line style (width comes from the geometry). -/
def style (cap : LineCap := .butt) (jn : LineJoin := .miter) (ml : Int := 10)
    (dash : List Int := []) (phase : Int := 0) : LineStyle :=
  { cap, join := jn, miterLimit := Content.Fixed.ofInt ml,
    dash := { array := dash.map Content.Fixed.ofInt, phase := Content.Fixed.ofInt phase } }

/-- The geometry for user → device-pixel linear map `m` (pixels) and width `w`. -/
def geo (m : Aff) (w : Rat) : Geo :=
  Geo.make (m * Aff.scale subUnit subUnit) w 26

/-- The 200 × 200 test window. -/
def window : IRect := ⟨0, 0, 200, 200⟩

/-- The stroke mask. -/
def mask (g : Geo) (l : LineStyle) (p : DPath) : Mask :=
  fillEdges (strokeDPath {} g l p) .nonzero window

/-- Covered area in px². -/
def area (g : Geo) (l : LineStyle) (p : DPath) : Float := (mask g l p).total.toFloat / 255.0

/-- Write a mask as a binary PGM. -/
def writePgm (path : System.FilePath) (m : Mask) : IO Unit := do
  let header := s!"P5\n{m.w} {m.h}\n255\n".toUTF8
  IO.FS.writeBinFile path (header ++ m.data)

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL raster-stroke: {msg}"
  let near := fun (a b rel : Float) => (a - b).abs ≤ b * rel
  let id1 := Aff.id
  -- Circle stroked with width 4 (annulus 28 … 32) and width 40 (annulus 5 … 45).
  let c4 := area (geo id1 4) (style) (circle 100 100 30)
  if !near c4 (3.14159265 * (32 * 32 - 28 * 28)) 0.005 then
    failures := failures + 1; report s!"circle width 4: area {c4}"
  let c40 := area (geo id1 40) (style) (circle 100 100 25)
  if !near c40 (3.14159265 * (45 * 45 - 5 * 5)) 0.005 then
    failures := failures + 1; report s!"circle width 40: area {c40}"
  -- Round caps add one disc of radius w/2 (w = 10): 20·10 + π·25.
  let rc := area (geo id1 10) (style .round) (poly [(50, 50), (70, 50)])
  if !near rc (200 + 3.14159265 * 25) 0.01 then
    failures := failures + 1; report s!"round caps: area {rc}"
  -- Joins at a right angle, width 10: bevel < round < miter, miter = union + 25.
  let pth := poly [(50, 50), (100, 50), (100, 100)]
  let jm := area (geo id1 10) (style) pth
  let jr := area (geo id1 10) (style (jn := .round)) pth
  let jb := area (geo id1 10) (style (jn := .bevel)) pth
  if !(near jm (2 * 500 - 25 + 25) 0.001 && near jb (975 + 12.5) 0.002 &&
      near jr (975 + 3.14159265 * 25 / 4) 0.005) then
    failures := failures + 1; report s!"joins: miter {jm} round {jr} bevel {jb}"
  -- Dashes: [6 2] on a 160-long line of width 2 → 3/4 of 320.
  let d := area (geo id1 2) (style (dash := [6, 2])) (poly [(20, 20), (180, 20)])
  if !near d 240 0.001 then failures := failures + 1; report s!"dash ratio: {d}"
  -- Phase 6 starts in the gap: [6 2] phase 6 on a 16-long line = gap 2, dash 6, gap 2, dash 6.
  let dp := area (geo id1 2) (style (dash := [6, 2]) (phase := 6)) (poly [(20, 20), (36, 20)])
  if !near dp 24 0.001 then failures := failures + 1; report s!"dash phase: {dp}"
  -- Negative phase is reduced modulo the period: phase −2 ≡ 6.
  let dn := area (geo id1 2) (style (dash := [6, 2]) (phase := -2)) (poly [(20, 20), (36, 20)])
  if !near dn 24 0.001 then failures := failures + 1; report s!"negative phase: {dn}"
  -- Odd array [4] ≡ [4 4]: half of the line.
  let dodd := area (geo id1 2) (style (dash := [4])) (poly [(20, 20), (100, 20)])
  if !near dodd 80 0.001 then failures := failures + 1; report s!"odd dash array: {dodd}"
  -- Zero-length dashes with square caps (w = 2): 2 × 2 squares every 8 px (0, 8, …, 80).
  let dz := area (geo id1 2) (style .square (dash := [0, 8])) (poly [(20, 20), (100, 20)])
  if !near dz (11 * 4) 0.001 then failures := failures + 1; report s!"zero dashes: {dz}"
  -- All-zero and negative arrays are solid.
  let solid := area (geo id1 2) (style) (poly [(20, 20), (100, 20)])
  let dzero := area (geo id1 2) (style (dash := [0, 0])) (poly [(20, 20), (100, 20)])
  let dneg := area (geo id1 2) (style (dash := [3, -1])) (poly [(20, 20), (100, 20)])
  if dzero != solid || dneg != solid then
    failures := failures + 1; report s!"degenerate dashes: {dzero} {dneg} vs {solid}"
  -- Dashes through a corner keep the join: a dash longer than the path equals solid.
  let dl := area (geo id1 4) (style (dash := [500, 1])) pth
  let sl := area (geo id1 4) (style) pth
  if dl != sl then failures := failures + 1; report s!"long dash through corner: {dl} vs {sl}"
  -- Closed square outline 40 × 40, width 4: (44² − 36²) = 640 with miter joins (incl. start).
  let sq := area (geo id1 4) (style) (poly [(50, 50), (90, 50), (90, 90), (50, 90)] true)
  if !near sq 640 0.001 then failures := failures + 1; report s!"closed square: {sq}"
  -- Rotation by 45° with scale √2: a pen of radius 2 is 2√2 px; a 45°-rotated device view of
  -- a vertical line compares with the axis-aligned case through the exact widths.
  let rot : Aff := ⟨1, 1, -1, 1, 0, 0⟩
  let r45 := mask (geo rot 4) (style) (poly [(100, 20), (100, 180)])
  let wexp : Float := 4 * 1.41421356
  let wgot := r45.total.toFloat / 255.0 / 160.0
  if !near wgot wexp 0.01 then failures := failures + 1; report s!"rotated pen width {wgot}"
  -- Reflection (det < 0): the same joins as without it (outer side computed in pen space).
  let refl := area (geo (Aff.scale 1 (-1)) 10) (style (jn := .bevel)) pth
  if refl != jb then failures := failures + 1; report s!"reflected bevel {refl} vs {jb}"
  -- Non-uniform scale (x by 3, y by 1/2): vertical line of user width 2 is 6 px wide.
  let ne := area (geo (Aff.scale 3 (1/2)) 2) (style) (poly [(100, 20), (100, 120)])
  if !near ne 600 0.001 then failures := failures + 1; report s!"elliptic pen: {ne}"
  -- Degenerate CTM: a solid hairline even with dashes.
  let hz := area (geo (Aff.scale 1 0) 5) (style (dash := [1, 1])) (poly [(20, 20), (100, 20)])
  if !(hz ≥ 78 && hz ≤ 82) then failures := failures + 1; report s!"degenerate CTM hairline {hz}"
  -- Zero width with dashes: the hairline is dashed in user space.
  let hd := area (geo id1 0) (style (dash := [4, 4])) (poly [(20, 20), (100, 20)])
  if !(hd ≥ 38 && hd ≤ 44) then failures := failures + 1; report s!"dashed hairline {hd}"
  -- Page-space stroke through CTM and view: a horizontal page line y = 20 from x = 10 to 30,
  -- CTM scale 2 (user width 1 → 2 page units), box [0 0 100 100] at zoom 1: rows 79 … 81.
  let pt := fun (x y : Int) => (⟨Content.Fixed.ofInt x, Content.Fixed.ofInt y⟩ : Content.Point)
  let path : Content.Path := ⟨#[.moveTo (pt 10 20), .lineTo (pt 30 20)]⟩
  let ss : Content.StrokeStyle := { ({} : Content.GState).strokeStyle with
    ctm := ⟨Content.Fixed.ofInt 2, Content.Fixed.zero, Content.Fixed.zero, Content.Fixed.ofInt 2,
      Content.Fixed.zero, Content.Fixed.zero⟩ }
  let m := strokePath (viewMatrix 1 .r0 ⟨0, 0, 100, 100⟩) path ss ⟨0, 0, 100, 100⟩
  if m.x0 != 10 || m.y0 != 79 || m.w != 20 || m.h != 2 || m.total != 40 * 255 then
    failures := failures + 1
    report s!"page stroke: mask {m.x0},{m.y0} {m.w}×{m.h} total {m.total}"
  -- Random polylines: shape, window and the S3 edge bound.
  let mut s := 777
  for i in [0:100] do
    let nv := 2 + s % 5
    let mut pts : List (Rat × Rat) := []
    for _ in [0:nv] do
      let s1 := lcg s
      let s2 := lcg s1
      s := s2
      pts := (((s1 % 2400 : Nat) : Rat) / 10 - 20, ((s2 % 2400 : Nat) : Rat) / 10 - 20) :: pts
    let cap : LineCap := match s % 3 with | 0 => .butt | 1 => .round | _ => .square
    let jn : LineJoin := match (s / 3) % 3 with | 0 => .miter | 1 => .round | _ => .bevel
    let dash := if s % 2 = 0 then [5, 3] else []
    let p := poly pts (s % 5 == 0)
    let w : Rat := ((s % 13 : Nat) : Rat) / 2
    let es := strokeDPath {} (geo id1 w) (style cap jn 10 dash) p
    let mk := fillEdges es .nonzero window
    if mk.data.size != mk.w * mk.h then
      failures := failures + 1; report s!"random {i}: buffer size"
    if mk.x0 < 0 || mk.y0 < 0 || mk.x0 + mk.w > 200 || mk.y0 + mk.h > 200 then
      failures := failures + 1; report s!"random {i}: mask outside window"
    if es.size > 3 * polyCap * (curveSegCap * p.size + maxDashSteps + p.size + 1) then
      failures := failures + 1; report s!"random {i}: {es.size} edges above the bound"
  -- Optional PGM dump.
  if let some dir ← IO.getEnv "SAFEPDF_PGM_DIR" then
    IO.FS.createDirAll dir
    writePgm (System.FilePath.mk dir / "stroke-circle40.pgm")
      (mask (geo id1 40) (style) (circle 100 100 25))
    writePgm (System.FilePath.mk dir / "stroke-joins-round.pgm")
      (mask (geo id1 10) (style .round .round) pth)
    writePgm (System.FilePath.mk dir / "stroke-dashed-ellipse.pgm")
      (mask (geo (Aff.scale 3 1) 4) (style .round .round 10 [6, 4]) (circle 100 100 40))
  return failures

end SafePdf.Tests.RasterStroke
