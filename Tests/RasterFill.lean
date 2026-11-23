import SafePdf.Core.Raster.Fill

/-!
# Fill core suite (task 7.2a)

Plan.md §6 Phase 7 (scanline fill, nonzero + even-odd, Bézier flattening, anti-aliasing) and
§4 S3. The flattening bound and the work bound are theorems in `SafePdf.Core.Raster.Fill`;
this suite checks the rasterizer's behaviour by evaluation:

* a circle of radius 50 made of 4 cubics covers `π·r²` within 0.5%;
* a self-overlapping pentagram: even-odd leaves the centre empty, nonzero fills it;
* on deterministic pseudo-random polygons (fixed seed): the buffer has `w·h` bytes, the mask
  lies inside the window, per pixel even-odd coverage ≤ nonzero coverage, and the two rules
  agree exactly on triangles (simple polygons);
* a subpixel-offset rectangle has the exact fractional area (within rounding);
* a page-space `Content.Path` through `Geom.viewMatrix` lands where expected (y flipped).

Set `SAFEPDF_PGM_DIR=<dir>` to also write the circle and star masks as PGM files there (for
eyeballing; never committed).
-/

namespace SafePdf.Tests.RasterFill

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill

/-- One step of a 31-bit linear congruential generator. -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- A point in subpixel units from pixel coordinates given as rationals (rounded). -/
def fp (x y : Rat) : FPt := ⟨toSub x, toSub y⟩

/-- A closed polygon as a device path. -/
def polyPath (pts : List FPt) : DPath :=
  match pts with
  | [] => #[]
  | p :: rest => (#[DSeg.moveTo p] ++ (rest.map DSeg.lineTo).toArray).push .closePath

/-- A circle of radius `r` around `(cx, cy)` from 4 cubics (κ = 0.5523). -/
def circle (cx cy r : Rat) : DPath :=
  let k := r * 5523 / 10000
  #[.moveTo (fp (cx + r) cy),
    .curveTo (fp (cx + r) (cy + k)) (fp (cx + k) (cy + r)) (fp cx (cy + r)),
    .curveTo (fp (cx - k) (cy + r)) (fp (cx - r) (cy + k)) (fp (cx - r) cy),
    .curveTo (fp (cx - r) (cy - k)) (fp (cx - k) (cy - r)) (fp cx (cy - r)),
    .curveTo (fp (cx + k) (cy - r)) (fp (cx + r) (cy - k)) (fp (cx + r) cy),
    .closePath]

/-- A pentagram (self-overlapping star) centred at `(50, 50)`. -/
def star : DPath :=
  polyPath [fp 50 5, fp 77 90, fp 7 36, fp 93 36, fp 23 90]

/-- Write a mask as a binary PGM. -/
def writePgm (path : System.FilePath) (m : Mask) : IO Unit := do
  let header := s!"P5\n{m.w} {m.h}\n255\n".toUTF8
  IO.FS.writeBinFile path (header ++ m.data)

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL raster-fill: {msg}"
  let window : IRect := ⟨0, 0, 120, 120⟩
  -- Circle area.
  let c := fillDPath (circle 60 60 50) .nonzero window
  let area : Float := c.total.toFloat / 255.0
  let exact : Float := 3.14159265358979 * 2500.0
  if (area - exact).abs > exact * 0.005 then
    failures := failures + 1; report s!"circle area {area} vs {exact}"
  -- Star: even-odd hole in the middle, nonzero filled.
  let sn := fillDPath star .nonzero window
  let se := fillDPath star .evenOdd window
  if sn.get 50 50 != 255 || se.get 50 50 != 0 then
    failures := failures + 1
    report s!"star centre: nonzero {sn.get 50 50}, even-odd {se.get 50 50}"
  if !(se.total < sn.total) then
    failures := failures + 1; report "star: even-odd total not below nonzero total"
  -- Subpixel rectangle [3.5, 8.25) × [5, 9): area 19 px².
  let r := fillDPath (polyPath [fp (7/2) 5, fp (33/4) 5, fp (33/4) 9, fp (7/2) 9]) .nonzero window
  if !(r.total * 100 ≥ 19 * 255 * 99 && r.total * 100 ≤ 19 * 255 * 101) then
    failures := failures + 1; report s!"subpixel rectangle total {r.total}"
  -- Random polygons.
  let mut s := 4242
  for i in [0:200] do
    let nv := 3 + s % 6
    let mut pts : List FPt := []
    for _ in [0:nv] do
      let s1 := lcg s
      let s2 := lcg s1
      s := s2
      -- coordinates in [-20, 140) px, subpixel resolution
      pts := ⟨(s1 % (160 * 256) : Nat) - 20 * 256, (s2 % (160 * 256) : Nat) - 20 * 256⟩ :: pts
    let p := polyPath pts
    let mn := fillDPath p .nonzero window
    let me := fillDPath p .evenOdd window
    if mn.data.size != mn.w * mn.h || me.data.size != me.w * me.h then
      failures := failures + 1; report s!"poly {i}: buffer size"
    if mn.x0 < 0 || mn.y0 < 0 || mn.x0 + mn.w > 120 || mn.y0 + mn.h > 120 then
      failures := failures + 1; report s!"poly {i}: mask outside window"
    let mut bad := false
    for y in [0:120] do
      for x in [0:120] do
        if me.get x y > mn.get x y then bad := true
    if bad then
      failures := failures + 1; report s!"poly {i}: even-odd coverage above nonzero"
    if nv == 3 && mn.data != me.data then
      failures := failures + 1; report s!"poly {i}: rules disagree on a triangle"
  -- Page-space path through the view transform: the rectangle [10, 30] × [20, 25] (page
  -- units) on the box [0 0 100 100] at zoom 1 is rows 75 … 80, columns 10 … 30 on screen.
  let pt := fun (x y : Int) => (⟨Content.Fixed.ofInt x, Content.Fixed.ofInt y⟩ : Content.Point)
  let path : Content.Path := ⟨#[.moveTo (pt 10 20), .lineTo (pt 30 20), .lineTo (pt 30 25),
    .lineTo (pt 10 25), .closePath]⟩
  let m := fillPath (viewMatrix 1 .r0 ⟨0, 0, 100, 100⟩) path .nonzero ⟨0, 0, 100, 100⟩
  if m.x0 != 10 || m.y0 != 75 || m.w != 20 || m.h != 5 || m.total != 100 * 255 then
    failures := failures + 1
    report s!"page path: mask {m.x0},{m.y0} {m.w}×{m.h} total {m.total}"
  -- Optional PGM dump.
  if let some dir ← IO.getEnv "SAFEPDF_PGM_DIR" then
    IO.FS.createDirAll dir
    writePgm (System.FilePath.mk dir / "circle.pgm") c
    writePgm (System.FilePath.mk dir / "star-nonzero.pgm") sn
    writePgm (System.FilePath.mk dir / "star-evenodd.pgm") se
  return failures

end SafePdf.Tests.RasterFill
