import SafePdf.Core.Raster.Clip
import SafePdf.Core.Content.Interp

/-!
# Clipping and path rendering suite (task 7.2c)

Plan.md §6 Phase 7 (clipping, anti-aliasing, compositing of path items), ISO 32000-2 §8.5.4.
The coverage bounds, buffer shape and work bound are theorems in
`SafePdf.Core.Raster.Clip`; this suite checks behaviour by evaluation:

* a rectangle clipped by a smaller rectangle paints exactly the smaller one;
* an even-odd clip with a hole leaves the hole unpainted (nonzero fills it);
* nested clips paint only the intersection;
* colours: gray 0.5 → 128 ± 1, RGB, naive CMYK, constant alpha 0.5 → half-way to white;
* the clip cache is hit by items sharing a clip list (and by a nested clip's parent);
* `Mask.inter` coverage ≤ both operands on overlapping circles (anti-aliased edges);
* a content stream run through the interpreter (`Content.interpBytes`) renders to the expected
  small image (y flip of the view transform; hairline placeholder stroke);
* `renderPaths` on a page with `/Rotate 90` swaps width and height;
* timing of 1000 filled rectangles under one shared clip on a 612 × 792 page (printed).

Set `SAFEPDF_PPM_DIR=<dir>` to also write the rendered test pages as PPM files there.
-/

namespace SafePdf.Tests.RasterClip

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill
open SafePdf.Core.Raster.Clip
open SafePdf.Core.Content (FillRule Clip ClipPath Color Comp DisplayItem DisplayList Path)

/-- A page-space point from integers. -/
def pt (x y : Int) : Content.Point := ⟨Content.Fixed.ofInt x, Content.Fixed.ofInt y⟩

/-- A closed polygon (one subpath). -/
def polySegs (pts : List (Int × Int)) : Array Content.Segment :=
  match pts with
  | [] => #[]
  | (x, y) :: rest =>
    (#[Content.Segment.moveTo (pt x y)] ++
      (rest.map fun (a, b) => Content.Segment.lineTo (pt a b)).toArray).push .closePath

/-- Rectangle `[x0, x1] × [y0, y1]`. -/
def rectP (x0 y0 x1 y1 : Int) : Path := ⟨polySegs [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]⟩

/-- A component `n / 100`. -/
def comp (n : Nat) : Comp :=
  Comp.ofFixed (Content.Fixed.div (Content.Fixed.ofInt n) (Content.Fixed.ofInt 100))

/-- Opaque fill item. -/
def fillI (p : Path) (c : Color) (clip : Clip := []) (rule : FillRule := .nonzero) :
    DisplayItem :=
  .fillPath p rule { color := c, alpha := Comp.one } clip

/-- Black. -/
def black : Color := .gray Comp.zero

/-- RGB of pixel `(x, y)`. -/
def px (img : Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (getB img.data i, getB img.data (i + 1), getB img.data (i + 2))

/-- Number of pixels that are not pure white. -/
def inked (img : Image) : Nat := Id.run do
  let mut n := 0
  for y in [0:img.h] do
    for x in [0:img.w] do
      if px img x y != (255, 255, 255) then n := n + 1
  return n

/-- Write an RGBA image as a binary PPM (alpha dropped). -/
def writePpm (path : System.FilePath) (img : Image) : IO Unit := do
  let mut rgb := ByteArray.empty
  for i in [0:img.w * img.h] do
    rgb := rgb.push (UInt8.ofNat (getB img.data (4 * i)))
    rgb := rgb.push (UInt8.ofNat (getB img.data (4 * i + 1)))
    rgb := rgb.push (UInt8.ofNat (getB img.data (4 * i + 2)))
  IO.FS.writeBinFile path (s!"P6\n{img.w} {img.h}\n255\n".toUTF8 ++ rgb)

/-- A circle of radius `r` around `(cx, cy)` from 4 cubics. -/
def circleP (cx cy r : Int) : Path :=
  let k : Int := r * 5523 / 10000
  ⟨#[.moveTo (pt (cx + r) cy),
    .curveTo (pt (cx + r) (cy + k)) (pt (cx + k) (cy + r)) (pt cx (cy + r)),
    .curveTo (pt (cx - k) (cy + r)) (pt (cx - r) (cy + k)) (pt (cx - r) cy),
    .curveTo (pt (cx - r) (cy - k)) (pt (cx - k) (cy - r)) (pt cx (cy - r)),
    .curveTo (pt (cx + k) (cy - r)) (pt (cx + r) (cy - k)) (pt (cx + r) cy),
    .closePath]⟩

/-- A page with box `[0 0 w h]` and the given rotation. -/
def mkPage (w h : Nat) (rot : Doc.Rotation) : Doc.Page :=
  let r := Doc.Rect.ofCorners ⟨0, 0⟩ ⟨0, 0⟩ ⟨w, 0⟩ ⟨h, 0⟩
  { num := 1, gen := 0, mediaBox := r, mediaBoxDefaulted := false, cropBox := r, rotate := rot,
    resources := none, contents := none, cropBox_sub := Doc.Rect.sub_refl r }

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL raster-clip: {msg}"
  let idm := Aff.id
  let mut dumps : Array (String × Image) := #[]
  -- 1. Rectangle [2,18]² clipped by [5,10]²: exactly 25 black pixels.
  let i1 := renderItems {} idm 20 20 #[fillI (rectP 2 2 18 18) black [⟨rectP 5 5 10 10, .nonzero⟩]]
  dumps := dumps.push ("clip-rect", i1)
  if inked i1 != 25 || px i1 5 5 != (0, 0, 0) || px i1 9 9 != (0, 0, 0) then
    failures := failures + 1; report s!"clipped rectangle: {inked i1} inked"
  -- 2. Even-odd clip with a hole: outer [2,18]², inner [7,13]² in one path.
  let ring : Path := ⟨polySegs [(2, 2), (18, 2), (18, 18), (2, 18)] ++
    polySegs [(7, 7), (13, 7), (13, 13), (7, 13)]⟩
  let i2e := renderItems {} idm 20 20 #[fillI (rectP 0 0 20 20) black [⟨ring, .evenOdd⟩]]
  let i2n := renderItems {} idm 20 20 #[fillI (rectP 0 0 20 20) black [⟨ring, .nonzero⟩]]
  dumps := dumps.push ("clip-evenodd", i2e)
  if px i2e 10 10 != (255, 255, 255) || px i2e 4 4 != (0, 0, 0) || inked i2e != 256 - 36 then
    failures := failures + 1; report s!"even-odd hole: centre {px i2e 10 10}, inked {inked i2e}"
  if px i2n 10 10 != (0, 0, 0) || inked i2n != 256 then
    failures := failures + 1; report s!"nonzero ring: centre {px i2n 10 10}, inked {inked i2n}"
  -- 3. Nested clips: [0,12]² then [8,20]² → only [8,12]² (16 px).
  let nested : Clip := [⟨rectP 8 8 20 20, .nonzero⟩, ⟨rectP 0 0 12 12, .nonzero⟩]
  let i3 := renderItems {} idm 20 20 #[fillI (rectP 0 0 20 20) black nested]
  if inked i3 != 16 || px i3 8 8 != (0, 0, 0) || px i3 7 8 != (255, 255, 255) then
    failures := failures + 1; report s!"nested clips: {inked i3} inked"
  -- 4. Colours.
  let col := fun (c : Color) (a : Comp) =>
    px (renderItems {} idm 2 2 #[.fillPath (rectP 0 0 2 2) .nonzero { color := c, alpha := a } []]) 1 1
  let g := col (.gray (comp 50)) Comp.one
  if g.1 < 127 || g.1 > 129 || g.1 != g.2.1 || g.1 != g.2.2 then
    failures := failures + 1; report s!"gray 0.5 → {g}"
  if col (.rgb Comp.one Comp.zero Comp.zero) Comp.one != (255, 0, 0) then
    failures := failures + 1; report "rgb red"
  if col (.cmyk Comp.zero Comp.zero Comp.zero Comp.one) Comp.one != (0, 0, 0) ||
      col (.cmyk Comp.one Comp.zero Comp.zero Comp.zero) Comp.one != (0, 255, 255) then
    failures := failures + 1; report "cmyk"
  let a := col black (comp 50)
  if a.1 < 127 || a.1 > 129 then
    failures := failures + 1; report s!"alpha 0.5 black on white → {a}"
  if col (.pattern (Name.ofString "P0")) Comp.one != (128, 128, 128) then
    failures := failures + 1; report "pattern placeholder"
  -- 5. Cache: 3 items share a clip (2 hits); a nested clip reuses its parent (1 more hit).
  let c1 : Clip := [⟨rectP 1 1 15 15, .nonzero⟩]
  let c2 : Clip := ⟨rectP 3 3 9 9, .evenOdd⟩ :: c1
  let st := renderItemsCounted {} idm 20 20
    #[fillI (rectP 0 0 20 20) black c1, fillI (rectP 0 0 20 20) black c1,
      fillI (rectP 0 0 20 20) black c1, fillI (rectP 0 0 20 20) (.gray (comp 50)) c2]
  if st.cache.hits != 3 || st.cache.entries.length != 2 then
    failures := failures + 1
    report s!"cache: hits {st.cache.hits}, entries {st.cache.entries.length}"
  -- 6. Mask intersection ≤ operands on two overlapping circles (anti-aliased edges).
  let ma := (fillCounted {} idm (circleP 20 20 15) .nonzero ⟨0, 0, 50, 50⟩).1
  let mb := (fillCounted {} idm (circleP 30 25 15) .nonzero ⟨0, 0, 50, 50⟩).1
  let mi := ma.inter mb
  let mut bad := 0
  for y in [0:50] do
    for x in [0:50] do
      let v := (mi.get x y).toNat
      if v > (ma.get x y).toNat || v > (mb.get x y).toNat then bad := bad + 1
  if bad != 0 || mi.data.size != mi.w * mi.h || mi.total == 0 then
    failures := failures + 1; report s!"mask intersection: {bad} bad pixels"
  -- 7. Interpreter → display list → image. Page [0 0 8 8] at zoom 1: page y is flipped.
  -- Clip to the lower-left 4×4 page square, fill all red: device rows 4…7, cols 0…3.
  -- Then a blue hairline along page y = 1.5 (device row 6, whole width).
  let content := "q 0 0 4 4 re W n 1 0 0 rg 0 0 8 8 re f Q 0 0 1 RG 0 1.5 m 8 1.5 l S"
  let r := Content.interpBytes {} content.toUTF8
  let i7 := renderPaths (mkPage 8 8 .r0) 1 .r0 r.items
  dumps := dumps.push ("interp", i7)
  let W : Nat × Nat × Nat := (255, 255, 255)
  let R : Nat × Nat × Nat := (255, 0, 0)
  let B : Nat × Nat × Nat := (0, 0, 255)
  let expected : List (List (Nat × Nat × Nat)) :=
    [[W, W, W, W, W, W, W, W], [W, W, W, W, W, W, W, W], [W, W, W, W, W, W, W, W],
     [W, W, W, W, W, W, W, W], [R, R, R, R, W, W, W, W], [R, R, R, R, W, W, W, W],
     [B, B, B, B, B, B, B, B], [R, R, R, R, W, W, W, W]]
  let got := (List.range 8).map fun y => (List.range 8).map fun x => px i7 x y
  if i7.w != 8 || i7.h != 8 || got != expected then
    failures := failures + 1; report s!"interpreted page: {got}"
  -- 8. Rotation: a 30 × 10 page at /Rotate 90 renders 10 × 30, zoom 2 → 20 × 60.
  let i8 := renderPaths (mkPage 30 10 .r90) 2 .r0 #[fillI (rectP 0 0 5 5) black]
  if i8.w != 20 || i8.h != 60 || i8.data.size != 4 * 20 * 60 || inked i8 != 100 then
    failures := failures + 1; report s!"rotated page {i8.w}×{i8.h}, inked {inked i8}"
  -- 9. Timing: 1000 filled 10 × 10 rectangles under one shared clip, 612 × 792 page.
  let clip9 : Clip := [⟨circleP 306 396 280, .nonzero⟩]
  let items9 : DisplayList := (Array.range 1000).map fun k =>
    let x : Int := (k % 50 : Nat) * 12
    let y : Int := (k / 50 : Nat) * 39
    fillI (rectP x y (x + 10) (y + 10)) (.rgb (comp (k % 100)) (comp 30) (comp 60)) clip9
  let t0 ← IO.monoMsNow
  let st9 := renderItemsCounted {} (viewMatrix 1 .r0 ⟨0, 0, 612, 792⟩) 612 792 items9
  let n9 := st9.buf.size
  let t1 ← IO.monoMsNow
  IO.println s!"  raster-clip: 1000 rects under 1 clip on 612×792: {t1 - t0} ms (buffer {n9} bytes, cache hits {st9.cache.hits}, steps {st9.steps})"
  dumps := dumps.push ("rects1000", ⟨612, 792, st9.buf⟩)
  if st9.cache.hits != 999 then
    failures := failures + 1; report s!"timing page: cache hits {st9.cache.hits}"
  if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
    IO.FS.createDirAll dir
    for (name, img) in dumps do
      writePpm (System.FilePath.mk dir / s!"{name}.ppm") img
  return failures

end SafePdf.Tests.RasterClip
