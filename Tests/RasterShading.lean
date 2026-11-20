import SafePdf.Core.Raster.Shading
import SafePdf.Core.Content.Interp

/-!
# Shading suite (task 7.3d)

Plan.md §6 Phase 7 ("shadings"), ISO 32000-2 §7.10 (functions), §8.7.4 (shadings), §8.7.3
(shading patterns). The buffer shapes (`paint_size`, `renderShading_size`,
`renderFill_size`), the lookup-index ranges (`axialIndex_range`, `radialIndex_range`), the
function output size (`Fn.eval_length`) and the work bounds (`paint_steps_le`,
`renderShading_steps_le`) are theorems in `SafePdf.Core.Raster.Shading`; this suite checks
behaviour by evaluation:

* functions: exponential `N = 1, 2` and non-integral `N`, stitching at and between bounds,
  sampled 1-in and 2-in multilinear interpolation, PostScript calculator programs;
* axial: end and middle colours, `/Extend` off (outside unpainted) and on, a clip, a `/BBox`;
* radial: concentric circles (colour by distance), two circles against a `Float` reference
  of the larger admissible root (±1 index), `/Extend`;
* meshes: a type 4 triangle (Gouraud), a type 5 lattice, a type 6 Coons patch (corner
  colours), a type 1 function shading (PostScript `{ add 2 div }`);
* a shading pattern fill with `/Background` through `loadShadings` and `renderFill`;
* timing of a full-page 612 × 792 axial and radial shading (printed).

Set `SAFEPDF_PPM_DIR=<dir>` to also write the rendered test pages as PPM files there.
-/

namespace SafePdf.Tests.RasterShading

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Shading
open SafePdf.Core.Content (Fixed Comp Color Clip ClipPath DisplayItem DisplayList Path Matrix
  FillStyle Source FillRule)
open SafePdf.Core.Raster

/-- A name. -/
def nm (s : String) : Name := Name.ofString s

/-- Bytes from naturals. -/
def bytes (l : List Nat) : ByteArray := ByteArray.mk (l.map UInt8.ofNat).toArray

/-- An object source over an in-memory table; streams decoded with their filters. -/
def memSource (objs : List (Nat × IndirectBody)) : Source Unit :=
  ⟨fun s n _ => match objs.find? (·.1 == n) with
     | some (_, b) => (.ok b, s)
     | none => (.error (.malformed 0 "missing"), s),
   fun s _ st => (Filter.decodeBytes {} st.dict st.data (.unsupported "image codec"), s)⟩

/-- View of a `W × H` page at zoom 1 (y flipped, origin top-left). -/
def view (W H : Nat) : Aff := viewMatrix 1 .r0 ⟨0, 0, W, H⟩

/-- An integer. -/
def I (n : Int) : PdfObject := .int n

/-- A number array. -/
def nums (l : List Int) : PdfObject := .array (l.map PdfObject.int)

/-- A real `n / d` as a PDF number (exact decimal when `d` is a power of ten). -/
def R (n : Int) (scale : Nat) : PdfObject := .real ⟨n, scale⟩

/-- A type 2 function dictionary. -/
def expFn (c0 c1 : List Int) (n : PdfObject) : PdfObject :=
  .dict [(nm "FunctionType", I 2), (nm "Domain", nums [0, 1]), (nm "C0", nums c0),
    (nm "C1", nums c1), (nm "N", n)]

/-- An axial shading dictionary. -/
def axialDict (cs : String) (coords : List Int) (fn : PdfObject) (ext : Bool × Bool := (false, false))
    (extra : Dict := []) : PdfObject :=
  .dict ([(nm "ShadingType", I 2), (nm "ColorSpace", .name (nm cs)), (nm "Coords", nums coords),
    (nm "Function", fn), (nm "Extend", .array [.bool ext.1, .bool ext.2])] ++ extra)

/-- A radial shading dictionary. -/
def radialDict (cs : String) (coords : List Int) (fn : PdfObject) (ext : Bool × Bool := (false, false)) :
    PdfObject :=
  .dict [(nm "ShadingType", I 3), (nm "ColorSpace", .name (nm cs)), (nm "Coords", nums coords),
    (nm "Function", fn), (nm "Extend", .array [.bool ext.1, .bool ext.2])]

/-- Render `sh` and `fillPath` items onto a white `W × H` page. -/
def render (W H : Nat) (tbl : ShadingTable) (items : List DisplayItem) : Clip.Image :=
  let st := items.foldl (fun st it =>
    match it with
    | .shading n c cl => renderShading {} (view W H) W H tbl st n c cl
    | .fillPath p r s cl => renderFill {} (view W H) W H tbl st p r s cl
    | _ => st) ({ buf := Clip.whiteBuf W H } : Clip.RState)
  ⟨W, H, st.buf⟩

/-- Load page resources `res` for `items` from `objs` and render. -/
def renderRes (W H : Nat) (objs : List (Nat × IndirectBody)) (res : Dict)
    (items : List DisplayItem) : Clip.Image × ShadingTable :=
  let (tbl, _) := loadShadings {} (memSource objs) () res items.toArray
  (render W H tbl items, tbl)

/-- One `sh` item of shading `Sh` (identity CTM). -/
def shItem (clip : Clip := []) : DisplayItem := .shading (nm "Sh") Matrix.identity clip

/-- Resources with one shading `Sh` = object 1. -/
def shRes : Dict := [(nm "Shading", .dict [(nm "Sh", .ref 1 0)])]

/-- Render one shading object on a `W × H` page. -/
def renderOne (W H : Nat) (o : IndirectBody) (clip : Clip := []) : Clip.Image :=
  (renderRes W H [(1, o)] shRes [shItem clip]).1

/-- RGB of pixel `(x, y)`. -/
def px (img : Clip.Image) (x y : Nat) : Nat × Nat × Nat :=
  let i := 4 * (y * img.w + x)
  (Clip.getB img.data i, Clip.getB img.data (i + 1), Clip.getB img.data (i + 2))

/-- `|a − b| ≤ tol`. -/
def near (a b tol : Nat) : Bool := a ≤ b + tol && b ≤ a + tol

/-- Rectangle path in page space. -/
def rect (x0 y0 x1 y1 : Int) : Path :=
  ⟨#[.moveTo ⟨Fixed.ofInt x0, Fixed.ofInt y0⟩, .lineTo ⟨Fixed.ofInt x1, Fixed.ofInt y0⟩,
    .lineTo ⟨Fixed.ofInt x1, Fixed.ofInt y1⟩, .lineTo ⟨Fixed.ofInt x0, Fixed.ofInt y1⟩, .closePath]⟩

/-- A function's outputs as floats (×1000, rounded). -/
def ev (f : Fn) (xs : List Rat) (n : Nat) : List Int :=
  (f.eval xs n).map fun q => (q * 1000 + 1 / 2).floor

/-- Reference radial index at page point `(x, y)` by `Float`: the larger root `s` of the
two-circle equation with `r(s) ≥ 0`, inside `[0, 1]` (no extension); `none` if none. -/
def refRadial (x0 y0 r0 x1 y1 r1 x y : Float) : Option Nat :=
  let cx := x1 - x0; let cy := y1 - y0; let dr := r1 - r0
  let px := x - x0; let py := y - y0
  let a := cx * cx + cy * cy - dr * dr
  let b := px * cx + py * cy + r0 * dr
  let c := px * px + py * py - r0 * r0
  let roots : List Float :=
    if a == 0 then (if b == 0 then [] else [c / (2 * b)])
    else
      let disc := b * b - a * c
      if disc < 0 then [] else
      let sq := Float.sqrt disc
      let s1 := (b + sq) / a; let s2 := (b - sq) / a
      if s1 ≥ s2 then [s1, s2] else [s2, s1]
  match roots.find? (fun s => r0 + s * dr ≥ 0 && 0 ≤ s && s ≤ 1) with
  | some s => some (s * 255 + 0.5).floor.toUInt64.toNat
  | none => none

/-- Write an RGBA image as a binary PPM (alpha dropped). -/
def writePpm (path : System.FilePath) (img : Clip.Image) : IO Unit := do
  let mut rgb := ByteArray.empty
  for i in [0:img.w * img.h] do
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i)))
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i + 1)))
    rgb := rgb.push (UInt8.ofNat (Clip.getB img.data (4 * i + 2)))
  IO.FS.writeBinFile path (s!"P6\n{img.w} {img.h}\n255\n".toUTF8 ++ rgb)

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL raster-shading: {msg}"
  let mut dumps : Array (String × Clip.Image) := #[]
  -- 1. Functions.
  let e1 := Fn.exp (0, 1) none [0, 10] [1, 20] 1
  let e2 := Fn.exp (0, 1) none [0] [1] 2
  let eh := Fn.exp (0, 1) none [0] [1] (1 / 2)
  if ev e1 [1 / 4] 2 != [250, 12500] || ev e2 [1 / 2] 1 != [250] || ev e2 [2] 1 != [1000] ||
      ev eh [1 / 4] 1 != [500] then
    failures := failures + 1
    report s!"exponential: {ev e1 [1/4] 2} {ev e2 [1/2] 1} {ev e2 [2] 1} {ev eh [1/4] 1}"
  let st := Fn.stitch (0, 1) none [Fn.exp (0, 1) none [0] [1] 1, Fn.exp (0, 1) none [1] [0] 1]
    [1 / 2] [(0, 1), (0, 1)]
  if ev st [1 / 4] 1 != [500] || ev st [1 / 2] 1 != [1000] || ev st [3 / 4] 1 != [500] ||
      ev st [1] 1 != [0] || ev st [0] 1 != [0] then
    failures := failures + 1
    report s!"stitching: {ev st [1/4] 1} {ev st [1/2] 1} {ev st [3/4] 1} {ev st [1] 1}"
  let s1 := Fn.sampled [(0, 1)] [(0, 1)] [3] 8 [] [] #[0, 255, 51]
  let s2 := Fn.sampled [(0, 1), (0, 1)] [(0, 1)] [2, 2] 8 [] [] #[0, 255, 255, 0]
  if ev s1 [1 / 4] 1 != [500] || ev s1 [3 / 4] 1 != [600] || ev s1 [1] 1 != [200] ||
      ev s2 [1 / 2, 1 / 2] 1 != [500] || ev s2 [1, 0] 1 != [1000] || ev s2 [1 / 4, 0] 1 != [250] then
    failures := failures + 1
    report s!"sampled: {ev s1 [1/4] 1} {ev s1 [3/4] 1} {ev s2 [1/2, 1/2] 1} {ev s2 [1/4, 0] 1}"
  let ps := fun (src : String) (nIn nOut : Nat) =>
    Fn.ps (List.replicate nIn (0, 1)) (List.replicate nOut (-1000, 1000))
      ((psProgram src.toUTF8).getD [])
  if ev (ps "{ 2 mul exch 3 mul add }" 2 1) [1 / 2, 1 / 4] 1 != [2000] ||
      ev (ps "{ dup 0.5 gt { 1 exch sub } if }" 1 1) [3 / 4] 1 != [250] ||
      ev (ps "{ 0.5 lt { 7 } { 9 } ifelse }" 1 1) [1 / 4] 1 != [7000] ||
      ev (ps "{ 90 mul sin 2 sqrt mul }" 1 1) [1 / 2] 1 != [1000] ||
      ev (ps "{ 3 copy pop pop 4 1 roll }" 3 4) [1 / 10, 2 / 10, 3 / 10] 4 != [100, 100, 200, 300] ||
      ev (ps "{ pop pop }" 1 1) [1 / 2] 1 != [0] then
    failures := failures + 1
    report s!"postscript: {ev (ps "{ 2 mul exch 3 mul add }" 2 1) [1/2, 1/4] 1} {ev (ps "{ 90 mul sin 2 sqrt mul }" 1 1) [1/2] 1} {ev (ps "{ 3 copy pop pop 4 1 roll }" 3 4) [1/10, 2/10, 3/10] 4}"
  -- 2. Axial black → white over the page width (256 × 2).
  let ax := renderOne 256 2 (.obj (axialDict "DeviceGray" [0, 0, 256, 0] (expFn [0] [1] (I 1))))
  dumps := dumps.push ("axial-gray", ax)
  if px ax 0 0 != (0, 0, 0) || px ax 255 1 != (255, 255, 255) || (px ax 128 0).1 != 128 ||
      (px ax 64 1).1 != 64 then
    failures := failures + 1; report s!"axial endpoints/midpoint: {px ax 0 0} {px ax 128 0} {px ax 255 1}"
  -- N = 2: midpoint 0.25 → 64.
  let ax2 := renderOne 256 1 (.obj (axialDict "DeviceGray" [0, 0, 256, 0] (expFn [0] [1] (I 2))))
  if !near (px ax2 128 0).1 64 1 then
    failures := failures + 1; report s!"axial N=2 midpoint: {px ax2 128 0}"
  -- 3. Extend off / on: red → blue on [64, 192] of a 256-wide page.
  let rb := expFn [1, 0, 0] [0, 0, 1] (I 1)
  let axOff := renderOne 256 1 (.obj (axialDict "DeviceRGB" [64, 0, 192, 0] rb))
  let axOn := renderOne 256 1 (.obj (axialDict "DeviceRGB" [64, 0, 192, 0] rb (true, true)))
  dumps := dumps.push ("axial-extend", axOn)
  if px axOff 10 0 != (255, 255, 255) || px axOff 250 0 != (255, 255, 255) ||
      px axOn 10 0 != (255, 0, 0) || px axOn 250 0 != (0, 0, 255) ||
      !near (px axOff 64 0).1 255 1 || !near (px axOff 191 0).2.2 255 1 ||
      !near (px axOn 128 0).1 127 1 || !near (px axOn 128 0).2.2 128 1 then
    failures := failures + 1
    report s!"extend: off {px axOff 10 0} {px axOff 64 0} {px axOff 250 0}; on {px axOn 10 0} {px axOn 128 0} {px axOn 250 0}"
  -- 4. A clip (left half) and a /BBox (x ≤ 32).
  let clipL : Clip := [⟨rect 0 0 128 4, .nonzero⟩]
  let axC := renderOne 256 4 (.obj (axialDict "DeviceGray" [0, 0, 256, 0] (expFn [0] [1] (I 1)))) clipL
  let axB := renderOne 256 4 (.obj (axialDict "DeviceGray" [0, 0, 256, 0] (expFn [0] [1] (I 1))
    (false, false) [(nm "BBox", nums [0, 0, 32, 4])]))
  if (px axC 100 2).1 != 100 || px axC 200 2 != (255, 255, 255) ||
      (px axB 20 2).1 != 20 || px axB 40 2 != (255, 255, 255) then
    failures := failures + 1; report s!"clip/bbox: {px axC 100 2} {px axC 200 2} {px axB 20 2} {px axB 40 2}"
  -- 5. Radial, concentric: r ∈ [0, 40] around (50, 50), red → blue.
  let rc := renderOne 100 100 (.obj (radialDict "DeviceRGB" [50, 50, 0, 50, 50, 40] rb))
  let rcE := renderOne 100 100 (.obj (radialDict "DeviceRGB" [50, 50, 0, 50, 50, 40] rb (true, true)))
  dumps := dumps.push ("radial-concentric", rc)
  -- pixel (70, 49) is page (70.5, 50.5): distance ≈ 20.5 → s ≈ 0.513 → index 131
  if !near (px rc 50 50).1 255 5 || !near (px rc 70 49).2.2 131 1 || px rc 2 2 != (255, 255, 255) ||
      px rcE 2 2 != (0, 0, 255) then
    failures := failures + 1; report s!"radial concentric: {px rc 50 50} {px rc 70 49} {px rc 2 2} {px rcE 2 2}"
  -- 6. Two circles against the Float reference (gray, no extend).
  let g01 := expFn [0] [1] (I 1)
  let two := renderOne 100 100 (.obj (radialDict "DeviceGray" [30, 50, 10, 70, 45, 25] g01))
  dumps := dumps.push ("radial-two", two)
  let mut bad := 0
  for y in [0:100] do
    for x in [0:100] do
      -- device (x + ½, y + ½) is page (x + ½, 100 − y − ½)
      let r := refRadial 30 50 10 70 45 25 (x.toFloat + 0.5) (100 - y.toFloat - 0.5)
      let v := (px two x y).1
      let ok := match r with
        | some i => near v i 1
        | none => v == 255
      if !ok then bad := bad + 1
  if bad > 4 then
    failures := failures + 1; report s!"radial two circles: {bad} pixels differ from the reference"
  -- 7. Meshes. Type 4: one triangle red/green/blue (8-bit coordinates, flags, components).
  let meshDict := fun (ty : Int) (extra : Dict) => [(nm "ShadingType", I ty),
    (nm "ColorSpace", .name (nm "DeviceRGB")), (nm "BitsPerCoordinate", I 8),
    (nm "BitsPerComponent", I 8), (nm "BitsPerFlag", I 8),
    (nm "Decode", nums [0, 255, 0, 255, 0, 1, 0, 1, 0, 1])] ++ extra
  let t4 := renderOne 64 64 (.stream ⟨meshDict 4 [], bytes [0, 0, 0, 255, 0, 0, 0, 64, 0, 0, 255, 0,
    0, 0, 64, 0, 0, 255]⟩)
  dumps := dumps.push ("mesh-type4", t4)
  -- vertex (0,0) is device bottom-left; (1, 62) is near it, (62, 62) near (64, 0), (1, 1) near (0, 64)
  if !near (px t4 1 62).1 255 12 || !near (px t4 61 62).2.1 255 12 || !near (px t4 1 2).2.2 255 12 ||
      px t4 60 4 != (255, 255, 255) then
    failures := failures + 1; report s!"type 4: {px t4 1 62} {px t4 61 62} {px t4 1 2} {px t4 60 4}"
  -- Type 5: a 2 × 2 lattice (one quad), black at the bottom row, white at the top.
  let t5 := renderOne 32 32 (.stream ⟨(meshDict 5 [(nm "VerticesPerRow", I 2)]).filter
      (·.1 != nm "BitsPerFlag"),
    bytes [0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 32, 255, 255, 255, 32, 32, 255, 255, 255]⟩)
  if !near (px t5 16 31).1 4 5 || !near (px t5 16 0).1 251 5 || !near (px t5 16 16).1 128 9 then
    failures := failures + 1; report s!"type 5: {px t5 16 31} {px t5 16 16} {px t5 16 0}"
  -- Type 6: a flat Coons square [0, 64]² (straight edges), corner colours red, green, blue, black
  -- at p00 = (0,0), p03 = (0,64), p33 = (64,64), p30 = (64,0).
  let coons : List Nat := [0, 0, 0, 0, 21, 0, 43, 0, 64, 21, 64, 43, 64, 64, 64, 43, 64, 21, 64,
    0, 43, 0, 21, 0]
  let coonsPts : List Nat := (List.range 12).foldl (fun acc k =>
    acc ++ [min 255 (coons.getD (2 * k) 0 * 255 / 64), min 255 (coons.getD (2 * k + 1) 0 * 255 / 64)]) []
  let t6dict := (meshDict 6 []).map fun kv =>
    if kv.1 == nm "Decode" then (kv.1, nums [0, 64, 0, 64, 0, 1, 0, 1, 0, 1]) else kv
  let t6 := renderOne 64 64 (.stream ⟨t6dict,
    bytes ([0] ++ coonsPts ++ [255, 0, 0, 0, 255, 0, 0, 0, 255, 0, 0, 0])⟩)
  dumps := dumps.push ("mesh-coons", t6)
  if !near (px t6 1 62).1 255 16 || !near (px t6 1 1).2.1 255 16 || !near (px t6 62 1).2.2 255 16 ||
      !near (px t6 62 62).1 0 16 then
    failures := failures + 1; report s!"type 6: {px t6 1 62} {px t6 1 1} {px t6 62 1} {px t6 62 62}"
  -- Type 1: f(x, y) = (x + y) / 2 (PostScript), domain [0 1]², matrix scale 64.
  let fnPs : IndirectBody := .stream ⟨[(nm "FunctionType", I 4), (nm "Domain", nums [0, 1, 0, 1]),
    (nm "Range", nums [0, 1])], "{ add 2 div }".toUTF8⟩
  let t1 := (renderRes 64 64 [(1, .obj (.dict [(nm "ShadingType", I 1),
    (nm "ColorSpace", .name (nm "DeviceGray")), (nm "Matrix", nums [64, 0, 0, 64, 0, 0]),
    (nm "Function", .ref 2 0)])), (2, fnPs)] shRes [shItem]).1
  dumps := dumps.push ("function-based", t1)
  if !near (px t1 0 63).1 2 3 || !near (px t1 63 0).1 253 3 || !near (px t1 32 31).1 128 3 then
    failures := failures + 1; report s!"type 1: {px t1 0 63} {px t1 32 31} {px t1 63 0}"
  -- 8. A shading pattern (/Background black, /BBox [0 0 30 10], axis [10, 20] in pattern space,
  -- pattern matrix: translate by 10) filling the page-space rectangle [0, 60] × [0, 10].
  let patRes : Dict := [(nm "Pattern", .dict [(nm "P0", .ref 5 0)])]
  let patObj : IndirectBody := .obj (.dict [(nm "PatternType", I 2),
    (nm "Matrix", nums [1, 0, 0, 1, 10, 0]),
    (nm "Shading", axialDict "DeviceGray" [10, 0, 20, 0] (expFn [0] [1] (I 1)) (false, false)
      [(nm "Background", nums [0]), (nm "BBox", nums [0, 0, 30, 10])])])
  let patItem : DisplayItem := .fillPath (rect 0 0 60 10) .nonzero { color := .pattern (nm "P0"), alpha := Comp.one } []
  let (pf, ptbl) := renderRes 64 10 [(5, patObj)] patRes [patItem]
  dumps := dumps.push ("pattern", pf)
  -- page x 5 → pattern −5: outside the BBox → white; page 12 → pattern 2.5 (s < 0) → background;
  -- page 25 → pattern 15.5 → s = 0.55 → 140; page 35 → pattern 25.5 (s > 1) → background;
  -- page 45 → pattern 35.5 > 30 → white; page 62 → outside the path → white.
  if ptbl.patterns.length != 1 || px pf 5 5 != (255, 255, 255) || px pf 12 5 != (0, 0, 0) ||
      !near (px pf 25 5).1 140 1 || px pf 35 5 != (0, 0, 0) || px pf 45 5 != (255, 255, 255) ||
      px pf 62 5 != (255, 255, 255) then
    failures := failures + 1
    report s!"pattern: {ptbl.patterns.length} {px pf 5 5} {px pf 12 5} {px pf 25 5} {px pf 35 5} {px pf 45 5} {px pf 62 5}"
  -- 9. A Separation space with a PostScript tint transform (tint → CMYK (0, t, t, 0)): t = 1 → red.
  let sepCS : PdfObject := .array [.name (nm "Separation"), .name (nm "Spot"), .name (nm "DeviceCMYK"),
    .ref 3 0]
  let tint : IndirectBody := .stream ⟨[(nm "FunctionType", I 4), (nm "Domain", nums [0, 1]),
    (nm "Range", nums [0, 1, 0, 1, 0, 1, 0, 1])], "{ 0 exch dup 0 }".toUTF8⟩
  let sepSh := PdfObject.dict [(nm "ShadingType", I 2), (nm "ColorSpace", sepCS),
    (nm "Coords", nums [0, 0, 16, 0]), (nm "Function", expFn [0] [1] (I 1))]
  let sp := (renderRes 16 1 [(1, .obj sepSh), (3, tint)] shRes [shItem]).1
  -- pixel 0: s = 1/32 → index 8 → t = 8/255 → (255, 247, 247); pixel 15 → index 247
  if px sp 15 0 != (255, 8, 8) || px sp 0 0 != (255, 247, 247) then
    failures := failures + 1; report s!"separation tint: {px sp 0 0} {px sp 15 0}"
  -- 10. Unknown and malformed shadings paint nothing.
  let un := (renderRes 4 1 [(1, .obj (.dict [(nm "ShadingType", I 2)]))] shRes [shItem,
    .shading (nm "Nope") Matrix.identity []]).1
  if px un 0 0 != (255, 255, 255) then
    failures := failures + 1; report "malformed shading painted"
  -- 11. Timing: full-page 612 × 792 axial and radial.
  let W := 612
  let H := 792
  let t0 ← IO.monoMsNow
  let fa := renderOne W H (.obj (axialDict "DeviceRGB" [0, 0, 612, 792] rb))
  let n0 := (px fa 300 400).1
  let t1 ← IO.monoMsNow
  let fr := renderOne W H (.obj (radialDict "DeviceRGB" [200, 300, 10, 306, 396, 500] rb (true, true)))
  let n1 := (px fr 300 400).1
  let t2 ← IO.monoMsNow
  let fm := (renderRes W H [(1, .obj (.dict [(nm "ShadingType", I 1),
    (nm "ColorSpace", .name (nm "DeviceGray")), (nm "Matrix", nums [612, 0, 0, 792, 0, 0]),
    (nm "Function", .ref 2 0)])), (2, fnPs)] shRes [shItem]).1
  let n2 := (px fm 300 400).1
  let t3 ← IO.monoMsNow
  IO.println s!"  raster-shading: 612×792 axial {t1 - t0} ms ({n0}), radial {t2 - t1} ms ({n1}), function-based mesh {t3 - t2} ms ({n2})"
  dumps := dumps.push ("full-axial", fa)
  dumps := dumps.push ("full-radial", fr)
  dumps := dumps.push ("full-function", fm)
  if let some dir ← IO.getEnv "SAFEPDF_PPM_DIR" then
    IO.FS.createDirAll dir
    for (name, img) in dumps do
      writePpm (System.FilePath.mk dir / s!"shading-{name}.ppm") img
  return failures

end SafePdf.Tests.RasterShading
