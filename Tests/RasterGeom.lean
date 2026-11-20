import SafePdf.Core.Raster.Geom

/-!
# Rational geometry and C2 property suite (task 7.1)

Plan.md §4 C2 and §6 Phase 7. The C2 round-trips are theorems in
`SafePdf.Core.Raster.Geom`; this suite exercises the same definitions on many deterministic
pseudo-random inputs (fixed seed) and checks, by evaluation:

* `toPage ∘ toScreen = id` and `toScreen ∘ toPage = id` over ℚ, for random zooms, all four
  rotations, page `/Rotate` × user rotation, random boxes and points;
* points of the box land in `[0, W] × [0, H]` (`toScreen_mem`);
* `Aff.inv` inverts random invertible matrices, `Aff.mul` is associative and composes
  application in row-vector order;
* one `Content.Matrix.apply` (the interpreter's `Fixed` arithmetic) is within `1/2 · 10⁻⁶`
  per coordinate of the exact ℚ application (`Matrix.apply_x_err`);
* a test-only `Float` mirror of `toScreen`/`toPage` agrees with the ℚ model within `10⁻⁶`
  and round-trips within `10⁻⁶` (C2's "float version tested", for the formulas; the
  rasterizer's own float code does not exist yet).
-/

namespace SafePdf.Tests.RasterGeom

open SafePdf.Core
open SafePdf.Core.Raster.Geom

/-- One step of a 31-bit linear congruential generator. -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- A pseudo-random rational in `[-lim, lim]` with denominator `1 … 97`, and the next seed. -/
def genRat (s : Nat) (lim : Nat) : Rat × Nat :=
  let s1 := lcg s
  let s2 := lcg s1
  let den := s2 % 97 + 1
  let num : Int := (s1 % (2 * lim * den + 1) : Nat) - (lim * den : Nat)
  ((num : Rat) / (den : Rat), s2)

/-- A pseudo-random rotation and the next seed. -/
def genRot (s : Nat) : Doc.Rotation × Nat :=
  let s1 := lcg s
  (rotOfQuarters (s1 / 7), s1)

/-- A `Rat` as a `Float`. -/
def ratToFloat (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

/-- `Float` mirror of `toScreen` (the four `viewMatrix` cases). -/
def toScreenF (z : Float) (r : Doc.Rotation) (llx lly urx ury x y : Float) : Float × Float :=
  match r with
  | .r0 => (z * (x - llx), z * (ury - y))
  | .r90 => (z * (y - lly), z * (x - llx))
  | .r180 => (z * (urx - x), z * (y - lly))
  | .r270 => (z * (ury - y), z * (urx - x))

/-- `Float` mirror of `toPage` (closed-form inverse of each case). -/
def toPageF (z : Float) (r : Doc.Rotation) (llx lly urx ury u v : Float) : Float × Float :=
  match r with
  | .r0 => (u / z + llx, ury - v / z)
  | .r90 => (v / z + llx, u / z + lly)
  | .r180 => (urx - u / z, v / z + lly)
  | .r270 => (urx - v / z, ury - u / z)

/-- `|a − b| ≤ eps`. -/
def near (a b eps : Float) : Bool := Float.abs (a - b) ≤ eps

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let mut s := 7071
  let report := fun (msg : String) => IO.println s!"  FAIL raster-geom: {msg}"
  for i in [0:400] do
    -- Zoom in (0, 8], box with llx ≤ urx, lly ≤ ury, point anywhere, screen point anywhere.
    let (z0, s1) := genRat s 8
    let z := if z0 < 0 then -z0 else z0
    let z := if z == 0 then 1/7 else z
    let (x1, s2) := genRat s1 1000
    let (x2, s3) := genRat s2 1000
    let (y1, s4) := genRat s3 1000
    let (y2, s5) := genRat s4 1000
    let bx : Box := ⟨min x1 x2, min y1 y2, max x1 x2, max y1 y2⟩
    let (px, s6) := genRat s5 2000
    let (py, s7) := genRat s6 2000
    let (qx, s8) := genRat s7 5000
    let (qy, s9) := genRat s8 5000
    let (r, s10) := genRot s9
    let (u, s11) := genRot s10
    s := s11
    let p : Pt := ⟨px, py⟩
    let q : Pt := ⟨qx, qy⟩
    if toPage z r bx (toScreen z r bx p) != p then
      failures := failures + 1; report s!"case {i}: toPage ∘ toScreen ≠ id"
    if toScreen z r bx (toPage z r bx q) != q then
      failures := failures + 1; report s!"case {i}: toScreen ∘ toPage ≠ id"
    if toPageView z r u bx (toScreenView z r u bx p) != p ||
        toScreenView z r u bx (toPageView z r u bx q) != q then
      failures := failures + 1; report s!"case {i}: view round trip (user rotation) ≠ id"
    -- A point inside the box (midpoint-ish blend of the corners) lands on screen.
    let inside : Pt := ⟨(bx.llx * 2 + bx.urx) / 3, (bx.lly + bx.ury * 4) / 5⟩
    let sp := toScreen z r bx inside
    let (w, h) := screenSize z r bx
    if !(0 ≤ sp.x && sp.x ≤ w && 0 ≤ sp.y && sp.y ≤ h) then
      failures := failures + 1; report s!"case {i}: in-box point off screen"
    -- Random invertible matrix: inverse, associativity, composition order.
    let m : Aff := ⟨x1 / 100, y1 / 100, x2 / 100, y2 / 100, px, py⟩
    let n : Aff := ⟨z, qx / 1000, qy / 1000, z + 1, x2, y1⟩
    if m.det != 0 then
      if Aff.apply m.inv (Aff.apply m p) != p || Aff.apply m (Aff.apply m.inv q) != q then
        failures := failures + 1; report s!"case {i}: Aff.inv"
    if m * n * m != m * (n * m) || Aff.apply (m * n) p != Aff.apply n (Aff.apply m p) then
      failures := failures + 1; report s!"case {i}: Aff.mul"
    -- Fixed vs ℚ: one matrix application within 1/2 · 10⁻⁶ per coordinate.
    let fx (v : Rat) : Content.Fixed := Content.Fixed.clamp (v * 1000).floor
    let fm : Content.Matrix := ⟨fx (x1 / 1000), fx (y1 / 1000), fx (x2 / 1000),
      fx (y2 / 1000), fx px, fx py⟩
    let fp : Content.Point := ⟨fx (qx / 10), fx (qy / 10)⟩
    let got := Content.Matrix.apply fm fp
    let ex := Aff.apply (Aff.ofMatrix fm) (ptOfPoint fp)
    let dx := Fixed.toRat got.x - ex.x
    let dy := Fixed.toRat got.y - ex.y
    let tol : Rat := 1 / 2000000
    if !(-tol ≤ dx && dx ≤ tol && -tol ≤ dy && dy ≤ tol) then
      failures := failures + 1; report s!"case {i}: Fixed apply error > 1/2·10⁻⁶"
    -- Float mirror of the view transform.
    let F := ratToFloat
    let (fu, fv) := toScreenF (F z) r (F bx.llx) (F bx.lly) (F bx.urx) (F bx.ury) (F px) (F py)
    let sq := toScreen z r bx p
    if !(near fu (F sq.x) 1e-6 && near fv (F sq.y) 1e-6) then
      failures := failures + 1; report s!"case {i}: Float toScreen differs from ℚ"
    let (bx', by') := toPageF (F z) r (F bx.llx) (F bx.lly) (F bx.urx) (F bx.ury) fu fv
    if !(near bx' (F px) 1e-6 && near by' (F py) 1e-6) then
      failures := failures + 1; report s!"case {i}: Float round trip error > 1e-6"
  return failures

end SafePdf.Tests.RasterGeom
