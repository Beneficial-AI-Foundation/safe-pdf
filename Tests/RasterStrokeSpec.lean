import SafePdf.Core.Raster.Stroke

/-!
# Fast stroker vs. reference stroker (task 7.2i)

Plan.md §6 Phase 7 (stroking; M7 speed criterion). The stroker of
`SafePdf.Core.Raster.Stroke` (sections 4–8: integer frame, 64-bit offsets, joins and
orientation tests with exact `Int` fallbacks, common-denominator chord geometry `mkSeg`) must
return exactly the edges — hence exactly the masks — of the `Rat` reference of section 10
(`strokeDPathSpec`, `strokeEdgesSpec`, `mkSegSpec`). This suite compares them on
pseudo-random inputs (fixed seed):

* **chord geometry** (4000 cases): `mkSeg` vs `mkSegSpec` (every field) for random pens
  (identity, uniform and non-uniform scales, rotations, reflections, shears, random rational
  maps with small and large denominators, tiny and huge radii, the hairline pen) and random
  chords from one subpixel to `2³¹` units, with all three dash metrics;
* **device paths** (3000 cases): `strokeDPath` vs `strokeDPathSpec` on random lines, cubics,
  several subpaths, `closePath`, repeated points (degenerate subpaths), coordinate scales from a
  few pixels to beyond the coordinate limit; widths 0, tiny, normal and huge (frames beyond the
  64-bit bound: `Int` fallback); every cap and join; miter limits 1 … 10⁶; dash patterns (none,
  odd, zero-length dots, all-zero, negative, fine patterns beyond `maxDashSteps`, phases); pen
  maps as above plus degenerate ones; configurations with small arc caps, coarse and fine
  tolerances, a small coordinate limit and a small dash budget;
* **page paths** (1000 cases): `strokeEdges` vs `strokeEdgesSpec` through random CTMs
  (`Fixed` entries, including non-uniform, reflecting and degenerate ones) and view matrices
  (zooms, all four rotations); for 300 of them also the masks (`strokePath` vs `fillEdges` of
  the reference edges).

Guards check that most cases produce edges and that the `Int` fallbacks (frames outside the
64-bit bounds) are exercised.
-/

namespace SafePdf.Tests.RasterStrokeSpec

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill
open SafePdf.Core.Raster.Stroke
open SafePdf.Core.Content (LineCap LineJoin LineStyle DashPattern)

/-- Linear congruential generator step (Knuth's MMIX constants, 64 bits). -/
def next (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A pseudo-random number in `[0, n)` and the next state. -/
def rand (s : UInt64) (n : Nat) : Nat × UInt64 :=
  let s := next s
  (if n = 0 then 0 else (s >>> 33).toNat % n, s)

/-- A pseudo-random integer in `[lo, hi]` (wide ranges via two draws). -/
def randI (s : UInt64) (lo hi : Int) : Int × UInt64 :=
  let span := (hi - lo + 1).toNat
  let (k1, s) := rand s 2147483648
  let (k2, s) := rand s 2147483648
  (lo + ((k1 * 2147483648 + k2) % (max 1 span) : Nat), s)

/-- A random rational `n / d` with `|n| ≤ nmax`, `1 ≤ d ≤ dmax`. -/
def randQ (s : UInt64) (nmax dmax : Nat) : Rat × UInt64 :=
  let (n, s) := randI s (-(nmax : Int)) nmax
  let (d, s) := randI s 1 (max 1 dmax)
  ((n : Rat) / (d : Rat), s)

/-- A random device point for coordinate scale `sc`. -/
def randPt (s : UInt64) (sc : Nat) : FPt × UInt64 :=
  let (lo, hi) : Int × Int := match sc with
    | 0 => (5 * 256, 15 * 256)
    | 1 => (-20 * 256, 140 * 256)
    | 2 => (-536870912, 536870912)
    | _ => (-2147483648, 2147483648)
  let (x, s) := randI s lo hi
  let (y, s) := randI s lo hi
  (⟨x, y⟩, s)

/-- A random device path of `n` segments at scale `sc` (sometimes repeating the last point,
mixing scales). -/
def randPath (s : UInt64) (n sc : Nat) : DPath × UInt64 := Id.run do
  let mut s := s
  let (p0, s1) := randPt s sc
  s := s1
  let mut last := p0
  let mut out : DPath := #[.moveTo p0]
  for _ in [0:n] do
    let (k, s1) := rand s 20
    s := s1
    let (sc', s1) := rand s 25
    s := s1
    let scale := if sc' = 0 then 3 else sc
    let (p, s1) := randPt s scale
    s := s1
    let p := if k ≥ 17 then last else p
    if k < 2 then out := out.push (.moveTo p)
    else if k < 4 then out := out.push .closePath
    else if k < 11 ∨ k ≥ 17 then out := out.push (.lineTo p)
    else
      let (c1, s1) := randPt s scale
      let (c2, s2) := randPt s1 scale
      s := s2
      out := out.push (.curveTo c1 c2 p)
    last := p
  return (out, s)

/-- A random linear map (pen space → device pixels), kind `k`. -/
def randMap (s : UInt64) : Aff × UInt64 :=
  let (k, s) := rand s 12
  let (q1, s) := randQ s 40 7
  let (q2, s) := randQ s 40 7
  let (q3, s) := randQ s 1000000 999983
  let (q4, s) := randQ s 1000000 999979
  let m : Aff := match k with
    | 0 => Aff.id
    | 1 => Aff.scale (q1.floor.natAbs + 1 : Nat) (q1.floor.natAbs + 1 : Nat)
    | 2 => Aff.scale (q1 + 1 / 3) (q2 + 1 / 7)                     -- non-uniform
    | 3 => ⟨3 / 5, 4 / 5, -4 / 5, 3 / 5, 0, 0⟩                      -- rotation
    | 4 => ⟨q1, 0, 0, -q1, 0, 0⟩                                    -- reflection
    | 5 => ⟨1, 0, q1, 1, 0, 0⟩                                      -- shear
    | 6 => ⟨q3, q4, q4 * 2, q3 / 3, 0, 0⟩                           -- large denominators
    | 7 => Aff.scale (1 / 1000) (1 / 997)                           -- tiny
    | 8 => Aff.scale 1000 (-999)                                    -- huge, reflecting
    | 9 => ⟨q1, q2, 2 * q1, 2 * q2, 0, 0⟩                           -- degenerate
    | 10 => ⟨0, q1, q2, 0, 0, 0⟩                                    -- swap axes
    | _ => ⟨q1, q2, q3, q4, 0, 0⟩
  (m, s)

/-- A random line width. -/
def randWidth (s : UInt64) : Rat × UInt64 :=
  let (k, s) := rand s 20
  let (q, s) := randQ s 80 4
  let w : Rat := match k with
    | 0 => 0
    | 1 => 1 / 100
    | 2 => 5000
    | 3 => 3000000                                                  -- frame beyond 2⁴⁴
    | _ => if q < 0 then -q else q
  (w, s)

/-- A random line style. -/
def randLine (s : UInt64) : LineStyle × UInt64 :=
  let (c, s) := rand s 3
  let (j, s) := rand s 3
  let (mk, s) := rand s 7
  let (dk, s) := rand s 12
  let (a, s) := randI s 0 20000000
  let (b, s) := randI s 0 20000000
  let (ph, s) := randI s (-30000000) 30000000
  let cap : LineCap := match c with | 0 => .butt | 1 => .round | _ => .square
  let jn : LineJoin := match j with | 0 => .miter | 1 => .round | _ => .bevel
  let ml : Int := match mk with
    | 0 => 1000000 | 1 => 1414214 | 2 => 4000000 | 3 => 10000000 | 4 => 100000000
    | 5 => 1000000000000 | _ => 0
  let fx := Content.Fixed.clamp
  let arr : List Content.Fixed := match dk with
    | 0 => [fx a]
    | 1 => [fx a, fx b]
    | 2 => [fx 0, fx b]
    | 3 => [fx a, fx 0, fx 0, fx b]
    | 4 => [fx 0, fx 0]
    | 5 => [fx a, fx (-1000000)]
    | 6 => [fx 1000, fx 1000]                                       -- beyond maxDashSteps
    | 7 => [fx a, fx b, fx (a / 3)]
    | _ => []
  ({ cap, join := jn, miterLimit := fx ml, dash := { array := arr, phase := fx ph } }, s)

/-- A random raster configuration. The dash budget is at most 1500 steps and the chords per
cubic at most 40 (the reference is slow; above the dash budget a path is stroked solid, which
is compared too). -/
def randCfg (s : UInt64) : Config × UInt64 :=
  let (k, s) := rand s 8
  let c : Config := match k with
    | 0 => { arcSegCap := 1 }
    | 1 => { arcSegCap := 4, tol := 1 }
    | 2 => { tol := 100 }
    | 3 => { coordLimit := 1048576 }
    | 4 => { maxDashSteps := 50 }
    | 5 => { curveSegCap := 3 }
    | _ => {}
  ({ c with maxDashSteps := min c.maxDashSteps 1500, curveSegCap := min c.curveSegCap 40 }, s)

/-- Field-by-field equality of two chord geometries. -/
def segEq (a b : SegG) : Bool :=
  a.p == b.p && a.q == b.q && a.d.x == b.d.x && a.d.y == b.d.y && a.len == b.len &&
    a.ax == b.ax && a.ay == b.ay && a.nx == b.nx && a.ny == b.ny && a.tx == b.tx &&
    a.ty == b.ty && a.smooth == b.smooth && a.lim == b.lim && a.small == b.small

/-- One chord-geometry case; `(failure, small)`. -/
def segCase (s : UInt64) : Option String × Bool × UInt64 :=
  let (m, s) := randMap s
  let (w, s) := randWidth s
  let (cfg, s) := randCfg s
  let (sc, s) := rand s 4
  let (p, s) := randPt s sc
  let (q, s) := randPt s sc
  let (tiny, s) := rand s 5
  let q := if tiny = 0 then ⟨p.x + 1, p.y⟩ else q
  let geo := Geo.make (m * Aff.scale subUnit subUnit) w cfg
  if p = q then (none, true, s) else
  let a := mkSeg geo.pen geo.metric p q (sc = 1)
  let b := mkSegSpec geo.pen geo.metric p q (sc = 1)
  if segEq a b then (none, a.small, s)
  else (some s!"mkSeg ({p.x},{p.y})→({q.x},{q.y}) w={w}: frame ({a.ax},{a.ay},{a.nx},{a.ny},{a.tx},{a.ty}) len {a.len} vs ({b.ax},{b.ay},{b.nx},{b.ny},{b.tx},{b.ty}) len {b.len}", a.small, s)

/-- One device-path case; `(failure, edges produced)`. -/
def pathCase (s : UInt64) : Option String × Bool × UInt64 :=
  let (sc, s) := rand s 10
  let scale := if sc < 3 then 0 else if sc < 8 then 1 else if sc < 9 then 2 else 3
  let (many, s) := rand s 8
  let (n, s) := if many = 0 then randI s 12 30 else randI s 1 8
  let (p, s) := randPath s n.toNat scale
  let (m, s) := randMap s
  let (w, s) := randWidth s
  let (line, s) := randLine s
  let (cfg, s) := randCfg s
  let geo := Geo.make (m * Aff.scale subUnit subUnit) w cfg
  let f := strokeDPath cfg geo line p
  let r := strokeDPathSpec cfg geo line p
  if f == r then (none, r.size > 0, s)
  else (some s!"device path ({p.size} segs, scale {scale}, w={w}, cap {repr line.cap}, join {repr line.join}): {f.size} vs {r.size} edges", r.size > 0, s)

/-- A random page point (raw `Fixed`, units 10⁻⁶ pt). -/
def randCPt (s : UInt64) : Content.Point × UInt64 :=
  let (x, s) := randI s (-50000000) 700000000
  let (y, s) := randI s (-50000000) 850000000
  (⟨Content.Fixed.clamp x, Content.Fixed.clamp y⟩, s)

/-- A random page path. -/
def randCPath (s : UInt64) (n : Nat) : Content.Path × UInt64 := Id.run do
  let mut s := s
  let (p0, s1) := randCPt s
  s := s1
  let mut out : Array Content.Segment := #[.moveTo p0]
  for _ in [0:n] do
    let (k, s1) := rand s 10
    s := s1
    let (p, s1) := randCPt s
    s := s1
    if k = 0 then out := out.push (.moveTo p)
    else if k = 1 then out := out.push .closePath
    else if k < 6 then out := out.push (.lineTo p)
    else
      let (c1, s1) := randCPt s
      let (c2, s2) := randCPt s1
      s := s2
      out := out.push (.curveTo c1 c2 p)
  return (⟨out⟩, s)

/-- A random CTM (`Fixed` entries). -/
def randCtm (s : UInt64) : Content.Matrix × UInt64 :=
  let (k, s) := rand s 6
  let (a, s) := randI s (-3000000) 3000000
  let (b, s) := randI s (-3000000) 3000000
  let (e, s) := randI s (-100000000) 100000000
  let fx := Content.Fixed.clamp
  let z := Content.Fixed.zero
  let m : Content.Matrix := match k with
    | 0 => Content.Matrix.identity
    | 1 => ⟨fx a, z, z, fx a, fx e, fx e⟩
    | 2 => ⟨fx a, z, z, fx b, z, fx e⟩                              -- non-uniform / reflecting
    | 3 => ⟨fx a, fx b, fx (-b), fx a, fx e, z⟩                     -- rotation and scale
    | 4 => ⟨fx a, fx b, fx (2 * a), fx (2 * b), z, z⟩               -- degenerate
    | _ => ⟨fx a, fx b, fx e, fx a, z, z⟩
  (m, s)

/-- A random view matrix (page → device pixels). -/
def randView (s : UInt64) : Aff × UInt64 :=
  let (z, s) := rand s 5
  let (r, s) := rand s 4
  let zoom : Rat := match z with | 0 => 1 | 1 => 3 / 2 | 2 => 2 | 3 => 1 / 3 | _ => 25 / 18
  let rot : Doc.Rotation := match r with | 0 => .r0 | 1 => .r90 | 2 => .r180 | _ => .r270
  (viewMatrix zoom rot ⟨0, 0, 612, 792⟩, s)

/-- One page-path case (with masks when `masks`); `(failure, edges produced)`. -/
def pageCase (s : UInt64) (masks : Bool) : Option String × Bool × UInt64 :=
  let (n, s) := randI s 1 6
  let (path, s) := randCPath s n.toNat
  let (ctm, s) := randCtm s
  let (view, s) := randView s
  let (line, s) := randLine s
  let (wk, s) := rand s 6
  let (wr, s) := randI s 0 8000000
  let width := Content.Fixed.clamp (if wk = 0 then 0 else wr)
  let (cfg, s) := randCfg s
  let style : Content.StrokeStyle :=
    { color := .gray Content.Comp.zero, alpha := Content.Comp.one,
      line := { line with width }, ctm }
  let f := strokeEdges view path style cfg
  let r := strokeEdgesSpec view path style cfg
  if f != r then
    (some s!"page path ({path.segs.size} segs): {f.size} vs {r.size} edges", r.size > 0, s)
  else if masks then
    let win : IRect := ⟨0, 0, 400, 400⟩
    let mf := strokePath view path style win cfg
    let mr := fillEdgesSpec r .nonzero win cfg
    if mf.x0 == mr.x0 && mf.y0 == mr.y0 && mf.w == mr.w && mf.h == mr.h && mf.data == mr.data
    then (none, r.size > 0, s)
    else (some s!"page path masks differ ({mf.w}×{mf.h} vs {mr.w}×{mr.h})", r.size > 0, s)
  else (none, r.size > 0, s)

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let report := fun (msg : String) => IO.println s!"  FAIL raster-stroke-spec: {msg}"
  let mut s : UInt64 := 20260722
  -- Chord geometry.
  let mut large := 0
  for _ in [0:4000] do
    let (res, small, s1) := segCase s
    s := s1
    if !small then large := large + 1
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 10 then report msg
  if large < 50 then
    failures := failures + 1; report s!"only {large} chords outside the 64-bit frame bound"
  -- Device paths.
  let mut painted := 0
  for _ in [0:3000] do
    let (res, p, s1) := pathCase s
    s := s1
    if p then painted := painted + 1
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 10 then report msg
  if painted < 2000 then
    failures := failures + 1; report s!"only {painted} of 3000 device paths produced edges"
  -- Page paths (masks for the first 300).
  let mut paintedP := 0
  for i in [0:1000] do
    let (res, p, s1) := pageCase s (i < 300)
    s := s1
    if p then paintedP := paintedP + 1
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 10 then report msg
  if paintedP < 500 then
    failures := failures + 1; report s!"only {paintedP} of 1000 page paths produced edges"
  return failures

end SafePdf.Tests.RasterStrokeSpec
