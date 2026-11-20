import SafePdf.Core.Raster.Fill

/-!
# Fast scanline filler vs. reference filler (task 7.2f)

Plan.md §6 Phase 7 (scanline fill, M7 speed criterion). `Fill.fillEdgesCounted` (64-bit
active edges, insertion-sorted crossings carried across sample rows, one reused `UInt32`
accumulator) must produce exactly the mask — origin, size, every byte — and the counted work
of the 7.2a reference `Fill.fillEdgesCountedSpec`; `Fill.ofContentPath` (64-bit point mapping)
must produce exactly the device path of `Fill.ofContentPathSpec` (`Rat` per point). This suite
compares them on pseudo-random inputs (fixed seed):

* **paths** (4000 cases): random lines and cubics, several subpaths, often self-intersecting;
  1–8 segments, or 40–200 (many edges, exercising the insertion sort's swap budget and its
  `mergeSort` fallback); coordinate scales tiny (a few pixels), normal, large (`±2²⁹`
  subpixel units) and huge (beyond the fast-path guard, `±2³¹`: reference fallback); both fill
  rules; `vSamples` 0–20; flattening tolerances 1, 26, 100; clip windows random (also
  partial, off-path, empty and inverted);
* **raw edges** (1000 cases): edge arrays built directly, with windings in `−2 … 2` and some
  degenerate (`y0 ≥ y1`) edges;
* **point mapping** (3000 cases): view matrices (zooms 1, 3/2, 2, 1/3, 4/3, 25/18; all four
  rotations; integer and fractional boxes) and random matrices with small and large
  denominators, points with raw `Fixed` values up to `±10¹⁸`, several coordinate limits.

A guard checks that most fill cases paint something.
-/

namespace SafePdf.Tests.RasterFillSpec

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill

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

/-- A random device path of `n` segments at scale `sc` (mixing scales sometimes). -/
def randPath (s : UInt64) (n sc : Nat) : DPath × UInt64 := Id.run do
  let mut s := s
  let (p0, s1) := randPt s sc
  s := s1
  let mut out : DPath := #[.moveTo p0]
  for _ in [0:n] do
    let (k, s1) := rand s 16
    s := s1
    let (sc', s1) := rand s 20
    s := s1
    let scale := if sc' = 0 then 3 else sc
    let (p, s1) := randPt s scale
    s := s1
    if k < 2 then out := out.push (.moveTo p)
    else if k < 3 then out := out.push .closePath
    else if k < 10 then out := out.push (.lineTo p)
    else
      let (c1, s1) := randPt s scale
      let (c2, s2) := randPt s1 scale
      s := s2
      out := out.push (.curveTo c1 c2 p)
  return (out, s)

/-- A random clip window (pixels). -/
def randWin (s : UInt64) : IRect × UInt64 :=
  let (k, s) := rand s 10
  let (x0, s) := randI s (-10) 40
  let (y0, s) := randI s (-10) 40
  let (w, s) := randI s 0 150
  let (h, s) := randI s 0 150
  if k = 0 then (⟨x0, y0, x0 - w, y0 - h⟩, s)     -- inverted
  else if k = 1 then (⟨x0, y0, x0, y0 + h⟩, s)    -- empty
  else if k = 2 then (⟨-100, -100, 200, 200⟩, s)  -- larger than the normal range
  else (⟨x0, y0, x0 + w, y0 + h⟩, s)

/-- A random raster configuration. -/
def randCfg (s : UInt64) : Config × UInt64 :=
  let (v, s) := rand s 21
  let (t, s) := rand s 3
  ({ vSamples := v, tol := if t = 0 then 1 else if t = 1 then 26 else 100 }, s)

/-- Compare the fast and the reference rasterizer on `edges`. -/
def compare (edges : Array Edge) (rule : Content.FillRule) (win : IRect) (cfg : Config) :
    Option String × Bool :=
  let f := fillEdgesCounted edges rule win cfg
  let r := fillEdgesCountedSpec edges rule win cfg
  let painted := r.1.total > 0
  if f.1.x0 == r.1.x0 && f.1.y0 == r.1.y0 && f.1.w == r.1.w && f.1.h == r.1.h &&
      f.1.data == r.1.data && f.2 == r.2 then (none, painted)
  else
    (some s!"{edges.size} edges, win ({win.x0},{win.y0},{win.x1},{win.y1}), S={cfg.vSamples}: fast ({f.1.x0},{f.1.y0},{f.1.w}×{f.1.h}, total {f.1.total}, steps {f.2}) vs spec ({r.1.x0},{r.1.y0},{r.1.w}×{r.1.h}, total {r.1.total}, steps {r.2})", painted)

/-- One random path case. -/
def pathCase (s : UInt64) : Option String × Bool × UInt64 :=
  let (sc, s) := rand s 10
  let scale := if sc < 3 then 0 else if sc < 8 then 1 else if sc < 9 then 2 else 3
  let (many, s) := rand s 6
  let (n, s) := if many = 0 then randI s 40 200 else randI s 1 8
  let (p, s) := randPath s n.toNat scale
  let (win, s) := randWin s
  let (cfg, s) := randCfg s
  let (r, s) := rand s 2
  let rule : Content.FillRule := if r = 0 then .nonzero else .evenOdd
  let (res, painted) := compare (flatten cfg win p) rule win cfg
  (res, painted, s)

/-- Did a path case take the fast path? (Recomputes the case's guard.) -/
def pathFast (s : UInt64) : Bool :=
  let (sc, s) := rand s 10
  let scale := if sc < 3 then 0 else if sc < 8 then 1 else if sc < 9 then 2 else 3
  let (many, s) := rand s 6
  let (n, s) := if many = 0 then randI s 40 200 else randI s 1 8
  let (p, s) := randPath s n.toNat scale
  let (win, s) := randWin s
  let (cfg, _) := randCfg s
  let es := (flatten cfg win p).mergeSort (fun a b => a.y0 ≤ b.y0)
  fastOK es (maskRect es win)

/-- `sortAct` on `n` edges in strictly decreasing crossing order (far beyond the swap
budget, so the `mergeSort` fallback runs): the result is sorted and keeps every edge. -/
def sortFallbackOK (n : Nat) : Bool :=
  let a : Array AEdge := (Array.range n).map fun i =>
    { x0 := 0, y0 := 0, y1 := 1, dx := 0, dy := 1, wind := 1,
      cx := (n - i : Nat).toInt64, on := true }
  let r := sortAct a
  r.size == n && sortedFrom r r.size 0 Int64.minValue &&
    (r.foldl (fun acc e => acc + e.cx.toInt) 0) == ((n * (n + 1) / 2 : Nat) : Int)

/-- One random raw-edge case (windings `−2 … 2`, some degenerate edges). -/
def edgeCase (s : UInt64) : Option String × Bool × UInt64 := Id.run do
  let mut s := s
  let (n, s1) := randI s 0 60
  s := s1
  let mut es : Array Edge := #[]
  for _ in [0:n.toNat] do
    let (x0, s1) := randI s (-20 * 256) (140 * 256)
    let (y0, s2) := randI s1 (-20 * 256) (140 * 256)
    let (x1, s3) := randI s2 (-20 * 256) (140 * 256)
    let (dy, s4) := randI s3 (-300) (60 * 256)
    let (wk, s5) := rand s4 12
    s := s5
    let wind : Int := if wk < 5 then 1 else if wk < 10 then -1 else if wk = 10 then 2 else 0
    es := es.push ⟨x0, y0, x1, y0 + dy, wind⟩
  let (win, s1) := randWin s
  let (cfg, s2) := randCfg s1
  let (r, s3) := rand s2 2
  let rule : Content.FillRule := if r = 0 then .nonzero else .evenOdd
  let (res, painted) := compare es rule win cfg
  return (res, painted, s3)

/-- A random rational with a small or (rarely) a large denominator. -/
def randRat (s : UInt64) (big : Bool) (mag : Int) : Rat × UInt64 :=
  let (n, s) := randI s (-mag) mag
  let (d, s) := if big then randI s 1 1000000007 else randI s 1 8
  ((n : Rat) / (d : Rat), s)

/-- A random page → device matrix. -/
def randAff (s : UInt64) : Aff × UInt64 :=
  let (k, s) := rand s 4
  if k < 2 then
    let zs : Array Rat := #[1, 3 / 2, 2, 1 / 3, 4 / 3, 25 / 18]
    let (zi, s) := rand s zs.size
    let (ri, s) := rand s 4
    let rot : Doc.Rotation := if ri = 0 then .r0 else if ri = 1 then .r90 else
      if ri = 2 then .r180 else .r270
    let (llx, s) := randRat s false 2000
    let (lly, s) := randRat s false 2000
    let (urx, s) := randRat s false 20000
    let (ury, s) := randRat s false 20000
    (viewMatrix (zs.getD zi 1) rot ⟨llx, lly, urx, ury⟩, s)
  else
    let big := k = 3
    let (a, s) := randRat s big 40
    let (b, s) := randRat s big 40
    let (c, s) := randRat s big 40
    let (d, s) := randRat s big 40
    let (e, s) := randRat s big 5000
    let (f, s) := randRat s big 5000
    (⟨a, b, c, d, e, f⟩, s)

/-- A random content point (raw `Fixed` values; mostly page-sized, sometimes enormous). -/
def randCPt (s : UInt64) : Content.Point × UInt64 :=
  let (k, s) := rand s 10
  let mag : Int := if k < 7 then 1000000000 else if k < 9 then 1000000000000 else
    1000000000000000000
  let (x, s) := randI s (-mag) mag
  let (y, s) := randI s (-mag) mag
  (⟨Content.Fixed.clamp x, Content.Fixed.clamp y⟩, s)

/-- One random point-mapping case: a path of 1–6 segments through a random matrix. -/
def mapCase (s : UInt64) : Option String × UInt64 := Id.run do
  let (m, s) := randAff s
  let mut s := s
  let (n, s1) := randI s 1 6
  s := s1
  let mut segs : Array Content.Segment := #[]
  for _ in [0:n.toNat] do
    let (k, s1) := rand s 4
    let (p, s2) := randCPt s1
    let (c1, s3) := randCPt s2
    let (c2, s4) := randCPt s3
    s := s4
    segs := segs.push (if k = 0 then .moveTo p else if k = 1 then .lineTo p else
      if k = 2 then .curveTo c1 c2 p else .closePath)
  let (lk, s1) := rand s 3
  s := s1
  let cfg : Config := { coordLimit := if lk = 0 then 1000 else Limits.default.coordLimit }
  let path : Content.Path := ⟨segs⟩
  if ofContentPath m path cfg == ofContentPathSpec m path cfg then return (none, s)
  return (some s!"matrix {repr m}, path {repr path}", s)

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let mut s : UInt64 := 0x72f
  let mut painted := 0
  let nPath := 4000
  let nEdge := 1000
  let nMap := 3000
  let mut fast := 0
  for _ in [0:nPath] do
    if pathFast s then fast := fast + 1
    let (res, p, s') := pathCase s
    s := s'
    if p then painted := painted + 1
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 5 then IO.println s!"  FAIL raster-fill-spec (path): {msg}"
  for _ in [0:nEdge] do
    let (res, p, s') := edgeCase s
    s := s'
    if p then painted := painted + 1
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 5 then IO.println s!"  FAIL raster-fill-spec (edges): {msg}"
  let mut mapFast := 0
  for _ in [0:nMap] do
    if (IAff.ofAff? (randAff s).1).isSome then mapFast := mapFast + 1
    let (res, s') := mapCase s
    s := s'
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 5 then IO.println s!"  FAIL raster-fill-spec (mapping): {msg}"
  -- The inputs must exercise the filler: at least half of the fill cases paint something.
  if 2 * painted < nPath + nEdge then
    failures := failures + 1
    IO.println s!"  FAIL raster-fill-spec: only {painted} of {nPath + nEdge} fill cases paint"
  -- Both sides of each guard must be exercised.
  if 2 * fast < nPath || fast == nPath then
    failures := failures + 1
    IO.println s!"  FAIL raster-fill-spec: {fast} of {nPath} path cases on the fast path"
  if 3 * mapFast < nMap || mapFast == nMap then
    failures := failures + 1
    IO.println s!"  FAIL raster-fill-spec: {mapFast} of {nMap} matrices on the 64-bit path"
  if !(sortFallbackOK 0 && sortFallbackOK 1 && sortFallbackOK 2 && sortFallbackOK 500) then
    failures := failures + 1
    IO.println "  FAIL raster-fill-spec: sortAct fallback"
  IO.println s!"  raster-fill-spec: {nPath} paths ({fast} fast) + {nEdge} edge sets ({painted} painting), {nMap} mappings ({mapFast} 64-bit), {failures} mismatches"
  return failures

end SafePdf.Tests.RasterFillSpec
