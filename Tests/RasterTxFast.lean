import SafePdf.Core.Raster.Transparency

/-!
# Fast transparency vs. the 7.3c reference (task 7.2g)

Plan.md §6 Phase 7 (transparency; M7 speed criterion). Task 7.2g restricts every layer's
combine pass to its dirty rectangle (the union of the bounds of what was painted into it,
`Painter.bound`, `Clip.itemBound`), gives item layers a reused, partially initialised scratch
buffer, and rewrites the per-pixel loops (`combineFast`, `lumLoop`, `alphaLoop`, `fillBuf`,
`solidBuf`). The 7.3c driver is kept as `Transparency.renderTxSpec`. This suite checks, on
pseudo-random inputs (fixed seed), that the bytes are identical:

* `combineFast` vs `combine`: random buffers (backdrop and layer equal on about half of the
  pixels), rectangles (also empty or off-page), alphas (also 0, 255 and > 255), all 16 blend
  modes, masks (also short) — 3000 cases;
* `renderTx` (with `Clip.itemBound` bounds, and without bounds) vs `renderTxSpec` on random
  scenes of 1–24 × 1–24 pixel pages: opaque and translucent fills with anti-aliased edges and
  clips, strokes, all blend modes, soft-mask references, groups (alpha, blend, soft mask;
  nested up to 11 deep, beyond `maxLayerDepth`; sometimes unbalanced; a third of them knockout
  groups, task 7.3i), soft-mask definitions (luminosity with a backdrop colour, alpha; nested)
  — 1500 scenes;
* task 7.9: every pixel of 1500 random strokes (widths 0–12 px, skewed CTMs, caps, joins,
  miter limits 1–30, dashes, curves) lies inside `Clip.strokeBound`; 1000 strokes through a
  stroke geometry table built from a translated copy of their style (`Stroke.strokePathT`)
  give `Stroke.strokePath`'s mask; `renderTx` vs
  `renderTxSpec` on 300 scenes of knockout groups with wide strokes on pages of up to 96 × 96
  pixels (lazy knockout frames `Transparency.knockL`, item bounds smaller than the page).
-/

namespace SafePdf.Tests.RasterTxFast

open SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill
open SafePdf.Core.Raster.Clip
open SafePdf.Core.Raster.Transparency
open SafePdf.Core.Content (FillRule Clip Color Comp DisplayItem Path BlendMode GroupInfo
  SoftMaskInfo FillStyle StrokeStyle)

/-- Linear congruential generator step (Knuth's MMIX constants, 64 bits). -/
def next (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A pseudo-random number in `[0, n)` and the next state. -/
def rand (s : UInt64) (n : Nat) : Nat × UInt64 :=
  let s := next s
  (if n = 0 then 0 else (s >>> 33).toNat % n, s)

/-- A pseudo-random integer in `[lo, hi]`. -/
def randI (s : UInt64) (lo hi : Int) : Int × UInt64 :=
  let (k, s) := rand s (hi - lo + 1).toNat
  (lo + k, s)

/-- `n` random bytes. -/
def randBytes (n : Nat) (s : UInt64) : ByteArray × UInt64 := Id.run do
  let mut s := s
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (b, s') := rand s 256
    s := s'
    out := out.push b.toUInt8
  return (out, s)

/-- All blend modes. -/
def modes : Array BlendMode :=
  #[.normal, .multiply, .screen, .overlay, .darken, .lighten, .colorDodge, .colorBurn,
    .hardLight, .softLight, .difference, .exclusion, .hue, .saturation, .color, .luminosity]

/-- A random blend mode (half of the time `Normal`). -/
def randMode (s : UInt64) : BlendMode × UInt64 :=
  let (k, s) := rand s 2
  if k = 0 then (.normal, s) else
  let (i, s) := rand s modes.size
  (modes[i]?.getD .normal, s)

/-! ## `combineFast` vs `combine` -/

/-- One `combine` comparison: `none` if equal, else a description. -/
def combineCase (s : UInt64) : Option String × UInt64 := Id.run do
  let (W, s) := rand s 16; let W := W + 1
  let (H, s) := rand s 16; let H := H + 1
  let (back, s) := randBytes (4 * W * H) s
  let (cur0, s) := randBytes (4 * W * H) s
  -- the layer equals the backdrop on about half of the pixels
  let mut cur := cur0
  let mut st := s
  for i in [0:W * H] do
    let (k, s') := rand st 2
    st := s'
    if k = 0 then
      for c in [0:4] do
        cur := setB cur (4 * i + c) (back[4 * i + c]?.getD 0)
  let s := st
  let (x0, s) := randI s (-3) (W + 2)
  let (y0, s) := randI s (-3) (H + 2)
  let (x1, s) := randI s (-3) (W + 3)
  let (y1, s) := randI s (-3) (H + 3)
  let (ak, s) := rand s 5
  let (av, s) := rand s 256
  let alpha := if ak = 0 then 0 else if ak = 1 then 255 else if ak = 2 then 300 else av
  let (m, s) := randMode s
  let (mk, s) := rand s 3
  let (short, s) := rand s 4
  let (mbytes, s) := randBytes (if short = 0 then W * H / 2 else W * H) s
  let fx : Fx := { alpha, blend := m, mask := if mk = 0 then none else some mbytes }
  let r : IRect := ⟨x0, y0, x1, y1⟩
  if combineFast W H r back cur fx == combine W H r back cur fx then (none, s)
  else (some s!"combine W={W} H={H} rect={repr r} alpha={alpha} mode={repr m}", s)

/-! ## Driver: `renderTx` vs `renderTxSpec` -/

/-- Renderer state. -/
structure TS where
  /-- Path renderer state. -/
  rs : Raster.Clip.RState
  /-- Transparency state. -/
  tx : TxState := {}

/-- The painter (page coordinates are device pixels); with `Clip.itemBound` bounds when
`bounded`. -/
def painter (W H : Nat) (bounded : Bool) : Painter TS where
  buf := (·.rs.buf)
  setBuf := fun s b => { s with rs := { s.rs with buf := b } }
  tx := (·.tx)
  setTx := fun s t => { s with tx := t }
  paint := fun s it => { s with rs := renderItem {} Aff.id W H defaultStroke s.rs it }
  bound := fun it => if bounded then some (itemBound {} Aff.id W H it) else none

/-- The page through the fast driver. -/
def renderFast (W H : Nat) (bounded : Bool) (items : Array DisplayItem) : ByteArray :=
  (items.foldl (renderTx (painter W H bounded) W H maxMaskDepth)
    { rs := { buf := whiteBuf W H } }).rs.buf

/-- The page through the reference driver. -/
def renderSpec (W H : Nat) (items : Array DisplayItem) : ByteArray :=
  (items.foldl (renderTxSpec (painter W H false) W H maxMaskDepth)
    { rs := { buf := whiteBuf W H } }).rs.buf

/-- A page-space point from thousandths of a pixel. -/
def ptm (x y : Int) : Content.Point := ⟨Content.Fixed.clamp (x * 1000), Content.Fixed.clamp (y * 1000)⟩

/-- A component `n / 100`. -/
def comp (n : Nat) : Comp :=
  Comp.ofFixed (Content.Fixed.div (Content.Fixed.ofInt n) (Content.Fixed.ofInt 100))

/-- A random polygon (rectangle or triangle, fractional coordinates) around a `W × H` page. -/
def randPath (W H : Nat) (s : UInt64) : Path × UInt64 :=
  let (x0, s) := randI s (-3000) (W * 1000 + 2000)
  let (y0, s) := randI s (-3000) (H * 1000 + 2000)
  let (w, s) := rand s (W * 700 + 2000)
  let (h, s) := rand s (H * 700 + 2000)
  let (tri, s) := rand s 3
  if tri = 0 then
    (⟨#[.moveTo (ptm x0 y0), .lineTo (ptm (x0 + w) (y0 + h / 3)), .lineTo (ptm (x0 + w / 2) (y0 + h)),
      .closePath]⟩, s)
  else
    (⟨#[.moveTo (ptm x0 y0), .lineTo (ptm (x0 + w) y0), .lineTo (ptm (x0 + w) (y0 + h)),
      .lineTo (ptm x0 (y0 + h)), .closePath]⟩, s)

/-- A random colour. -/
def randColor (s : UInt64) : Color × UInt64 :=
  let (k, s) := rand s 3
  let (r, s) := rand s 101
  let (g, s) := rand s 101
  let (b, s) := rand s 101
  if k = 0 then (.gray (comp r), s) else (.rgb (comp r) (comp g) (comp b), s)

/-- A random opacity: 1 (half of the time), 0.5, or random. -/
def randAlpha (s : UInt64) : Comp × UInt64 :=
  let (k, s) := rand s 4
  let (v, s) := rand s 101
  if k ≤ 1 then (Comp.one, s) else if k = 2 then (comp 50, s) else (comp v, s)

/-- A random soft-mask reference (mostly none). -/
def randSmask (s : UInt64) : Option Nat × UInt64 :=
  let (k, s) := rand s 5
  let (id, s) := rand s 4
  (if k = 0 then some id else none, s)

/-- A random painting item: fill (mostly) or stroke, sometimes clipped. -/
def randPaint (W H : Nat) (s : UInt64) : DisplayItem × UInt64 :=
  let (p, s) := randPath W H s
  let (color, s) := randColor s
  let (alpha, s) := randAlpha s
  let (blend, s) := randMode s
  let (smask, s) := randSmask s
  let (ck, s) := rand s 4
  let (cp, s) := randPath W H s
  let clip : Clip := if ck = 0 then [⟨cp, .nonzero⟩] else []
  let (k, s) := rand s 6
  if k = 0 then
    let lw : Content.Fixed := Content.Fixed.clamp 1500000
    let st : StrokeStyle :=
      { color := color, alpha := alpha, blend := blend, smask := smask, line := { width := lw },
        ctm := Content.Matrix.identity }
    (.strokePath p st clip, s)
  else (.fillPath p .nonzero { color, alpha, blend, smask } clip, s)

/-- A random scene of about `n` items; `fuel` bounds soft-mask nesting. -/
partial def randScene (W H : Nat) (fuel n : Nat) (s : UInt64) : Array DisplayItem × UInt64 := Id.run do
  let mut s := s
  let mut out : Array DisplayItem := #[]
  let mut depth := 0
  for _ in [0:n] do
    let (k, s1) := rand s 12
    s := s1
    if k ≤ 1 && depth < 11 then
      let (alpha, s1) := randAlpha s
      let (blend, s1) := randMode s1
      let (smask, s1) := randSmask s1
      let (ko, s1) := rand s1 3
      s := s1
      out := out.push (.groupBegin { alpha, blend, smask, knockout := ko = 0 })
      depth := depth + 1
    else if k = 2 then
      if depth > 0 then
        out := out.push .groupEnd
        depth := depth - 1
      else
        let (u, s1) := rand s 5
        s := s1
        if u = 0 then out := out.push .groupEnd
    else if k = 3 && fuel > 0 then
      let (id, s1) := rand s 4
      let (kind, s1) := rand s1 2
      let (bc, s1) := randColor s1
      let (m, s1) := rand s1 6
      let (items, s1) := randScene W H (fuel - 1) (m + 1) s1
      s := s1
      let info : SoftMaskInfo := { kind := if kind = 0 then .luminosity else .alpha, backdrop := bc }
      out := out.push (.softMask id info items)
    else
      let (it, s1) := randPaint W H s
      s := s1
      out := out.push it
  -- close the open groups (usually)
  let (u, s1) := rand s 4
  s := s1
  if u ≠ 0 then
    for _ in [0:depth] do out := out.push .groupEnd
  return (out, s)

/-- One scene comparison: `none` if equal, else a description; and whether the scene paints
inside a layer. -/
def sceneCase (s : UInt64) : Option String × Bool × UInt64 :=
  let (W, s) := rand s 24; let W := W + 1
  let (H, s) := rand s 24; let H := H + 1
  let (n, s) := rand s 14
  let (items, s) := randScene W H 2 (n + 1) s
  let spec := renderSpec W H items
  let fast := renderFast W H true items
  let slow := renderFast W H false items
  let layered := items.any fun it => match it with
    | .groupBegin _ | .softMask .. => true
    | .fillPath _ _ st _ => st.blend != .normal || st.smask.isSome
    | _ => false
  if fast == spec && slow == spec then (none, layered, s)
  else (some s!"scene W={W} H={H} items={items.size} bounded-equal={fast == spec} unbounded-equal={slow == spec}",
    layered, s)

/-! ## Stroke bounds and lazy knockout frames (task 7.9) -/

/-- A random open or closed polyline (2–7 points, any turn, sometimes a curve) over a `W × H`
page. -/
def randLine (W H : Nat) (s : UInt64) : Path × UInt64 := Id.run do
  let (n, s1) := rand s 6
  let (x, s1) := randI s1 0 (W * 1000)
  let (y, s1) := randI s1 0 (H * 1000)
  let mut s := s1
  let mut segs : Array Content.Segment := #[.moveTo (ptm x y)]
  for _ in [0:n + 1] do
    let (k, s1) := rand s 5
    let (x, s1) := randI s1 0 (W * 1000)
    let (y, s1) := randI s1 0 (H * 1000)
    let (cx, s1) := randI s1 0 (W * 1000)
    let (cy, s1) := randI s1 0 (H * 1000)
    s := s1
    segs := segs.push (if k = 0 then .curveTo (ptm cx cy) (ptm x y) (ptm x y) else .lineTo (ptm x y))
  let (c, s1) := rand s 3
  s := s1
  if c = 0 then segs := segs.push .closePath
  return (⟨segs⟩, s)

/-- A random stroke style: width 0–12 px, CTM scaled 0.2–3 and skewed (its translation never
matters), caps, joins, miter limits 1–30, sometimes dashed. -/
def randLineStyle (s : UInt64) : StrokeStyle × UInt64 :=
  let (w, s) := rand s 12001
  let (a, s) := randI s 200 3000
  let (d, s) := randI s 200 3000
  let (b, s) := randI s (-1500) 1500
  let (c, s) := randI s (-1500) 1500
  let (cap, s) := rand s 3
  let (join, s) := rand s 3
  let (ml, s) := randI s 1000 30000
  let (dk, s) := rand s 4
  let (dl, s) := randI s 500 6000
  let (color, s) := randColor s
  let (alpha, s) := randAlpha s
  let fx := fun (v : Int) => Content.Fixed.clamp (v * 1000)
  let line : Content.LineStyle :=
    { width := fx w, miterLimit := fx ml,
      cap := if cap = 0 then .butt else if cap = 1 then .round else .square,
      join := if join = 0 then .miter else if join = 1 then .round else .bevel,
      dash := if dk = 0 then { array := [fx dl, fx (dl / 2)] } else {} }
  ({ color, alpha, line, ctm := ⟨fx a, fx b, fx c, fx d, fx 17, fx (-5)⟩ }, s)

/-- One stroke: every pixel the stroker covers lies inside `Clip.strokeBound`. -/
def strokeBoundCase (s : UInt64) : Option String × UInt64 :=
  let W := 120
  let H := 100
  let (p, s) := randLine W H s
  let (st, s) := randLineStyle s
  let mk := Raster.Stroke.strokePath Aff.id p st (pageRect W H) {}
  let b := strokeBound {} Aff.id p st
  let out := (List.range mk.h).any fun j => (List.range mk.w).any fun i =>
    let x : Int := mk.x0 + i
    let y : Int := mk.y0 + j
    mk.get x y ≠ 0 && !(b.x0 ≤ x && x < b.x1 && b.y0 ≤ y && y < b.y1)
  if out then (some s!"stroke outside its bound: {repr st.line} bound {repr b}", s) else (none, s)

/-- A random scene for the lazy knockout frames: knockout groups (some translucent, some
nested, some unbalanced) of translucent and opaque wide strokes and fills on a page of up to
96 × 96 pixels, so that item bounds are much smaller than the page. -/
def randKScene (W H : Nat) (n : Nat) (s : UInt64) : Array DisplayItem × UInt64 := Id.run do
  let mut s := s
  let mut out : Array DisplayItem := #[]
  let mut depth := 0
  for _ in [0:n] do
    let (k, s1) := rand s 10
    s := s1
    if k ≤ 1 && depth < 6 then
      let (alpha, s1) := randAlpha s
      let (ko, s1) := rand s1 4
      s := s1
      out := out.push (.groupBegin { alpha, knockout := ko ≠ 0 })
      depth := depth + 1
    else if k = 2 && depth > 0 then
      out := out.push .groupEnd
      depth := depth - 1
    else if k ≤ 5 then
      let (p, s1) := randLine W H s
      let (st, s1) := randLineStyle s1
      let (ck, s1) := rand s1 4
      let (cp, s1) := randPath W H s1
      s := s1
      out := out.push (.strokePath p st (if ck = 0 then [⟨cp, .nonzero⟩] else []))
    else
      let (it, s1) := randPaint W H s
      s := s1
      out := out.push it
  for _ in [0:depth] do out := out.push .groupEnd
  return (out, s)

/-- One lazy-knockout scene: the fast driver (with bounds) equals the reference driver. -/
def kSceneCase (s : UInt64) : Option String × UInt64 :=
  let (W, s) := rand s 72; let W := W + 25
  let (H, s) := rand s 72; let H := H + 25
  let (n, s) := rand s 40
  let (items, s) := randKScene W H (n + 1) s
  if renderFast W H true items == renderSpec W H items then (none, s)
  else (some s!"knockout scene W={W} H={H} items={items.size}", s)

/-- Masks with the same rectangle and bytes. -/
def sameMask (a b : Mask) : Bool := a.x0 == b.x0 && a.y0 == b.y0 && a.w == b.w && a.h == b.h && a.data == b.data

/-- One stroke through a geometry table (`Stroke.strokePathT`) made from a translated copy of
its style and another style: the mask of `Stroke.strokePath`. -/
def geoTableCase (s : UInt64) : Option String × UInt64 :=
  let (p, s) := randLine 120 100 s
  let (st, s) := randLineStyle s
  let (other, s) := randLineStyle s
  let (dx, s) := randI s (-50000) 50000
  let moved : StrokeStyle :=
    { st with ctm := { st.ctm with e := Content.Fixed.clamp (dx * 1000), f := Content.Fixed.clamp (-dx * 300) } }
  let t : Raster.Stroke.GeoTable := ((({ view := Aff.id, cfg := {} } : Raster.Stroke.GeoTable).add other).add moved)
  let a := Raster.Stroke.strokePathT t Aff.id p st (pageRect 120 100) {}
  let b := Raster.Stroke.strokePath Aff.id p st (pageRect 120 100) {}
  if sameMask a b then (none, s) else (some s!"geometry table: {repr st.line}", s)

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let mut s : UInt64 := 0x72e7
  for _ in [0:3000] do
    let (res, s') := combineCase s
    s := s'
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 5 then IO.println s!"  FAIL raster-tx-fast: {msg}"
  let mut layered := 0
  let n := 1500
  for _ in [0:n] do
    let (res, l, s') := sceneCase s
    s := s'
    if l then layered := layered + 1
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 10 then IO.println s!"  FAIL raster-tx-fast: {msg}"
  -- The scenes must exercise layers.
  if 2 * layered < n then
    failures := failures + 1
    IO.println s!"  FAIL raster-tx-fast: only {layered} of {n} scenes use layers"
  -- task 7.9: stroke bounds, lazy knockout frames on larger pages
  for _ in [0:1500] do
    let (res, s') := strokeBoundCase s
    s := s'
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 10 then IO.println s!"  FAIL raster-tx-fast: {msg}"
  for _ in [0:1000] do
    let (res, s') := geoTableCase s
    s := s'
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 10 then IO.println s!"  FAIL raster-tx-fast: {msg}"
  for _ in [0:300] do
    let s0 := s
    let (res, s') := kSceneCase s
    s := s'
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 10 then IO.println s!"  FAIL raster-tx-fast: {msg} seed={s0}"
  IO.println s!"  raster-tx-fast: 3000 combine cases, {n} scenes ({layered} with layers), 1500 stroke bounds, 1000 geometry-table strokes, 300 knockout scenes, {failures} mismatches"
  return failures

end SafePdf.Tests.RasterTxFast
