import SafePdf
import Tests.RasterGlyph
import Tests.RasterFillSpec

/-!
# Fixed-point glyph transform vs. the exact `Rat` path (task 7.2h)

Plan.md §6 Phase 7 (M7 speed criterion). `Raster.Glyph.outlineToDF` (64-bit fixed-point
glyph matrices, certified rounding, `Rat` fallback near rounding boundaries) must produce
exactly the device path of the reference `outlineToD` (every point through the exact
rational matrix); `runPath` exactly that of `runPathSpec`; and `columnGroups` must split a
run's path into groups whose fills partition the whole fill's coverage. Pseudo-random inputs
(fixed seed):

* **outlines** (3000 cases): random outlines (moves, lines, quadratics — also one before any
  move —, cubics, closes; 1–60 segments) with glyph coordinates that are integers (most fonts),
  arbitrary raw `Fixed` values (CFF fractions), or huge (beyond the 64-bit guard, `> 2³⁶` raw:
  fallback); glyph matrices composed like the renderer's — a font matrix (`1/1000`,
  `1/2048`, `1/unitsPerEm`, skewed CID matrices), the placement `[Tfs·Th 0 0 Tfs tx Trise]`
  with random sizes, `Tz`, rises and offsets, `Tm`, `CTM`, and the view (zooms, rotations) —
  plus matrices with **exact rounding ties** (`k/512` px per unit, translations on half
  subpixels: forces the fallback); several coordinate limits;
* **runs** (fixture pages, `Tests/fonts/` TrueType, Type 1 and CFF programs, 150 random
  content streams: sizes, `Tz`, `Tc`, `Tw`, `Ts`, `TJ` kerning, `Tm` with skew and rotation,
  `cm` scales): every glyph run's `runPath` equals `runPathSpec`, and the fills of its
  `columnGroups` are disjoint and sum to the whole fill, pixel by pixel.

Guards check that most matrices take the fixed-point path and that some groups split.
-/

namespace SafePdf.Tests.RasterGlyphSpec

open SafePdf.Core
open SafePdf.Core.Content
open SafePdf.Core.Raster
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Glyph
open SafePdf.Core.Font.Outline (Outline OSeg)
open SafePdf.Tests.RasterFillSpec (rand randI)

/-- A `Fixed` from a raw value (clamped). -/
def fx (r : Int) : Fixed := Fixed.clamp r

/-- A random glyph-space coordinate (raw `Fixed`): kind 0 integer units, 1 arbitrary raw,
2 huge. -/
def randCoord (s : UInt64) (kind : Nat) : Int × UInt64 :=
  match kind with
  | 0 => let (v, s) := randI s (-1500) 3000; (v * 1000000, s)
  | 1 => randI s (-1500000000) 3000000000
  | _ => randI s (-200000000000000) 200000000000000

/-- A random glyph point. -/
def randGPt (s : UInt64) (kind : Nat) : Point × UInt64 :=
  let (x, s) := randCoord s kind
  let (y, s) := randCoord s kind
  (⟨fx x, fx y⟩, s)

/-- A random outline of `n` segments (coordinate kind `kind`, sometimes mixed). -/
def randOutline (s : UInt64) (n kind : Nat) : Outline × UInt64 := Id.run do
  let mut s := s
  let mut out : Array OSeg := #[]
  let (first, s1) := rand s 10
  s := s1
  if first = 0 then
    let (c, s1) := randGPt s kind
    let (p, s2) := randGPt s1 kind
    s := s2
    out := out.push (.quadTo c p)
  let (p0, s1) := randGPt s kind
  s := s1
  out := out.push (.moveTo p0)
  for _ in [0:n] do
    let (k, s1) := rand s 12
    let (mix, s2) := rand s1 25
    s := s2
    let kd := if mix = 0 then 2 else kind
    let (a, s1) := randGPt s kd
    let (b, s2) := randGPt s1 kd
    let (c, s3) := randGPt s2 kd
    s := s3
    if k < 1 then out := out.push (.moveTo a)
    else if k < 2 then out := out.push .close
    else if k < 5 then out := out.push (.lineTo a)
    else if k < 8 then out := out.push (.quadTo a b)
    else out := out.push (.curveTo a b c)
  match Outline.ofArray out with
  | some o => return (o, s)
  | none => return (Outline.empty, s)

/-- A random rational with a small decimal or binary denominator. -/
def randQ (s : UInt64) (lo hi : Int) (den : Nat) : Rat × UInt64 :=
  let (v, s) := randI s (lo * den) (hi * den)
  ((v : Rat) / (den : Rat), s)

/-- A random font matrix (glyph → text space). -/
def randFont (s : UInt64) : Aff × UInt64 :=
  let (k, s) := rand s 6
  match k with
  | 0 => (Aff.scale (1 / 1000) (1 / 1000), s)
  | 1 => (Aff.scale (1 / 2048) (1 / 2048), s)
  | 2 => let (u, s) := randI s 16 16384; (Aff.scale (1 / (u : Rat)) (1 / (u : Rat)), s)
  | 3 =>
    let (c, s) := randQ s (-1) 1 1000000
    (⟨1 / 1000, 0, c / 1000, 1 / 1000, 0, 0⟩, s)
  | 4 =>
    let (a, s) := randQ s 0 1 1000000
    let (e, s) := randQ s (-1) 1 1000000
    (⟨a / 100 + 1 / 10000, 0, 0, a / 100 + 1 / 10000, e, 0⟩, s)
  | _ => (Aff.scale (1 / 1000) (1 / 1000), s)

/-- A random `Fixed`-valued rational (raw `/ 10⁶`) in `[lo, hi]`. -/
def randFx (s : UInt64) (lo hi : Int) : Rat × UInt64 := randQ s lo hi 1000000

/-- A random `Tm × CTM × view` (text space → device pixels). -/
def randRm (s : UInt64) : Aff × UInt64 := Id.run do
  let mut s := s
  let (a, s1) := randFx s (-2) 2
  let (b, s2) := randFx s1 (-1) 1
  let (c, s3) := randFx s2 (-1) 1
  let (d, s4) := randFx s3 (-2) 2
  let (e, s5) := randFx s4 0 600
  let (f, s6) := randFx s5 0 800
  s := s6
  let (k, s1) := rand s 4
  s := s1
  let tm : Aff := if k = 0 then ⟨a, b, c, d, e, f⟩ else ⟨1, 0, 0, 1, e, f⟩
  let (ca, s1) := randFx s (1 / 2) 3
  let (ce, s2) := randFx s1 (-50) 50
  s := s2
  let ctm : Aff := ⟨ca, 0, 0, ca, ce, ce⟩
  let zooms : List Rat := [1, 3 / 2, 2, 1 / 3, 4 / 3, 25 / 18, 300 / 72]
  let (zi, s1) := rand s zooms.length
  let (rot, s2) := rand s1 4
  s := s2
  let z := zooms.getD zi 1
  let view : Aff := match rot with
    | 0 => ⟨z, 0, 0, -z, 0, 792 * z⟩
    | 1 => ⟨0, z, z, 0, 0, 0⟩
    | 2 => ⟨-z, 0, 0, z, 612 * z, 0⟩
    | _ => ⟨0, -z, -z, 0, 792 * z, 612 * z⟩
  return (tm * ctm * view, s)

/-- A random glyph setting: font matrix, `rm`, placement at offset 0, offset `tx`. -/
def randSetting (s : UInt64) : (Aff × Aff × Aff × Rat) × UInt64 :=
  let (F, s) := randFont s
  let (rm, s) := randRm s
  let (tfs, s) := randFx s 1 40
  let (tz, s) := randFx s 50 150
  let (rise, s) := randFx s (-5) 5
  let (tx, s) := randFx s (-20) 900
  ((F, rm, ⟨tfs * tz / 100, 0, 0, tfs, 0, rise⟩, tx), s)

/-- A tie-heavy setting: `k/512` px per glyph unit (after the font matrix), translations on
half subpixels (offsets on `1/64` pt), so many exact values sit on rounding boundaries. -/
def tieSetting (s : UInt64) : (Aff × Aff × Aff × Rat) × UInt64 :=
  let (k, s) := randI s 1 64
  let (e, s) := randI s 0 200000
  let (f, s) := randI s 0 200000
  let (t, s) := randI s 0 4000
  ((Aff.scale (1 / 1000) (1 / 1000), ⟨1, 0, 0, 1, (e : Rat) / 512, (f : Rat) / 512⟩,
    ⟨(k : Rat) * 1000 / 512, 0, 0, (k : Rat) * 1000 / 512, 0, 0⟩, (t : Rat) / 64), s)

/-- One outline case: `(fast-path matrix?, equal?)`. -/
def outlineCase (lim : Int) (o : Outline) (set : Aff × Aff × Aff × Rat) : Bool × Bool :=
  let (F, rm, P0, tx) := set
  let P : Aff := { P0 with e := tx }
  let m := F * P * rm
  let spec := outlineToD lim m o
  let L := F * P0 * rm
  match GXf.ofAff? L with
  | some x =>
    let viaRat := outlineToDF lim x (x.off (L.e + tx * rm.a) (L.f + tx * rm.b)) (fun _ => m) o == spec
    -- the integer translation (`GTx`, as `glyphStepF` uses it) when it applies
    let viaInt := match (GTx.make? x L rm).bind fun t => GTx.at? x t (tx * 1000000).num with
      | some off => outlineToDF lim x off (fun _ => m) o == spec
      | none => true
    (true, viaRat && viaInt)
  | none => (false, true)

/-- Random content for a fixture font page (codes `A`–`C`). -/
def randContent (s : UInt64) : String × UInt64 := Id.run do
  let mut s := s
  let (sz, s1) := randI s 1 60
  let (tz, s2) := randI s1 40 160
  let (tc, s3) := randI s2 (-3) 5
  let (ts, s4) := randI s3 (-4) 4
  let (sk, s5) := randI s4 (-40) 40
  let (rot, s6) := rand s5 3
  let (cs, s7) := randI s6 1 30
  s := s7
  let (x, s1) := randI s 0 150
  let (y, s2) := randI s1 0 150
  let (k1, s3) := randI s2 (-300) 300
  let (n, s4) := rand s3 12
  s := s4
  let mut str := ""
  for _ in [0:n + 1] do
    let (c, s1) := rand s 3
    s := s1
    str := str.push (Char.ofNat (65 + c))
  let tm := match rot with
    | 0 => s!"1 0 0.{(sk.natAbs : Nat)} 1 {x} {y} Tm"
    | 1 => s!"0.8 0.6 -0.6 0.8 {x} {y} Tm"
    | _ => s!"1 0 0 1 {x} {y} Tm"
  return (s!"q 0.{cs} 0 0 0.{cs} 3 7 cm 10 0 0 10 0 0 cm BT /F1 {sz} Tf {tz} Tz {tc} Tc {ts} Ts 2 Tw {tm} [({str}) {k1} ({str}) ] TJ ET Q", s)

/-- Check one rendered page: every glyph run's fast path equals the reference, and the
column groups partition the fill. Returns `(runs, mismatches, groups split, group errors)`. -/
def pageCase (pdf : ByteArray) : Nat × Nat × Nat × Nat := Id.run do
  match Doc.openDoc {} pdf with
  | .error _ => return (0, 0, 0, 0)
  | .ok d =>
    match d.pages.toList with
    | [] => return (0, 0, 0, 0)
    | p :: _ =>
      match (Text.extractDocPage {} d p (Filter.Budget.init {})).1 with
      | .error _ => return (0, 0, 0, 0)
      | .ok pt =>
        let (srcs, _) := loadSources {} (Text.docSource {} d) (Filter.Budget.init {})
          (p.resources.getD [])
        let cfg : Fill.Config := {}
        let view := viewMatrix 1 (rotAdd p.rotate .r0) (Box.ofRect p.cropBox)
        let win : Fill.IRect := ⟨0, 0, 200, 200⟩
        let mut runs := 0
        let mut bad := 0
        let mut split := 0
        let mut gbad := 0
        for it in pt.items do
          match it with
          | .glyphRun r _ =>
            match srcs.get r.font with
            | none => pure ()
            | some gs =>
              let fi := pt.fonts.get r.font
              let fk := Text.fontKey r.font
              let a := (runPath cfg view fi fk gs r {}).1
              let b := (runPathSpec cfg view fi fk gs r {}).1
              runs := runs + 1
              if a != b then bad := bad + 1
              let groups := columnGroups a
              if groups.size > 1 then split := split + 1
              let whole := (Fill.fillEdgesCounted (Fill.flatten cfg win a) .nonzero win cfg).1
              let ms := groups.map fun g => (Fill.fillEdgesCounted (Fill.flatten cfg win g) .nonzero win cfg).1
              -- per pixel of the window: sum and count of nonzero group coverages
              let mut sum : Array Nat := Array.replicate (200 * 200) 0
              let mut cnt : Array Nat := Array.replicate (200 * 200) 0
              let mut ok := true
              for m in ms do
                for dy in [0:m.h] do
                  for dx in [0:m.w] do
                    let xx := m.x0 + (dx : Int)
                    let yy := m.y0 + (dy : Int)
                    let v := (m.get xx yy).toNat
                    if v != 0 then
                      if xx < 0 || yy < 0 || 200 ≤ xx || 200 ≤ yy then ok := false
                      else
                        let k := yy.toNat * 200 + xx.toNat
                        sum := sum.modify k (· + v)
                        cnt := cnt.modify k (· + 1)
              for k in [0:200 * 200] do
                let w := (whole.get ((k % 200 : Nat) : Int) ((k / 200 : Nat) : Int)).toNat
                if cnt.getD k 0 > 1 || sum.getD k 0 != w then ok := false
              if !ok then gbad := gbad + 1
          | _ => pure ()
        return (runs, bad, split, gbad)

/-- Run the suite; the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let mut s : UInt64 := 0x7215
  let mut nOut := 0
  let mut fast := 0
  let mut ties := 0
  for i in [0:3000] do
    let (n, s1) := rand s 60
    let (kind, s2) := rand s1 3
    let (o, s3) := randOutline s2 (n + 1) (if kind = 2 then 1 else kind)
    let tie := i % 5 = 4
    let (set, s4) := if tie then tieSetting s3 else randSetting s3
    let (li, s5) := rand s4 3
    s := s5
    let lim : Int := match li with
      | 0 => 1073741824
      | 1 => 1048576
      | _ => 200000
    let (f, ok) := outlineCase lim o set
    nOut := nOut + 1
    if f then fast := fast + 1
    if tie && f then ties := ties + 1
    if !ok then
      failures := failures + 1
      if failures ≤ 5 then IO.println s!"  FAIL raster-glyph-spec (outline {i}): fast path differs from outlineToD"
  if fast * 10 < nOut * 9 then
    failures := failures + 1
    IO.println s!"  FAIL raster-glyph-spec: only {fast} of {nOut} matrices on the fixed-point path"
  -- runs on fixture pages
  let ttf ← IO.FS.readBinFile "Tests/fonts/tiny.ttf"
  let t1 ← IO.FS.readBinFile "Tests/fonts/tiny.t1"
  let cff ← IO.FS.readBinFile "Tests/fonts/tiny.cff"
  let mut runs := 0
  let mut split := 0
  for i in [0:150] do
    let (c, s1) := randContent s
    s := s1
    let pdf := match i % 3 with
      | 0 => RasterGlyph.ttPage ttf c
      | 1 => RasterGlyph.t1Page t1 c
      | _ => RasterGlyph.cffPage cff c
    let (n, bad, sp, gbad) := pageCase pdf
    runs := runs + n
    split := split + sp
    if bad + gbad > 0 then
      failures := failures + 1
      if failures ≤ 5 then
        IO.println s!"  FAIL raster-glyph-spec (page {i}): {bad} runs differ, {gbad} group partitions wrong: {c}"
  if runs < 100 || split = 0 then
    failures := failures + 1
    IO.println s!"  FAIL raster-glyph-spec: {runs} runs checked, {split} split into groups"
  IO.println s!"  raster-glyph-spec: {nOut} outlines ({fast} fixed-point, {ties} tie-heavy), {runs} runs ({split} split), {failures} mismatches"
  return failures

end SafePdf.Tests.RasterGlyphSpec
