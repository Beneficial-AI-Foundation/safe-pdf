import SafePdf.Core.Raster.Clip

/-!
# Fast compositor vs. reference compositor (task 7.2e)

Plan.md §6 Phase 7 (compositing; M7 speed criterion). `Clip.composite` (row loops, `UInt32`
arithmetic, zero-coverage skip, opaque fast path) must produce exactly the bytes of the 7.2c
reference `Clip.compositeSpec … (covAt fm cm) …` (one pixel at a time through `blendPx`).
This suite compares the two on pseudo-random inputs (fixed seed):

* page widths/heights 1–24, buffers of exactly `4·W·H` bytes and, sometimes, odd sizes;
* fill masks and clip masks at random origins (also negative and off-page), random sizes,
  coverage bytes biased to 0 and 255, sometimes with a short data array;
* compositing rectangles: mostly covering the page (as `paintMask` passes), sometimes random
  (also empty, inverted, off-page);
* random colours and alphas (0, 255, random, and out-of-range values → reference fallback).
-/

namespace SafePdf.Tests.RasterComposite

open SafePdf.Core.Raster.Fill
open SafePdf.Core.Raster.Clip

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

/-- A coverage byte, biased: ⅓ zero, ⅓ full, ⅓ uniform. -/
def randCov (s : UInt64) : UInt8 × UInt64 :=
  let (k, s) := rand s 3
  if k = 0 then (0, s) else if k = 1 then (255, s) else
  let (v, s) := rand s 256
  (v.toUInt8, s)

/-- `n` bytes from `gen`. -/
def randBytes (gen : UInt64 → UInt8 × UInt64) (n : Nat) (s : UInt64) : ByteArray × UInt64 :=
  Id.run do
    let mut s := s
    let mut out := ByteArray.empty
    for _ in [0:n] do
      let (b, s') := gen s
      s := s'
      out := out.push b
    return (out, s)

/-- A random mask around a `W × H` page. -/
def randMask (W H : Nat) (s : UInt64) : Mask × UInt64 :=
  let (x0, s) := randI s (-4) ((W : Int) - 1)
  let (y0, s) := randI s (-4) ((H : Int) - 1)
  let (w, s) := rand s 20
  let (h, s) := rand s 20
  let (short, s) := rand s 8
  let n := if short = 0 then (w * h) / 2 else w * h
  let (data, s) := randBytes randCov n s
  ({ x0, y0, w, h, data }, s)

/-- A colour component: usually a byte, sometimes out of range. -/
def randComp (s : UInt64) : Nat × UInt64 :=
  let (k, s) := rand s 20
  if k = 0 then (256 + (s >>> 40).toNat % 300, next s) else rand s 256

/-- One comparison: `none` if equal, else a description; and whether the reference changed
the buffer at all. -/
def oneCase (s : UInt64) : Option String × Bool × UInt64 := Id.run do
  let (W, s) := rand s 24; let W := W + 1
  let (H, s) := rand s 24; let H := H + 1
  let (odd, s) := rand s 6
  let (delta, s) := rand s 7
  let size := if odd = 0 then 4 * W * H + delta - 3 else 4 * W * H
  let (b, s) := randBytes (fun s => let (v, s) := rand s 256; (v.toUInt8, s)) size s
  let (fm, s) := randMask W H s
  let (hasClip, s) := rand s 2
  let (cm0, s) := randMask W H s
  let cm := if hasClip = 0 then none else some cm0
  let (rx0, s) := randI s (-5) ((W : Int) + 5)
  let (ry0, s) := randI s (-5) ((H : Int) + 5)
  let (rx1, s) := randI s (-5) ((W : Int) + 5)
  let (ry1, s) := randI s (-5) ((H : Int) + 5)
  let (rk, s) := rand s 4
  let r : IRect :=
    if rk = 0 then ⟨rx0, ry0, rx1, ry1⟩ else ⟨min rx0 (-1), min ry0 (-1), (W : Int) + 2, (H : Int) + 2⟩
  let (cr, s) := randComp s
  let (cg, s) := randComp s
  let (cb, s) := randComp s
  let (ak, s) := rand s 5
  let (av, s) := rand s 256
  let alpha := if ak = 0 then 255 else if ak = 1 then 0 else if ak = 2 then 300 + av else av
  let fast := composite b W fm cm r (cr, cg, cb) alpha
  let spec := compositeSpec b W (covAt fm cm) r (cr, cg, cb) alpha
  let painted := spec.data != b.data
  if fast.data == spec.data then return (none, painted, s)
  return (some s!"W={W} H={H} size={size} fm=({fm.x0},{fm.y0},{fm.w},{fm.h},{fm.data.size}) clip={hasClip} r=({rx0},{ry0},{rx1},{ry1}) rgb=({cr},{cg},{cb}) alpha={alpha}", painted, s)

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  let mut s : UInt64 := 0x7e2e
  let mut painted := 0
  let n := 5000
  for _ in [0:n] do
    let (res, p, s') := oneCase s
    s := s'
    if p then painted := painted + 1
    if let some msg := res then
      failures := failures + 1
      if failures ≤ 5 then IO.println s!"  FAIL raster-composite: {msg}"
  -- The inputs must exercise compositing: at least a third of the cases change the page.
  if 3 * painted < n then
    failures := failures + 1
    IO.println s!"  FAIL raster-composite: only {painted} of {n} cases paint anything"
  IO.println s!"  raster-composite: {n} cases, {painted} painting, {failures} mismatches"
  return failures

end SafePdf.Tests.RasterComposite
