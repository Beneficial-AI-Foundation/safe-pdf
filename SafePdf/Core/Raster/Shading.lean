import SafePdf.Core.Raster.Clip
import SafePdf.Core.Content.Run

/-!
# Shadings: PDF functions, smooth shadings and shading patterns (task 7.3d)

Plan.md §6 Phase 7 ("shadings"; "Proven: totality, resource bounds"), §4 **S3**.
ISO 32000-2 §7.10 (functions: types 0, 2, 3, 4), §8.7.4 (shadings: `sh`, shading
dictionaries, types 1–7), §8.7.3 (shading patterns, `PatternType 2`).

## Functions (§7.10)

`Fn` is a parsed function; `Fn.eval f xs n` always returns exactly `n` outputs
(`Fn.eval_length`). Arithmetic is exact over `ℚ`, rounded to a `2⁻²⁴` grid and saturated to
`±2⁴⁰` after each step (`qd`), so numbers stay small.

* **Type 0 (sampled)**: `/Size`, `/BitsPerSample` (1, 2, 4, 8, 12, 16, 24, 32), `/Encode`,
  `/Decode`, `/Domain`, `/Range`; samples read big-endian, MSB first, rows not padded; short
  data reads as zeros. At most `maxFnInputs` (8) inputs and `maxFnSamples` (2²⁰) sample
  values (local caps). Interpolation is **multilinear** (`/Order 3` cubic is treated as
  linear — documented degradation).
* **Type 2 (exponential)**: `C0 + xᴺ (C1 − C0)`; an integral `N` is exact (repeated
  multiplication), a non-integral `N` uses `2^(N · log₂ x)` in 30-bit fixed point
  (`log2Q`/`exp2Q`, error ≈ 2⁻²⁵ relative).
* **Type 3 (stitching)**: `/Functions`, `/Bounds`, `/Encode`; parsing is bounded by a depth
  (`maxFnDepth` 8) and a node budget (`maxFnNodes` 256) — a wide, deep tree cannot make
  loading exponential; evaluation recurses on a depth fuel.
* **Type 4 (PostScript calculator)**: a **bounded interpreter** of the full operator set of
  §7.10.5 (arithmetic incl. `sqrt`, `sin`, `cos`, `atan`, `exp`, `ln`, `log` via the
  fixed-point routines above; relational, boolean and bitwise operators; `if`/`ifelse`;
  `copy`, `dup`, `exch`, `index`, `pop`, `roll`). Program text ≤ `maxPSBytes` (64 KiB),
  block nesting ≤ `maxPSNest` (100), operand stack ≤ 100 entries; a program has no loops, so
  every operator executes at most once (`psExec` recurses on a fuel equal to the token
  count). Any error (stack under/overflow, type error) makes the evaluation return the
  domain-clipped inputs' default: all outputs 0.
* An array of functions (`/Function [f₁ … fₙ]` in a shading) is `Fn.arr`: the outputs are
  the first output of each.

## Shadings (§8.7.4)

`loadShading` parses a shading dictionary/stream into a `Prepared` shading:

* **Colour space** (`ShadeCS`): `Run.csInfo` (the interpreter's resolution, as images), plus
  for `Separation`/`DeviceN` the **tint transform parsed with `Fn`** (any function type), so
  spot-colour gradients render in their alternate space. `Pattern` is rejected.
* **Types 2 (axial) and 3 (radial)** are rendered **per device pixel** (`axialRow`,
  `radialRow`): the device → shading map is inverted exactly once; per row the start is
  evaluated exactly, per pixel the parameter advances by rounded fixed-point steps (as
  `Image.place`), in machine integers (`Int64`, values clamped so nothing overflows).
  Axial: `s` = the projection onto the axis (2²⁴ fixed point). Radial: the two-circle
  equation `|p − c(s)| = r(s)` is solved per pixel in **normalised integer units** (the
  visited window and both circles scaled to ≤ 2¹³ units, so every intermediate is < 2⁶⁰),
  with an integer Newton square root seeded by the previous pixel's root (`isqrtFrom`;
  `Nat.sqrt` at each row start); the larger root with `r(s) ≥ 0` wins
  (§8.7.4.5.4), `/Extend` admits `s < 0` / `s > 1`. The colour comes from a **256-entry
  lookup table** (`lut`, as MuPDF) over `s ∈ [0, 1]` built once per shading (`/Domain`
  `[t0 t1]` mapped). Edges are not anti-aliased.
* **Type 1 (function-based)**: the function is sampled on a 65 × 65 grid over `/Domain`
  (as MuPDF's `FUNSEGS` 64), mapped by `/Matrix`, and drawn as Gouraud-shaded triangles.
* **Types 4–7 (meshes)**: vertices decoded with `/BitsPerCoordinate`, `/BitsPerComponent`,
  `/BitsPerFlag` and `/Decode` (bits read continuously, no per-vertex padding, as MuPDF);
  type 4 edge flags 0/1/2, type 5 `/VerticesPerRow` lattices, types 6/7 patches with edge
  flags 0–3 (Coons patches get their interior tensor points from §8.7.4.5.7's formula); every
  patch is evaluated on an **8 × 8 grid** (MuPDF subdivides 3 levels = 8 × 8) and drawn as
  128 **Gouraud-shaded triangles** (corner colours bilinear). With a `/Function`, vertices
  carry `t` and colours come from the lookup table per pixel. At most `maxMeshVertices`
  (2¹⁶) vertices / `maxPatches` (4096) patches per shading.
* **`/BBox`** is applied as one more clip path (in shading space); **`/Background`** is
  ignored by `sh` (§8.7.4.5.1) and painted under the shading for patterns.

Triangles are rasterised by pixel-centre edge functions in 1/256-pixel integer coordinates
(`triRow`); a page's mesh painting visits at most `maxMeshVisits` pixels in total (larger
triangles beyond the budget are skipped), so `paint_steps_le` bounds every shading by
`W · H + maxMeshVisits` pixel visits.

## Shading patterns (§8.7.3)

`renderFill` paints a `fillPath` item whose colour is `Color.pattern n` with shading pattern
`n` (`PatternType 2`: `/Shading`, `/Matrix`): fill mask ∩ clip ∩ the shading's `/BBox`, the
`/Background` first, then the shading. `renderStroke` does the same through the stroke mask
of a `strokePath` item, and `Glyph` through the glyph masks of a text run (task 7.3f). The
pattern is the one the runner recorded (`FillStyle.pattern`/`StrokeStyle.pattern`: the
resource's `ResRef`, so a form's own `/Pattern` resources are found) and its matrix is
composed with the use's **base matrix** (`pattern /Matrix × base`, base = the CTM at the
start of the using page or form: §8.7.3 maps pattern space to the default space of the page
or form in which the pattern is used). Tiling patterns (`PatternType 1`) and unknown names
fall back to the path renderer (mid-grey).

## Wiring into `Glyph.renderPage`

`loadShadings limits src s res items : ShadingTable × σ` loads every `sh` resource and every
pattern used by a fill, stroke or glyph-run colour once, by the `ResRef` the runner recorded
(`res`: the page's resources, for unannotated items), including items inside soft masks
(`DisplayList.foldDeep`). `renderShading cfg m W H tbl st r name ctm alpha clip` paints an
`sh` item with its `ca` (`renderShading_size`, `renderShading_steps_le`); `renderFill` /
`renderStroke` paint `fillPath`/`strokePath` items, delegating non-pattern colours to
`Clip.renderItem` (`renderFill_size`, `renderStroke_size`).
-/

namespace SafePdf.Core.Raster.Shading

open SafePdf SafePdf.Core
open SafePdf.Core.Raster.Geom
open SafePdf.Core.Raster.Fill (IRect Mask Config)
open SafePdf.Core.Content (Fixed Comp Color DeviceSpace Source FillStyle FillRule Matrix Clip
  ClipPath Path DisplayItem DisplayList ResRef PatternUse)
open SafePdf.Core.Content.Run (CSInfo)

/-! ## 1. Numbers -/

/-- The rounding grid of function arithmetic: `2²⁴`. -/
def qScale : Int := 16777216

/-- Saturation bound of function arithmetic: `2⁴⁰`. -/
def qMax : Rat := 1099511627776

/-- Saturate to `±qMax` and round to the `2⁻²⁴` grid (halves up). -/
def qd (x : Rat) : Rat :=
  let x := if qMax < x then qMax else if x < -qMax then -qMax else x
  (((x * (qScale : Rat) + 1 / 2).floor : Int) : Rat) / (qScale : Rat)

/-- Clamp `x` into `[lo, hi]` (`lo` wins if the interval is empty). -/
def clampR (lo hi x : Rat) : Rat := if x < lo then lo else if hi < x then hi else x

/-- Linear interpolation of `x` from `[x0, x1]` to `[y0, y1]` (`y0` when `x0 = x1`). -/
def interp (x x0 x1 y0 y1 : Rat) : Rat :=
  if x1 = x0 then y0 else qd (y0 + (x - x0) * (y1 - y0) / (x1 - x0))

/-- `x ^ n` for a natural `n` by square-and-multiply, rounded after every product
(`n ≤ 2¹⁶` steps through the bit length). -/
def powNat (x : Rat) (n : Nat) : Rat :=
  go 17 x n 1
where
  /-- Square-and-multiply over the low `fuel` bits of `n`. -/
  go : Nat → Rat → Nat → Rat → Rat
    | 0, _, _, acc => acc
    | fuel + 1, b, n, acc =>
      if n = 0 then acc
      else go fuel (qd (b * b)) (n / 2) (if n % 2 = 1 then qd (acc * b) else acc)

/-- One in 30-bit fixed point. -/
def f30 : Nat := 1073741824

/-- `2^(2^-k)` in 30-bit fixed point for `k = 1 … 30` (repeated square roots of 2). -/
def exp2Consts : Array Nat :=
  (List.range 30).foldl (fun (acc : Array Nat × Nat) _ =>
    let c := Nat.sqrt (acc.2 * f30)
    (acc.1.push c, c)) (#[], 2 * f30) |>.1

/-- `log₂ x` for `x > 0` with 30 fractional bits (bit-by-bit squaring of the mantissa);
`-64` for `x ≤ 2⁻³⁰`. -/
def log2Q (x : Rat) : Rat :=
  let X : Int := (x * (f30 : Rat)).floor
  if X ≤ 0 then -64 else
  let Xn := X.toNat
  let e := Nat.log2 Xn
  let m0 : Nat := if 30 ≤ e then Xn >>> (e - 30) else Xn <<< (30 - e)
  let r := (List.range 30).foldl (fun (acc : Nat × Nat) _ =>
    let sq := acc.1 * acc.1 / f30
    if 2 * f30 ≤ sq then (sq / 2, 2 * acc.2 + 1) else (sq, 2 * acc.2)) (m0, 0)
  ((e : Int) - 30 : Int) + (r.2 : Rat) / (f30 : Rat)

/-- `2^y` with 30-bit precision (integer part clamped to `[-64, 40]`). -/
def exp2Q (y : Rat) : Rat :=
  let n : Int := y.floor
  let n := if n < -64 then -64 else if 40 < n then 40 else n
  let fr := clampR 0 1 (y - n)
  let F : Nat := (fr * (f30 : Rat)).floor.toNat
  let r := (List.range 30).foldl (fun (acc : Nat) k =>
    if (F >>> (29 - k)) % 2 = 1 then acc * exp2Consts.getD k f30 / f30 else acc) f30
  let p : Rat := if 0 ≤ n then ((2 ^ n.toNat : Nat) : Rat) else 1 / ((2 ^ (-n).toNat : Nat) : Rat)
  qd ((r : Rat) / (f30 : Rat) * p)

/-- `x ^ y`: exact for integral `y` (negative: reciprocal), else `2^(y log₂ x)` for `x > 0`;
`0` for a non-integral power of `x ≤ 0` and for `0` to a negative power. -/
def rpow (x y : Rat) : Rat :=
  if y.den = 1 then
    if 0 ≤ y.num then powNat x (min y.num.toNat 65536)
    else let p := powNat x (min (-y.num).toNat 65536); if p = 0 then 0 else qd (1 / p)
  else if x ≤ 0 then 0
  else exp2Q (y * log2Q x)

/-- `√x` with 24 fractional bits (`0` for `x ≤ 0`). -/
def sqrtQ (x : Rat) : Rat :=
  if x ≤ 0 then 0 else
  ((Nat.sqrt (x * (2 ^ 48 : Nat)).floor.toNat : Nat) : Rat) / ((2 ^ 24 : Nat) : Rat)

/-- `π` to 20 digits. -/
def piQ : Rat := 314159265358979323846 / 100000000000000000000

/-- `ln 2` to 20 digits. -/
def ln2Q : Rat := 69314718055994530942 / 100000000000000000000

/-- `log₁₀ 2` to 20 digits. -/
def log10_2Q : Rat := 30102999566398119521 / 100000000000000000000

/-- Sum of `n` Taylor terms `t₀ + t₁ + …` with `t_{k+1} = t_k · q / ((2k + a)(2k + a + 1))`
(sine: `a = 2`, `t₀ = r`, `q = −r²`; cosine: `a = 1`, `t₀ = 1`). -/
def taylor (q : Rat) (a : Nat) : Nat → Nat → Rat → Rat → Rat
  | 0, _, _, acc => acc
  | n + 1, k, t, acc =>
    let t' := qd (t * q / (((2 * k + a) * (2 * k + a + 1) : Nat) : Rat))
    taylor q a n (k + 1) t' (acc + t')

/-- Reduce an angle in degrees to radians in `[-π, π]`. -/
def radOfDeg (d : Rat) : Rat :=
  let k : Int := ((d + 180) / 360).floor
  qd ((d - 360 * k - 180 + 180) * piQ / 180 - (if 180 < d - 360 * k then 2 * piQ else 0))

/-- `sin` of an angle in degrees (20 Taylor terms after reduction to `[-π, π]`). -/
def sinDeg (d : Rat) : Rat := let r := radOfDeg d; qd (taylor (-(r * r)) 2 20 0 r r)

/-- `cos` of an angle in degrees. -/
def cosDeg (d : Rat) : Rat := let r := radOfDeg d; qd (taylor (-(r * r)) 1 20 0 1 1)

/-- `atan z` (radians) for any `z`: one half-angle reduction then 30 series terms
(`|z| ≤ 1`), else `±π/2 − atan(1/z)`. -/
def atanQ (z : Rat) : Rat :=
  let core := fun (z : Rat) =>
    let h := qd (z / (1 + sqrtQ (1 + z * z)))
    let h2 := qd (h * h)
    let s := (List.range 30).foldl (fun (acc : Rat × Rat) k =>
      (acc.1 + acc.2 / ((2 * k + 1 : Nat) : Rat), qd (-(acc.2 * h2)))) (0, h)
    2 * s.1
  if z.num.natAbs ≤ z.den then qd (core z)
  else qd ((if 0 < z then piQ / 2 else -piQ / 2) - core (1 / z))

/-- PostScript `atan num den`: the angle in degrees in `[0, 360)`. -/
def atan2Deg (num den : Rat) : Rat :=
  let a : Rat :=
    if den = 0 then (if 0 < num then piQ / 2 else if num < 0 then -piQ / 2 else 0)
    else
      let b := atanQ (num / den)
      if 0 < den then b else if 0 ≤ num then b + piQ else b - piQ
  let d := qd (a * 180 / piQ)
  if d < 0 then d + 360 else d

/-- A `Fixed` as `ℚ`. -/
def ofFx (x : Fixed) : Rat := Fixed.toRat x

/-- `ℚ` → `Fixed`, rounded to 10⁻⁶ and saturated. -/
def toFx (q : Rat) : Fixed := Fixed.clamp ((q * 1000000 + 1 / 2).floor)

/-! ## 2. The PostScript calculator (§7.10.5) -/

/-- A PostScript calculator operand. -/
inductive PSVal where
  /-- A number (integers and reals alike; `cvi`/`idiv`/… truncate). -/
  | num (q : Rat)
  /-- A boolean. -/
  | bool (b : Bool)
  deriving Inhabited, BEq

/-- A parsed calculator program. -/
inductive PSOp where
  /-- Push a number. -/
  | num (q : Rat)
  /-- Push a boolean (`true`, `false`). -/
  | bool (b : Bool)
  /-- An operator, by name. -/
  | op (name : String)
  /-- `{ … } if`. -/
  | ifp (t : List PSOp)
  /-- `{ … } { … } ifelse`. -/
  | ifelse (t e : List PSOp)
  deriving Inhabited

/-- A calculator token. -/
inductive PSTok where
  /-- `{`. -/
  | lb
  /-- `}`. -/
  | rb
  /-- A number. -/
  | num (q : Rat)
  /-- An operator name. -/
  | word (w : String)
  deriving Inhabited, BEq

/-- Maximum calculator program size in bytes (local cap). -/
def maxPSBytes : Nat := 65536

/-- Maximum `{ }` nesting of a calculator program (local cap). -/
def maxPSNest : Nat := 100

/-- Maximum operand stack depth (§7.10.5: 100). -/
def maxPSStack : Nat := 100

/-- Is `b` a PostScript delimiter or whitespace? -/
def psDelim (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 13 || b == 12 || b == 0 || b == 123 || b == 125 ||
  b == 37 || b == 40 || b == 41 || b == 60 || b == 62 || b == 91 || b == 93 || b == 47

/-- Parse a number word (`[+-]digits[.digits]`, also `.5`, `5.`; exponents are not allowed
in the calculator). -/
def psNumber (w : List Char) : Option Rat :=
  let (neg, w) := match w with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ip := w.takeWhile Char.isDigit
  let rest := w.drop ip.length
  let (fp, rest) := match rest with
    | '.' :: r => let f := r.takeWhile Char.isDigit; (f, r.drop f.length)
    | r => ([], r)
  if !rest.isEmpty || (ip.isEmpty && fp.isEmpty) then none else
  let digits := fun (cs : List Char) => cs.foldl (fun n c => 10 * n + (c.toNat - 48)) 0
  let v : Rat := ((digits ip : Nat) : Rat) + ((digits fp : Nat) : Rat) / ((10 ^ fp.length : Nat) : Rat)
  some (if neg then -v else v)

/-- Tokenize a calculator program (fuel: one step per byte). -/
def psTokens (b : ByteArray) : (fuel i : Nat) → List PSTok → List PSTok
  | 0, _, acc => acc.reverse
  | fuel + 1, i, acc =>
    match b[i]? with
    | none => acc.reverse
    | some c =>
      if c == 123 then psTokens b fuel (i + 1) (.lb :: acc)
      else if c == 125 then psTokens b fuel (i + 1) (.rb :: acc)
      else if c == 37 then
        -- comment: skip to end of line
        let j := (List.range (b.size - i)).find? (fun k => b[i + k]? == some 10 || b[i + k]? == some 13)
        psTokens b fuel (i + (j.getD (b.size - i))) acc
      else if psDelim c then psTokens b fuel (i + 1) acc
      else
        let n := ((List.range (b.size - i)).find? (fun k => match b[i + k]? with
          | some d => psDelim d
          | none => true)).getD (b.size - i)
        let w : List Char := ((List.range n).map fun k => Char.ofNat (b[i + k]?.getD 0).toNat)
        let tok : PSTok := match psNumber w with
          | some q => .num q
          | none => .word (String.ofList w)
        psTokens b fuel (i + max n 1) (tok :: acc)

/-- Parse a token sequence up to its closing `}` into a program (fuel: one step per token;
`nest`: remaining nesting depth). Returns the program and the tokens after the `}`. -/
def psParse : (fuel nest : Nat) → List PSTok → List PSOp → Option (List PSOp × List PSTok)
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | fuel + 1, nest, t :: ts, acc =>
    match t with
    | .rb => some (acc.reverse, ts)
    | .num q => psParse fuel nest ts (.num q :: acc)
    | .word "true" => psParse fuel nest ts (.bool true :: acc)
    | .word "false" => psParse fuel nest ts (.bool false :: acc)
    | .word w => psParse fuel nest ts (.op w :: acc)
    | .lb =>
      match nest with
      | 0 => none
      | nest' + 1 =>
        match psParse fuel nest' ts [] with
        | none => none
        | some (b1, .word "if" :: rest) => psParse fuel nest rest (.ifp b1 :: acc)
        | some (b1, .lb :: rest) =>
          match psParse fuel nest' rest [] with
          | some (b2, .word "ifelse" :: rest2) => psParse fuel nest rest2 (.ifelse b1 b2 :: acc)
          | _ => none
        | some _ => none

/-- Parse a whole calculator program `{ … }`. -/
def psProgram (b : ByteArray) : Option (List PSOp) :=
  if maxPSBytes < b.size then none else
  let toks := psTokens b (b.size + 1) 0 []
  match toks with
  | .lb :: rest =>
    match psParse (toks.length + 1) maxPSNest rest [] with
    | some (p, _) => some p
    | none => none
  | _ => none

/-- Truncate toward zero. -/
def truncQ (q : Rat) : Int := if q < 0 then -((-q).floor) else q.floor

/-- Apply a unary numeric operator. -/
def psUnary (name : String) (x : Rat) : Option Rat :=
  match name with
  | "abs" => some (if x < 0 then -x else x)
  | "neg" => some (-x)
  | "ceiling" => some (x.ceil : Rat)
  | "floor" => some (x.floor : Rat)
  | "round" => some ((x + 1 / 2).floor : Rat)
  | "truncate" => some (truncQ x : Rat)
  | "cvi" => some (truncQ x : Rat)
  | "cvr" => some x
  | "sqrt" => if x < 0 then none else some (sqrtQ x)
  | "sin" => some (sinDeg x)
  | "cos" => some (cosDeg x)
  | "ln" => if x ≤ 0 then none else some (qd (log2Q x * ln2Q))
  | "log" => if x ≤ 0 then none else some (qd (log2Q x * log10_2Q))
  | _ => none

/-- Apply a binary numeric operator (`x` below `y` on the stack). -/
def psBinary (name : String) (x y : Rat) : Option PSVal :=
  match name with
  | "add" => some (.num (qd (x + y)))
  | "sub" => some (.num (qd (x - y)))
  | "mul" => some (.num (qd (x * y)))
  | "div" => if y = 0 then none else some (.num (qd (x / y)))
  | "idiv" =>
    let a := truncQ x; let b := truncQ y
    if b = 0 then none else some (.num (Int.tdiv a b : Rat))
  | "mod" =>
    let a := truncQ x; let b := truncQ y
    if b = 0 then none else some (.num (Int.tmod a b : Rat))
  | "exp" => some (.num (rpow x y))
  | "atan" => if x = 0 ∧ y = 0 then none else some (.num (atan2Deg x y))
  | "bitshift" =>
    let a := truncQ x; let s := truncQ y
    if 31 < s.natAbs then some (.num 0)
    else some (.num (if 0 ≤ s then ((a <<< s.toNat : Int) : Rat) else ((a >>> (-s).toNat : Int) : Rat)))
  | "eq" => some (.bool (x = y))
  | "ne" => some (.bool (x ≠ y))
  | "gt" => some (.bool (y < x))
  | "ge" => some (.bool (y ≤ x))
  | "lt" => some (.bool (x < y))
  | "le" => some (.bool (x ≤ y))
  | _ => none

/-- Bitwise `and`/`or`/`xor` on integers. -/
def psBits (name : String) (a b : Int) : Option Int :=
  let toN := fun (i : Int) => (i % 4294967296).toNat
  let r : Option Nat := match name with
    | "and" => some (toN a &&& toN b)
    | "or" => some (toN a ||| toN b)
    | "xor" => some (toN a ^^^ toN b)
    | _ => none
  r.map fun n => if n < 2147483648 then (n : Int) else (n : Int) - 4294967296

/-- `n j roll` on a stack (top first): rotate the top `n` elements by `j` positions. -/
def psRoll (st : List PSVal) (n : Nat) (j : Int) : List PSVal :=
  if n = 0 then st else
  let top := st.take n
  let k := (j % (n : Int)).toNat
  -- positive j moves elements toward the top: the top `k` elements go below the rest
  (top.drop k ++ top.take k) ++ st.drop n

/-- Execute one operator on the stack (top first). `none`: error. -/
def psStep (name : String) (st : List PSVal) : Option (List PSVal) :=
  match name, st with
  | "dup", v :: r => some (v :: v :: r)
  | "pop", _ :: r => some r
  | "exch", a :: b :: r => some (b :: a :: r)
  | "index", .num n :: r =>
    let i := truncQ n
    if 0 ≤ i ∧ i.toNat < r.length then (r[i.toNat]?).map (· :: r) else none
  | "copy", .num n :: r =>
    let i := truncQ n
    if 0 ≤ i ∧ i.toNat ≤ r.length then some (r.take i.toNat ++ r) else none
  | "roll", .num j :: .num n :: r =>
    let k := truncQ n
    if 0 ≤ k ∧ k.toNat ≤ r.length then some (psRoll r k.toNat (truncQ j)) else none
  | "not", .bool b :: r => some (.bool (!b) :: r)
  | "not", .num n :: r => some (.num (((truncQ n).toNat ^^^ 4294967295 : Nat) : Rat) :: r)
  | "and", .bool b :: .bool a :: r => some (.bool (a && b) :: r)
  | "or", .bool b :: .bool a :: r => some (.bool (a || b) :: r)
  | "xor", .bool b :: .bool a :: r => some (.bool (a ^^ b) :: r)
  | "and", .num b :: .num a :: r => (psBits "and" (truncQ a) (truncQ b)).map fun i => .num (i : Rat) :: r
  | "or", .num b :: .num a :: r => (psBits "or" (truncQ a) (truncQ b)).map fun i => .num (i : Rat) :: r
  | "xor", .num b :: .num a :: r => (psBits "xor" (truncQ a) (truncQ b)).map fun i => .num (i : Rat) :: r
  | "eq", .bool b :: .bool a :: r => some (.bool (a == b) :: r)
  | "ne", .bool b :: .bool a :: r => some (.bool (a != b) :: r)
  | n, .num y :: .num x :: r =>
    match psUnary n y with
    | some v => some (.num v :: .num x :: r)
    | none => (psBinary n x y).map (· :: r)
  | n, .num x :: r => (psUnary n x).map fun v => .num v :: r
  | _, _ => none

/-- Run a program on a stack. Recursion on `fuel` (each call consumes one unit; the program
has no loops, so `fuel` = its token count suffices); `none` on any error or when the stack
exceeds `maxPSStack`. -/
def psExec : (fuel : Nat) → List PSOp → List PSVal → Option (List PSVal)
  | _, [], st => some st
  | 0, _ :: _, _ => none
  | fuel + 1, o :: rest, st =>
    if maxPSStack < st.length then none else
    match o with
    | .num q => psExec fuel rest (.num q :: st)
    | .bool b => psExec fuel rest (.bool b :: st)
    | .op name =>
      match psStep name st with
      | some st' => psExec fuel rest st'
      | none => none
    | .ifp t =>
      match st with
      | .bool true :: r =>
        match psExec fuel t r with
        | some st' => psExec fuel rest st'
        | none => none
      | .bool false :: r => psExec fuel rest r
      | _ => none
    | .ifelse t e =>
      match st with
      | .bool c :: r =>
        match psExec fuel (if c then t else e) r with
        | some st' => psExec fuel rest st'
        | none => none
      | _ => none

/-- Number of operations in a program (nested blocks included): the fuel `psExec` needs. -/
def psSize : List PSOp → Nat
  | [] => 0
  | .ifp t :: r => 1 + psSize t + psSize r
  | .ifelse t e :: r => 1 + psSize t + psSize e + psSize r
  | _ :: r => 1 + psSize r

/-! ## 3. Functions (§7.10) -/

/-- A parsed PDF function. Domains and ranges are `(min, max)` pairs. -/
inductive Fn where
  /-- Type 0: domain, range, `/Size`, bits per sample, encode, decode, raw samples
  (`Π size · n` of them, last index varying slowest). -/
  | sampled (domain range : List (Rat × Rat)) (size : List Nat) (bps : Nat)
      (encode decode : List (Rat × Rat)) (samples : Array Nat)
  /-- Type 2: domain, optional range, `C0`, `C1`, `N`. -/
  | exp (domain : Rat × Rat) (range : Option (List (Rat × Rat))) (c0 c1 : List Rat) (n : Rat)
  /-- Type 3: domain, optional range, sub-functions, bounds, encode pairs. -/
  | stitch (domain : Rat × Rat) (range : Option (List (Rat × Rat))) (fns : List Fn)
      (bounds : List Rat) (encode : List (Rat × Rat))
  /-- Type 4: domain, range, program. -/
  | ps (domain range : List (Rat × Rat)) (prog : List PSOp)
  /-- An array of 1-output functions; output `i` is the first output of function `i`. -/
  | arr (fns : List Fn)
  deriving Inhabited

/-- Maximum nesting of stitching functions (local cap). -/
def maxFnDepth : Nat := 8

/-- Maximum number of function nodes parsed for one shading (local cap). -/
def maxFnNodes : Nat := 256

/-- Maximum number of inputs of a sampled function (local cap; `2^m` corners per value). -/
def maxFnInputs : Nat := 8

/-- Maximum number of sample values of a sampled function (local cap). -/
def maxFnSamples : Nat := 1 <<< 20

/-- Clip a list of values to a list of ranges (values beyond the ranges are kept). -/
def clipTo (rng : List (Rat × Rat)) (xs : List Rat) : List Rat :=
  xs.zipIdx.map fun (x, i) =>
    match rng[i]? with
    | some (lo, hi) => clampR lo hi x
    | none => x

/-- Pad with zeros or truncate to exactly `n` values. -/
def fit (n : Nat) (xs : List Rat) : List Rat := (xs ++ List.replicate n 0).take n

/-- `fit` returns exactly `n` values. -/
theorem fit_length (n : Nat) (xs : List Rat) : (fit n xs).length = n := by
  simp [fit]

/-- Strides of a sampled function's sample array (first input varies fastest), times `n`. -/
def strides (size : List Nat) (n : Nat) : List Nat :=
  (size.foldl (fun (acc : List Nat × Nat) s => (acc.2 :: acc.1, acc.2 * s)) ([], n)).1.reverse

/-- Evaluate a sampled function (multilinear interpolation). -/
def sampledEval (domain range : List (Rat × Rat)) (size : List Nat) (bps : Nat)
    (encode decode : List (Rat × Rat)) (samples : Array Nat) (xs : List Rat) : List Rat :=
  let n := range.length
  let m := size.length
  let maxS : Rat := ((2 ^ bps - 1 : Nat) : Rat)
  -- encoded, clipped input coordinates: (floor index, fraction) per input
  let cs : List (Nat × Rat × Nat) := (List.range m).map fun i =>
    let x := xs.getD i 0
    let (d0, d1) := domain.getD i (0, 1)
    let sz := size.getD i 1
    let (e0, e1) := encode.getD i (0, ((sz - 1 : Nat) : Rat))
    let e := clampR 0 ((sz - 1 : Nat) : Rat) (interp (clampR d0 d1 x) d0 d1 e0 e1)
    let k : Nat := e.floor.toNat
    let k := if sz ≤ k + 1 then sz - 1 else k
    (k, e - (k : Rat), sz)
  let st := strides size n
  let corners := List.range (2 ^ m)
  let outs := (List.range n).map fun j =>
    let v := corners.foldl (fun (acc : Rat) c =>
      let wi := (List.range m).foldl (fun (a : Rat × Nat) i =>
        let (k, f, sz) := cs.getD i (0, 0, 1)
        let bit := (c >>> i) % 2 = 1
        let w := if bit then f else 1 - f
        let idx := if bit then min (k + 1) (sz - 1) else k
        (a.1 * w, a.2 + idx * st.getD i 0)) (1, 0)
      if wi.1 = 0 then acc else acc + wi.1 * ((samples[wi.2 + j]?.getD 0 : Nat) : Rat)) 0
    let (d0, d1) := decode.getD j (range.getD j (0, 1))
    interp (qd v) 0 maxS d0 d1
  clipTo range outs

/-- The stitching sub-function index of `x`: the number of bounds `≤ x` (the last subdomain
is closed). -/
def stitchIndex (bounds : List Rat) (x : Rat) : Nat :=
  (bounds.filter (· ≤ x)).length

/-- Evaluate a function with a nesting fuel (`[]` when the fuel runs out). -/
def Fn.evalD : Nat → Fn → List Rat → List Rat
  | 0, _, _ => []
  | d + 1, f, xs =>
    match f with
    | .sampled dom rng size bps enc dec smp => sampledEval dom rng size bps enc dec smp xs
    | .exp (d0, d1) rng c0 c1 n =>
      let x := clampR d0 d1 (xs.headD 0)
      let p := rpow x n
      let out := (c0.zip c1).map fun (a, b) => qd (a + p * (b - a))
      match rng with
      | some r => clipTo r out
      | none => out
    | .stitch (d0, d1) rng fns bounds enc =>
      let x := clampR d0 d1 (xs.headD 0)
      let k := stitchIndex bounds x
      let lo := if k = 0 then d0 else bounds.getD (k - 1) d0
      let hi := if k < bounds.length then bounds.getD k d1 else d1
      let (e0, e1) := enc.getD k (0, 1)
      let x' := interp x lo hi e0 e1
      let out := match fns[k]? with
        | some g => Fn.evalD d g [x']
        | none => []
      match rng with
      | some r => clipTo r out
      | none => out
    | .ps dom rng prog =>
      let ins := clipTo dom (fit dom.length xs)
      match psExec (psSize prog + 1) prog (ins.map PSVal.num).reverse with
      | some st =>
        let outs := (st.take rng.length).reverse.map fun v => match v with
          | .num q => q
          | .bool b => if b then 1 else 0
        if outs.length = rng.length then clipTo rng outs else List.replicate rng.length 0
      | none => List.replicate rng.length 0
    | .arr fns => fns.map fun g => (Fn.evalD d g xs).headD 0

/-- **Evaluate a function**: exactly `n` outputs (`Fn.eval_length`), nesting bounded by
`maxFnDepth`. -/
def Fn.eval (f : Fn) (xs : List Rat) (n : Nat) : List Rat := fit n (Fn.evalD (maxFnDepth + 1) f xs)

/-- **Function evaluation is total with a fixed output size.** -/
theorem Fn.eval_length (f : Fn) (xs : List Rat) (n : Nat) : (f.eval xs n).length = n :=
  fit_length n _

/-- The input domain of a function's first input (for lookup tables). -/
def Fn.domain0 : Fn → Rat × Rat
  | .sampled dom .. => dom.headD (0, 1)
  | .exp dom .. => dom
  | .stitch dom .. => dom
  | .ps dom .. => dom.headD (0, 1)
  | .arr _ => (0, 1)

/-! ## 4. Reading objects -/

/-- A number as `ℚ`. -/
def numQ (o : PdfObject) : Option Rat := (Content.Interp.num? o).map ofFx

/-- Entry `k` of `d`, resolved one level. -/
def ent {σ : Type} (src : Source σ) (s : σ) (d : Dict) (k : String) : Option PdfObject × σ :=
  match Dict.get? d (Content.Run.nm k) with
  | none => (none, s)
  | some o => let r := Content.Run.resolve src s o; (some r.1, r.2)

/-- A numeric array entry (elements must be direct numbers). -/
def numsQ (o : Option PdfObject) : Option (List Rat) :=
  match o with
  | some (.array xs) => xs.mapM numQ
  | _ => none

/-- Consecutive pairs of a list (`[a, b, c, d] ↦ [(a, b), (c, d)]`). -/
def pairs : List Rat → List (Rat × Rat)
  | a :: b :: r => (a, b) :: pairs r
  | _ => []

/-- A natural-number entry. -/
def natQ (o : Option PdfObject) : Option Nat :=
  match o with
  | some o => Content.Interp.nat? o
  | none => none

/-- The dictionary of an object and, for a stream, its object number and the stream. -/
def fetchBody {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) :
    Option (Dict × Option (Nat × Stream)) × σ :=
  match o with
  | .ref n g =>
    match src.fetch s n g with
    | (.ok (.obj (.dict d)), s) => (some (d, none), s)
    | (.ok (.stream st), s) => (some (st.dict, some (n, st)), s)
    | (_, s) => (none, s)
  | .dict d => (some (d, none), s)
  | _ => (none, s)

/-- The decoded data of a stream body (`none` for dictionaries or failed decodes). -/
def bodyData {σ : Type} (src : Source σ) (s : σ) : Option (Nat × Stream) → Option ByteArray × σ
  | some (n, st) =>
    match src.decode s n st with
    | (.ok b, s) => (some b, s)
    | (.error _, s) => (none, s)
  | none => (none, s)

/-- Read `n ≤ 32` bits, most significant first, from bit `pos` (missing bytes read as 0). -/
def readBits (b : ByteArray) (pos n : Nat) : Nat :=
  if pos % 8 = 0 ∧ n = 8 then (b[pos / 8]?.getD 0).toNat
  else
    (List.range n).foldl (fun acc k =>
      let p := pos + k
      2 * acc + ((b[p / 8]?.getD 0).toNat >>> (7 - p % 8)) % 2) 0

/-- Valid bits per sample of a sampled function. -/
def validBps (b : Nat) : Bool := [1, 2, 4, 8, 12, 16, 24, 32].contains b

/-- Parse a function object (types 0, 2, 3, 4; an array is `Fn.arr`) with a nesting fuel
`depth` and a node budget (returned decremented by the nodes parsed). -/
def parseFn {σ : Type} (src : Source σ) : (depth budget : Nat) → σ → PdfObject → Option Fn × Nat × σ
  | 0, b, s, _ => (none, b, s)
  | depth + 1, b, s, o =>
    if b = 0 then (none, 0, s) else
    let b := b - 1
    let (ro, s) := match o with
      | .ref .. => (Content.Run.resolve src s o)
      | o => (o, s)
    match ro with
    | .array xs =>
      let r := xs.foldl (fun (acc : Option (List Fn) × Nat × σ) x =>
        match acc.1 with
        | none => acc
        | some fs =>
          match parseFn src depth acc.2.1 acc.2.2 x with
          | (some f, b, s) => (some (f :: fs), b, s)
          | (none, b, s) => (none, b, s)) (some [], b, s)
      (r.1.map fun fs => .arr fs.reverse, r.2)
    | _ =>
    let (body, s) := fetchBody src s o
    match body with
    | none => (none, b, s)
    | some (d, stm) =>
      let (ty, s) := ent src s d "FunctionType"
      let (dom, s) := ent src s d "Domain"
      let (rng, s) := ent src s d "Range"
      let domain := pairs ((numsQ dom).getD [])
      let range := pairs ((numsQ rng).getD [])
      match natQ ty with
      | some 0 =>
        let (sz, s) := ent src s d "Size"
        let (bp, s) := ent src s d "BitsPerSample"
        let (en, s) := ent src s d "Encode"
        let (de, s) := ent src s d "Decode"
        let size : List Nat := match sz with
          | some (.array xs) => (xs.mapM Content.Interp.nat?).getD []
          | _ => []
        let bps := (natQ bp).getD 0
        let m := size.length
        let n := range.length
        let total := size.foldl (· * ·) 1 * n
        if m = 0 ∨ maxFnInputs < m ∨ n = 0 ∨ m ≠ domain.length ∨ size.any (· = 0) ∨
            maxFnSamples < total ∨ !validBps bps then (none, b, s) else
        let (data, s) := bodyData src s stm
        match data with
        | none => (none, b, s)
        | some data =>
          let smp := (Array.range total).map fun i => readBits data (i * bps) bps
          (some (.sampled domain range size bps (pairs ((numsQ en).getD []))
            (pairs ((numsQ de).getD [])) smp), b, s)
      | some 2 =>
        let (c0, s) := ent src s d "C0"
        let (c1, s) := ent src s d "C1"
        let (nn, s) := ent src s d "N"
        match nn.bind numQ with
        | none => (none, b, s)
        | some n =>
          let c0 := (numsQ c0).getD [0]
          let c1 := (numsQ c1).getD [1]
          if c0.length ≠ c1.length then (none, b, s) else
          (some (.exp (domain.headD (0, 1)) (if range.isEmpty then none else some range) c0 c1 n),
            b, s)
      | some 3 =>
        let (fs, s) := ent src s d "Functions"
        let (bd, s) := ent src s d "Bounds"
        let (en, s) := ent src s d "Encode"
        match fs with
        | some (.array xs) =>
          let r := xs.foldl (fun (acc : Option (List Fn) × Nat × σ) x =>
            match acc.1 with
            | none => acc
            | some fs =>
              match parseFn src depth acc.2.1 acc.2.2 x with
              | (some f, b, s) => (some (f :: fs), b, s)
              | (none, b, s) => (none, b, s)) (some [], b, s)
          match r.1 with
          | none => (none, r.2)
          | some fns =>
            let bounds := (numsQ bd).getD []
            if bounds.length + 1 ≠ fns.length then (none, r.2) else
            (some (.stitch (domain.headD (0, 1)) (if range.isEmpty then none else some range)
              fns.reverse bounds (pairs ((numsQ en).getD []))), r.2)
        | _ => (none, b, s)
      | some 4 =>
        let (data, s) := bodyData src s stm
        match data.bind psProgram with
        | some prog =>
          if domain.isEmpty ∨ range.isEmpty then (none, b, s)
          else (some (.ps domain range prog), b, s)
        | none => (none, b, s)
      | _ => (none, b, s)

/-- Parse a function with the default caps. -/
def loadFn {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) : Option Fn × σ :=
  let r := parseFn src (maxFnDepth + 1) maxFnNodes s o
  (r.1, r.2.2)

/-! ## 5. Colour spaces -/

/-- A shading's colour space: the interpreter's resolution and, for `Separation`/`DeviceN`,
the tint transform and alternate space. -/
structure ShadeCS where
  /-- Resolved space. -/
  info : CSInfo
  /-- Number of colour components. -/
  n : Nat
  /-- Tint transform and alternate device space. -/
  tint : Option (Fn × DeviceSpace) := none

/-- Number of components of a resolved space (`0` for `Pattern`). -/
def csComps : CSInfo → Nat
  | .dev d _ => d.nComps
  | .pattern => 0
  | .indexed .. => 1
  | .separation .. => 1
  | .deviceN n _ => n
  | .lab => 3

/-- RGB bytes of the components `xs`. -/
def ShadeCS.rgb (cs : ShadeCS) (xs : List Rat) : Nat × Nat × Nat :=
  match cs.tint with
  | some (f, alt) =>
    match Content.Interp.deviceColor alt ((f.eval xs alt.nComps).map toFx) with
    | some c => Clip.deviceRGB c
    | none => (0, 0, 0)
  | none => Clip.deviceRGB (cs.info.color ((fit cs.n xs).map toFx))

/-- Resolve a shading's `/ColorSpace` (`Pattern` and unknown spaces: `none`). -/
def loadCS {σ : Type} (src : Source σ) (s : σ) (o : PdfObject) : Option ShadeCS × σ :=
  match Content.Run.csInfo src s o with
  | (none, s) => (none, s)
  | (some .pattern, s) => (none, s)
  | (some info, s) =>
    let base : ShadeCS := { info, n := csComps info }
    let (ro, s) := Content.Run.resolve src s o
    let tintOf := fun (alt tint : PdfObject) (s : σ) =>
      match Content.Run.baseDevice src s alt with
      | (some a, s) =>
        match loadFn src s tint with
        | (some f, s) => (some { base with tint := some (f, a) }, s)
        | (none, s) => (some base, s)
      | (none, s) => (some base, s)
    match ro with
    | .array [.name f, _, alt, tint] =>
      if f = Content.Run.nm "Separation" then tintOf alt tint s else (some base, s)
    | .array (.name f :: _ :: alt :: tint :: _) =>
      if f = Content.Run.nm "DeviceN" then tintOf alt tint s else (some base, s)
    | _ => (some base, s)

/-- The 256-entry RGB lookup table of `f` over `t ∈ [t0, t1]` (768 bytes). -/
def buildLut (cs : ShadeCS) (f : Fn) (t0 t1 : Rat) : ByteArray :=
  (List.range 256).foldl (fun acc (i : Nat) =>
    let t := qd (t0 + (i : Rat) * (t1 - t0) / 255)
    let c := cs.rgb (f.eval [t] cs.n)
    ((acc.push (UInt8.ofNatClamp c.1)).push (UInt8.ofNatClamp c.2.1)).push
      (UInt8.ofNatClamp c.2.2)) ByteArray.empty

/-! ## 6. Shading geometry -/

/-- A mesh vertex: shading-space coordinates in `1/4096` units and three colour channels in
`1/16` units (RGB bytes, or the lookup-table index in channel `r` when a function is used). -/
structure MV where
  /-- `x · 4096`. -/
  x : Int
  /-- `y · 4096`. -/
  y : Int
  /-- Red (or table index) · 16. -/
  r : Int
  /-- Green · 16. -/
  g : Int
  /-- Blue · 16. -/
  b : Int
  deriving Inhabited, Repr, BEq

/-- A Gouraud-shaded triangle. -/
structure Tri where
  /-- First vertex. -/
  a : MV
  /-- Second vertex. -/
  b : MV
  /-- Third vertex. -/
  c : MV
  deriving Inhabited, Repr

/-- What a shading paints. -/
inductive Geo where
  /-- Type 2: axis from `(x0, y0)` to `(x1, y1)`, extend flags. -/
  | axial (x0 y0 x1 y1 : Rat) (e0 e1 : Bool)
  /-- Type 3: circles `(x0, y0, r0)` and `(x1, y1, r1)`, extend flags. -/
  | radial (x0 y0 r0 x1 y1 r1 : Rat) (e0 e1 : Bool)
  /-- Types 1, 4–7: triangles in shading space. -/
  | mesh (tris : Array Tri)
  deriving Inhabited

/-- A shading ready to paint. -/
structure Prepared where
  /-- Geometry. -/
  geo : Geo
  /-- 256-entry RGB lookup table (axial, radial, meshes with a function). -/
  lut : ByteArray := ByteArray.empty
  /-- Mesh channels are lookup-table indices (`r`). -/
  useLut : Bool := false
  /-- `/BBox` (shading space). -/
  bbox : Option (Fixed × Fixed × Fixed × Fixed) := none
  /-- `/Background` as RGB (patterns only). -/
  background : Option (Nat × Nat × Nat) := none
  deriving Inhabited

/-- Maximum number of mesh vertices of a type 4 or 5 shading (local cap). -/
def maxMeshVertices : Nat := 1 <<< 16

/-- Maximum number of patches of a type 6 or 7 shading (local cap). -/
def maxPatches : Nat := 4096

/-- Grid steps per side of a function-based shading (MuPDF `FUNSEGS`). -/
def funSegs : Nat := 64

/-- Grid steps per side of a patch (MuPDF subdivides 3 levels). -/
def patchSegs : Nat := 8

/-- Round to an integer (halves up). -/
def roundQ (q : Rat) : Int := (q + 1 / 2).floor

/-- A shading-space point as vertex coordinates. -/
def mvOf (x y : Rat) (c : Int × Int × Int) : MV :=
  ⟨roundQ (x * 4096), roundQ (y * 4096), c.1, c.2.1, c.2.2⟩

/-- Channels of an RGB colour. -/
def chRGB (c : Nat × Nat × Nat) : Int × Int × Int := (16 * c.1, 16 * c.2.1, 16 * c.2.2)

/-- Channels of a parameter `t` on `[t0, t1]` (lookup index · 16, clamped). -/
def chT (t0 t1 t : Rat) : Int × Int × Int :=
  let i := if t1 = t0 then 0 else roundQ (clampR 0 1 ((t - t0) / (t1 - t0)) * 4080)
  (i, 0, 0)

/-- Two triangles of a quad `v0 v1 v2 v3` (in order around it). -/
def quad (v0 v1 v2 v3 : MV) : List Tri := [⟨v0, v1, v2⟩, ⟨v0, v2, v3⟩]

/-- Triangles of a row-major `(cols + 1) × (rows + 1)` vertex grid. -/
def gridTris (g : Array MV) (cols rows : Nat) : Array Tri :=
  (List.range rows).foldl (fun acc j =>
    (List.range cols).foldl (fun acc i =>
      let at_ := fun (i j : Nat) => g[j * (cols + 1) + i]?.getD default
      acc ++ (quad (at_ i j) (at_ (i + 1) j) (at_ (i + 1) (j + 1)) (at_ i (j + 1))).toArray)
      acc) #[]

/-- Type 1: the function sampled on a `(funSegs + 1)²` grid over `domain`, mapped by `mat`. -/
def functionMesh (cs : ShadeCS) (f : Fn) (domain : List Rat) (mat : Aff) : Array Tri :=
  let (x0, x1, y0, y1) := match domain with
    | [a, b, c, d] => (a, b, c, d)
    | _ => ((0 : Rat), (1 : Rat), (0 : Rat), (1 : Rat))
  let N := funSegs
  let g : Array MV := (Array.range ((N + 1) * (N + 1))).map fun k =>
    let i := k % (N + 1)
    let j := k / (N + 1)
    let x := qd (x0 + (i : Rat) * (x1 - x0) / (N : Rat))
    let y := qd (y0 + (j : Rat) * (y1 - y0) / (N : Rat))
    let p := mat.apply ⟨x, y⟩
    mvOf p.x p.y (chRGB (cs.rgb (f.eval [x, y] cs.n)))
  gridTris g N N

/-- Mesh decoding parameters. -/
structure MeshParams where
  /-- `/BitsPerCoordinate`. -/
  bpc : Nat
  /-- `/BitsPerComponent`. -/
  bpcomp : Nat
  /-- `/BitsPerFlag` (types 4, 6, 7). -/
  bpflag : Nat
  /-- `/Decode` x range. -/
  xr : Rat × Rat
  /-- `/Decode` y range. -/
  yr : Rat × Rat
  /-- `/Decode` ranges of the colour values (one per value). -/
  cr : List (Rat × Rat)
  /-- Colour values per vertex (1 with a function). -/
  nc : Nat
  /-- Colour values → channels. -/
  chan : List Rat → Int × Int × Int

/-- Decode a sample of `bits` bits into `[lo, hi]`. -/
def decodeSample (raw bits : Nat) (r : Rat × Rat) : Rat :=
  let mx : Nat := 2 ^ bits - 1
  if mx = 0 then r.1 else qd (r.1 + (raw : Rat) * (r.2 - r.1) / (mx : Rat))

/-- Bits of one point. -/
def MeshParams.pointBits (mp : MeshParams) : Nat := 2 * mp.bpc

/-- Bits of one colour. -/
def MeshParams.colorBits (mp : MeshParams) : Nat := mp.nc * mp.bpcomp

/-- Read a point at bit `pos` (shading space). -/
def MeshParams.point (mp : MeshParams) (data : ByteArray) (pos : Nat) : Rat × Rat :=
  (decodeSample (readBits data pos mp.bpc) mp.bpc mp.xr,
   decodeSample (readBits data (pos + mp.bpc) mp.bpc) mp.bpc mp.yr)

/-- Read a colour at bit `pos` (as channels). -/
def MeshParams.color (mp : MeshParams) (data : ByteArray) (pos : Nat) : Int × Int × Int :=
  mp.chan ((List.range mp.nc).map fun k =>
    decodeSample (readBits data (pos + k * mp.bpcomp) mp.bpcomp) mp.bpcomp
      (mp.cr.getD k (0, 1)))

/-- Read a vertex (point then colour) at bit `pos`. -/
def MeshParams.vertex (mp : MeshParams) (data : ByteArray) (pos : Nat) : MV :=
  let p := mp.point data pos
  mvOf p.1 p.2 (mp.color data (pos + mp.pointBits))

/-- Type 4: free-form triangles with edge flags (`fuel` vertices at most). State: the last
triangle. -/
def type4Loop (mp : MeshParams) (data : ByteArray) (total : Nat) :
    (fuel pos : Nat) → Option Tri → Array Tri → Array Tri
  | 0, _, _, acc => acc
  | fuel + 1, pos, prev, acc =>
    let vb := mp.bpflag + mp.pointBits + mp.colorBits
    if total < pos + vb then acc else
    let flag := readBits data pos mp.bpflag
    let vd := mp.vertex data (pos + mp.bpflag)
    match prev, flag with
    | some t, 1 => let t' : Tri := ⟨t.b, t.c, vd⟩; type4Loop mp data total fuel (pos + vb) (some t') (acc.push t')
    | some t, 2 => let t' : Tri := ⟨t.a, t.c, vd⟩; type4Loop mp data total fuel (pos + vb) (some t') (acc.push t')
    | _, _ =>
      if total < pos + 3 * vb then acc else
      let t' : Tri := ⟨vd, mp.vertex data (pos + vb + mp.bpflag),
        mp.vertex data (pos + 2 * vb + mp.bpflag)⟩
      type4Loop mp data total fuel (pos + 3 * vb) (some t') (acc.push t')

/-- Type 5: a lattice of `vpr` vertices per row. -/
def type5Mesh (mp : MeshParams) (data : ByteArray) (vpr : Nat) : Array Tri :=
  let vb := mp.pointBits + mp.colorBits
  if vpr < 2 ∨ vb = 0 then #[] else
  let nv := min maxMeshVertices (data.size * 8 / vb)
  let rows := nv / vpr
  if rows < 2 then #[] else
  let g := (Array.range (rows * vpr)).map fun k => mp.vertex data (k * vb)
  gridTris g (vpr - 1) (rows - 1)

/-- A point with integer coordinates (`1/4096` units). -/
abbrev IP := Int × Int

/-- MuPDF's `compute_tensor_interior` (ISO 32000-2 §8.7.4.5.7). -/
def tensorInterior (a b c d e f g h : IP) : IP :=
  ((-4 * a.1 + 6 * (b.1 + c.1) - 2 * (d.1 + e.1) + 3 * (f.1 + g.1) - h.1) / 9,
   (-4 * a.2 + 6 * (b.2 + c.2) - 2 * (d.2 + e.2) + 3 * (f.2 + g.2) - h.2) / 9)

/-- The 4 × 4 poles (row-major, `pole i j` at `4 i + j`) of a patch from its stream points
(12 for a Coons patch, 16 for a tensor patch), as MuPDF's `make_tensor_patch`. -/
def poles (pt : Array IP) (tensor : Bool) : Array IP :=
  let q := fun (k : Nat) => pt[k]?.getD (0, 0)
  -- boundary in stream order: p00 p01 p02 p03 p13 p23 p33 p32 p31 p30 p20 p10
  let p00 := q 0; let p01 := q 1; let p02 := q 2; let p03 := q 3
  let p13 := q 4; let p23 := q 5; let p33 := q 6; let p32 := q 7
  let p31 := q 8; let p30 := q 9; let p20 := q 10; let p10 := q 11
  let (p11, p12, p22, p21) :=
    if tensor then (q 12, q 13, q 14, q 15)
    else (tensorInterior p00 p01 p10 p03 p30 p31 p13 p33,
          tensorInterior p03 p02 p13 p00 p33 p32 p10 p30,
          tensorInterior p33 p32 p23 p30 p03 p02 p20 p00,
          tensorInterior p30 p31 p20 p33 p00 p01 p23 p03)
  #[p00, p01, p02, p03, p10, p11, p12, p13, p20, p21, p22, p23, p30, p31, p32, p33]

/-- Cubic Bernstein weights at `k / 8` (sum 512). -/
def bern (k : Nat) : Array Int :=
  let u : Int := k; let v : Int := 8 - k
  #[v * v * v, 3 * u * v * v, 3 * u * u * v, u * u * u]

/-- Point `(a/8, b/8)` of a tensor patch (first pole index along `a`). -/
def patchPoint (pl : Array IP) (a b : Nat) : IP :=
  let wa := bern a; let wb := bern b
  let s := (List.range 16).foldl (fun (acc : Int × Int) k =>
    let w := wa.getD (k / 4) 0 * wb.getD (k % 4) 0
    let p := pl.getD k (0, 0)
    (acc.1 + w * p.1, acc.2 + w * p.2)) (0, 0)
  ((s.1 + 131072) / 262144, (s.2 + 131072) / 262144)

/-- Bilinear corner colours (`c0` at pole 00, `c1` at 03, `c2` at 33, `c3` at 30) at
`(a/8, b/8)`. -/
def patchColor (c : Array (Int × Int × Int)) (a b : Nat) : Int × Int × Int :=
  let s : Int := a; let r : Int := b
  let w0 := (8 - s) * (8 - r); let w1 := (8 - s) * r; let w2 := s * r; let w3 := s * (8 - r)
  let g := fun (k : Nat) => c.getD k (0, 0, 0)
  let mix := fun (f : Int × Int × Int → Int) =>
    (w0 * f (g 0) + w1 * f (g 1) + w2 * f (g 2) + w3 * f (g 3) + 32) / 64
  (mix (·.1), mix (·.2.1), mix (·.2.2))

/-- The triangles of one patch (a `patchSegs × patchSegs` grid). -/
def patchTris (pl : Array IP) (c : Array (Int × Int × Int)) : Array Tri :=
  let N := patchSegs
  let g : Array MV := (Array.range ((N + 1) * (N + 1))).map fun k =>
    let j := k % (N + 1)
    let i := k / (N + 1)
    let p := patchPoint pl i j
    let col := patchColor c i j
    ⟨p.1, p.2, col.1, col.2.1, col.2.2⟩
  gridTris g N N

/-- Types 6 and 7: patches with edge flags (`fuel` patches at most). State: the previous
patch's stream-order points and corner colours. -/
def patchLoop (mp : MeshParams) (data : ByteArray) (total : Nat) (tensor : Bool) :
    (fuel pos : Nat) → Option (Array IP × Array (Int × Int × Int)) → Array Tri → Array Tri
  | 0, _, _, acc => acc
  | fuel + 1, pos, prev, acc =>
    let np := if tensor then 16 else 12
    if total < pos + mp.bpflag then acc else
    let flag := readBits data pos mp.bpflag
    let (sp, sc) : Nat × Nat := if flag = 0 then (0, 0) else (4, 2)
    let need := mp.bpflag + (np - sp) * mp.pointBits + (4 - sc) * mp.colorBits
    if total < pos + need then acc else
    let p0 := pos + mp.bpflag
    let rd := (List.range (np - sp)).map fun k =>
      let q := mp.point data (p0 + k * mp.pointBits)
      ((roundQ (q.1 * 4096), roundQ (q.2 * 4096)) : IP)
    let c0 := p0 + (np - sp) * mp.pointBits
    let rc := (List.range (4 - sc)).map fun k => mp.color data (c0 + k * mp.colorBits)
    let next := pos + need
    let shared : Option (List IP × List (Int × Int × Int)) :=
      if flag = 0 then some ([], [])
      else match prev with
        | none => none
        | some (pp, pc) =>
          let gp := fun (k : Nat) => pp.getD k (0, 0)
          let gc := fun (k : Nat) => pc.getD k (0, 0, 0)
          match flag with
          | 1 => some ([gp 3, gp 4, gp 5, gp 6], [gc 1, gc 2])
          | 2 => some ([gp 6, gp 7, gp 8, gp 9], [gc 2, gc 3])
          | 3 => some ([gp 9, gp 10, gp 11, gp 0], [gc 3, gc 0])
          | _ => none
    match shared with
    | none => patchLoop mp data total tensor fuel next prev acc
    | some (sp', sc') =>
      let pts := (sp' ++ rd).toArray
      let cols := (sc' ++ rc).toArray
      patchLoop mp data total tensor fuel next (some (pts, cols))
        (acc ++ patchTris (poles pts tensor) cols)

/-! ## 7. Loading a shading -/

/-- Maximum number of mesh triangles per page (all shadings together; local cap). -/
def maxPageTriangles : Nat := 1 <<< 20

/-- Two booleans of an `/Extend` array (default `[false false]`). -/
def extendOf (o : Option PdfObject) : Bool × Bool :=
  match o with
  | some (.array [.bool a, .bool b]) => (a, b)
  | _ => (false, false)

/-- The `/Matrix` of a type 1 shading as an exact affine map (default identity). -/
def matOf (o : Option PdfObject) : Aff :=
  match numsQ o with
  | some [a, b, c, d, e, f] => ⟨a, b, c, d, e, f⟩
  | _ => Aff.id

/-- The geometry of a mesh shading (types 4–7) from its dictionary and decoded data. -/
def meshGeo {σ : Type} (src : Source σ) (s : σ) (ty : Nat) (d : Dict) (cs : ShadeCS)
    (fn : Option Fn) (data : ByteArray) : Option (Array Tri) × σ :=
  let (bc, s) := ent src s d "BitsPerCoordinate"
  let (bk, s) := ent src s d "BitsPerComponent"
  let (bf, s) := ent src s d "BitsPerFlag"
  let (dc, s) := ent src s d "Decode"
  let (vr, s) := ent src s d "VerticesPerRow"
  let dec := pairs ((numsQ dc).getD [])
  let nc := if fn.isSome then 1 else cs.n
  let cr := dec.drop 2
  let chan : List Rat → Int × Int × Int := match fn with
    | some _ =>
      let (t0, t1) := cr.headD (0, 1)
      fun xs => chT t0 t1 (xs.headD 0)
    | none => fun xs => chRGB (cs.rgb xs)
  let ok := fun (b : Option Nat) (fl : Bool) => match b with
    | some b => (b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8 ∨ b = 12 ∨ b = 16 ∨ b = 24 ∨ b = 32) ∨
        (fl ∧ b ≤ 8)
    | none => false
  let bpc := (natQ bc).getD 0
  let bpcomp := (natQ bk).getD 0
  let bpflag := (natQ bf).getD 0
  if !(ok (natQ bc) false && ok (natQ bk) false) || dec.length < 2 + nc || nc = 0 then (none, s)
  else
  let mp : MeshParams := ⟨bpc, bpcomp, bpflag, dec.getD 0 (0, 1), dec.getD 1 (0, 1), cr, nc, chan⟩
  let total := data.size * 8
  match ty with
  | 4 => (some (type4Loop mp data total maxMeshVertices 0 none #[]), s)
  | 5 => (some (type5Mesh mp data ((natQ vr).getD 0)), s)
  | 6 => (some (patchLoop mp data total false maxPatches 0 none #[]), s)
  | 7 => (some (patchLoop mp data total true maxPatches 0 none #[]), s)
  | _ => (none, s)

/-- **Load a shading** (dictionary or stream object, types 1–7) into a `Prepared` shading;
`none` when it is malformed, unsupported (a `Pattern` colour space, a missing function for
types 1–3), or its data cannot be decoded. -/
def loadShading {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (o : PdfObject) :
    Option Prepared × σ :=
  let (body, s) := fetchBody src s o
  match body with
  | none => (none, s)
  | some (d, stm) =>
    let (ty, s) := ent src s d "ShadingType"
    let (cso, s) := ent src s d "ColorSpace"
    let (fo, s) := ent src s d "Function"
    let (bg, s) := ent src s d "Background"
    let (co, s) := ent src s d "Coords"
    let (dm, s) := ent src s d "Domain"
    let (ex, s) := ent src s d "Extend"
    let (mo, s) := ent src s d "Matrix"
    let (csr, s) := match Dict.get? d (Content.Run.nm "ColorSpace"), cso with
      | some raw, some _ => loadCS src s raw
      | _, _ => (none, s)
    match csr with
    | none => (none, s)
    | some cs =>
    let (fn, s) := match Dict.get? d (Content.Run.nm "Function"), fo with
      | some raw, some _ => loadFn src s raw
      | _, _ => (none, s)
    let bbox := Content.Run.bboxOf d
    let background := (numsQ bg).map fun xs => cs.rgb xs
    let base : Prepared := { geo := .mesh #[], bbox, background }
    let dom := (numsQ dm).getD []
    let (t0, t1) := match dom with
      | [a, b] => (a, b)
      | _ => ((0 : Rat), (1 : Rat))
    let ext := extendOf ex
    match natQ ty, fn with
    | some 1, some f => (some { base with geo := .mesh (functionMesh cs f dom (matOf mo)) }, s)
    | some 2, some f =>
      match numsQ co with
      | some [x0, y0, x1, y1] =>
        (some { base with geo := .axial x0 y0 x1 y1 ext.1 ext.2, lut := buildLut cs f t0 t1 }, s)
      | _ => (none, s)
    | some 3, some f =>
      match numsQ co with
      | some [x0, y0, r0, x1, y1, r1] =>
        if r0 < 0 ∨ r1 < 0 then (none, s) else
        (some { base with geo := .radial x0 y0 r0 x1 y1 r1 ext.1 ext.2,
                          lut := buildLut cs f t0 t1 }, s)
      | _ => (none, s)
    | some k, _ =>
      if k < 4 ∨ 7 < k then (none, s) else
      let (data, s) := bodyData src s stm
      match data with
      | none => (none, s)
      | some data =>
        if limits.maxDecodedStreamBytes < data.size then (none, s) else
        let (g, s) := meshGeo src s k d cs fn data
        match g with
        | none => (none, s)
        | some tris =>
          let lutInfo : ByteArray × Bool := match fn with
            | some f =>
              let (dt0, dt1) := ((pairs (((numsQ (Dict.get? d (Content.Run.nm "Decode"))).getD [])
                )).drop 2).headD (0, 1)
              (buildLut cs f dt0 dt1, true)
            | none => (ByteArray.empty, false)
          (some { base with geo := .mesh tris, lut := lutInfo.1, useLut := lutInfo.2 }, s)
    | none, _ => (none, s)

/-! ## 8. Painting -/

/-- Read a byte (`0` out of range). -/
@[inline] def rd (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then (b.get i h).toNat else 0

/-- Composite `(r, g, b)` with opacity `a` (bytes) at byte offset `j` of the page buffer
(`Clip.blend`; an opaque pixel is written directly). -/
def putPx (buf : ByteArray) (j r g b a : Nat) : ByteArray :=
  if a = 0 then buf
  else if a = 255 then
    Clip.setB (Clip.setB (Clip.setB buf j (UInt8.ofNatClamp r)) (j + 1) (UInt8.ofNatClamp g))
      (j + 2) (UInt8.ofNatClamp b)
  else
    let buf := Clip.setB buf j (Clip.blend r (rd buf j) a)
    let buf := Clip.setB buf (j + 1) (Clip.blend g (rd buf (j + 1)) a)
    Clip.setB buf (j + 2) (Clip.blend b (rd buf (j + 2)) a)

/-- `putPx` preserves the buffer size. -/
theorem putPx_size (buf : ByteArray) (j r g b a : Nat) : (putPx buf j r g b a).size = buf.size := by
  unfold putPx; split
  · rfl
  · split <;> simp only [Clip.setB_size]

/-- Opacity of pixel `(x, y)`: clip coverage times the constant alpha. -/
@[inline] def opacity (cm : Option Mask) (alpha : Nat) (x y : Int) : Nat :=
  match cm with
  | none => alpha
  | some c => Clip.mul255 (c.get x y).toNat alpha

/-- A lookup-table index from a machine integer: clamped to `[0, 255]`. -/
@[inline] def lutIdx (v : Int64) : Nat := min v.toNatClampNeg 255

/-- **Lookup indices are in range**: the three bytes read for index `lutIdx v` lie inside a
256-entry RGB table (`buildLut_size`). -/
theorem lutIdx_lt (v : Int64) : 3 * lutIdx v + 2 < 768 := by
  have := Nat.min_le_right v.toNatClampNeg 255
  unfold lutIdx; omega

/-- The lookup table has 256 RGB entries. -/
theorem buildLut_size (cs : ShadeCS) (f : Fn) (t0 t1 : Rat) : (buildLut cs f t0 t1).size = 768 := by
  unfold buildLut
  suffices h : ∀ (l : List Nat) (acc : ByteArray), (l.foldl (fun acc (i : Nat) =>
      let t := qd (t0 + (i : Rat) * (t1 - t0) / 255)
      let c := cs.rgb (f.eval [t] cs.n)
      ((acc.push (UInt8.ofNatClamp c.1)).push (UInt8.ofNatClamp c.2.1)).push
        (UInt8.ofNatClamp c.2.2)) acc).size = acc.size + 3 * l.length by
    rw [h]; simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons i rest ih => intro acc; simp only [List.foldl]; rw [ih]; simp [ByteArray.size_push]; omega

/-- Composite lookup-table entry `i` at byte `bi` with opacity `a`. -/
@[inline] def putIdx (lut : ByteArray) (bi i : Nat) (a : UInt32) (b : ByteArray) : ByteArray :=
  Clip.pxU b bi (Clip.getU lut (3 * i)) (Clip.getU lut (3 * i + 1)) (Clip.getU lut (3 * i + 2)) a

/-- Opacity of the pixel whose clip byte is at `ci` (`cd` the clip mask's bytes, if any). -/
@[inline] def opac (cd : Option ByteArray) (ci : Nat) (al : UInt32) : UInt32 :=
  match cd with
  | none => al
  | some d => Clip.mul255U (Clip.getU d ci) al

/-- One of the axial parameter's fixed point (`2²⁴`). -/
def tOne : Int64 := 16777216

/-- **Axial pixel**: parameter `t` (`tOne` = 1) → lookup index, `-1` (nothing) outside
`[0, 1]` unless extended. -/
@[inline] def axialIdx (e0 e1 : Bool) (t : Int64) : Int64 :=
  if t < 0 then (if e0 then 0 else -1)
  else if tOne < t then (if e1 then 255 else -1)
  else (t * 255 + 8388608) >>> 24

/-- Paint one row of an axial shading: `n` pixels, clip bytes from `ci`, page bytes from
`bi`, parameter `t` advancing by `dt`. -/
def axialRow (lut : ByteArray) (cd : Option ByteArray) (al : UInt32) (e0 e1 : Bool) (dt : Int64) :
    (n ci bi : Nat) → (t : Int64) → ByteArray → ByteArray
  | 0, _, _, _, b => b
  | n + 1, ci, bi, t, b =>
    let i := axialIdx e0 e1 t
    let b := if i < 0 then b else putIdx lut bi (lutIdx i) (opac cd ci al) b
    axialRow lut cd al e0 e1 dt n (ci + 1) (bi + 4) (t + dt) b

/-- An axial row preserves the buffer size. -/
theorem axialRow_size (lut : ByteArray) (cd : Option ByteArray) (al : UInt32) (e0 e1 : Bool)
    (dt : Int64) : ∀ (n ci bi : Nat) (t : Int64) (b : ByteArray),
      (axialRow lut cd al e0 e1 dt n ci bi t b).size = b.size
  | 0, _, _, _, _ => rfl
  | n + 1, ci, bi, t, b => by
    simp only [axialRow]; rw [axialRow_size lut cd al e0 e1 dt n]
    split
    · rfl
    · exact Clip.pxU_size _ _ _ _ _ _

/-- Clamp an integer to `[-2^e, 2^e]` as a machine integer. -/
def clampI64 (e : Nat) (v : Int) : Int64 :=
  let m : Int := 2 ^ e
  Int64.ofInt (if v < -m then -m else if m < v then m else v)

/-- Clip-byte offset of `(x, y)` in mask `cm` (0 without one). -/
def clipOff (cm : Option Mask) (x y : Int) : Nat :=
  match cm with
  | none => 0
  | some c => Clip.offs c.x0 c.y0 c.w x y

/-- Paint `fuel` rows of `r` of an axial shading whose parameter at device point `(x, y)` is
`α x + β y + γ` (`tOne` = 1). Row starts are exact (clamped to `±2⁴⁰`), per-pixel steps
rounded (clamped to `±2³⁰`). -/
def axialRows (W : Nat) (lut : ByteArray) (cm : Option Mask) (al : UInt32) (e0 e1 : Bool)
    (alpha beta gamma : Rat) (r : IRect) (dt : Int64) : (fuel : Nat) → (y : Int) → ByteArray → ByteArray
  | 0, _, buf => buf
  | fuel + 1, y, buf =>
    let t0 := ((alpha * ((r.x0 : Rat) + 1 / 2) + beta * ((y : Rat) + 1 / 2) + gamma) * 16777216).floor
    axialRows W lut cm al e0 e1 alpha beta gamma r dt fuel (y + 1)
      (axialRow lut (cm.map (·.data)) al e0 e1 dt r.width (clipOff cm r.x0 y)
        (4 * (y.toNat * W + r.x0.toNat)) (clampI64 40 t0) buf)

/-- Axial rows preserve the buffer size. -/
theorem axialRows_size (W : Nat) (lut : ByteArray) (cm : Option Mask) (al : UInt32)
    (e0 e1 : Bool) (alpha beta gamma : Rat) (r : IRect) (dt : Int64) :
    ∀ (fuel : Nat) (y : Int) (buf : ByteArray),
      (axialRows W lut cm al e0 e1 alpha beta gamma r dt fuel y buf).size = buf.size
  | 0, _, _ => rfl
  | fuel + 1, y, buf => by
    simp only [axialRows]
    rw [axialRows_size W lut cm al e0 e1 alpha beta gamma r dt fuel, axialRow_size]

/-- **Paint an axial shading** over rectangle `r` (inside the page and the clip mask's
rectangle) through the shading → device map `dev`. -/
def paintAxial (W : Nat) (lut : ByteArray) (cm : Option Mask) (al : UInt32) (dev : Aff)
    (x0 y0 x1 y1 : Rat) (e0 e1 : Bool) (r : IRect) (buf : ByteArray) : ByteArray :=
  let dx := x1 - x0
  let dy := y1 - y0
  let D := dx * dx + dy * dy
  if D = 0 ∨ dev.det = 0 then buf else
  let A := Aff.inv dev
  let alpha := (A.a * dx + A.b * dy) / D
  let beta := (A.c * dx + A.d * dy) / D
  let gamma := ((A.e - x0) * dx + (A.f - y0) * dy) / D
  axialRows W lut cm al e0 e1 alpha beta gamma r (clampI64 30 (roundQ (alpha * 16777216)))
    r.height r.y0 buf

/-- Constants of a radial shading in normalised integer units (`|values| ≤ 2¹⁴`, so every
intermediate of `radialIdx` stays below `2⁶⁰`). -/
structure RadK where
  /-- `c1 − c0`, x. -/
  cx : Int64
  /-- `c1 − c0`, y. -/
  cy : Int64
  /-- `r0`. -/
  r0 : Int64
  /-- `r1 − r0`. -/
  dr : Int64
  /-- `|c1 − c0|² − (r1 − r0)²`. -/
  a : Int64
  /-- `/Extend` at `s = 0`. -/
  e0 : Bool
  /-- `/Extend` at `s = 1`. -/
  e1 : Bool

/-- Fixed-point one of the radial parameter (`2¹⁶`). -/
def sOne : Int64 := 65536

/-- Is the root `s` (`sOne` = 1) admissible: `r(s) ≥ 0` and inside `[0, 1]` or extended? -/
@[inline] def RadK.ok (k : RadK) (s : Int64) : Bool :=
  0 ≤ k.r0 * sOne + s * k.dr && (0 ≤ s || k.e0) && (s ≤ sOne || k.e1)

/-- Lookup index of an admissible root (clamped to `[0, sOne]`). -/
@[inline] def sIndex (s : Int64) : Int64 :=
  let s := if s < 0 then 0 else if sOne < s then sOne else s
  (s * 255 + 32768) >>> 16

/-- The index of root `s` if admissible, else `-1`. -/
@[inline] def pick (k : RadK) (s : Int64) : Int64 := if k.ok s then sIndex s else -1

/-- Integer square root of `n` by Newton's method from the guess `g` (the previous pixel's
root; `0`: none, then `Nat.sqrt`). One step from any positive guess lands at or above
`⌊√n⌋`; at most 8 decreasing steps follow (an unconverged result over-estimates). -/
def isqrtFrom (n g : UInt64) : UInt64 :=
  if n = 0 then 0
  else if g = 0 then UInt64.ofNat (Nat.sqrt n.toNat)
  else go 8 ((g + n / g) / 2)
where
  /-- Decreasing Newton steps while they decrease. -/
  go : Nat → UInt64 → UInt64
    | 0, x => x
    | f + 1, x =>
      if x = 0 then x else
      let y := (x + n / x) / 2
      if y < x then go f y else x

/-- **Radial pixel** from `b = P·(c1 − c0) + r0 (r1 − r0)`, `c = |P|² − r0²` (`P` the point
in normalised units relative to `c0`), the discriminant `b² − a c` and its square root
`sq`: the larger admissible root `s` of `a s² − 2 b s + c = 0` (§8.7.4.5.4: the circle with
the larger `s` is on top); `-1` when no root is admissible. -/
@[inline] def radialIdx (k : RadK) (b c disc sq : Int64) : Int64 :=
  if k.a = 0 then
    if b = 0 then -1 else pick k (c * sOne / (2 * b))
  else
    if disc < 0 then -1 else
    let sp := (b + sq) * sOne / k.a
    let sm := (b - sq) * sOne / k.a
    let big := if 0 < k.a then sp else sm
    let small := if 0 < k.a then sm else sp
    if k.ok big then sIndex big else pick k small

/-- Paint one row of a radial shading: `n` pixels; `(u, v)` is the point in normalised units
times `2¹⁸`, advancing by `(du, dv)`; `g` the previous square root. -/
def radialRow (lut : ByteArray) (cd : Option ByteArray) (al : UInt32) (k : RadK) (du dv : Int64) :
    (n ci bi : Nat) → (u v : Int64) → (g : UInt64) → ByteArray → ByteArray
  | 0, _, _, _, _, _, b => b
  | n + 1, ci, bi, u, v, g, b =>
    let px := u >>> 18
    let py := v >>> 18
    let bb := px * k.cx + py * k.cy + k.r0 * k.dr
    let c := px * px + py * py - k.r0 * k.r0
    let disc := bb * bb - k.a * c
    let sq := if k.a ≠ 0 ∧ 0 ≤ disc then isqrtFrom disc.toUInt64 g else g
    let i := radialIdx k bb c disc sq.toInt64
    let b := if i < 0 then b else putIdx lut bi (lutIdx i) (opac cd ci al) b
    radialRow lut cd al k du dv n (ci + 1) (bi + 4) (u + du) (v + dv) sq b

/-- A radial row preserves the buffer size. -/
theorem radialRow_size (lut : ByteArray) (cd : Option ByteArray) (al : UInt32) (k : RadK)
    (du dv : Int64) : ∀ (n ci bi : Nat) (u v : Int64) (g : UInt64) (b : ByteArray),
      (radialRow lut cd al k du dv n ci bi u v g b).size = b.size
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, ci, bi, u, v, g, b => by
    simp only [radialRow]; rw [radialRow_size lut cd al k du dv n]
    split <;> (split <;> first | rfl | exact Clip.pxU_size _ _ _ _ _ _)

/-- Paint `fuel` rows of `r`; `B` maps device points to normalised units times `2¹⁸`. -/
def radialRows (W : Nat) (lut : ByteArray) (cm : Option Mask) (al : UInt32) (k : RadK) (B : Aff)
    (r : IRect) (du dv : Int64) : (fuel : Nat) → (y : Int) → ByteArray → ByteArray
  | 0, _, buf => buf
  | fuel + 1, y, buf =>
    let p := B.apply ⟨(r.x0 : Rat) + 1 / 2, (y : Rat) + 1 / 2⟩
    radialRows W lut cm al k B r du dv fuel (y + 1)
      (radialRow lut (cm.map (·.data)) al k du dv r.width (clipOff cm r.x0 y)
        (4 * (y.toNat * W + r.x0.toNat)) (clampI64 40 p.x.floor) (clampI64 40 p.y.floor) 0 buf)

/-- Radial rows preserve the buffer size. -/
theorem radialRows_size (W : Nat) (lut : ByteArray) (cm : Option Mask) (al : UInt32) (k : RadK)
    (B : Aff) (r : IRect) (du dv : Int64) : ∀ (fuel : Nat) (y : Int) (buf : ByteArray),
      (radialRows W lut cm al k B r du dv fuel y buf).size = buf.size
  | 0, _, _ => rfl
  | fuel + 1, y, buf => by
    simp only [radialRows]; rw [radialRows_size W lut cm al k B r du dv fuel, radialRow_size]

/-- `|q|`. -/
def absQ (q : Rat) : Rat := if q < 0 then -q else q

/-- **Paint a radial shading** over rectangle `r` through `dev`. Normalisation: the largest
of `|c1 − c0|`, the radii and the distances (per axis) from `c0` to the corners of `r` in
shading space becomes `2¹³` units. -/
def paintRadial (W : Nat) (lut : ByteArray) (cm : Option Mask) (al : UInt32) (dev : Aff)
    (x0 y0 r0 x1 y1 r1 : Rat) (e0 e1 : Bool) (r : IRect) (buf : ByteArray) : ByteArray :=
  if dev.det = 0 ∨ r.width = 0 ∨ r.height = 0 then buf else
  let A := Aff.inv dev
  let cs : List Pt := [⟨r.x0, r.y0⟩, ⟨r.x1, r.y0⟩, ⟨r.x0, r.y1⟩, ⟨r.x1, r.y1⟩].map A.apply
  let L := cs.foldl (fun m p => max m (max (absQ (p.x - x0)) (absQ (p.y - y0))))
    (max (max (absQ (x1 - x0)) (absQ (y1 - y0))) (max r0 r1))
  if L ≤ 0 then buf else
  let K := 8192 / L
  let k : RadK :=
    let cx := clampI64 14 (roundQ ((x1 - x0) * K))
    let cy := clampI64 14 (roundQ ((y1 - y0) * K))
    let dr := clampI64 14 (roundQ ((r1 - r0) * K))
    { cx, cy, r0 := clampI64 14 (roundQ (r0 * K)), dr, a := cx * cx + cy * cy - dr * dr, e0, e1 }
  -- device → normalised units · 2¹⁸
  let S : Rat := K * 262144
  let B : Aff := A * ⟨S, 0, 0, S, -x0 * S, -y0 * S⟩
  radialRows W lut cm al k B r (clampI64 30 (roundQ B.a)) (clampI64 30 (roundQ B.b)) r.height r.y0
    buf

/-- A triangle in device space: vertices in `1/256` pixels and channels. -/
structure DTri where
  /-- Vertex x coordinates. -/
  x0 : Int
  /-- . -/
  y0 : Int
  /-- . -/
  x1 : Int
  /-- . -/
  y1 : Int
  /-- . -/
  x2 : Int
  /-- . -/
  y2 : Int
  /-- Channels of the three vertices. -/
  c : MV × MV × MV

/-- Paint one row of a triangle: `fuel` pixels from column `x`, edge functions `w0 w1 w2`
(normalised to the sign of the area `ar > 0`) advancing by `d0 d1 d2`. -/
def triRow (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (alpha : Nat)
    (t : DTri) (ar d0 d1 d2 y : Int) : (fuel : Nat) → (x w0 w1 w2 : Int) → ByteArray → ByteArray
  | 0, _, _, _, _, buf => buf
  | fuel + 1, x, w0, w1, w2, buf =>
    let buf :=
      if 0 ≤ w0 ∧ 0 ≤ w1 ∧ 0 ≤ w2 ∧ 0 ≤ x ∧ x < W ∧ 0 ≤ y then
        let ch := fun (f : MV → Int) => (w0 * f t.c.1 + w1 * f t.c.2.1 + w2 * f t.c.2.2) / ar
        let a := opacity cm alpha x y
        let j := 4 * (y.toNat * W + x.toNat)
        if useLut then
          let i := (ch (·.r) + 8) / 16
          let i := if i < 0 then 0 else if 255 < i then 255 else i
          let k := 3 * i.toNat
          putPx buf j (rd lut k) (rd lut (k + 1)) (rd lut (k + 2)) a
        else
          putPx buf j ((ch (·.r) + 8) / 16).toNat ((ch (·.g) + 8) / 16).toNat
            ((ch (·.b) + 8) / 16).toNat a
      else buf
    triRow W lut useLut cm alpha t ar d0 d1 d2 y fuel (x + 1) (w0 + d0) (w1 + d1) (w2 + d2) buf

/-- A triangle row preserves the buffer size. -/
theorem triRow_size (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (alpha : Nat)
    (t : DTri) (ar d0 d1 d2 y : Int) : ∀ (fuel : Nat) (x w0 w1 w2 : Int) (buf : ByteArray),
      (triRow W lut useLut cm alpha t ar d0 d1 d2 y fuel x w0 w1 w2 buf).size = buf.size
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, x, w0, w1, w2, buf => by
    simp only [triRow]
    rw [triRow_size W lut useLut cm alpha t ar d0 d1 d2 y fuel]
    split
    · split <;> exact putPx_size _ _ _ _ _ _
    · rfl

/-- Edge function of `(xa, ya) → (xb, yb)` at `(px, py)`. -/
@[inline] def edge (xa ya xb yb px py : Int) : Int := (xb - xa) * (py - ya) - (yb - ya) * (px - xa)

/-- Paint `fuel` rows of rectangle `r` of a triangle (signed area `sg · ar`). -/
def triRows (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (alpha : Nat)
    (t : DTri) (sg ar : Int) (r : IRect) : (fuel : Nat) → (y : Int) → ByteArray → ByteArray
  | 0, _, buf => buf
  | fuel + 1, y, buf =>
    let px := 256 * r.x0 + 128
    let py := 256 * y + 128
    let w0 := sg * edge t.x1 t.y1 t.x2 t.y2 px py
    let w1 := sg * edge t.x2 t.y2 t.x0 t.y0 px py
    let w2 := sg * edge t.x0 t.y0 t.x1 t.y1 px py
    triRows W lut useLut cm alpha t sg ar r fuel (y + 1)
      (triRow W lut useLut cm alpha t ar (-(sg * 256 * (t.y2 - t.y1))) (-(sg * 256 * (t.y0 - t.y2)))
        (-(sg * 256 * (t.y1 - t.y0))) y r.width r.x0 w0 w1 w2 buf)

/-- Triangle rows preserve the buffer size. -/
theorem triRows_size (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (alpha : Nat)
    (t : DTri) (sg ar : Int) (r : IRect) : ∀ (fuel : Nat) (y : Int) (buf : ByteArray),
      (triRows W lut useLut cm alpha t sg ar r fuel y buf).size = buf.size
  | 0, _, _ => rfl
  | fuel + 1, y, buf => by
    simp only [triRows]; rw [triRows_size W lut useLut cm alpha t sg ar r fuel, triRow_size]

/-- An exact affine map as integer coefficients: shading units (`1/4096`) → device `1/256`
pixels, scaled by `2²⁰`. -/
structure IAff where
  /-- . -/
  a : Int
  /-- . -/
  b : Int
  /-- . -/
  c : Int
  /-- . -/
  d : Int
  /-- . -/
  e : Int
  /-- . -/
  f : Int

/-- Integer coefficients of `dev`. -/
def IAff.ofAff (m : Aff) : IAff :=
  ⟨roundQ (m.a * 65536), roundQ (m.b * 65536), roundQ (m.c * 65536), roundQ (m.d * 65536),
   roundQ (m.e * 268435456), roundQ (m.f * 268435456)⟩

/-- Map a vertex to device `1/256` pixels. -/
@[inline] def IAff.map (m : IAff) (v : MV) : Int × Int :=
  ((m.a * v.x + m.c * v.y + m.e) >>> 20, (m.b * v.x + m.d * v.y + m.f) >>> 20)

/-- Floor division by 256. -/
@[inline] def fl256 (v : Int) : Int := v >>> 8

/-- The device triangle of `t` and its pixel rectangle. -/
def devTri (m : IAff) (t : Tri) : DTri × IRect :=
  let p0 := m.map t.a; let p1 := m.map t.b; let p2 := m.map t.c
  let r : IRect := ⟨fl256 (min p0.1 (min p1.1 p2.1)), fl256 (min p0.2 (min p1.2 p2.2)),
    fl256 (max p0.1 (max p1.1 p2.1)) + 1, fl256 (max p0.2 (max p1.2 p2.2)) + 1⟩
  (⟨p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, (t.a, t.b, t.c)⟩, r)

/-- Maximum number of pixels visited by the mesh painting of one item (local cap; triangles
beyond the budget are skipped). -/
def maxMeshVisits : Nat := 1 <<< 26

/-- A device triangle as machine integers (coordinates bounded by `2²³`, `fastOK`). -/
structure FTri where
  /-- Vertex 0. -/
  x0 : Int64
  /-- . -/
  y0 : Int64
  /-- Vertex 1. -/
  x1 : Int64
  /-- . -/
  y1 : Int64
  /-- Vertex 2. -/
  x2 : Int64
  /-- . -/
  y2 : Int64
  /-- Red (or table index) channels of the vertices (`· 16`). -/
  r0 : Int64
  /-- . -/
  r1 : Int64
  /-- . -/
  r2 : Int64
  /-- Green channels. -/
  g0 : Int64
  /-- . -/
  g1 : Int64
  /-- . -/
  g2 : Int64
  /-- Blue channels. -/
  b0 : Int64
  /-- . -/
  b1 : Int64
  /-- . -/
  b2 : Int64

/-- Can triangle `t` use machine integers? Coordinates within `±2²³` (1/256 px) and channels
within `[0, 4080]`: then every edge value is below `2⁴⁹` and every channel sum below `2⁶¹`. -/
def fastOK (t : DTri) : Bool :=
  let c := fun (v : Int) => decide (-8388608 ≤ v ∧ v ≤ 8388608)
  let ch := fun (v : MV) => decide (0 ≤ v.r ∧ v.r ≤ 4080 ∧ 0 ≤ v.g ∧ v.g ≤ 4080 ∧ 0 ≤ v.b ∧ v.b ≤ 4080)
  c t.x0 && c t.y0 && c t.x1 && c t.y1 && c t.x2 && c t.y2 && ch t.c.1 && ch t.c.2.1 && ch t.c.2.2

/-- The machine-integer form of a device triangle. -/
def FTri.ofD (t : DTri) : FTri :=
  let o := Int64.ofInt
  ⟨o t.x0, o t.y0, o t.x1, o t.y1, o t.x2, o t.y2, o t.c.1.r, o t.c.2.1.r, o t.c.2.2.r,
   o t.c.1.g, o t.c.2.1.g, o t.c.2.2.g, o t.c.1.b, o t.c.2.1.b, o t.c.2.2.b⟩

/-- A channel (`· 16`) as a colour byte. -/
@[inline] def chByte (v : Int64) : UInt32 := UInt32.ofNat (min ((v + 8) >>> 4).toNatClampNeg 255)

/-- Paint one row of a triangle with machine integers: `n` pixels, clip bytes from `ci`, page
bytes from `bi`, edge values `w0 w1 w2` (normalised to a positive area `ar`) advancing by
`d0 d1 d2`. -/
def triRowF (lut : ByteArray) (useLut : Bool) (cd : Option ByteArray) (al : UInt32) (t : FTri)
    (ar d0 d1 d2 : Int64) : (n ci bi : Nat) → (w0 w1 w2 : Int64) → ByteArray → ByteArray
  | 0, _, _, _, _, _, b => b
  | n + 1, ci, bi, w0, w1, w2, b =>
    let b :=
      if 0 ≤ w0 && 0 ≤ w1 && 0 ≤ w2 then
        let a := opac cd ci al
        if useLut then
          putIdx lut bi (lutIdx (((w0 * t.r0 + w1 * t.r1 + w2 * t.r2) / ar + 8) >>> 4)) a b
        else
          Clip.pxU b bi (chByte ((w0 * t.r0 + w1 * t.r1 + w2 * t.r2) / ar))
            (chByte ((w0 * t.g0 + w1 * t.g1 + w2 * t.g2) / ar))
            (chByte ((w0 * t.b0 + w1 * t.b1 + w2 * t.b2) / ar)) a
      else b
    triRowF lut useLut cd al t ar d0 d1 d2 n (ci + 1) (bi + 4) (w0 + d0) (w1 + d1) (w2 + d2) b

/-- A fast triangle row preserves the buffer size. -/
theorem triRowF_size (lut : ByteArray) (useLut : Bool) (cd : Option ByteArray) (al : UInt32)
    (t : FTri) (ar d0 d1 d2 : Int64) : ∀ (n ci bi : Nat) (w0 w1 w2 : Int64) (b : ByteArray),
      (triRowF lut useLut cd al t ar d0 d1 d2 n ci bi w0 w1 w2 b).size = b.size
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, ci, bi, w0, w1, w2, b => by
    simp only [triRowF]; rw [triRowF_size lut useLut cd al t ar d0 d1 d2 n]
    split
    · split
      · exact Clip.pxU_size _ _ _ _ _ _
      · exact Clip.pxU_size _ _ _ _ _ _
    · rfl

/-- Edge function on machine integers. -/
@[inline] def edgeF (xa ya xb yb px py : Int64) : Int64 := (xb - xa) * (py - ya) - (yb - ya) * (px - xa)

/-- Paint `fuel` rows of rectangle `r` (inside the page and the clip's rectangle) of a fast
triangle (signed area `sg · ar`). -/
def triRowsF (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (al : UInt32)
    (t : FTri) (sg ar : Int64) (r : IRect) : (fuel : Nat) → (y : Int) → ByteArray → ByteArray
  | 0, _, buf => buf
  | fuel + 1, y, buf =>
    let px := Int64.ofInt (256 * r.x0 + 128)
    let py := Int64.ofInt (256 * y + 128)
    triRowsF W lut useLut cm al t sg ar r fuel (y + 1)
      (triRowF lut useLut (cm.map (·.data)) al t ar (-(sg * 256 * (t.y2 - t.y1)))
        (-(sg * 256 * (t.y0 - t.y2))) (-(sg * 256 * (t.y1 - t.y0))) r.width (clipOff cm r.x0 y)
        (4 * (y.toNat * W + r.x0.toNat)) (sg * edgeF t.x1 t.y1 t.x2 t.y2 px py)
        (sg * edgeF t.x2 t.y2 t.x0 t.y0 px py) (sg * edgeF t.x0 t.y0 t.x1 t.y1 px py) buf)

/-- Fast triangle rows preserve the buffer size. -/
theorem triRowsF_size (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (al : UInt32)
    (t : FTri) (sg ar : Int64) (r : IRect) : ∀ (fuel : Nat) (y : Int) (buf : ByteArray),
      (triRowsF W lut useLut cm al t sg ar r fuel y buf).size = buf.size
  | 0, _, _ => rfl
  | fuel + 1, y, buf => by
    simp only [triRowsF]; rw [triRowsF_size W lut useLut cm al t sg ar r fuel, triRowF_size]

/-- Paint one triangle inside `win` (budget permitting): buffer and pixels visited. Bounded
triangles (`fastOK`) use machine integers, others exact integers. -/
def paintTri (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (alpha : Nat)
    (m : IAff) (win : IRect) (acc : ByteArray × Nat) (t : Tri) : ByteArray × Nat :=
  let (dt, r) := devTri m t
  let r := r.inter win
  let n := r.width * r.height
  if maxMeshVisits < acc.2 + n then acc else
  let ar := edge dt.x0 dt.y0 dt.x1 dt.y1 dt.x2 dt.y2
  if ar = 0 then (acc.1, acc.2 + n) else
  let sg : Int := if 0 < ar then 1 else -1
  if fastOK dt then
    (triRowsF W lut useLut cm (UInt32.ofNat (min alpha 255)) (FTri.ofD dt) (Int64.ofInt sg)
      (Int64.ofInt (sg * ar)) r r.height r.y0 acc.1, acc.2 + n)
  else (triRows W lut useLut cm alpha dt sg (sg * ar) r r.height r.y0 acc.1, acc.2 + n)

/-- A triangle preserves the size and stays within the visit budget. -/
theorem paintTri_inv (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (alpha : Nat)
    (m : IAff) (win : IRect) (acc : ByteArray × Nat) (t : Tri) (h : acc.2 ≤ maxMeshVisits) :
    (paintTri W lut useLut cm alpha m win acc t).1.size = acc.1.size ∧
      (paintTri W lut useLut cm alpha m win acc t).2 ≤ maxMeshVisits := by
  unfold paintTri
  simp only
  split
  · exact ⟨rfl, h⟩
  · split
    · exact ⟨rfl, by omega⟩
    · split
      · exact ⟨triRowsF_size _ _ _ _ _ _ _ _ _ _ _ _, by omega⟩
      · exact ⟨triRows_size _ _ _ _ _ _ _ _ _ _ _ _, by omega⟩

/-- Painting a list of triangles preserves the size and the visit budget. -/
theorem foldl_paintTri_inv (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask)
    (alpha : Nat) (m : IAff) (win : IRect) (l : List Tri) :
    ∀ (acc : ByteArray × Nat), acc.2 ≤ maxMeshVisits →
      (l.foldl (paintTri W lut useLut cm alpha m win) acc).1.size = acc.1.size ∧
        (l.foldl (paintTri W lut useLut cm alpha m win) acc).2 ≤ maxMeshVisits := by
  induction l with
  | nil => intro acc h; exact ⟨rfl, h⟩
  | cons t rest ih =>
    intro acc h
    have h1 := paintTri_inv W lut useLut cm alpha m win acc t h
    have h2 := ih (paintTri W lut useLut cm alpha m win acc t) h1.2
    simp only [List.foldl]
    exact ⟨h2.1.trans h1.1, h2.2⟩

/-- **Paint a mesh** of triangles inside `win` through `dev`: buffer and pixels visited
(`≤ maxMeshVisits`). -/
def paintMesh (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask) (alpha : Nat)
    (dev : Aff) (win : IRect) (tris : Array Tri) (buf : ByteArray) : ByteArray × Nat :=
  tris.toList.foldl (paintTri W lut useLut cm alpha (IAff.ofAff dev) win) (buf, 0)

/-- Mesh painting preserves the size and visits at most `maxMeshVisits` pixels. -/
theorem paintMesh_inv (W : Nat) (lut : ByteArray) (useLut : Bool) (cm : Option Mask)
    (alpha : Nat) (dev : Aff) (win : IRect) (tris : Array Tri) (buf : ByteArray) :
    (paintMesh W lut useLut cm alpha dev win tris buf).1.size = buf.size ∧
      (paintMesh W lut useLut cm alpha dev win tris buf).2 ≤ maxMeshVisits :=
  foldl_paintTri_inv W lut useLut cm alpha _ win tris.toList (buf, 0) (Nat.zero_le _)

/-- The rectangle a shading paints: the window ∩ the page ∩ the clip mask's rectangle. -/
def paintRect (W H : Nat) (cm : Option Mask) (win : IRect) : IRect :=
  match cm with
  | none => win.inter (Clip.pageRect W H)
  | some c => (win.inter (Clip.pageRect W H)).inter c.rect

/-- The painted rectangle lies inside the page. -/
theorem paintRect_area_le (W H : Nat) (cm : Option Mask) (win : IRect) :
    (paintRect W H cm win).width * (paintRect W H cm win).height ≤ W * H := by
  have h1 := IRect.inter_width_le_right win (Clip.pageRect W H)
  have h2 := IRect.inter_height_le_right win (Clip.pageRect W H)
  have hw : (Clip.pageRect W H).width = W := by simp [Clip.pageRect, IRect.width]
  have hh : (Clip.pageRect W H).height = H := by simp [Clip.pageRect, IRect.height]
  unfold paintRect
  split
  · exact Nat.mul_le_mul (by omega) (by omega)
  · rename_i c
    have h3 := IRect.inter_width_le_left (win.inter (Clip.pageRect W H)) c.rect
    have h4 := IRect.inter_height_le_left (win.inter (Clip.pageRect W H)) c.rect
    exact Nat.mul_le_mul (by omega) (by omega)

/-- **Paint a prepared shading** through `dev` (shading space → device) over `paintRect`,
clip/coverage mask `cm`, constant alpha `alpha` (byte): the buffer and the pixels visited. -/
def paint (W H : Nat) (sh : Prepared) (dev : Aff) (cm : Option Mask) (win : IRect) (alpha : Nat)
    (buf : ByteArray) : ByteArray × Nat :=
  let r := paintRect W H cm win
  let al : UInt32 := UInt32.ofNat (min alpha 255)
  match sh.geo with
  | .axial x0 y0 x1 y1 e0 e1 =>
    (paintAxial W sh.lut cm al dev x0 y0 x1 y1 e0 e1 r buf, r.width * r.height)
  | .radial x0 y0 r0 x1 y1 r1 e0 e1 =>
    (paintRadial W sh.lut cm al dev x0 y0 r0 x1 y1 r1 e0 e1 r buf, r.width * r.height)
  | .mesh tris => paintMesh W sh.lut sh.useLut cm (min alpha 255) dev r tris buf

/-- Painting preserves the buffer size. -/
theorem paint_size (W H : Nat) (sh : Prepared) (dev : Aff) (cm : Option Mask) (win : IRect)
    (alpha : Nat) (buf : ByteArray) : (paint W H sh dev cm win alpha buf).1.size = buf.size := by
  unfold paint
  split
  · simp only [paintAxial]; split
    · rfl
    · exact axialRows_size _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp only [paintRadial]; split
    · rfl
    · split
      · rfl
      · exact radialRows_size _ _ _ _ _ _ _ _ _ _ _ _
  · exact (paintMesh_inv _ _ _ _ _ _ _ _ _).1

/-- **S3 for a shading.** Painting visits at most `W · H + maxMeshVisits` pixels (axial and
radial: the window ∩ page; meshes: the visit budget). -/
theorem paint_steps_le (W H : Nat) (sh : Prepared) (dev : Aff) (cm : Option Mask) (win : IRect)
    (alpha : Nat) (buf : ByteArray) :
    (paint W H sh dev cm win alpha buf).2 ≤ W * H + maxMeshVisits := by
  have hle := paintRect_area_le W H cm win
  unfold paint
  split
  · simp only; omega
  · simp only; omega
  · have := (paintMesh_inv W sh.lut sh.useLut cm (min alpha 255) dev (paintRect W H cm win)
      (by assumption) buf).2
    dsimp only; omega

/-! ## 9. Per-page table and display items -/

/-- A shading pattern (`PatternType 2`). -/
structure Pattern where
  /-- Its shading. -/
  shade : Prepared
  /-- `/Matrix`: pattern space → the default space of the page or form using it (composed
  with the use's base matrix at painting time, `PatternUse.base`). -/
  matrix : Matrix

/-- The shadings and shading patterns of a page, loaded before rendering, keyed by where the
resource lives and its name (`ResRef × Name`, task 7.3f: resolved by the runner, so a form's
own resources are found too). -/
structure ShadingTable where
  /-- `sh` operands (`none`: failed or unsupported, painted as nothing). -/
  shadings : List ((ResRef × Name) × Option Prepared) := []
  /-- Patterns (`none`: not a loadable shading pattern). -/
  patterns : List ((ResRef × Name) × Option Pattern) := []
  /-- Mesh triangles held so far (capped by `maxPageTriangles`). -/
  triangles : Nat := 0

instance : Inhabited ShadingTable := ⟨{}⟩

/-- The prepared shading of an `sh` resource. -/
def ShadingTable.shading? (t : ShadingTable) (r : ResRef) (n : Name) : Option Prepared :=
  ((t.shadings.find? (·.1 == (r, n))).map (·.2)).join

/-- The shading pattern of a pattern resource. -/
def ShadingTable.pattern? (t : ShadingTable) (r : ResRef) (n : Name) : Option Pattern :=
  ((t.patterns.find? (·.1 == (r, n))).map (·.2)).join

/-- The pattern resource a colour denotes, with the base matrix of its use: the recorded
`PatternUse`, or (an unannotated pattern colour, e.g. from the resource-free interpreter) the
page's resources and the identity. `none` for a non-pattern colour. -/
def patternRef (c : Color) (u : Option PatternUse) : Option (ResRef × Name × Matrix) :=
  match c with
  | .pattern n => some ((u.map (·.res)).getD .page, n, (u.map (·.base)).getD Matrix.identity)
  | _ => none

/-- The loaded shading pattern of a colour and its base matrix, if any. -/
def ShadingTable.patternOf (t : ShadingTable) (c : Color) (u : Option PatternUse) :
    Option (Pattern × Matrix) :=
  match patternRef c u with
  | some (r, n, base) => (t.pattern? r n).map (·, base)
  | none => none

/-- Number of mesh triangles of a prepared shading. -/
def Prepared.triangles (p : Prepared) : Nat :=
  match p.geo with
  | .mesh ts => ts.size
  | _ => 0

/-- Admit a loaded shading under the page's triangle cap. -/
def ShadingTable.admit (t : ShadingTable) (p : Option Prepared) : Option Prepared × Nat :=
  match p with
  | some sh =>
    if maxPageTriangles < t.triangles + sh.triangles then (none, t.triangles)
    else (some sh, t.triangles + sh.triangles)
  | none => (none, t.triangles)

/-- Load `sh` resource `n` living at `r` (once); `res` are the page's resources. -/
def ShadingTable.addShading {σ : Type} (limits : Limits) (src : Source σ) (res : Dict)
    (acc : ShadingTable × σ) (r : ResRef) (n : Name) : ShadingTable × σ :=
  let t := acc.1
  if t.shadings.any (·.1 == (r, n)) then acc else
  let (o, s) := Content.Run.resLookup src acc.2 res "Shading" r n
  let (p, s) := match o with
    | some o => loadShading limits src s o
    | none => (none, s)
  let (p, tc) := t.admit p
  ({ t with shadings := ((r, n), p) :: t.shadings, triangles := tc }, s)

/-- Load pattern resource `n` living at `r` (once) if it is a shading pattern. -/
def ShadingTable.addPattern {σ : Type} (limits : Limits) (src : Source σ) (res : Dict)
    (acc : ShadingTable × σ) (r : ResRef) (n : Name) : ShadingTable × σ :=
  let t := acc.1
  if t.patterns.any (·.1 == (r, n)) then acc else
  let (o, s) := Content.Run.resLookup src acc.2 res "Pattern" r n
  let (pd, s) := match o with
    | some o => fetchBody src s o
    | none => (none, s)
  let (p, s) : Option Pattern × σ := match pd with
    | some (d, _) =>
      match Dict.get? d (Content.Run.nm "PatternType"), Dict.get? d (Content.Run.nm "Shading") with
      | some (.int 2), some so =>
        match loadShading limits src s so with
        | (some sh, s) => (some ⟨sh, Content.Run.formMatrix d⟩, s)
        | (none, s) => (none, s)
      | _, _ => (none, s)
    | none => (none, s)
  let (sh, tc) := t.admit (p.map (·.shade))
  let p := match p, sh with
    | some p, some _ => some p
    | _, _ => none
  ({ t with patterns := ((r, n), p) :: t.patterns, triangles := tc }, s)

/-- Load the pattern of a colour (if it is a pattern colour). -/
def ShadingTable.addUse {σ : Type} (limits : Limits) (src : Source σ) (res : Dict)
    (acc : ShadingTable × σ) (c : Color) (u : Option PatternUse) : ShadingTable × σ :=
  match patternRef c u with
  | some (r, n, _) => ShadingTable.addPattern limits src res acc r n
  | none => acc

/-- **Load the shadings of a display list**: every distinct `sh` resource and every pattern
used by a fill, stroke or glyph-run colour, once, where the runner recorded it (`ResRef`;
`res`: the page's resources), including items nested in soft masks (`DisplayList.foldDeep`,
`Limits.maxXObjectDepth` levels). -/
def loadShadings {σ : Type} (limits : Limits) (src : Source σ) (s : σ) (res : Dict)
    (items : DisplayList) : ShadingTable × σ :=
  Content.DisplayList.foldDeep (fun acc it =>
    match it with
    | .shading n r _ _ _ => ShadingTable.addShading limits src res acc r n
    | .fillPath _ _ st _ => ShadingTable.addUse limits src res acc st.color st.pattern
    | .strokePath _ st _ => ShadingTable.addUse limits src res acc st.color st.pattern
    | .glyphRun run _ =>
      ShadingTable.addUse limits src res
        (ShadingTable.addUse limits src res acc run.fill.color run.fill.pattern)
        run.stroke.color run.stroke.pattern
    | _ => acc) limits.maxXObjectDepth ({}, s) items

/-- The clip of an `sh` item with the shading's `/BBox` (mapped by `ctm`) as one more path. -/
def withBBox (sh : Prepared) (ctm : Matrix) (clip : Clip) : Clip :=
  match sh.bbox with
  | none => clip
  | some (x0, y0, x1, y1) => ⟨Content.Run.rectPath ctm x0 y0 x1 y1, .nonzero⟩ :: clip

/-- Cost bound of a `/BBox` clip path (`Clip.pathCost` of a 5-segment path). -/
def bboxCost (cfg : Config) (W H : Nat) : Nat :=
  H * (cfg.samples * (cfg.segCap * 5 + 1) + W + 1) + W * H

/-- A rectangle path has five segments. -/
theorem rectPath_size (m : Matrix) (x0 y0 x1 y1 : Fixed) :
    (Content.Run.rectPath m x0 y0 x1 y1).segs.size = 5 := rfl

/-- The `/BBox` adds at most `bboxCost` to the clip's cost. -/
theorem withBBox_cost (cfg : Config) (W H : Nat) (sh : Prepared) (ctm : Matrix) (clip : Clip) :
    Clip.clipCost cfg W H (withBBox sh ctm clip) ≤ Clip.clipCost cfg W H clip + bboxCost cfg W H := by
  unfold withBBox
  split
  · omega
  · simp only [Clip.clipCost, Clip.pathCost, rectPath_size, bboxCost]
    omega

/-- **Paint an `sh` item** (`DisplayItem.shading name r ctm fill clip`): the shading of
`(r, name)` in the table, through `ctm × m`, under the clip (and its `/BBox`), with constant
alpha `alpha` (the item's `ca`, task 7.3f; its blend mode and soft mask are applied by the
transparency driver, see `Glyph.liftSh`); `/Background` ignored (§8.7.4.5.1). Nothing is drawn
for an unknown or failed shading. -/
def renderShading (cfg : Config) (m : Aff) (W H : Nat) (tbl : ShadingTable) (st : Clip.RState)
    (r : ResRef) (name : Name) (ctm : Matrix) (alpha : Comp) (clip : Clip) : Clip.RState :=
  match tbl.shading? r name with
  | none => st
  | some sh =>
    let c := Clip.clipMaskC cfg m W H st.cache (withBBox sh ctm clip)
    let p := paint W H sh (Aff.ofMatrix ctm * m) c.1 (Clip.itemWindow W H c.1)
      (Clip.compByte alpha) st.buf
    { buf := p.1, cache := c.2.1, steps := st.steps + c.2.2 + p.2 }

/-- Painting an `sh` item preserves the buffer size. -/
theorem renderShading_size (cfg : Config) (m : Aff) (W H : Nat) (tbl : ShadingTable)
    (st : Clip.RState) (r : ResRef) (name : Name) (ctm : Matrix) (alpha : Comp) (clip : Clip) :
    (renderShading cfg m W H tbl st r name ctm alpha clip).buf.size = st.buf.size := by
  unfold renderShading; split
  · rfl
  · exact paint_size _ _ _ _ _ _ _ _

/-- **S3 for an `sh` item.** The counted work is at most the clip's cost, the `/BBox` path's
cost and `W · H + maxMeshVisits` pixel visits (loading is bounded separately by the function,
mesh and table caps). -/
theorem renderShading_steps_le (cfg : Config) (m : Aff) (W H : Nat) (tbl : ShadingTable)
    (st : Clip.RState) (r : ResRef) (name : Name) (ctm : Matrix) (alpha : Comp) (clip : Clip) :
    (renderShading cfg m W H tbl st r name ctm alpha clip).steps ≤
      st.steps + Clip.clipCost cfg W H clip + bboxCost cfg W H + (W * H + maxMeshVisits) := by
  unfold renderShading; split
  · omega
  · rename_i sh _
    have h0 := Clip.clipMaskC_steps_le cfg m W H st.cache (withBBox sh ctm clip)
    have h1 := withBBox_cost cfg W H sh ctm clip
    have h2 := paint_steps_le W H sh (Aff.ofMatrix ctm * m)
      (Clip.clipMaskC cfg m W H st.cache (withBBox sh ctm clip)).1
      (Clip.itemWindow W H (Clip.clipMaskC cfg m W H st.cache (withBBox sh ctm clip)).1)
      (Clip.compByte alpha) st.buf
    simp only
    omega

/-- **Paint a shading pattern through a coverage mask** `mk` (the item's mask, already
intersected with its clip): `mk` ∩ the shading's `/BBox`, the `/Background` first (inside the
`/BBox`, as MuPDF bounds the shading by it), then the shading, through `pattern matrix × base
× m` (§8.7.3: the pattern matrix maps to the default space of the using page or form, `base`
maps that to page space), with alpha `alpha`. `cc`/`s`: the clip cache and the work so far. -/
def paintPattern (cfg : Config) (m : Aff) (W H : Nat) (st : Clip.RState) (pat : Pattern)
    (base : Matrix) (mk : Mask) (alpha : Comp) (cc : Clip.ClipCache) (s : Nat) : Clip.RState :=
  let mat := Matrix.mul pat.matrix base
  let bb := match pat.shade.bbox with
    | none => (mk, 0)
    | some (x0, y0, x1, y1) =>
      let g := Clip.fillCounted cfg m (Content.Run.rectPath mat x0 y0 x1 y1) .nonzero mk.rect
      (mk.inter g.1, g.2)
  let mk := bb.1
  let a := Clip.compByte alpha
  let win := mk.rect.inter (Clip.pageRect W H)
  let buf := match pat.shade.background with
    | some rgb => Clip.composite st.buf W mk none win rgb a
    | none => st.buf
  let pr := paint W H pat.shade (Aff.ofMatrix mat * m) (some mk) win a buf
  { buf := pr.1, cache := cc, steps := st.steps + s + bb.2 + mk.area + pr.2 }

/-- Painting a pattern through a mask preserves the buffer size. -/
theorem paintPattern_size (cfg : Config) (m : Aff) (W H : Nat) (st : Clip.RState) (pat : Pattern)
    (base : Matrix) (mk : Mask) (alpha : Comp) (cc : Clip.ClipCache) (s : Nat) :
    (paintPattern cfg m W H st pat base mk alpha cc s).buf.size = st.buf.size := by
  unfold paintPattern
  simp only
  rw [paint_size]
  split
  · exact Clip.composite_size _ _ _ _ _ _ _
  · rfl

/-- **Paint a path filled with a shading pattern**: fill mask ∩ clip, then `paintPattern`. -/
def renderPatternFill (cfg : Config) (m : Aff) (W H : Nat) (st : Clip.RState) (pat : Pattern)
    (base : Matrix) (p : Path) (rule : FillRule) (alpha : Comp) (clip : Clip) : Clip.RState :=
  let c := Clip.clipMaskC cfg m W H st.cache clip
  let f := Clip.fillCounted cfg m p rule (Clip.itemWindow W H c.1)
  paintPattern cfg m W H st pat base (Clip.combine f.1 c.1) alpha c.2.1 (c.2.2 + f.2)

/-- Painting a pattern fill preserves the buffer size. -/
theorem renderPatternFill_size (cfg : Config) (m : Aff) (W H : Nat) (st : Clip.RState)
    (pat : Pattern) (base : Matrix) (p : Path) (rule : FillRule) (alpha : Comp) (clip : Clip) :
    (renderPatternFill cfg m W H st pat base p rule alpha clip).buf.size = st.buf.size :=
  paintPattern_size _ _ _ _ _ _ _ _ _ _ _

/-- **Paint a path stroked with a shading pattern** (task 7.3f): stroke mask (by `stroke`, as
`Clip.renderItem`) ∩ clip, then `paintPattern`. -/
def renderPatternStroke (cfg : Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn)
    (st : Clip.RState) (pat : Pattern) (base : Matrix) (p : Path) (style : Content.StrokeStyle)
    (clip : Clip) : Clip.RState :=
  let c := Clip.clipMaskC cfg m W H st.cache clip
  let fm := stroke cfg m (Clip.itemWindow W H c.1) p style
  paintPattern cfg m W H st pat base (Clip.combine fm c.1) style.alpha c.2.1 c.2.2

/-- **Paint a `fillPath` item**: a fill with a shading pattern colour through
`renderPatternFill`, everything else (device colours, tiling patterns, unknown patterns) by
`Clip.renderItem`. -/
def renderFill (cfg : Config) (m : Aff) (W H : Nat) (tbl : ShadingTable) (st : Clip.RState)
    (p : Path) (rule : FillRule) (style : FillStyle) (clip : Clip) : Clip.RState :=
  match tbl.patternOf style.color style.pattern with
  | some (pat, base) => renderPatternFill cfg m W H st pat base p rule style.alpha clip
  | none => Clip.renderItem cfg m W H Clip.noStroke st (.fillPath p rule style clip)

/-- Painting a fill preserves the buffer size. -/
theorem renderFill_size (cfg : Config) (m : Aff) (W H : Nat) (tbl : ShadingTable)
    (st : Clip.RState) (p : Path) (rule : FillRule) (style : FillStyle) (clip : Clip) :
    (renderFill cfg m W H tbl st p rule style clip).buf.size = st.buf.size := by
  unfold renderFill renderPatternFill
  split
  · exact paintPattern_size _ _ _ _ _ _ _ _ _ _ _
  · exact Clip.renderItem_size _ _ _ _ _ _ _

/-- **Paint a `strokePath` item** (task 7.3f): a stroke with a shading pattern colour through
`renderPatternStroke`, everything else by `Clip.renderItem`. -/
def renderStroke (cfg : Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn) (tbl : ShadingTable)
    (st : Clip.RState) (p : Path) (style : Content.StrokeStyle) (clip : Clip) : Clip.RState :=
  match tbl.patternOf style.color style.pattern with
  | some (pat, base) => renderPatternStroke cfg m W H stroke st pat base p style clip
  | none => Clip.renderItem cfg m W H stroke st (.strokePath p style clip)

/-- Painting a stroke preserves the buffer size. -/
theorem renderStroke_size (cfg : Config) (m : Aff) (W H : Nat) (stroke : Clip.StrokeFn)
    (tbl : ShadingTable) (st : Clip.RState) (p : Path) (style : Content.StrokeStyle) (clip : Clip) :
    (renderStroke cfg m W H stroke tbl st p style clip).buf.size = st.buf.size := by
  unfold renderStroke renderPatternStroke
  split
  · exact paintPattern_size _ _ _ _ _ _ _ _ _ _ _
  · exact Clip.renderItem_size _ _ _ _ _ _ _

/-! ## 10. Checks -/

#guard (Fn.exp (0, 1) none [0] [1] 2).eval [1 / 2] 1 == [1 / 4]
#guard (Fn.stitch (0, 1) none [.exp (0, 1) none [0] [1] 1, .exp (0, 1) none [1] [0] 1] [1 / 2]
  [(0, 1), (0, 1)]).eval [1 / 2] 1 == [1]
#guard (Fn.sampled [(0, 1)] [(0, 1)] [2] 8 [] [] #[0, 255]).eval [1 / 2] 1 == [1 / 2]
#guard ((psProgram "{ 2 mul exch 3 mul add }".toUTF8).map fun p =>
  (Fn.ps [(0, 1), (0, 1)] [(0, 10)] p).eval [1 / 2, 1 / 4] 1) == some [2]
#guard psProgram "{ 1 { 2 } if".toUTF8 |>.isNone
#guard axialIdx false false (-1) == -1 && axialIdx true false (-1) == 0 &&
  axialIdx false false tOne == 255 && axialIdx false false (tOne / 2) == 128 &&
  axialIdx false true (tOne + 1) == 255
#guard isqrtFrom 1000000 0 == 1000 && isqrtFrom 1000000 900 == 1000 && isqrtFrom 999999 1000 == 999
#guard stitchIndex [1 / 2] (1 / 2) == 1 && stitchIndex [1 / 2] (1 / 4) == 0

end SafePdf.Core.Raster.Shading
