import SafePdf

/-!
# Fuzz driver (Plan.md §6 Phase 0, §7 items 2–3)

Calls every parser entry point on generated inputs and reports outcomes per entry point:
`SafePdf.parse` (opens the file, task 2.11), `SafePdf.parseObjectAt` at offset 0 and at a pseudo-random
offset (`Limits.default`) and at offset 0 with `maxObjectDepth := 8`,
`SafePdf.parseIndirectAt` at offset 0, and `Core.Lex.lexAll`. Deterministic: all
randomness comes from a SplitMix64 generator seeded by `--seed`, so a campaign (and any
input it reports) is reproduced exactly by rerunning with the same arguments.

Modes, chosen per iteration:
* random bytes (length uniform in `[0, max-len]`, sometimes prefixed with `%PDF-1.x`);
* mutation of a seed input (files read from `--seeds` directories, plus a few built-in
  seeds) by bit flips, byte overwrite, byte insert/delete, block duplicate, and splice.

Long inputs (task 13.6): `--long` turns on the repetition mutator. Three iterations in four
build an input of `10^3 .. 9*10^6` repetitions (capped at `--long-bytes`, default 4 MiB) of a
token, an operator, a dictionary entry (also with a counter, so every key is distinct), an
object, or a slice of a seed, inside a frame that makes the shape meaningful (a path, a
dictionary, an array, an indirect object, a file with a trailer, a text object, ...). A
quadratic algorithm cannot hide behind a 4 KiB input there.

Budget: every call is allowed `--budget-base-ms` plus a rate per KiB of input (per entry point,
or `--budget-us-per-kib` for all)
(a linear budget). A call over it is a FAILURE (`fuzz: FAIL ...` line, exit code 3), not a
count. A call over twice its budget is abandoned (its thread keeps running; the campaign
goes on, and stops after three abandoned calls). `--time-limit S` bounds the run time: no new
iteration starts after S seconds.

Usage:
```
lake exe fuzz [--iters N] [--seed S] [--max-len L] [--slow-ms T] [--seeds DIR]...
              [--long] [--long-bytes B] [--recipe NAME] [--time-limit S]
              [--budget-base-ms M] [--budget-us-per-kib U]
```
Defaults: 10000 iterations, seed 1, max length 4096, slow threshold 100 ms, seed
directories `Tests/adversarial` and `corpus` (missing directories are skipped), budget
`--budget-base-ms` plus a per-entry-point rate (`budgetUsDefault`), no time limit, no repetition.

Exit code: 0 when the campaign completes within budget; 1 if the shell part raised an
uncaught exception; 2 on bad arguments; 3 if some call went over its budget. Since the entry points are pure and total, they cannot crash; a hang
would show up as a slow input or a timeout of the whole run. Each call is timed separately;
calls slower than `--slow-ms` are reported with the entry point, position and input prefix.
The summary has one line per entry point and a total line with an input hash: the same
arguments give the same inputs, positions and outcome counts.
-/

namespace SafePdf.Fuzz

/-! ## SplitMix64 PRNG -/

/-- SplitMix64 generator state. -/
structure Rng where
  /-- Current state word. -/
  state : UInt64

/-- Advance the generator and return 64 random bits. -/
def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A random natural number in `[0, n)` (`0` when `n = 0`). -/
def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (if n == 0 then 0 else x.toNat % n, g)

/-- A random byte. -/
def Rng.byte (g : Rng) : UInt8 × Rng :=
  let (x, g) := g.next
  (x.toUInt8, g)

/-- `n` random bytes. -/
def Rng.bytes (g : Rng) (n : Nat) : ByteArray × Rng := Id.run do
  let mut g := g
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    let (b, g') := g.byte
    g := g'
    out := out.push b
  return (out, g)

/-! ## Mutations -/

/-- Bytes that tend to matter to a PDF parser. -/
def interesting : Array UInt8 :=
  #[0, 9, 10, 12, 13, 32, 37, 40, 41, 47, 48, 49, 57, 60, 62, 91, 93, 92, 123, 125, 255]

/-- Replace the byte at `i` (no-op when out of range). -/
def setByte (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  ⟨b.data.modify i (fun _ => v)⟩

/-- Apply one random mutation to `b`, possibly using `other` as a splice partner. -/
def mutateOnce (g : Rng) (b other : ByteArray) : ByteArray × Rng :=
  let (op, g) := g.below 7
  let (i, g) := g.below (b.size + 1)
  match op with
  | 0 => -- bit flip
    let (bit, g) := g.below 8
    let old := (b[i]?).getD 0
    (setByte b i (old ^^^ ((1 : UInt8) <<< bit.toUInt8)), g)
  | 1 => -- overwrite with random byte
    let (v, g) := g.byte
    (setByte b i v, g)
  | 2 => -- overwrite with interesting byte
    let (k, g) := g.below interesting.size
    (setByte b i (interesting[k]?.getD 0), g)
  | 3 => -- insert random byte(s)
    let (n, g) := g.below 4
    let (ins, g) := g.bytes (n + 1)
    (b.extract 0 i ++ ins ++ b.extract i b.size, g)
  | 4 => -- delete a run of bytes
    let (n, g) := g.below 16
    (b.extract 0 i ++ b.extract (i + n + 1) b.size, g)
  | 5 => -- duplicate a block
    let (n, g) := g.below 64
    (b.extract 0 (i + n) ++ b.extract i b.size, g)
  | _ => -- splice: prefix of `b`, suffix of `other`
    let (j, g) := g.below (other.size + 1)
    (b.extract 0 i ++ other.extract j other.size, g)

/-- Apply `k` random mutations. -/
def mutate (g : Rng) (b other : ByteArray) : Nat → ByteArray × Rng
  | 0 => (b, g)
  | k + 1 =>
    let (b, g) := mutateOnce g b other
    mutate g b other k

/-! ## Command line -/

/-- Default fixed part of the per-call budget (ms); see the calibration in `progress.md` 13.6. -/
def budgetBaseDefault : Nat := 1000

/-- Default linear part of the per-call budget, per entry point in the order of `entryNames`
(microseconds per KiB of input). Worst rates measured on the fixed tree (4 MiB repetition
inputs, 275 to 333 iterations, loaded 8-core machine): `parse` 233, `parseObjectAt` 87,
`parseIndirectAt` 56, `lexAll` 32, `runBytes` 7191 (unclosed `[` / `<<` runs: linear but 7 to
12 microseconds per bracket; valid operator streams cost about 120; mutated 200 KB seed
files in the smoke profile 7299). The defaults are 3.5 times (`runBytes`) to 30 times (`lexAll`) those
figures. The rate stays below what the quadratic of 13.1 and 13.2 reaches at 4 MiB. -/
def budgetUsDefault : Array Nat := #[1500, 1000, 1000, 1000, 1000, 1000, 25000]

/-- Campaign configuration. -/
structure Config where
  /-- Number of inputs to try. -/
  iters : Nat := 10000
  /-- PRNG seed. -/
  seed : Nat := 1
  /-- Maximum generated input length in bytes. -/
  maxLen : Nat := 4096
  /-- Report inputs whose parse takes longer than this many milliseconds. -/
  slowMs : Nat := 100
  /-- Directories of seed files; `none` means the defaults. -/
  seedDirs : Option (List String) := none
  /-- Repetition mutator on (task 13.6). -/
  long : Bool := false
  /-- Maximum size of a repetition input in bytes. -/
  longBytes : Nat := 4 <<< 20
  /-- With `--long`: use only the recipe of this name (reproduction, evidence runs). -/
  recipe : Option String := none
  /-- Stop starting iterations after this many seconds (`0`: no limit). -/
  timeLimit : Nat := 0
  /-- Fixed part of the per-call budget, milliseconds. -/
  budgetBaseMs : Nat := budgetBaseDefault
  /-- Linear part of the per-call budget, microseconds per KiB of input; `0` means the
  per-entry defaults `budgetUsDefault`. -/
  budgetUsPerKiB : Nat := 0

/-- Parse command-line arguments. -/
def parseArgs (cfg : Config) : List String → Except String Config
  | [] => .ok cfg
  | "--iters" :: v :: rest => num v >>= fun n => parseArgs { cfg with iters := n } rest
  | "--seed" :: v :: rest => num v >>= fun n => parseArgs { cfg with seed := n } rest
  | "--max-len" :: v :: rest => num v >>= fun n => parseArgs { cfg with maxLen := n } rest
  | "--slow-ms" :: v :: rest => num v >>= fun n => parseArgs { cfg with slowMs := n } rest
  | "--long" :: rest => parseArgs { cfg with long := true } rest
  | "--long-bytes" :: v :: rest => num v >>= fun n => parseArgs { cfg with longBytes := n } rest
  | "--recipe" :: v :: rest => parseArgs { cfg with recipe := some v } rest
  | "--time-limit" :: v :: rest => num v >>= fun n => parseArgs { cfg with timeLimit := n } rest
  | "--budget-base-ms" :: v :: rest =>
    num v >>= fun n => parseArgs { cfg with budgetBaseMs := n } rest
  | "--budget-us-per-kib" :: v :: rest =>
    num v >>= fun n => parseArgs { cfg with budgetUsPerKiB := n } rest
  | "--seeds" :: v :: rest =>
    parseArgs { cfg with seedDirs := some (cfg.seedDirs.getD [] ++ [v]) } rest
  | a :: _ => .error s!"unknown or incomplete argument: {a}"
where
  num (v : String) : Except String Nat :=
    match v.toNat? with
    | some n => .ok n
    | none => .error s!"not a natural number: {v}"

/-- Usage text. -/
def usage : String :=
  "usage: fuzz [--iters N] [--seed S] [--max-len L] [--slow-ms T] [--seeds DIR]... \
    [--long] [--long-bytes B] [--recipe NAME] [--time-limit S] \
    [--budget-base-ms M] [--budget-us-per-kib U]"

/-- Largest seed file read in full; larger files are truncated to this many bytes. -/
def maxSeedBytes : Nat := 1 <<< 20

/-- Collect regular files under `dir` (recursing at most `depth` levels), sorted by path so
the campaign does not depend on directory-listing order. -/
def collectFiles (dir : System.FilePath) : Nat → IO (Array System.FilePath)
  | 0 => return #[]
  | depth + 1 => do
    let mut out := #[]
    for e in (← dir.readDir) do
      if ← e.path.isDir then
        -- Decompression bombs (task 3.6a) decode up to `maxDecodedStreamBytes` by design and
        -- would always show up as slow inputs; they have their own suite (`Tests/Bombs.lean`).
        if e.fileName == "bombs" then continue
        out := out ++ (← collectFiles e.path depth)
      else
        out := out.push e.path
    return out.qsort (fun a b => a.toString < b.toString)

/-- Read the first `maxSeedBytes` bytes of a file. -/
def readPrefix (p : System.FilePath) : IO ByteArray := do
  let h ← IO.FS.Handle.mk p .read
  h.read maxSeedBytes.toUSize

/-- Built-in seeds, so mutation mode has material even without seed directories. -/
def builtinSeeds : Array ByteArray :=
  #["%PDF-1.7\n%\xe2\xe3\xcf\xd3\n1 0 obj\n<< /Type /Catalog >>\nendobj\ntrailer\n<< /Root 1 0 R >>\n%%EOF\n".toUTF8,
    "%PDF-2.0\n".toUTF8,
    "junk before header %PDF-1.4\n".toUTF8,
    "%PDF-".toUTF8,
    "[1 2 0 R << /A (x) /B <00ff> >> /N#20 -3.5 true null]".toUTF8,
    "1 0 obj << /Length 5 >> stream\nhello\nendstream endobj".toUTF8,
    "12 0 obj\n<< /Type /Page /Kids [3 0 R] /Res << /F << /F1 5 0 R >> >> >>\nendobj\n".toUTF8,
    "(a\\(b\\)\\101\\\r\n (n)) <4142 4> /A#42 +.5 -0 [] << >>".toUTF8,
    String.join (List.replicate 300 "[") |>.toUTF8,
    String.join (List.replicate 40 "<< /K [") |>.toUTF8]

/-- Load seed inputs from the given directories, skipping missing ones. -/
def loadSeeds (dirs : List String) : IO (Array ByteArray) := do
  let mut seeds := builtinSeeds
  for d in dirs do
    let p : System.FilePath := d
    if !(← p.isDir) then
      IO.println s!"fuzz: seed directory {d} not found, skipping"
      continue
    let files ← collectFiles p 4
    for f in files do
      seeds := seeds.push (← readPrefix f)
    IO.println s!"fuzz: {files.size} seed file(s) from {d}"
  return seeds

/-! ## Campaign -/

/-- Hex dump of at most the first `n` bytes. -/
def hexPrefix (b : ByteArray) (n : Nat) : String :=
  let digits := "0123456789abcdef".toList
  (b.extract 0 n).foldl (init := "") fun s x =>
    s.push (digits[(x >>> 4).toNat]?.getD '?') |>.push (digits[(x &&& 15).toNat]?.getD '?')

/-- FNV-1a fold of a byte array into a running 64-bit hash (for the determinism check). -/
def fnv (h : UInt64) (b : ByteArray) : UInt64 :=
  b.foldl (init := h ^^^ b.size.toUInt64) fun h x => (h ^^^ x.toUInt64) * 0x100000001b3

/-! ## Repetition mutator (task 13.6) -/

/-- A repeated shape: `pre`, then `n` copies of the unit, then `post`. With `numbered`, copy `i`
of the unit is `a ++ toString i ++ b`, so every copy differs (distinct dictionary keys). -/
structure Recipe where
  /-- Name, for failure reports. -/
  name : String
  /-- Frame before the repetition. -/
  pre : String
  /-- The unit, or its part before the counter. -/
  a : String
  /-- Part of the unit after the counter (empty unless `numbered`). -/
  b : String := ""
  /-- Frame after the repetition. -/
  post : String
  /-- Put a counter between `a` and `b`. -/
  numbered : Bool := false

/-- Recipes: tokens, operators, dictionary entries and objects, each in a frame where the shape
matters (a path, a dictionary, an array, an indirect object, a file with a trailer, a text
object). `path-lines` is the 13.1 shape, `dict-keys*` the 13.2 shape. -/
def recipes : Array Recipe :=
  #[{ name := "path-lines", pre := "0 0 m ", a := "1 1 l ", post := "f" },
    { name := "path-curves", pre := "0 0 m ", a := "1 2 3 4 5 6 c ", post := "S" },
    { name := "path-rects", pre := "", a := "0 0 1 1 re ", post := "f" },
    { name := "dict-keys", pre := "<< ", a := "/K", b := " 1 ", post := ">>", numbered := true },
    { name := "dict-keys-dup", pre := "<< ", a := "/K 1 ", post := ">>" },
    { name := "dict-keys-content", pre := "/T << ", a := "/K", b := " 1 ", post := ">> BDC",
      numbered := true },
    { name := "dict-keys-indirect", pre := "1 0 obj\n<< ", a := "/K", b := " 1 ",
      post := ">>\nendobj\n", numbered := true },
    { name := "dict-keys-file",
      pre := "%PDF-1.7\n1 0 obj\n<< /Type /Catalog ", a := "/K", b := " 1 ",
      post := ">>\nendobj\ntrailer\n<< /Root 1 0 R >>\n%%EOF\n", numbered := true },
    { name := "array-items", pre := "[ ", a := "1 ", post := "]" },
    { name := "array-open", pre := "", a := "[ ", post := "" },
    { name := "array-nested", pre := "", a := "[ 1 ", post := "" },
    { name := "dict-open", pre := "", a := "<< /A ", post := "" },
    { name := "gs-q", pre := "", a := "q ", post := "" },
    { name := "gs-Q", pre := "q ", a := "Q ", post := "" },
    { name := "text-show", pre := "BT /F1 12 Tf ", a := "(abc) Tj ", post := "ET" },
    { name := "text-array", pre := "BT /F1 12 Tf ", a := "[(a) -20 (b)] TJ ", post := "ET" },
    { name := "cm", pre := "", a := "1 0 0 1 1 1 cm ", post := "0 0 1 1 re f" },
    { name := "objects", pre := "%PDF-1.7\n", a := "", b := " 0 obj\n<< /A [1 2] >>\nendobj\n",
      post := "trailer\n<< /Size 1 >>\n%%EOF\n", numbered := true },
    { name := "xref-entries", pre := "xref\n0 1\n", a := "0000000000 65535 f \n",
      post := "trailer\n<< >>\nstartxref\n0\n%%EOF\n" },
    { name := "comments", pre := "", a := "% c\n", post := "1 0 obj null endobj" },
    { name := "refs", pre := "[", a := "1 0 R ", post := "]" },
    { name := "hex-strings", pre := "[", a := "<41>", post := "]" },
    { name := "string-escapes", pre := "(", a := "\\101", post := ")" },
    { name := "string-parens", pre := "", a := "( ", post := "" },
    { name := "names", pre := "[", a := "/N#20", post := "]" },
    { name := "whitespace", pre := "1 0 obj ", a := " \n", post := "null endobj" },
    { name := "numbers", pre := "[", a := "-0.5 ", post := "]" }]

/-- `n` copies of `u`. -/
def repeatBytes (u : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (n * u.size)
  for _ in [0:n] do
    out := out ++ u
  return out

/-- The repetition of a recipe's unit, `n` times (counter `0 .. n-1` when numbered). -/
def Recipe.body (r : Recipe) (n : Nat) : ByteArray :=
  if r.numbered then Id.run do
    let ab := r.a.toUTF8
    let bb := r.b.toUTF8
    let mut out := ByteArray.emptyWithCapacity (n * (ab.size + bb.size + 7))
    for i in [0:n] do
      out := out ++ ab ++ (toString i).toUTF8 ++ bb
    return out
  else repeatBytes (r.a ++ r.b).toUTF8 n

/-- Size of one copy of a recipe's unit (counter counted as 7 digits). -/
def Recipe.unitSize (r : Recipe) : Nat :=
  r.a.utf8ByteSize + r.b.utf8ByteSize + (if r.numbered then 7 else 0)

/-- Number of copies: `m * 10^(3+e)` (`m` in 1..9, `e` in 0..3), capped to `cap` bytes. -/
def repCount (g : Rng) (unit cap : Nat) : Nat × Rng :=
  let (e, g) := g.below 4
  let (m, g) := g.below 9
  (max 1 (min ((m + 1) * 10 ^ (3 + e)) (cap / max 1 unit)), g)

/-- A repetition input and a description of it. Cases `0 .. recipes.size-1` are recipes (a
third behind a `%PDF-1.7` header); the next two repeat a token or a short slice of a random
seed at a random position inside that seed. -/
def genLong (g : Rng) (cap : Nat) (seeds : Array ByteArray) (only : Option Nat := none) :
    ByteArray × String × Rng :=
  let (r, g) := g.below (recipes.size + 2)
  let r := only.getD r
  match recipes[r]? with
  | some rc =>
    let (n, g) := repCount g rc.unitSize cap
    let (h, g) := g.below 3
    let pre := if h == 0 then "%PDF-1.7\n" else ""
    ((pre ++ rc.pre).toUTF8 ++ rc.body n ++ rc.post.toUTF8,
      s!"rep {rc.name} x{n}", g)
  | none =>
    let (i, g) := g.below seeds.size
    let base := seeds[i]?.getD ByteArray.empty
    let (p, g) := g.below (base.size + 1)
    let (l, g) := g.below 32
    let isTok := r == recipes.size
    let len := if isTok then
        -- up to and including the next delimiter, at most 32 bytes
        let tail := (base.extract p (p + 32)).toList
        (tail.takeWhile (fun c => !(c == 32 || c == 10 || c == 13 || c == 47 || c == 91 ||
          c == 60 || c == 40))).length + 1
      else l + 1
    let u := base.extract p (p + len)
    let (n, g) := repCount g (max 1 u.size) cap
    (base.extract 0 p ++ repeatBytes u n ++ base.extract p base.size,
      s!"rep {if isTok then "token" else "slice"} x{n} unit {hexPrefix u 16}", g)

/-- Generate a short input (random bytes, or a mutated seed) for one iteration. -/
def genShort (g : Rng) (cfg : Config) (seeds : Array ByteArray) : ByteArray × Rng :=
  let (mode, g) := g.below 4
  if mode == 0 then
    -- random bytes, sometimes behind a header
    let (n, g) := g.below (cfg.maxLen + 1)
    let (body, g) := g.bytes n
    let (hdr, g) := g.below 2
    let (minor, g) := g.below 10
    let pre := if hdr == 0 then s!"%PDF-1.{minor}\n".toUTF8 else ByteArray.empty
    ((pre ++ body).extract 0 cfg.maxLen, g)
  else
    let (i, g) := g.below seeds.size
    let (j, g) := g.below seeds.size
    let base := (seeds[i]?.getD ByteArray.empty)
    let other := (seeds[j]?.getD ByteArray.empty)
    let (k, g) := g.below 8
    let (b, g) := mutate g base other (k + 1)
    -- keep large seeds whole (truncating them would never test the full file)
    (if base.size > cfg.maxLen then b else b.extract 0 cfg.maxLen, g)

/-- Generate the input for one iteration and a description of how it was made. With `--long`,
three iterations in four use the repetition mutator (never truncated to `--max-len`). -/
def genInput (g : Rng) (cfg : Config) (seeds : Array ByteArray) :
    ByteArray × String × Rng :=
  -- the extra draw only happens with `--long`, so the smoke profile's inputs are unchanged
  let (w, g) := if cfg.long then g.below 4 else (1, g)
  if cfg.long && w != 0 then
    genLong g cfg.longBytes seeds (cfg.recipe.bind fun n => recipes.findIdx? (·.name == n))
  else
    let (b, g) := genShort g cfg seeds
    (b, "short", g)

/-! ## Entry points under test -/

/-- Outcome class of one call: `0` ok, `1` malformed (including a structural cycle,
`Error.cycle`), `2` limit exceeded, `3` unsupported (including an encrypted document that
cannot be decrypted, `Error.encryption`). -/
def classify {α : Type} : Except Error α → Nat
  | .ok _ => 0
  | .error (.malformed ..) => 1
  | .error (.cycle ..) => 1
  | .error (.limitExceeded _) => 2
  | .error (.unsupported _) => 3
  | .error (.encryption _) => 3

/-- Limits with a small nesting depth, so the depth limit is hit often. -/
def shallowLimits : Limits := { maxObjectDepth := 8 }

/-- Names of the entry points, in the order `runEntry` numbers them. -/
def entryNames : Array String :=
  #["parse", "parseObjectAt@0", "parseObjectAt@rand", "parseObjectAt@0/depth8",
    "parseIndirectAt@0", "lexAll", "runBytes"]

/-- Call entry point `k` on `input` (`pos` is the pseudo-random position) and classify the
result. A lexer error counts as malformed. -/
def runEntry (k : Nat) (input : ByteArray) (pos : Nat) : Nat :=
  match k with
  | 0 => classify (SafePdf.parse input)
  | 1 => classify (SafePdf.parseObjectAt Limits.default input 0)
  | 2 => classify (SafePdf.parseObjectAt Limits.default input pos)
  | 3 => classify (SafePdf.parseObjectAt shallowLimits input 0)
  | 4 => classify (SafePdf.parseIndirectAt Limits.default input 0)
  | 5 => match SafePdf.Core.Lex.lexAll input with
    | .ok _ => 0
    | .error _ => 1
  | _ => -- page content: tokenizer and runner (13.1 path building, 13.2 inline dictionaries)
    let env : SafePdf.Core.Content.Env Unit Unit :=
      { cfg := {}, src := SafePdf.Core.Content.Source.empty, observe := fun w _ _ _ => w }
    let st := SafePdf.Core.Content.runBytes env [] input () ()
    if st.items.size == 0 then 1 else 0

/-- Per-entry-point counters. -/
structure Stat where
  /-- Calls returning `.ok`. -/
  ok : Nat := 0
  /-- `Error.malformed` (and lexer errors). -/
  malformed : Nat := 0
  /-- `Error.limitExceeded`. -/
  limit : Nat := 0
  /-- `Error.unsupported`. -/
  unsupported : Nat := 0
  /-- Calls slower than the threshold. -/
  slow : Nat := 0
  /-- Calls over their linear budget (failures). -/
  over : Nat := 0
  /-- Calls abandoned after twice their budget (failures). -/
  abandoned : Nat := 0
  /-- Largest cost in microseconds per KiB among inputs of at least `calibMin` bytes. -/
  maxUsKiB : Nat := 0
  /-- Slowest call in milliseconds. -/
  maxMs : Nat := 0

/-- Record one outcome class and duration. -/
def Stat.record (s : Stat) (c : Nat) (ms : Nat) (isSlow : Bool) (isOver : Bool)
    (usKiB : Nat) : Stat :=
  let s := match c with
    | 0 => { s with ok := s.ok + 1 }
    | 1 => { s with malformed := s.malformed + 1 }
    | 2 => { s with limit := s.limit + 1 }
    | _ => { s with unsupported := s.unsupported + 1 }
  { s with
    slow := s.slow + (if isSlow then 1 else 0)
    over := s.over + (if isOver then 1 else 0)
    maxMs := max s.maxMs ms
    maxUsKiB := max s.maxUsKiB usKiB }

/-- 64-bit hash as 16 hex digits. -/
def hashHex (hash : UInt64) : String :=
  hexPrefix ⟨#[(hash >>> 56).toUInt8, (hash >>> 48).toUInt8, (hash >>> 40).toUInt8,
    (hash >>> 32).toUInt8, (hash >>> 24).toUInt8, (hash >>> 16).toUInt8,
    (hash >>> 8).toUInt8, hash.toUInt8]⟩ 8

/-! ## Campaign loop -/

/-- Inputs below this size run inline; larger ones run in a watched thread so that a call that
never finishes is abandoned instead of hanging the campaign. -/
def watchBytes : Nat := 65536

/-- Inputs of at least this size count for the calibration figure (microseconds per KiB). -/
def calibMin : Nat := 65536

/-- Maximum number of abandoned (still running) calls before the campaign stops. -/
def maxAbandoned : Nat := 3

/-- The linear budget of entry point `k` on `size` bytes, in milliseconds. -/
def Config.budgetMs (cfg : Config) (k size : Nat) : Nat :=
  let us := if cfg.budgetUsPerKiB == 0 then budgetUsDefault[k]?.getD 25000 else cfg.budgetUsPerKiB
  cfg.budgetBaseMs + (size * us) / (1024 * 1000)

/-- Call entry point `k` and time it: outcome class (`none` when abandoned after `hardMs`) and
elapsed nanoseconds. Large inputs run in a dedicated thread that is polled every millisecond. -/
def timedCall (k : Nat) (input : ByteArray) (pos : Nat) (hardMs : Nat) :
    IO (Option Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  if input.size < watchBytes then
    -- `lazyPure` forces the pure call to run here, between the two clock reads
    let c ← IO.lazyPure (fun _ => runEntry k input pos)
    let t1 ← IO.monoNanosNow
    return (some c, t1 - t0)
  else
    let task := Task.spawn (prio := .dedicated) fun _ => runEntry k input pos
    let mut fin ← IO.hasFinished task
    while !fin do
      if (← IO.monoNanosNow) - t0 > hardMs * 1000000 then break
      IO.sleep 1
      fin ← IO.hasFinished task
    let t1 ← IO.monoNanosNow
    return (if fin then some task.get else none, t1 - t0)

/-- Run the campaign and print the summary: one line per entry point, then a total line with
the input hash (same arguments → same summary lines, apart from timing-dependent slow
counts; the slowest-call times are on a separate `timing` line). Returns the number of
failures (calls over their budget or abandoned). -/
def campaign (cfg : Config) : IO Nat := do
  if let some n := cfg.recipe then
    unless recipes.any (·.name == n) do
      throw (IO.userError s!"unknown recipe {n}; known: {", ".intercalate (recipes.toList.map (·.name))}")
  let seeds ← loadSeeds (cfg.seedDirs.getD ["Tests/adversarial", "corpus"])
  let rate := if cfg.budgetUsPerKiB == 0 then toString budgetUsDefault
    else toString cfg.budgetUsPerKiB
  IO.println s!"fuzz: iters={cfg.iters} seed={cfg.seed} max-len={cfg.maxLen} seeds={seeds.size} \
    long={cfg.long} long-bytes={cfg.longBytes} time-limit={cfg.timeLimit}s \
    budget={cfg.budgetBaseMs}ms+{rate}us/KiB"
  let start ← IO.monoNanosNow
  let mut g : Rng := ⟨cfg.seed.toUInt64⟩
  let mut stats : Array Stat := entryNames.map (fun _ => {})
  let mut slowInputs := 0
  let mut failures := 0
  let mut abandoned := 0
  let mut done := 0
  let mut totalBytes := 0
  let mut maxBytes := 0
  let mut hash : UInt64 := 0xcbf29ce484222325
  for it in [0:cfg.iters] do
    if cfg.timeLimit > 0 && (← IO.monoNanosNow) - start > cfg.timeLimit * 1000000000 then
      IO.println s!"fuzz: time limit {cfg.timeLimit}s reached after {done} iterations"
      break
    if abandoned ≥ maxAbandoned then
      IO.println s!"fuzz: stopping, {abandoned} calls abandoned"
      break
    let (input, desc, g') := genInput g cfg seeds
    let (pos, g') := g'.below (input.size + 1)
    g := g'
    done := done + 1
    totalBytes := totalBytes + input.size
    maxBytes := max maxBytes input.size
    hash := fnv hash input
    let mut slowHere := false
    for k in [0:entryNames.size] do
      let name := entryNames[k]?.getD "?"
      let budget := cfg.budgetMs k input.size
      let (c?, ns) ← timedCall k input pos (2 * budget)
      let ms := ns / 1000000
      let usKiB := if input.size ≥ calibMin then (ns / 1000) * 1024 / input.size else 0
      match c? with
      | none =>
        abandoned := abandoned + 1
        failures := failures + 1
        stats := stats.modify k fun s => { s with abandoned := s.abandoned + 1, maxMs := max s.maxMs ms }
        IO.println s!"fuzz: FAIL abandoned iteration {it} {name} (pos {pos}): no result after \
          {ms} ms (budget {budget} ms), {input.size} bytes, {desc}, prefix {hexPrefix input 32}"
      | some c =>
        let isSlow := ms > cfg.slowMs
        let isOver := ms > budget
        stats := stats.modify k (·.record c ms isSlow isOver usKiB)
        if isOver then
          failures := failures + 1
          IO.println s!"fuzz: FAIL over budget iteration {it} {name} (pos {pos}): {ms} ms > \
            {budget} ms, {input.size} bytes, {usKiB} us/KiB, {desc}, prefix {hexPrefix input 32}"
        else if isSlow then
          slowHere := true
          IO.println s!"fuzz: SLOW iteration {it} {name} (pos {pos}): \
            {ms} ms, {input.size} bytes, {desc}, prefix {hexPrefix input 32}"
    if slowHere then slowInputs := slowInputs + 1
  for k in [0:entryNames.size] do
    let s := stats[k]?.getD {}
    IO.println s!"fuzz: summary {entryNames[k]?.getD "?"}: ok={s.ok} \
      error={s.malformed + s.limit + s.unsupported} (malformed {s.malformed}, \
      limit {s.limit}, unsupported {s.unsupported}) slow(>{cfg.slowMs}ms)={s.slow} \
      over-budget={s.over} abandoned={s.abandoned}"
  -- timing varies between runs, so it is kept off the summary lines
  let maxes := (List.range entryNames.size).map fun k =>
    s!"{entryNames[k]?.getD "?"}={(stats[k]?.getD {}).maxMs}"
  IO.println s!"fuzz: timing (slowest call, ms): {" ".intercalate maxes}"
  let rates := (List.range entryNames.size).map fun k =>
    s!"{entryNames[k]?.getD "?"}={(stats[k]?.getD {}).maxUsKiB}"
  IO.println s!"fuzz: calibration (worst us/KiB on inputs >= {calibMin} bytes): \
    {" ".intercalate rates}"
  let elapsed := ((← IO.monoNanosNow) - start) / 1000000
  IO.println s!"fuzz: summary: iters={done} entry-points={entryNames.size} \
    slow-inputs={slowInputs} failures={failures} bytes={totalBytes} max-bytes={maxBytes} \
    input-hash={hashHex hash} elapsed-ms={elapsed}"
  return failures

end SafePdf.Fuzz

/-- Entry point of the `fuzz` executable. -/
def main (args : List String) : IO UInt32 := do
  match SafePdf.Fuzz.parseArgs {} args with
  | .error e =>
    IO.eprintln e
    IO.eprintln SafePdf.Fuzz.usage
    return 2
  | .ok cfg =>
    try
      let failures ← SafePdf.Fuzz.campaign cfg
      -- an abandoned call may still be running: leave without waiting for its thread
      if failures > 0 then
        IO.eprintln s!"fuzz: {failures} call(s) over budget"
        (← IO.getStdout).flush
        IO.Process.exit 3
      return 0
    catch e =>
      IO.eprintln s!"fuzz: CRASH (uncaught exception): {e}"
      return 1
