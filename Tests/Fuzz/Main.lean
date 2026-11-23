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

Usage:
```
lake exe fuzz [--iters N] [--seed S] [--max-len L] [--slow-ms T] [--seeds DIR]...
```
Defaults: 10000 iterations, seed 1, max length 4096, slow threshold 100 ms, seed
directories `Tests/adversarial` and `corpus` (missing directories are skipped).

Exit code: 0 when the campaign completes; 1 if the shell part raised an uncaught exception;
2 on bad arguments. Since the entry points are pure and total, they cannot crash; a hang
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

/-- Parse command-line arguments. -/
def parseArgs (cfg : Config) : List String → Except String Config
  | [] => .ok cfg
  | "--iters" :: v :: rest => num v >>= fun n => parseArgs { cfg with iters := n } rest
  | "--seed" :: v :: rest => num v >>= fun n => parseArgs { cfg with seed := n } rest
  | "--max-len" :: v :: rest => num v >>= fun n => parseArgs { cfg with maxLen := n } rest
  | "--slow-ms" :: v :: rest => num v >>= fun n => parseArgs { cfg with slowMs := n } rest
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
  "usage: fuzz [--iters N] [--seed S] [--max-len L] [--slow-ms T] [--seeds DIR]..."

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

/-- Generate the input for one iteration. -/
def genInput (g : Rng) (cfg : Config) (seeds : Array ByteArray) : ByteArray × Rng :=
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

/-! ## Entry points under test -/

/-- Outcome class of one call: `0` ok, `1` malformed, `2` limit exceeded, `3` unsupported. -/
def classify {α : Type} : Except Error α → Nat
  | .ok _ => 0
  | .error (.malformed ..) => 1
  | .error (.limitExceeded _) => 2
  | .error (.unsupported _) => 3

/-- Limits with a small nesting depth, so the depth limit is hit often. -/
def shallowLimits : Limits := { maxObjectDepth := 8 }

/-- Names of the entry points, in the order `runEntry` numbers them. -/
def entryNames : Array String :=
  #["parse", "parseObjectAt@0", "parseObjectAt@rand", "parseObjectAt@0/depth8",
    "parseIndirectAt@0", "lexAll"]

/-- Call entry point `k` on `input` (`pos` is the pseudo-random position) and classify the
result. A lexer error counts as malformed. -/
def runEntry (k : Nat) (input : ByteArray) (pos : Nat) : Nat :=
  match k with
  | 0 => classify (SafePdf.parse input)
  | 1 => classify (SafePdf.parseObjectAt Limits.default input 0)
  | 2 => classify (SafePdf.parseObjectAt Limits.default input pos)
  | 3 => classify (SafePdf.parseObjectAt shallowLimits input 0)
  | 4 => classify (SafePdf.parseIndirectAt Limits.default input 0)
  | _ => match SafePdf.Core.Lex.lexAll input with
    | .ok _ => 0
    | .error _ => 1

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
  /-- Slowest call in milliseconds. -/
  maxMs : Nat := 0

/-- Record one outcome class and duration. -/
def Stat.record (s : Stat) (c : Nat) (ms : Nat) (isSlow : Bool) : Stat :=
  let s := match c with
    | 0 => { s with ok := s.ok + 1 }
    | 1 => { s with malformed := s.malformed + 1 }
    | 2 => { s with limit := s.limit + 1 }
    | _ => { s with unsupported := s.unsupported + 1 }
  { s with slow := s.slow + (if isSlow then 1 else 0), maxMs := max s.maxMs ms }

/-- 64-bit hash as 16 hex digits. -/
def hashHex (hash : UInt64) : String :=
  hexPrefix ⟨#[(hash >>> 56).toUInt8, (hash >>> 48).toUInt8, (hash >>> 40).toUInt8,
    (hash >>> 32).toUInt8, (hash >>> 24).toUInt8, (hash >>> 16).toUInt8,
    (hash >>> 8).toUInt8, hash.toUInt8]⟩ 8

/-! ## Campaign loop -/

/-- Run the campaign and print the summary: one line per entry point, then a total line with
the input hash (same arguments → same summary lines, apart from timing-dependent slow
counts; the slowest-call times are on a separate `timing` line). -/
def campaign (cfg : Config) : IO Unit := do
  let seeds ← loadSeeds (cfg.seedDirs.getD ["Tests/adversarial", "corpus"])
  IO.println s!"fuzz: iters={cfg.iters} seed={cfg.seed} max-len={cfg.maxLen} seeds={seeds.size}"
  let mut g : Rng := ⟨cfg.seed.toUInt64⟩
  let mut stats : Array Stat := entryNames.map (fun _ => {})
  let mut slowInputs := 0
  let mut totalBytes := 0
  let mut hash : UInt64 := 0xcbf29ce484222325
  for it in [0:cfg.iters] do
    let (input, g') := genInput g cfg seeds
    let (pos, g') := g'.below (input.size + 1)
    g := g'
    totalBytes := totalBytes + input.size
    hash := fnv hash input
    let mut slowHere := false
    for k in [0:entryNames.size] do
      let t0 ← IO.monoNanosNow
      -- `lazyPure` forces the pure call to run here, between the two clock reads
      let c ← IO.lazyPure (fun _ => runEntry k input pos)
      let t1 ← IO.monoNanosNow
      let ms := (t1 - t0) / 1000000
      let isSlow := ms > cfg.slowMs
      stats := stats.modify k (·.record c ms isSlow)
      if isSlow then
        slowHere := true
        IO.println s!"fuzz: SLOW iteration {it} {entryNames[k]?.getD "?"} (pos {pos}): \
          {ms} ms, {input.size} bytes, prefix {hexPrefix input 32}"
    if slowHere then slowInputs := slowInputs + 1
  for k in [0:entryNames.size] do
    let s := stats[k]?.getD {}
    IO.println s!"fuzz: summary {entryNames[k]?.getD "?"}: ok={s.ok} \
      error={s.malformed + s.limit + s.unsupported} (malformed {s.malformed}, \
      limit {s.limit}, unsupported {s.unsupported}) slow(>{cfg.slowMs}ms)={s.slow}"
  -- timing varies between runs, so it is kept off the summary lines
  let maxes := (List.range entryNames.size).map fun k =>
    s!"{entryNames[k]?.getD "?"}={(stats[k]?.getD {}).maxMs}"
  IO.println s!"fuzz: timing (slowest call, ms): {" ".intercalate maxes}"
  IO.println s!"fuzz: summary: iters={cfg.iters} entry-points={entryNames.size} \
    slow-inputs={slowInputs} bytes={totalBytes} input-hash={hashHex hash}"

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
      SafePdf.Fuzz.campaign cfg
      return 0
    catch e =>
      IO.eprintln s!"fuzz: CRASH (uncaught exception): {e}"
      return 1
