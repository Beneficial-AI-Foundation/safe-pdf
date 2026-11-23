import SafePdf.Core.Filter.Deflate

/-!
# Flate round-trip property suite (task 3.8)

Plan.md §6 Phase 3: "Correctness via round-trip with a Lean deflate on random data". For many
deterministic pseudo-random inputs (fixed seeds; sizes 0 … 200 000, around the 65535-byte
stored-block boundary; uniform and biased byte distributions) each encoder of
`SafePdf.Core.Filter.Deflate` (stored blocks, fixed Huffman with LZ77, fixed Huffman literals
only) is decoded by `Flate.flateDecode` (zlib wrapper, Adler-32 checked) and by raw
`Flate.inflate`, and the suite checks:

* with the limit equal to the input size, the output is exactly the input;
* with the limit one byte below the size, the result is
  `Error.limitExceeded .decodedStreamBytes`.

The stored-block round trip is also a theorem (`Deflate.inflate_deflateStored`,
`Deflate.zlibDecode_zlibStored`); fixed-Huffman blocks are checked only here.
-/

namespace SafePdf.Tests.FlateRoundTrip

open SafePdf
open SafePdf.Core.Filter.Flate
open SafePdf.Core.Filter.Deflate

/-- One step of a 31-bit linear congruential generator. -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- Byte distributions of the generated inputs. -/
inductive Dist where
  /-- Uniform over all 256 values (incompressible). -/
  | uniform
  /-- Uniform over the first `k` values. -/
  | alphabet (k : Nat)
  /-- Runs of one random byte, of random length 1 … 300. -/
  | runs
  /-- Mostly zero, one random byte in 16. -/
  | sparse
  /-- English-like text: skewed letter frequencies, spaces and newlines. -/
  | text

/-- Name of a distribution, for failure messages. -/
def Dist.name : Dist → String
  | .uniform => "uniform"
  | .alphabet k => s!"alphabet{k}"
  | .runs => "runs"
  | .sparse => "sparse"
  | .text => "text"

/-- Letters of `text`, most frequent first (repetition gives the skew). -/
def textAlphabet : ByteArray :=
  "eeeeeeeetttttaaaaoooiiinnnsssshhrrdlllcuumwfgypbvk          \n.,".toUTF8

/-- `n` bytes of distribution `d` from seed `seed`. -/
def gen (d : Dist) (n seed : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut x := seed
  let mut runByte : UInt8 := 0
  let mut runLeft := 0
  for _ in [0:n] do
    x := lcg x
    let r := x / 65536
    match d with
    | .uniform => b := b.push (r % 256).toUInt8
    | .alphabet k => b := b.push (r % k).toUInt8
    | .runs =>
      if runLeft == 0 then
        x := lcg x
        runByte := (x / 65536 % 256).toUInt8
        runLeft := r % 300 + 1
      b := b.push runByte
      runLeft := runLeft - 1
    | .sparse => b := b.push (if r % 16 == 0 then (r / 16 % 256).toUInt8 else 0)
    | .text => b := b.push (textAlphabet[r % textAlphabet.size]?.getD 32)
  return b

/-- The encoders under test: name and zlib-wrapped and raw outputs. -/
def encoders : List (String × (ByteArray → ByteArray) × (ByteArray → ByteArray)) :=
  [("stored", zlibStored, deflateStored),
   ("fixed+lz77", (zlibFixed · true), (deflateFixed · true)),
   ("fixed-literals", (zlibFixed · false), (deflateFixed · false))]

/-- Sizes tested: small, around powers of two, around the stored-block size 65535, up to
200 000. -/
def sizes : List Nat :=
  [0, 1, 2, 3, 4, 7, 100, 255, 256, 257, 1000, 4095, 4096, 32767, 32768, 32769, 65534, 65535,
    65536, 65537, 100000, 131070, 131071, 131072, 200000]

/-- Distributions tested. -/
def dists : List Dist :=
  [.uniform, .alphabet 2, .alphabet 4, .alphabet 16, .runs, .sparse, .text]

/-- Limits with the decoded-stream bound set to `n`. -/
def limitsOf (n : Nat) : Limits := { Limits.default with maxDecodedStreamBytes := n }

/-- `r` is `.ok` with exactly the bytes of `bs`. -/
def okEq (r : Except Error ByteArray) (bs : ByteArray) : Bool :=
  match r with
  | .ok o => o.data == bs.data
  | .error _ => false

/-- `r` is `Error.limitExceeded .decodedStreamBytes`. -/
def isLimit (r : Except Error ByteArray) : Bool :=
  match r with
  | .error (.limitExceeded .decodedStreamBytes) => true
  | _ => false

/-- Check one input against every encoder; returns the failure messages. -/
def checkInput (label : String) (bs : ByteArray) : List String := Id.run do
  let mut fails : List String := []
  for (name, zenc, raw) in encoders do
    let z := zenc bs
    let r := raw bs
    if !okEq (flateDecode (limitsOf bs.size) z) bs then
      fails := fails ++ [s!"{label} {name}: flateDecode round trip"]
    if !okEq (inflate bs.size r) bs then
      fails := fails ++ [s!"{label} {name}: raw inflate round trip"]
    if 0 < bs.size then
      if !isLimit (flateDecode (limitsOf (bs.size - 1)) z) then
        fails := fails ++ [s!"{label} {name}: limit size-1 not limitExceeded"]
      if !isLimit (inflate (bs.size - 1) r) then
        fails := fails ++ [s!"{label} {name}: raw limit size-1 not limitExceeded"]
  return fails

/-- Run the suite; returns the number of failures. -/
def run : IO Nat := do
  let mut cases := 0
  let mut failures := 0
  let mut seed := 2024
  -- Fixed sizes × distributions.
  for d in dists do
    for n in sizes do
      seed := lcg seed
      let fails := checkInput s!"{d.name} n={n} seed={seed}" (gen d n seed)
      cases := cases + 1
      for f in fails.take 3 do IO.println s!"  FAIL flate round trip: {f}"
      failures := failures + fails.length
  -- Random sizes (0 … 200 000, biased small) × distributions.
  for i in [0:40] do
    seed := lcg seed
    let n := if i % 2 == 0 then seed / 65536 % 2000 else seed / 1024 % 200001
    let d := dists[i % dists.length]?.getD .uniform
    let fails := checkInput s!"{d.name} n={n} seed={seed}" (gen d n seed)
    cases := cases + 1
    for f in fails.take 3 do IO.println s!"  FAIL flate round trip: {f}"
    failures := failures + fails.length
  -- All 256 byte values, ascending and descending.
  let asc : ByteArray := ⟨(List.range 256).toArray.map (·.toUInt8)⟩
  let desc : ByteArray := ⟨(List.range 256).reverse.toArray.map (·.toUInt8)⟩
  for (label, bs) in [("all-bytes-asc", asc), ("all-bytes-desc", desc)] do
    let fails := checkInput label bs
    cases := cases + 1
    for f in fails do IO.println s!"  FAIL flate round trip: {f}"
    failures := failures + fails.length
  IO.println s!"  flate round trip: {cases} input(s) × {encoders.length} encoder(s), {failures} failure(s)"
  return failures

end SafePdf.Tests.FlateRoundTrip
