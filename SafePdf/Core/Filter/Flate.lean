import SafePdf.Core.Error
import SafePdf.Core.Limits

/-!
# FlateDecode: inflate (Plan.md §6 Phase 3, §4 S2/S3/S7; RFC 1950, RFC 1951)

A total, bounded decoder for DEFLATE (RFC 1951) and its zlib wrapper (RFC 1950), the
`/FlateDecode` filter of PDF. It sits in the trusted path (Plan.md §6 Phase 3).

## Guarantees

* **Totality (S2)**: every function is a plain `def`; loops terminate by explicit measures
  (no `partial`, no fuel crutch). See "Measures" below.
* **Output bound (S3)**: the output buffer is carried as `Out limit`, a `ByteArray` together
  with a proof that its size is at most `limit`. A literal is pushed only when
  `out.size < limit`, a back-reference or stored block is copied only when
  `out.size + len ≤ limit`; otherwise the decoder returns
  `Error.limitExceeded .decodedStreamBytes` at once, before allocating. Hence
  `inflate_size_le`, `zlibDecode_size_le` and `flateDecode_size_le` hold by construction.
* **Local failure (S7)**: malformed input gives `Error.malformed (byteOffset) msg`.

## Design

* Bit reader: the state is a bit position `pos` into the input (bit `i` is bit `i % 8`,
  least significant first, of byte `i / 8`). Reading past the end is an error
  ("truncated"); readers never return a position beyond `input.size * 8`.
* Huffman codes: canonical tables as in Mark Adler's `puff.c` (`counts[len]` and `symbols`
  sorted by code). The specification decoder `decodeGo` reads one bit at a time, at most 15
  steps (structural recursion). The hot path `decodeSym` (task 3.11) first probes a 512-entry
  lookup table indexed by the next 9 bits (`mkTable`, built for the literal/length and
  distance codes); each entry is *defined* as the result of the same bit-by-bit loop run on the
  9-bit index (`tableEntry`, `decodeGoB`), and the `Huffman` structure carries that fact
  (`table_ok`). Since the loop only depends on the bits it reads, `decodeSym_eq` proves the
  fast decoder equal to `decodeGo` in every outcome; no canonical-code theory is needed.
* Performance (task 3.11): compiled `Nat` left shifts and powers go through GMP even for small
  values, so the hot paths use multiplications by constants and the `twoPow` table instead;
  Adler-32 is a tail-recursive loop with division-free reductions (`adlerGo`), equal to the
  RFC fold (`adler32_eq_foldl`). Benchmark: `scripts/bench-flate.sh`.
* Back-references are copied byte by byte, so overlapping copies (distance < length) work.

## Measures

* `codes` (literal/length loop): `limit - out.size`; every literal or copy strictly grows
  `out` (lengths are ≥ 3) and end-of-block returns.
* `blocks` (block loop): `input.size * 8 - pos`; each block consumes at least its 3 header
  bits. The progress fact is checked by an unreachable guard (proof-patterns §3.2).
* `readLengths` (dynamic header): `total - lengths.size`; each code-length symbol adds ≥ 1.
* Huffman decode (≤ 15 bit steps) and back-reference copy (≤ 258 steps): structural.

Work bound: mechanised in `SafePdf/Spec/FlateWork.lean` (task 3.8b) with counted twins of
`decodeGo`/`codes`/`stored`/`readLengths`/`readDynamic`/`blocks` whose first component is
proved equal to the functions here: in every outcome, `flateDecode` takes at most
`3360 · input.size + 3 · limits.maxDecodedStreamBytes + 12163` steps
(`FlateWork.flateDecodeW_steps_le`), and on success `3360 · input.size + 3 · output.size +
12163` (`FlateWork.flateDecodeW_steps_le_of_ok`); the constants include the cost model of
the 9-bit lookup tables (task 3.11). The definitions here are unchanged by it.

## Zlib semantics followed (and deviations)

* Over-subscribed Huffman codes are rejected. Incomplete codes are rejected, except (as in
  zlib's `inftrees.c` and `puff.c`) for a literal/length or distance code whose only used
  length is 1 (a single one-bit code), and for an all-zero distance code (then any distance
  symbol is an error when decoded). The code-length code must be complete.
* HLIT > 286 or HDIST > 30 is an error; literal/length symbols 286, 287 and distance symbols
  30, 31 are errors when decoded; a missing end-of-block code (length of symbol 256 = 0) is
  an error; repeat code 16 at index 0 and repeats running past HLIT + HDIST are errors.
* A distance greater than the bytes produced so far is an error (no preset dictionary).
* Bytes after the final block (and after the Adler-32 trailer) are ignored.
* `zlibDecode` checks CM = 8, CINFO ≤ 7, FCHECK; FDICT = 1 is `Error.unsupported`. The
  Adler-32 trailer is verified when `checkAdler = true` (the default, strict path); a missing
  or wrong trailer is then `Error.malformed`. With `checkAdler = false` (for the repair path,
  since some PDF writers omit or garble the trailer) the trailer is not read at all.
  CINFO (window size) is checked for range but distances are bounded only by the bytes
  produced, as in zlib's inflate with the default window.
-/

namespace SafePdf.Core.Filter.Flate

open SafePdf

/-- An output buffer whose size is at most `limit` (Plan.md §4 S3). -/
abbrev Out (limit : Nat) := { b : ByteArray // b.size ≤ limit }

/-- The error for an output that would exceed the limit. -/
def limitErr : Error := .limitExceeded .decodedStreamBytes

/-- The error for reading past the end of the input, at bit position `pos`. -/
def truncated (pos : Nat) : Error := .malformed (pos / 8) "flate: truncated input"

/-! ## Bit reader -/

/-- Bit `i` of the input, least significant bit of each byte first; `none` past the end. -/
@[inline] def bitAt (input : ByteArray) (i : Nat) : Option Nat :=
  if h : i / 8 < input.size then some ((input[i / 8].toNat >>> (i % 8)) &&& 1) else none

/-- `2 ^ n` for `n ≤ 24`, as a table. The compiled code of `Nat` left shifts and powers goes
through GMP even for small values (task 3.11 profile), so the hot path multiplies by constants
and reads masks from here instead. -/
def twoPow : Array Nat :=
  #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
    262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216]

/-- `twoPow` holds the powers of two up to `2 ^ 24`. -/
theorem twoPow_getD {n : Nat} (h : n ≤ 24) : twoPow[n]?.getD 0 = 2 ^ n := by
  have : ∀ k : Fin 25, twoPow[k.val]?.getD 0 = 2 ^ k.val := by decide
  exact this ⟨n, by omega⟩

/-- Read `n ≤ 24` bits (least significant first) at bit position `pos`; returns the value and
`pos + n`. Errors if fewer than `n` bits remain. -/
def readBits (input : ByteArray) (pos n : Nat) : Except Error (Nat × Nat) :=
  if pos + n ≤ input.size * 8 then
    if n ≤ 24 then
      let i := pos / 8
      let w := (input[i]?.getD 0).toNat ||| ((input[i + 1]?.getD 0).toNat * 256) |||
        ((input[i + 2]?.getD 0).toNat * 65536) ||| ((input[i + 3]?.getD 0).toNat * 16777216)
      .ok ((w >>> (pos % 8)) % (twoPow[n]?.getD 0), pos + n)
    else .error (.malformed (pos / 8) "flate: internal: readBits width")
  else .error (truncated pos)

/-- The next 9 bits at bit position `pos` (least significant first), read from two bytes; only
meaningful when `pos + 9 ≤ input.size * 8` (see `peek9_bit`). -/
@[inline] def peek9 (input : ByteArray) (pos : Nat) : Nat :=
  let i := pos / 8
  (((input[i]?.getD 0).toNat ||| (input[i + 1]?.getD 0).toNat * 256) >>> (pos % 8)) % 512

/-- A bit extracted with a shift and a mask is a `testBit`. -/
theorem shiftRight_and_one (x k : Nat) : (x >>> k) &&& 1 = (x.testBit k).toNat := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

/-- Bit `t < 9` of the 9-bit window over two bytes `a ||| b * 256` shifted by `r < 8`. -/
theorem window_bit (a b r t : Nat) (ha : a < 256) (ht : t < 9) :
    (((a ||| b * 256) >>> r) % 512).testBit t =
      if r + t < 8 then a.testBit (r + t) else b.testBit (r + t - 8) := by
  rw [show (512 : Nat) = 2 ^ 9 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    show b * 256 = b <<< 8 by rw [Nat.shiftLeft_eq], Nat.testBit_or, Nat.testBit_shiftLeft]
  simp only [ht, decide_true, Bool.true_and]
  split
  · rename_i h
    simp only [show ¬ (r + t ≥ 8) by omega, decide_false, Bool.false_and, Bool.or_false]
  · rename_i h
    have : a.testBit (r + t) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega) : 2 ^ 8 ≤ 2 ^ (r + t)))
    simp only [this, show r + t ≥ 8 by omega, decide_true, Bool.true_and, Bool.false_or]

/-- **Peek correctness**: when 9 bits remain, bit `t < 9` of `peek9` is the input bit at
`pos + t`. -/
theorem peek9_bit {input : ByteArray} {pos t : Nat} (hp : pos + 9 ≤ input.size * 8)
    (ht : t < 9) : bitAt input (pos + t) = some ((peek9 input pos >>> t) &&& 1) := by
  have h0 : pos / 8 < input.size := by omega
  have h1 : pos / 8 + 1 < input.size := by omega
  have hi : (pos + t) / 8 < input.size := by omega
  unfold bitAt peek9
  simp only [hi, ↓reduceDIte]
  rw [getElem?_pos input (pos / 8) h0, getElem?_pos input (pos / 8 + 1) h1]
  simp only [Option.getD_some, shiftRight_and_one, Option.some.injEq]
  rw [window_bit _ _ _ _ (UInt8.toNat_lt _) ht]
  split
  · rename_i h
    have e1 : (pos + t) / 8 = pos / 8 := by omega
    have e2 : (pos + t) % 8 = pos % 8 + t := by omega
    simp only [e1, e2]
  · rename_i h
    have e1 : (pos + t) / 8 = pos / 8 + 1 := by omega
    have e2 : (pos + t) % 8 = pos % 8 + t - 8 := by omega
    simp only [e1, e2]

/-! ## Canonical Huffman codes (puff-style) -/

/-- Puff's bit-by-bit canonical decode over an abstract bit source `src` (`none` = no bit),
on the tables `counts`/`symbols`; `none` on any failure. Used only to fill the lookup table
(`tableEntry`); `decodeGo` below is the same loop over the input. -/
def decodeGoB (src : Nat → Option Nat) (counts symbols : Array Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _, _, _ => none
  | fuel + 1, len, code, first, index, p =>
    match src p with
    | none => none
    | some b =>
      let code := code ||| b
      let count := counts[len]?.getD 0
      if code < first + count then
        match symbols[index + (code - first)]? with
        | some s => some (s, p + 1)
        | none => none
      else decodeGoB src counts symbols fuel (len + 1) (code * 2) ((first + count) * 2)
        (index + count) (p + 1)

/-- On success `decodeGoB` consumes between `1` and `fuel` bits. -/
theorem decodeGoB_some {src : Nat → Option Nat} {counts symbols : Array Nat} :
    ∀ {fuel len code first index p s p'},
      decodeGoB src counts symbols fuel len code first index p = some (s, p') →
      p < p' ∧ p' ≤ p + fuel
  | 0, _, _, _, _, _, _, _, h => by simp [decodeGoB] at h
  | fuel + 1, len, code, first, index, p, s, p', h => by
    rw [decodeGoB] at h
    split at h
    · simp at h
    · dsimp only at h
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
        · simp at h
      · have := decodeGoB_some h; omega

/-- The 9-bit source for table index `v`: bit `t < 9` of `v`, nothing beyond. -/
def src9 (v t : Nat) : Option Nat := if t < 9 then some ((v >>> t) &&& 1) else none

/-- Lookup-table entry for the 9-bit pattern `v`: `s * 16 + k` if the first `k ≤ 9` bits of `v`
decode to symbol `s`, else `0` (fall back to the bit-by-bit decoder). -/
def tableEntry (counts symbols : Array Nat) (v : Nat) : Nat :=
  match decodeGoB (src9 v) counts symbols 9 1 0 0 0 0 with
  | some (s, k) => s * 16 + k
  | none => 0

/-- The 512-entry primary lookup table of a code (task 3.11). -/
def mkTable (counts symbols : Array Nat) : Array Nat :=
  Array.ofFn (n := 512) fun v => tableEntry counts symbols v.val

/-- A canonical Huffman code: `counts[len]` codes of each length `0..15`, and the symbols
ordered by code, with an optional lookup table (`table`, empty or `mkTable counts symbols`)
whose entries are, by `table_ok`, exactly `tableEntry`. -/
structure Huffman where
  /-- Number of codes of each length; index 0 counts unused symbols. -/
  counts : Array Nat
  /-- Symbols in canonical code order. -/
  symbols : Array Nat
  /-- Lookup table indexed by the next 9 input bits (see `tableEntry`); may be empty. -/
  table : Array Nat
  /-- Every table entry is the `tableEntry` of its index. -/
  table_ok : ∀ (v : Nat) (hv : v < table.size), table[v] = tableEntry counts symbols v

/-- A code from its tables, with the lookup table (`withTable`) or without. -/
def Huffman.ofTables (withTable : Bool) (counts symbols : Array Nat) : Huffman :=
  if withTable then
    { counts, symbols, table := mkTable counts symbols,
      table_ok := fun v hv => by simp [mkTable] }
  else
    { counts, symbols, table := #[], table_ok := fun v hv => by simp at hv }

instance : Inhabited Huffman := ⟨Huffman.ofTables false #[] #[]⟩

/-- One-bit-at-a-time canonical decode (puff's `decode`). `len` is the current code length,
`code` the bits read so far, `first` the first code of length `len`, `index` the index of
that code's symbol. At most `fuel` (= 15) bits are read. This is the specification of
`decodeSym`, which uses the lookup table first (`decodeSym_eq`). -/
def decodeGo (input : ByteArray) (h : Huffman) :
    Nat → Nat → Nat → Nat → Nat → Nat → Except Error (Nat × Nat)
  | 0, _, _, _, _, p => .error (.malformed (p / 8) "flate: invalid Huffman code")
  | fuel + 1, len, code, first, index, p =>
    match bitAt input p with
    | none => .error (truncated p)
    | some b =>
      let code := code ||| b
      let count := h.counts[len]?.getD 0
      if code < first + count then
        match h.symbols[index + (code - first)]? with
        | some s => .ok (s, p + 1)
        | none => .error (.malformed (p / 8) "flate: internal: Huffman table")
      else decodeGo input h fuel (len + 1) (code * 2) ((first + count) * 2)
        (index + count) (p + 1)

/-- **Transfer**: if `decodeGoB` decodes `s` from a source whose bits are input bits (offset
`p0`), then `decodeGo` with at least as much fuel decodes `s` from the input, consuming the
same bits. -/
theorem decodeGoB_decodeGo (input : ByteArray) (h : Huffman) (src : Nat → Option Nat)
    (p0 : Nat) (hsrc : ∀ t b, src t = some b → bitAt input (p0 + t) = some b) :
    ∀ {fuel fuel' len code first index j s j'}, fuel ≤ fuel' →
      decodeGoB src h.counts h.symbols fuel len code first index j = some (s, j') →
      decodeGo input h fuel' len code first index (p0 + j) = .ok (s, p0 + j')
  | 0, _, _, _, _, _, _, _, _, _, hr => by simp [decodeGoB] at hr
  | fuel + 1, fuel', len, code, first, index, j, s, j', hf, hr => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    rw [decodeGoB] at hr
    rw [decodeGo]
    rcases hs : src j with _ | b
    · rw [hs] at hr; simp at hr
    · rw [hs] at hr
      rw [hsrc j b hs]
      dsimp only at hr ⊢
      by_cases hc : (code ||| b) < first + h.counts[len]?.getD 0
      · simp only [hc, ↓reduceIte] at hr ⊢
        rcases hsym : h.symbols[index + ((code ||| b) - first)]? with _ | s'
        · rw [hsym] at hr; simp at hr
        · rw [hsym] at hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          rfl
      · simp only [hc, ↓reduceIte] at hr ⊢
        have := decodeGoB_decodeGo input h src p0 hsrc (fuel' := f) (by omega) hr
        rw [Nat.add_assoc]
        exact this

/-- Decode one symbol with code `h` at bit position `pos`; returns the symbol and new
position. Fast path: when 9 bits remain and the code has a lookup table, one table probe
gives the symbol and its length; otherwise (long codes, end of input, invalid codes, no table)
the bit-by-bit `decodeGo`. Equal to `decodeGo` by `decodeSym_eq`. -/
@[inline] def decodeSym (input : ByteArray) (h : Huffman) (pos : Nat) :
    Except Error (Nat × Nat) :=
  if pos + 9 ≤ input.size * 8 then
    match h.table[peek9 input pos]? with
    | some e =>
      if e % 16 == 0 then decodeGo input h 15 1 0 0 0 pos
      else .ok (e / 16, pos + e % 16)
    | none => decodeGo input h 15 1 0 0 0 pos
  else decodeGo input h 15 1 0 0 0 pos

/-- **Table decoding is bit-by-bit decoding** (task 3.11): the fast `decodeSym` computes
exactly puff's `decodeGo` with fuel 15, in every outcome. -/
theorem decodeSym_eq (input : ByteArray) (h : Huffman) (pos : Nat) :
    decodeSym input h pos = decodeGo input h 15 1 0 0 0 pos := by
  unfold decodeSym
  split
  · rename_i hp
    rcases he : h.table[peek9 input pos]? with _ | e
    · rfl
    · dsimp only
      split
      · rfl
      · rename_i hne
        rw [Array.getElem?_eq_some_iff] at he
        obtain ⟨hv, rfl⟩ := he
        rw [h.table_ok _ hv] at hne ⊢
        unfold tableEntry at hne ⊢
        rcases hd : decodeGoB (src9 (peek9 input pos)) h.counts h.symbols 9 1 0 0 0 0 with
          _ | ⟨s, k⟩
        · rw [hd] at hne; simp at hne
        · dsimp only
          have hk := decodeGoB_some hd
          have hsrc : ∀ t b, src9 (peek9 input pos) t = some b →
              bitAt input (pos + t) = some b := by
            intro t b hb
            unfold src9 at hb
            split at hb
            · rename_i ht
              simp only [Option.some.injEq] at hb
              subst hb
              exact peek9_bit hp ht
            · simp at hb
          have := decodeGoB_decodeGo input h _ pos hsrc (fuel' := 15) (by omega) hd
          simp only [Nat.add_zero] at this
          rw [this]
          have e1 : (s * 16 + k) / 16 = s := by omega
          have e2 : (s * 16 + k) % 16 = k := by omega
          rw [e1, e2]
  · rfl

/-- Which kind of code is being built; decides which incomplete codes are accepted. -/
inductive CodeKind where
  /-- The code-length code: must be complete. -/
  | codeLengths
  /-- Literal/length or distance code: incomplete only if a single one-bit code (or, for
  distance codes, no code at all). -/
  | litOrDist
  deriving DecidableEq

/-- Count the codes of each length (lengths ≥ 16 are counted nowhere and rejected by
`build`). -/
def countLengths (lengths : Array Nat) : Array Nat :=
  lengths.foldl (fun c l => c.modify l (· + 1)) (Array.replicate 16 0)

/-- Remaining code space after lengths `1..15` (puff's `left`), or `none` if
over-subscribed. Starts with `left = 1` at length 0. -/
def leftOver (counts : Array Nat) : Option Nat :=
  go 1 1 15
where
  /-- Loop over lengths `len .. len + fuel - 1`. -/
  go (len left : Nat) : Nat → Option Nat
    | 0 => some left
    | fuel + 1 =>
      let c := counts[len]?.getD 0
      if c ≤ left * 2 then go (len + 1) (left * 2 - c) fuel else none

/-- Offsets of the first symbol of each length in the sorted table: `offs[1] = 0`,
`offs[l + 1] = offs[l] + counts[l]`. -/
def offsets (counts : Array Nat) : Array Nat :=
  (List.range 15).foldl (fun o l => o.push (o[l + 1]?.getD 0 + counts[l + 1]?.getD 0))
    #[0, 0]

/-- Build a canonical Huffman code from per-symbol code lengths (RFC 1951 §3.2.2), checking
for over-subscribed and (per `kind`) incomplete codes. -/
def build (kind : CodeKind) (lengths : Array Nat) : Except Error Huffman :=
  if lengths.any (· > 15) then .error (.malformed 0 "flate: internal: code length > 15")
  else
    let counts := countLengths lengths
    match leftOver counts with
    | none => .error (.malformed 0 "flate: over-subscribed Huffman code")
    | some left =>
      let used := lengths.size - counts[0]?.getD 0
      let onlyOneBit := used == counts[1]?.getD 0
      let ok := left == 0 || (kind == .litOrDist && onlyOneBit)
      if !ok then .error (.malformed 0 "flate: incomplete Huffman code")
      else
        let offs := offsets counts
        let init : Array Nat × Array Nat := (offs, Array.replicate used 0)
        let (_, syms) := (List.range lengths.size).foldl (fun (st : Array Nat × Array Nat) s =>
          let l := lengths[s]?.getD 0
          if l == 0 then st
          else
            let o := st.1[l]?.getD 0
            (st.1.modify l (· + 1), st.2.setIfInBounds o s)) init
        .ok (Huffman.ofTables (kind == .litOrDist) counts syms)

/-- Code lengths of the fixed literal/length code (RFC 1951 §3.2.6). -/
def fixedLitLengths : Array Nat :=
  (Array.replicate 144 8) ++ (Array.replicate 112 9) ++ (Array.replicate 24 7) ++
    (Array.replicate 8 8)

/-- The fixed literal/length code. -/
def fixedLit : Huffman :=
  match build .litOrDist fixedLitLengths with
  | .ok h => h
  | .error _ => default

/-- The fixed distance code: 32 codes of length 5 (a complete code, as in zlib); symbols 30
and 31 are rejected when decoded. -/
def fixedDist : Huffman :=
  match build .litOrDist (Array.replicate 32 5) with
  | .ok h => h
  | .error _ => default

/-! ## Length and distance tables (RFC 1951 §3.2.5) -/

/-- Base lengths for symbols 257..285. -/
def lenBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
    131, 163, 195, 227, 258]

/-- Extra bits for symbols 257..285. -/
def lenExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

/-- Base distances for distance symbols 0..29. -/
def distBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

/-- Extra bits for distance symbols 0..29. -/
def distExtra : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12,
    13, 13]

/-! ## Back-reference copy -/

/-- Append `n` bytes, each copied from `d` bytes before the current end (overlap-safe). -/
def copyBack (d : Nat) (hd : 0 < d) : (n : Nat) → (b : ByteArray) → d ≤ b.size → ByteArray
  | 0, b, _ => b
  | n + 1, b, h =>
    copyBack d hd n (b.push b[b.size - d]) (by simp [ByteArray.size_push]; omega)

/-- `copyBack` appends exactly `n` bytes. -/
theorem copyBack_size (d : Nat) (hd : 0 < d) (n : Nat) (b : ByteArray) (h : d ≤ b.size) :
    (copyBack d hd n b h).size = b.size + n := by
  induction n generalizing b with
  | zero => simp [copyBack]
  | succ n ih => simp [copyBack, ih, ByteArray.size_push]; omega

/-! ## Block decoding -/

set_option maxRecDepth 4000 in
/-- Decode literal/length and distance symbols until end-of-block (RFC 1951 §3.2.5). Returns
the output and the bit position after the end-of-block code. -/
def codes (input : ByteArray) (limit : Nat) (lit dist : Huffman) (out : Out limit)
    (pos : Nat) : Except Error (Out limit × Nat) :=
  match decodeSym input lit pos with
  | .error e => .error e
  | .ok (sym, p1) =>
    if sym < 256 then
      if h : out.1.size < limit then
        codes input limit lit dist
          ⟨out.1.push sym.toUInt8, by simp [ByteArray.size_push]; omega⟩ p1
      else .error limitErr
    else if sym == 256 then .ok (out, p1)
    else if 29 ≤ sym - 257 then .error (.malformed (pos / 8) "flate: invalid length symbol")
    else
      match readBits input p1 (lenExtra[sym - 257]?.getD 0) with
      | .error e => .error e
      | .ok (le, p2) =>
        let len := lenBase[sym - 257]?.getD 0 + le
        match decodeSym input dist p2 with
        | .error e => .error e
        | .ok (ds, p3) =>
          if 30 ≤ ds then .error (.malformed (p2 / 8) "flate: invalid distance symbol")
          else
            match readBits input p3 (distExtra[ds]?.getD 0) with
            | .error e => .error e
            | .ok (de, p4) =>
              let d := distBase[ds]?.getD 0 + de
              if hd : 0 < d ∧ d ≤ out.1.size then
                if hl : 0 < len ∧ out.1.size + len ≤ limit then
                  codes input limit lit dist
                    ⟨copyBack d hd.1 len out.1 hd.2, by rw [copyBack_size]; omega⟩ p4
                else .error limitErr
              else .error (.malformed (p3 / 8) "flate: invalid distance too far back")
termination_by limit - out.1.size
decreasing_by
  all_goals simp only [ByteArray.size_push, copyBack_size]
  all_goals omega

/-- A stored block (RFC 1951 §3.2.4) starting at bit position `pos` (just after the block
header): skip to a byte boundary, check `LEN`/`NLEN`, copy `LEN` bytes. -/
def stored (input : ByteArray) (limit : Nat) (out : Out limit) (pos : Nat) :
    Except Error (Out limit × Nat) :=
  let byte := (pos + 7) / 8
  if h : byte + 4 ≤ input.size then
    let len := input[byte].toNat ||| (input[byte + 1].toNat <<< 8)
    let nlen := input[byte + 2].toNat ||| (input[byte + 3].toNat <<< 8)
    if len + nlen != 65535 then
      .error (.malformed byte "flate: invalid stored block lengths")
    else if input.size < byte + 4 + len then .error (truncated ((byte + 4) * 8))
    else if hl : out.1.size + len ≤ limit then
      let chunk := input.extract (byte + 4) (byte + 4 + len)
      .ok (⟨out.1 ++ chunk, by
          simp only [ByteArray.size_append, chunk, ByteArray.size_extract]; omega⟩,
        (byte + 4 + len) * 8)
    else .error limitErr
  else .error (truncated pos)

/-- The order in which code-length code lengths are stored (RFC 1951 §3.2.7). -/
def clOrder : List Nat := [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Read the 3-bit code-length code lengths for the symbols in `order`. -/
def readClLengths (input : ByteArray) : List Nat → Array Nat → Nat →
    Except Error (Array Nat × Nat)
  | [], acc, p => .ok (acc, p)
  | s :: ss, acc, p =>
    match readBits input p 3 with
    | .error e => .error e
    | .ok (l, p') => readClLengths input ss (acc.setIfInBounds s l) p'

/-- Read `total` literal/length + distance code lengths with the code-length code `cl`,
expanding repeat codes 16, 17, 18 (RFC 1951 §3.2.7). -/
def readLengths (input : ByteArray) (cl : Huffman) (total : Nat) (acc : Array Nat)
    (pos : Nat) : Except Error (Array Nat × Nat) :=
  if _hdone : total ≤ acc.size then .ok (acc, pos)
  else
    match decodeSym input cl pos with
    | .error e => .error e
    | .ok (sym, p1) =>
      if sym < 16 then readLengths input cl total (acc.push sym) p1
      else
        let r : Except Error (Nat × Nat × Nat) :=
          if sym == 16 then
            match acc.back? with
            | none => .error (.malformed (pos / 8) "flate: invalid bit length repeat")
            | some prev => (readBits input p1 2).map fun (e, p) => (prev, 3 + e, p)
          else if sym == 17 then (readBits input p1 3).map fun (e, p) => (0, 3 + e, p)
          else (readBits input p1 7).map fun (e, p) => (0, 11 + e, p)
        match r with
        | .error e => .error e
        | .ok (v, n, p2) =>
          if h : 0 < n ∧ acc.size + n ≤ total then
            readLengths input cl total (acc ++ Array.replicate n v) p2
          else .error (.malformed (pos / 8) "flate: invalid bit length repeat")
termination_by total - acc.size
decreasing_by
  all_goals simp only [Array.size_push, Array.size_append, Array.size_replicate]
  all_goals omega

/-- Read a dynamic block header (RFC 1951 §3.2.7) and build its two codes. -/
def readDynamic (input : ByteArray) (pos : Nat) : Except Error (Huffman × Huffman × Nat) := do
  let (hlit, p1) ← readBits input pos 5
  let (hdist, p2) ← readBits input p1 5
  let (hclen, p3) ← readBits input p2 4
  let nlen := hlit + 257
  let ndist := hdist + 1
  if 286 < nlen ∨ 30 < ndist then
    throw (.malformed (pos / 8) "flate: too many length or distance symbols")
  let (cll, p4) ← readClLengths input (clOrder.take (hclen + 4)) (Array.replicate 19 0) p3
  let cl ← (build .codeLengths cll).mapError
    (fun _ => .malformed (p3 / 8) "flate: invalid code lengths set")
  let (lens, p5) ← readLengths input cl (nlen + ndist) #[] p4
  if lens[256]?.getD 0 == 0 then
    throw (.malformed (p4 / 8) "flate: invalid code -- missing end-of-block")
  let lit ← (build .litOrDist (lens.extract 0 nlen)).mapError
    (fun _ => .malformed (p4 / 8) "flate: invalid literal/lengths set")
  let dist ← (build .litOrDist (lens.extract nlen (nlen + ndist))).mapError
    (fun _ => .malformed (p4 / 8) "flate: invalid distances set")
  return (lit, dist, p5)

/-- Decode DEFLATE blocks starting at bit position `pos` until the final block. Returns the
output and the bit position after the final block. -/
def blocks (input : ByteArray) (limit : Nat) (out : Out limit) (pos : Nat) :
    Except Error (Out limit × Nat) :=
  match readBits input pos 3 with
  | .error e => .error e
  | .ok (hdr, p1) =>
    let final := hdr &&& 1
    let btype := hdr >>> 1
    let r : Except Error (Out limit × Nat) :=
      if btype == 0 then stored input limit out p1
      else if btype == 1 then codes input limit fixedLit fixedDist out p1
      else if btype == 2 then
        match readDynamic input p1 with
        | .error e => .error e
        | .ok (lit, dist, p2) => codes input limit lit dist out p2
      else .error (.malformed (pos / 8) "flate: invalid block type")
    match r with
    | .error e => .error e
    | .ok (out', p') =>
      if final == 1 then .ok (out', p')
      else if _h : pos < p' ∧ p' ≤ input.size * 8 then blocks input limit out' p'
      else .error (.malformed (pos / 8) "flate: internal: no progress")
termination_by input.size * 8 - pos

/-! ## Entry points -/

/-- Raw DEFLATE (RFC 1951) from bit position `pos`, output at most `limit` bytes. Returns the
output and the bit position after the final block. `cap` (task 8.10) is the capacity reserved
for the output buffer (`ByteArray.emptyWithCapacity`): with the expected output size the
buffer never grows by doubling (a reallocation copies it and briefly holds both). It is not
observable (`inflateAt_cap`). -/
def inflateAt (limit : Nat) (input : ByteArray) (pos : Nat) (cap : Nat := 0) :
    Except Error (Out limit × Nat) :=
  blocks input limit ⟨ByteArray.emptyWithCapacity cap, Nat.zero_le limit⟩ pos

/-- The reserved capacity does not change the result. -/
theorem inflateAt_cap (limit : Nat) (input : ByteArray) (pos cap : Nat) :
    inflateAt limit input pos cap = inflateAt limit input pos := rfl

/-- Raw DEFLATE (RFC 1951): decompress `input`, failing with
`Error.limitExceeded .decodedStreamBytes` as soon as the output would exceed `limit`.
Bytes after the final block are ignored. -/
def inflate (limit : Nat) (input : ByteArray) : Except Error ByteArray :=
  (inflateAt limit input 0).map (·.1.1)

/-- One Adler-32 step (RFC 1950 §8.2): add byte `x` to the sums `(a, b)`. -/
def adlerStep (st : Nat × Nat) (x : UInt8) : Nat × Nat :=
  let a := (st.1 + x.toNat) % 65521
  (a, (st.2 + a) % 65521)

/-- `x % 65521` for `x < 2 · 65521`, by one conditional subtraction (no division). -/
@[inline] def mod65521 (x : Nat) : Nat := if x < 65521 then x else x - 65521

/-- `mod65521` is `% 65521` below `2 · 65521`. -/
theorem mod65521_eq {x : Nat} (h : x < 2 * 65521) : mod65521 x = x % 65521 := by
  unfold mod65521
  split <;> omega

/-- The Adler-32 sums `(a, b)` after folding bytes `i, i+1, …` of `data` into `(a, b)`: a
tail-recursive loop without a pair or a division per byte (task 3.11). For sums below 65521
it is the left fold of `adlerStep` (`adlerGo_eq_foldl`). -/
def adlerGo (data : ByteArray) (i a b : Nat) : Nat × Nat :=
  if h : i < data.size then
    let a' := mod65521 (a + data[i].toNat)
    adlerGo data (i + 1) a' (mod65521 (b + a'))
  else (a, b)
termination_by data.size - i

/-- Adler-32 checksum (RFC 1950 §8.2). -/
def adler32 (data : ByteArray) : Nat :=
  let (a, b) := adlerGo data 0 1 0
  b * 65536 + a

/-- The loop `adlerGo` is the left fold of `adlerStep`. -/
theorem adlerGo_eq_foldl (data : ByteArray) :
    adlerGo data 0 1 0 = data.foldl adlerStep (1, 0) := by
  unfold ByteArray.foldl ByteArray.foldlM
  simp only [Nat.le_refl, ↓reduceDIte]
  suffices hl : ∀ (n j : Nat) (st : Nat × Nat), data.size - j ≤ n → st.1 < 65521 →
      st.2 < 65521 → adlerGo data j st.1 st.2 =
        (ByteArray.foldlM.loop (m := Id) (fun x1 x2 => pure (adlerStep x1 x2)) data data.size
          (Nat.le_refl _) n j st).run by
    exact hl (data.size - 0) 0 (1, 0) (by omega) (by decide) (by decide)
  intro n
  induction n with
  | zero =>
    intro j st hj _ _
    unfold ByteArray.foldlM.loop adlerGo
    have : ¬ j < data.size := by omega
    simp only [this, ↓reduceDIte]
    rfl
  | succ n ih =>
    intro j st hj ha hb
    unfold ByteArray.foldlM.loop
    rw [adlerGo]
    split
    · rename_i hlt
      have hx := data[j].toNat_lt
      have e1 : mod65521 (st.1 + data[j].toNat) = (adlerStep st data[j]).1 := by
        rw [mod65521_eq (by omega)]; rfl
      have e2 : mod65521 (st.2 + mod65521 (st.1 + data[j].toNat)) =
          (adlerStep st data[j]).2 := by
        rw [e1, mod65521_eq]
        · rfl
        · have : (adlerStep st data[j]).1 < 65521 := Nat.mod_lt _ (by decide)
          omega
      dsimp only
      rw [e2, e1]
      exact ih (j + 1) (adlerStep st data[j]) (by omega) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide))
    · rfl

/-- Adler-32 as the left fold of `adlerStep` from `(1, 0)` (its RFC 1950 definition). -/
theorem adler32_eq_foldl (data : ByteArray) :
    adler32 data = (let (a, b) := data.foldl adlerStep (1, 0); b * 65536 + a) := by
  unfold adler32
  rw [adlerGo_eq_foldl]

/-- Zlib stream (RFC 1950), with the output's size bound in its type; see `zlibDecode`. -/
def zlibDecodeOut (limit : Nat) (input : ByteArray) (checkAdler : Bool) (cap : Nat := 0) :
    Except Error (Out limit) :=
  if h : 2 ≤ input.size then
    let cmf := input[0].toNat
    let flg := input[1].toNat
    if cmf &&& 15 != 8 then .error (.malformed 0 "zlib: unknown compression method")
    else if 7 < cmf >>> 4 then .error (.malformed 0 "zlib: invalid window size")
    else if (cmf * 256 + flg) % 31 != 0 then .error (.malformed 1 "zlib: incorrect header check")
    else if flg &&& 32 != 0 then .error (.unsupported "zlib: preset dictionary (FDICT)")
    else
      match inflateAt limit input 16 cap with
      | .error e => .error e
      | .ok (out, p) =>
        if !checkAdler then .ok out
        else
          let i := (p + 7) / 8
          if hi : i + 4 ≤ input.size then
            let stored := (input[i].toNat <<< 24) ||| (input[i + 1].toNat <<< 16) |||
              (input[i + 2].toNat <<< 8) ||| input[i + 3].toNat
            if stored == adler32 out.1 then .ok out
            else .error (.malformed i "zlib: incorrect data check")
          else .error (.malformed i "zlib: missing Adler-32 trailer")
  else .error (.malformed 0 "zlib: truncated header")

/-- Zlib stream (RFC 1950): 2-byte header (CM = 8, CINFO ≤ 7, FCHECK; FDICT = 1 is
unsupported), DEFLATE body, then the big-endian Adler-32 of the output, verified when
`checkAdler` (strict default; the repair path may pass `false` to accept a missing or wrong
trailer). Trailing bytes after the trailer are ignored. Output at most `limit` bytes. `cap`:
the output buffer's reserved capacity (`inflateAt`; not observable, `zlibDecode_cap`). -/
def zlibDecode (limit : Nat) (input : ByteArray) (checkAdler : Bool := true) (cap : Nat := 0) :
    Except Error ByteArray :=
  (zlibDecodeOut limit input checkAdler cap).map (·.1)

/-- `/FlateDecode` without predictor: a zlib stream, output bounded by
`limits.maxDecodedStreamBytes`. `cap`: the output buffer's reserved capacity (task 8.10; not
observable, `flateDecode_cap`). -/
def flateDecode (limits : Limits) (input : ByteArray) (checkAdler : Bool := true)
    (cap : Nat := 0) : Except Error ByteArray :=
  zlibDecode limits.maxDecodedStreamBytes input checkAdler cap

/-- The reserved capacity does not change a zlib decode. -/
theorem zlibDecodeOut_cap (limit : Nat) (input : ByteArray) (checkAdler : Bool) (cap : Nat) :
    zlibDecodeOut limit input checkAdler cap = zlibDecodeOut limit input checkAdler := rfl

/-- The reserved capacity does not change a zlib decode. -/
theorem zlibDecode_cap (limit : Nat) (input : ByteArray) (checkAdler : Bool) (cap : Nat) :
    zlibDecode limit input checkAdler cap = zlibDecode limit input checkAdler := rfl

/-- The reserved capacity does not change `/FlateDecode`. -/
theorem flateDecode_cap (limits : Limits) (input : ByteArray) (checkAdler : Bool) (cap : Nat) :
    flateDecode limits input checkAdler cap = flateDecode limits input checkAdler := rfl

/-! ## Output bound (Plan.md §4 S3) -/

/-- **Output bound**: a successful raw inflate produces at most `limit` bytes. -/
theorem inflate_size_le {limit : Nat} {input out : ByteArray}
    (h : inflate limit input = .ok out) : out.size ≤ limit := by
  unfold inflate at h
  cases hr : inflateAt limit input 0 with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    simp only [hr, Except.map, Except.ok.injEq] at h
    subst h; exact r.1.2

/-- **Output bound**: a successful zlib decode produces at most `limit` bytes. -/
theorem zlibDecode_size_le {limit : Nat} {input out : ByteArray} {checkAdler : Bool}
    (h : zlibDecode limit input checkAdler = .ok out) : out.size ≤ limit := by
  unfold zlibDecode at h
  cases hr : zlibDecodeOut limit input checkAdler with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    simp only [hr, Except.map, Except.ok.injEq] at h
    subst h; exact r.2

/-- **Output bound** for `/FlateDecode`: at most `limits.maxDecodedStreamBytes` bytes. -/
theorem flateDecode_size_le {limits : Limits} {input out : ByteArray} {checkAdler : Bool}
    (h : flateDecode limits input checkAdler = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes :=
  zlibDecode_size_le h

/-! ## Test vectors

Generated with CPython's `zlib` (scratch script, not in the repo): `zlib.compress(data, level)`
for levels 0, 1, 6, 9 and `zlib.compressobj(wbits=-15)` for raw DEFLATE. Negative vectors
were built with a bit writer and each one checked to be rejected by `zlib.decompress`. Big
outputs are checked by size and Adler-32 (as computed by Python) rather than byte by byte. -/

section Tests

/-- Hex string to bytes; non-hex characters are skipped (test helper). -/
private def ofHex (s : String) : ByteArray :=
  go (s.toList.filterMap fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87) else none) ByteArray.empty
where
  /-- Pair up nibbles. -/
  go : List Nat → ByteArray → ByteArray
    | a :: b :: r, acc => go r (acc.push (a * 16 + b).toUInt8)
    | _, acc => acc

/-- Success with exactly these bytes. -/
private def okEq (r : Except Error ByteArray) (expected : ByteArray) : Bool :=
  match r with
  | .ok o => o.data == expected.data
  | .error _ => false

/-- Success with this size and this Adler-32. -/
private def okSum (r : Except Error ByteArray) (size adler : Nat) : Bool :=
  match r with
  | .ok o => o.size == size && adler32 o == adler
  | .error _ => false

/-- Failure with `Error.malformed`. -/
private def isMalformed (r : Except Error ByteArray) : Bool :=
  match r with
  | .error (.malformed _ _) => true
  | _ => false

/-- Failure with `Error.limitExceeded .decodedStreamBytes`. -/
private def isLimit (r : Except Error ByteArray) : Bool :=
  match r with
  | .error (.limitExceeded .decodedStreamBytes) => true
  | _ => false

/-- Failure with `Error.unsupported`. -/
private def isUnsupported (r : Except Error ByteArray) : Bool :=
  match r with
  | .error (.unsupported _) => true
  | _ => false

/-- A generous limit for the positive tests. -/
private def big : Nat := 1 <<< 24

-- Adler-32 (RFC 1950 §9 example values, cross-checked with Python's `zlib.adler32`).
#guard adler32 ByteArray.empty == 1
#guard adler32 "hello".toUTF8 == 103547413
#guard adler32 "Wikipedia".toUTF8 == 300286872
#guard adler32 (ByteArray.mk (Array.replicate 65536 0)) == 983041

-- Empty input, levels 0, 1, 6, 9.
#guard okEq (zlibDecode big (ofHex "7801010000ffff00000001")) ByteArray.empty
#guard okEq (zlibDecode big (ofHex "7801030000000001")) ByteArray.empty
#guard okEq (zlibDecode big (ofHex "789c030000000001")) ByteArray.empty
#guard okEq (zlibDecode big (ofHex "78da030000000001")) ByteArray.empty

-- "hello", levels 0 (stored), 1, 6, 9 (fixed Huffman), and raw DEFLATE.
#guard okEq (zlibDecode big (ofHex "7801010500faff68656c6c6f062c0215")) "hello".toUTF8
#guard okEq (zlibDecode big (ofHex "7801cb48cdc9c90700062c0215")) "hello".toUTF8
#guard okEq (zlibDecode big (ofHex "789ccb48cdc9c90700062c0215")) "hello".toUTF8
#guard okEq (zlibDecode big (ofHex "78dacb48cdc9c90700062c0215")) "hello".toUTF8
#guard okEq (inflate big (ofHex "cb48cdc9c90700")) "hello".toUTF8
#guard okEq (flateDecode Limits.default (ofHex "789ccb48cdc9c90700062c0215")) "hello".toUTF8

-- 1 KiB of text: level 1 (fixed), levels 6 and 9 (dynamic), level 0 (stored, below).
#guard okSum (zlibDecode big (ofHex
  "78010bc94855282ccd4cce56482aca2fcf5348cbaf50c82acd2d2856c82f4b2d5228014ae72456552aa4e4a7eb2904b8b829149714a526e6162b9416a72ab8e52496a4baa426e7a7a4ea29848c9a341a4ea3a96088e516001a936a32"))
  1024 445868594
#guard okSum (zlibDecode big (ofHex
  "789cedcccb0d80201005c0565e055461387ba00184f50baeb2e0af7a6dc384f3246346c25e26b7a04b7caee8f9c25ce226e08312f2c7c13e373c0f0a6da32139918d8222041d6ca6861c7b523075aa539d7e36bd1a936a32"))
  1024 445868594
#guard okSum (zlibDecode big (ofHex
  "78daedcccb0d80201005c0565e055461387ba00184f50baeb2e0af7a6dc384f3246346c25e26b7a04b7caee8f9c25ce226e08312f2c7c13e373c0f0a6da32139918d8222041d6ca6861c7b523075aa539d7e36bd1a936a32"))
  1024 445868594

-- 64 KiB of zeros (long, overlapping back-references), zlib and raw.
#guard okSum (zlibDecode big (ofHex
  "78daedc101010000008090feafee080a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006a000f0001"))
  65536 983041
#guard okSum (inflate big (ofHex
  "edc101010000008090feafee080a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006a"))
  65536 983041

-- Hand-built fixed blocks: a back-reference, and an overlapping copy of length 258.
#guard okEq (inflate big (ofHex "4b040200")) "aaaa".toUTF8
#guard okSum (inflate big (ofHex "4b4c1a8500")) 260 (adler32 (ByteArray.mk
  ((List.range 260).map (fun i => if i % 2 == 0 then (97 : UInt8) else 98)).toArray))

/-- Python `zlib.compress(text1k, 0)`: a stored block. -/
private def text1kL0Z : ByteArray := ofHex
  "7801010004fffb54686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a792064
   6f672e205044462073747265616d732075736520466c6174654465636f64652e2054686520717569636b2062726f776e
   20666f78206a756d7073206f76657220746865206c617a7920646f672e205044462073747265616d732075736520466c
   6174654465636f64652e2054686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c61
   7a7920646f672e205044462073747265616d732075736520466c6174654465636f64652e2054686520717569636b2062
   726f776e20666f78206a756d7073206f76657220746865206c617a7920646f672e205044462073747265616d73207573
   6520466c6174654465636f64652e2054686520717569636b2062726f776e20666f78206a756d7073206f766572207468
   65206c617a7920646f672e205044462073747265616d732075736520466c6174654465636f64652e2054686520717569
   636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f672e205044462073747265616d
   732075736520466c6174654465636f64652e2054686520717569636b2062726f776e20666f78206a756d7073206f7665
   7220746865206c617a7920646f672e205044462073747265616d732075736520466c6174654465636f64652e20546865
   20717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f672e20504446207374
   7265616d732075736520466c6174654465636f64652e2054686520717569636b2062726f776e20666f78206a756d7073
   206f76657220746865206c617a7920646f672e205044462073747265616d732075736520466c6174654465636f64652e
   2054686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f672e205044
   462073747265616d732075736520466c6174654465636f64652e2054686520717569636b2062726f776e20666f78206a
   756d7073206f76657220746865206c617a7920646f672e205044462073747265616d732075736520466c617465446563
   6f64652e2054686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67
   2e205044462073747265616d732075736520466c6174654465636f64652e2054686520717569636b2062726f776e2066
   6f78206a756d7073206f76657220746865206c617a7920646f672e205044462073747265616d732075736520466c6174
   654465636f64652e2054686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a79
   20646f672e205044462073747265616d732075736520461a936a32"

/-- Python `zlib.compress(bytes(1 << 20), 9)`: 1 MiB of zeros in 1039 bytes. -/
private def zeros1mZ : ByteArray := ofHex
  "78daedc13101000000c2a0f54f6d085fa000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
   000000000000000000000000000000000000000000000000003e0300f00001"

/-- Python `zlib.compress(uniform random 10 KiB, 6)` (seed 1234): stored blocks. -/
private def uni10kZ : ByteArray := ofHex
  "789c010028ffd7e13b032e112a32b579080f08b1f7ed4c2e5d3a07f97f21ee232d178a209af6b5887f66e8092402aa49
   f2c1551b27fe53266e490db138489ce814d58d145a8b4f994fed15c5b2fdaeeff317f157e1e0978c3f5fd5df3d34f8c0
   8262b03750894fa5e42428ca6d189213702ca29ceb218325da6733cb63eb78b869d759689a1eb44efff1aa474318544a
   23a657001f2c4b6f14ddc8a66ac38f9bd8a34d2f858ed2cc8d3ac08c6d98cb1ab2e177fb54c29d0125f5ca98dbf55fcd
   f45090bdb16956eaf20eef350dbbf32147a9b29498a996638e2568adaba4ea882b3d7d83be460eca13166a4fa0b5de23
   9c85f870b22a09a97553f4ff47224a7c54c9a742e414be23bcd11624a07465b1c2fc1a0fe52996daae4bf87b0fb6bed4
   5926096c6448438219efb9be93cbd0bc779204a0883d126fbd5ea495b98b5ae95601d17a62e38b59b5d1f8f6f5e3be34
   cd4136f0f93143837a24abc896b5cf60f2eea3e237ed2b26655aab58c18b66870f50a133171c85d9a5ae9dde55c0ca04
   9491a27f4f63e7e3d5ac89dec884fca17e925053d2501177b569dce30ccf2320247dc3f8c2799aa7e7209b0d5c494bc0
   db5a469a30faab4488dcf18ea15521e075e27f22884f8c4ac96f664a6cafd300b161720809b9e17905d4d8fed7a97ff8
   9cf0080a953fe77dcad66b15dcc839d35b5925bc577520c21041890eb01e8c0917d2f60f935d76fa1f967ce4ea598652
   d59f0495a6695e109dff09d953dead923028d6ab13d1e25dcf36a96133ca2da24025a9f6862720e605b4126e37e45b15
   88cc9e10acaf6c2c7c329908222b0e98b0dc09c8e92c6f28b2abb4c6b5300f4244e6b740311f885110adfc2adeb809d7
   a1625475d857ddff47c2f3c59c8d8449b743859f7f97554fe91d85d6bc19b20413659c61f3c690a1c4d48be41cab8363
   a130cebabada97c7d1908356e8b7665d1fc1e84379c09bbed28272a7e2a03f54805acfe6858de62e54e9fb181d9a6cc2
   43d224604e94be955cdff01a7bf4c831511b3a314b423ff1bd350a296945a0c183d896b8e57520a0186899cdbffc9c83
   555ea20a14afa8b8e83edf2996d536a545c989f615c003d00e712020bebafa141e0009703dc58e768298202695aaafd9
   f313e9d5a66c6a668b06d20fef038bdd071bd0d8552de47813743086046bccc40d604931ad34292f3be71067cecb66a8
   ac1d1fd6d1e372e3e7b9a792f93889fbb8efa6354a5e368cd295e9898b2d17f4a5e3331c7e106a2e31cccbbba9308b64
   47b2ba8ef714ee15d90d6438985c87db5195fc232764afe931ec39fafec8909525d672119d4dfe84ffa67b7ee434cc3c
   2a671fc69b7dcb5e6163457e3f079a8d69421f97c7a1e679564adefc44a25646fce7a9b059746b3984b8f6916ac829b9
   cacbc77362b782544546de80e98bdf7ec9c82823a09d1b17300b22f78475835f312738ae0fbb9b47eee432d9e138f454
   e447b30b69780c41b1b6530078174c6d299fadc8b821838cb6c7432a107d7f124d31daefb5abcb19df9aa05b29b7e52f
   90dae57e3c6dc8e78c87399ad2be3281e8be9b30e33a93b7ff56601bc2b5ac14b48cec73e80a11ff35a33d6c84b0db61
   109d80bdcbe4a37a5dd70788f4919daf8fb9cf5d995232460d23afa10f3596fca9f4d9781f41d2ced485a839d95e0992
   cf04f6278c56ff8e5819c3c91f17aea31b97b4703bcb48d065d8f98715eaea5911cb24e14a258373ca7adfa50f6b4266
   ab97b1bf7b508319a7328c47330f17b173460e0cd1fba8b04ffc4ded80b2b4fe8e3eec880870ede1871f9c8678f7c08d
   9f17501e2d36a215c3b186ff8369c71fffb83d53d7a847272430e6b0ff4767059384765046452008fedd7e5380d8d324
   4db5ae874fb8db19952e0e4bdb659ac24837e572fe3ed7358e453d4781c7ab64c3112e142fedc6df8dd688985b52949f
   6e7faf343981eca6ca9cd91bad95864b5c141a120988b0f95f83b4bd333611e5a497dd6d084446dd8d006a37abde7cd3
   ebf018203739ab868ceb269922864cb60dbe21160aed9a06163ff9be6b5ea04c151ef530743f8e9456910909e924416d
   24f90cfaedd0aa665764a72b4d9ab6f2d59994cb284d9891d2617fd56c8baebd794cac8c64679122fb09257edb08a2b2
   46d735952bbb1b4d9fa5406e7ebeeaa2bfce7219c8363ee04c09e1538ce48d970462bbbf35c8c21a7de3000667c577d6
   38291e349e1b61ecd4584435bc78a84f3d8b4d76c20b7a347002f057e89d977789a2022bd789dd912685ff54e74396a9
   a894a549649768e11d00f8c3b9cdf3a15dea7dcf65054fb3ee28d345c52d5464d75d19a317e2df9d55f77d2e49bf74c1
   42a034f86a9eb2591617373f5bbc70b959ae2646ab409d18eda4bb0b85d0178b9a41f14508323a877cd48b336b0a430e
   de6e9e1468d44e272f4513c4cedbdb7fd3e2434a6b8493300f15184eca87208898836a043070291ee4c51d15a92655a9
   3cc95965a36c0935d065aa14065740fdfac11b7bbdb9823ce3922ddb7cda5d9bb1f2d17e3dd0b8a793d023c99214a855
   8e88722430e77912e006e41838e9cc7b185c4dfb3399865cc1b58df3e2c044dfe02503ef11a24f3b569cd6eea17f30d6
   c782a2e71f7ab1f71ba550184b405b711ec9e3f1e50736174db65c4c20fdbadc5637d86e346e119fd6599fb75b17c483
   6c61b9c3bf4186205574a6e90eb679e3b16285f35ad36044eb3ea15cb727d2095e9c19e8d469226615d94d05e2fef630
   23caa6e798b4fe0cf61329b83a28c1cddea8b7cdd1edc252e32b323c159263af5bf4948f52be7e28fb2f9a4f7dc4922d
   90ae7efcc21d7411394e4339ecc2af348f84b68fa2ac89e9c994d344da98f1c247f264da686ba0040cb9f28790bdebfb
   7d375675f14a460fce8ddd8d2e8f74310f636f3043d8d46dbeb2d1e519db0057b394100da03154081ae383af26e2278a
   42534fd438244c8c2e18fef0e745ac22029943cebf9bdb7f257f250a547777812f4d67f99662311fa7c31648b8218f54
   9ae3baf1af82bdfdb30e983468ef60f2422cb6801c9a61b76314fc45caed9477fcc8f90dcdd637821b5031d6a6aadd05
   f160da15d04dae8e7d9bdf0acf7ef7055aea611769b7ebe79e72dc187f4dc2af7ea6a4c3cb5c43a22bebda26848526e5
   740ba092f2d02bc20a1949bccf2aabe5d53c741bf74fb5cbd6837536a4ba66c0ca9df4f704581a6c98c42c70fa3b206f
   00d516e5fd99923911361b46af63fc704fddf1a95c40410d60f4b1036e55a21ad87e9fefbfb7eeb620d7c5ce4aeaceb8
   3ef446ff2c2596ca459d417411544a46cb5edaf256132dae938f57fc26e7016d2ddb632e06592999271612cfd3d095cd
   52c897cdcef4c0028e80db59e29cc4a97c7d418366563a785bcd011a44f62da02471b2d40fa279b902e92add89ea598b
   fe0acda2ba863b51b5879f28fbb5de6f9457bed4a65805241f0320d78c07674f7b58e24c8385010b635fa2b74ff40307
   a0ba663b9546fc9cfc51e63ed1800182fb9e86f90fdd0f2a61d666b19d3740f11de14d665f919a0fb2aa1a636242bba1
   bcce34a19b30342e990201a326283cee2a15d4bebff050d604f137253bb9e8944e4f4668d98207c4d8647ce9b048e850
   f051373ea69958105f7bea55a89ec5a6a7bc9dc6a647b4f0e52fbd8e5e1dde3e15fcecc196e9f4d280ef750aa023450c
   2e359e484d3a154e25620ac55852a32a65881e9435b286cf19f6531e2fa37ca9ff1d45638c5f166285e1eb472e6425a8
   ab3c903dfeff607837f483a04bb01054cde8001a8dec35b009ee7dbaeb5f6420ab0f5a519c29dc9e29ce2374a356bccc
   1e681012cf5fd734e4c8eb22e9ed7ebfd149890059ac3d610d5e5fde95b2024150eee536095f59edfd60d7576735735f
   c1e989395cc12c474947479a956279d2921aa04a33333d6cb153e7cd4712d0f1080d104531d22da91d3100eed10a0171
   481e1ab2195d8fbde0ba883be728bbb53843474db25fb4b465dc48d0171349c05c0830234f4274bf0c74052345f14a70
   891d888f00d376775f8f9b98d1a50ba14829c2fa19dd67bfd48580ba693408f2d5efe02564f5a64e5ca8bd9bc3f8b84b
   09809ac810224a8e56a95fb527158979e1f4adcd8de66506c397f9917883ee752a2acb9b03723722458485a9b46b2d12
   5f5e7dbc9ef68569ad567f74457b94d92e0f3b52f72441e937baa5eb0f3430e573f8563741ed3859837cde52ad8d8343
   2e2578a1a33b390e317eea62101675443485073077b2be3663992a8a6a2b3e3cfe72da1e2c0ce147e9e75928904422b0
   057411fa8932afdd1746c21dd8e5d118ba6affa9d542d4327222be2917af115efa9fdf75c19127f1c59665e32581a18b
   a2787252163608e09a20ddf23b6bcfd634fd22cc759ceb08522e5402e813e3cb8458028d3aebd3fe8a132605eb7e955c
   ac7938797ca77703de118ee9442d772aad0d6990869e51b37619ab9517a84ea4cd05f260f76e892f7719a7d6979d654b
   ad66ee026d440cf17cb9f4246727ef9f86f5776e3eb60898db36812010f225aeb83d17d7650468c17bbeff94f8a01514
   730eeff30e6d3e065fd748c0c4587a495822cf73097306f102e5f22b0bc9d08c928f132134d104928afc1577809a8a82
   abd47d8471a1e8a6722d0c1318842e05e082509399f4cac5d1bd9228a5a5162c9ef23c57d531dda3d671bcbf88ae3298
   93b33aed7d877c8b577b40f22936642b7b131d8e66323ceed5dec7554655c3d44635fa330ca086ce7cd4ab453675d189
   ad9f585575fd3ee95f4d9aec592e35514f7047cf76da523bf7a1ec6caff69694912240629ea68de94d4b2a1815ed6d25
   6ad1dcff351d2b8a4f21d0b934e8254335acbaa34172c3b9f9482d60e30b970b344c9c52f9c48796cfdfdd95be3934da
   6b91df077cfccc2b9e628f59f111f1246424f625321877acb546d2117966854356f9c1e07e2844a0b14c252e23a18dfb
   0dd1bfe509c62ff2d165cbddd57d37de774cd241f82a993d1643839cc4f1244eb2dc6a3e8b3b27e3f6bc8b136fc06564
   e932fe3ee445a811253b662cf473d3a5a312fd6f1da9faecfe774f02d3737f08c4898aeed6a7f6658e57ef02ebe7e94a
   025ff45d03ee649ccf3d41e68b46478c8d61b15dbd195483ed79a8f937cb958e8060c4a93924c1d3338406c10f01ba22
   52330fa199042e7cc7b069c202627be9e2be64862c57bec797d5fd0ae629155c8f6b6aa5d8272dcae2815ff5aac6e5ce
   44737d2c2407e007a4b5dfcce362e3a32388b38ee3fdbdc131eed87536117020ae0f40eccb619c29c62842cde71c468e
   fb73d4bbe2da4e122a140dc45f17825058405a43a2a954b2562247c166124aceefd5cc02a5ceb1b0b884d7fbb2884f7d
   ee126178c7c7493ac6eb668ec47d82c04bf9125ba47bccf9a95172a80b9385330e6f31a2f99905ec4f27def3f306a7b8
   7dea317dcdb3ee1c44cc98204a36a017efc0b3013583990c05718b71193c1c7b2a085ed4a051802a9339a287ff8d6e72
   1dc2c3543acd49989b478c1443b341b3823a2fca7eecb3c97438811cd6bcb5c818ebdd35d5c03d49d281efcd8d0871f0
   dc107c5f030c6daa8e218fa495cab614a5430a0e3b35b2a2a068b1891b3d43e008db6f7fe36a1457fa0cf4b94de88a22
   314927fbe749e824b91a1f563e34185bca3bb991a1f897f3f09748682341f0edef6c27b39889ec4e7c2d62ec12a105f6
   ac889a77278a7033d6caa4a48bf9938c3fcc3ddcdd1ce4b8c51f578d143d88660e5e8f24341f05485e0db83cc27b09d0
   fb64c1fa0e9c6f0d1bfed66fa135cdfc77af1d34da89a3a070d13bb560d2a5cfccdb1fe7ccd54d37d27968bc246922b7
   134577cf02631902c98cbafaf5d6114ee8c4390615b513eefd1a92ffd496fa81996f0506ebf49568a8f577bd2adc6274
   422130ba0eb9c3585da94b2d58ea858bb8ab26850930674040a8b6fe1e757f0cbfa9f5b79181b7426cb24dd5be857e8c
   bf3696b750ba8a2ae107889557d36fc84d9ef1d4fadfc84d79ad7818bf323fc9792eb51691f80d8c5600ab8ba7c84d98
   3c40ac71c724eb4518855bede2201f7fd18df4fce9deefd60bb406d257730e6233e8f99c5e9dcf63fd57596fd0362194
   6de7565e962d53d96fb5cd4090c435f43e927f96e2bef891c8ab26c345f4d28733114ca4b91c8e6463a9515cf3664bf7
   d3798fd13bab22072e50bb9349adb5db2e2cb50276f65b617e57a120ec57bad1c309cb3af04010d0ac8449a5864c6248
   1b3fad2ef2e513783c1acadf30508d241fb8d821a3e031bed84139920f6d172ba1849070f0e44f6078998b7a638f3bf1
   6528544b69173b80827427d80ce989d33829d8188487cc51d364930ae57e32165692608bfafcc2df22a59ffd2e9ec88c
   023be564e32c747318ba0f5a9989ed0ff93bef3c6ed58d21ac9218237ab88a87948718c57d1ca498b1543ea2764ed60b
   62e69378b1810bd5308dc47ff71d8530264de323772b108b67970bf0c0cad812c4c17caf6e9cc4d4e5263ea01e683501
   d7a1c972b850a26d0b7c27550f4c700e1c4283215600e65b85f3de108fa601f4af4a1fbba0b6af132849372d2eea80e6
   d1035a052c5899193ebedb95d0cb034ddb2af067f2d9fd743681e716a52f76fdcb19cfccb7617b20e86f205d7b5b9e06
   fe86d4ec4dd81cf117da973824145bcc66361203a6641722d3b694cdb32650f0b54d315ba5f26d36ca52dccce8863893
   cf47efe2f41fa4b968262ddd4bc42372adfe9d04a9ecb2c96f402ab9547975eabfcd0fe1d68e8976e47693d602dafa95
   c09c1b3edbcf5c97c1b97a7bb5f20a4fe18f6ac8bd6db629c4a54d46c9e295c7f5378b6ca88ee9f46dcb2e93a3bc3300
   97e3e1a1c41e05983a4d028cf9d1adc65bdf8bb18904e31b410f063a486d58856514b3ce591f683602c87f5b844b3a7d
   f8c97f450a4c3559a1ac32cbba642d42d90e6b10e11d39dc2e7ea3b2141977d945c73a7035cff729e68161c5cfe8dba1
   ddfa5953c946bea7bff0fe32cde5189d24f34147353ec6e74eef8231134c0bf28ab96bf9d3282288964e95a61b19b9de
   88871c394d44c60a920b5621083c312c13d4bf8fb3710e8d1a5fff6228a213e7216800c89644a2b9b8d2a03b3e4b32b8
   6278162c6cccc31fb2ecc0a00be93d5e2ee4deb58d6577ea2a004219b54c924367f1ef11f5f22e5b74dcc709c06200d8
   06692d75927c10d5c29a1656a8c03c1785e1377dba26cc91e3c7d5a6632c35c08664399642df21f91cb0b6c5e4d2e6ab
   adad39ebf236c95420e610bf0e8855d3d624fb8d197f13dda0583dd4404cd900e9f5ac6688ad31d9d01448930a0417ac
   46aeb3dbb39fdd6694ae86275743c1cc49ceba6eb8151a3716bfd390efe01d868a7670fa4c152df92bcd916ac3668b7e
   c144bf7ec98688e245692a6f67e431cbb0ef850e93169fd850dc9087125103a57e9e5cdc4d3a16a7f1119cc0f5403568
   686b1f83fbdfdfe3f0d06cd9d800ef78dca61777151b07cd90cc24ad6ed8865164163c7ff6a711f9f24722dc29c0408b
   4856ea133f250bd13a247119a7d3cacfc19cf53c9bba7a76e8c277ee5e92ed9aa2b66a8487860df0fba195d7076471c1
   dfae4d896e6d78f8f7fa3fd2a738e311306e05e60c6d69ca3fbe287f6bbeefdd89bdc4d48cb4538c6f740481967ecbda
   6ce16a6cd48cc66fc61437d9bfb8a05645349e04a1d12cea1ac850eb35ae49191750320c07093594ca1567ffb043654b
   43bd6d1169cb9dbe11a82d103547ab5b6c92afa02d25feab6840954fe7f1355872e361c7a01be4b8ead385311b5b3bd9
   8eb7efdb5048affa0bcd4b84b1532b161bff3f10853be7b573d92d79f4caa294fbcd868695991bcaac5a0de079131e4b
   f48b4085b462fe6df18303ed86b000936e36b256e03b92b8e6b1d4928ea53f4e6da54fb819324bc6dae1d61ed380713f
   59336f9dde8273413d8475fbd0deb295696781e510d22c8bb5d9df9212ef694441b92fb38c7b1de9dc58d993315024e9
   5abb8321d814962f32374a40e680d6fe1d877c2b2b18d6833470f34a691efba094ee21aeb78b094354df70778be82e62
   d1ac7e8097da3715189342062ebd3f906f71a4d1cf60d731d116704b32a2be6d6c109598df9ef4297f2619b3f30ef350
   4f4eb15a4fe4ead49766a77b4dbc4f8be7d71123256ce05544ce34fea74dcc3f2cbd6cacbbbca0e9c3592bbfb6db2107
   75a999c40bf14fe320c7c31b01d803633482cb56e84b6f3d8730d496c76417bff1e46563d52a013c383e6ad27727d2d9
   22c9925177d931d904312255c3ad68906bbc2fca1d7c59511ef7186c17e643f30d438a8b9ea668bd81358e7b52bd769d
   0d54670809eacc3d3f9a16ea15b6bdfde942b238606a28b84a4ee903a13f05ef85eed318a6f3c617b63c53fa662df01f
   6986a477dd5f7249701be78eced95fc8cc2535303b032ac784a7f4353027824fdc2276c5994809fb050fcb842845ff33
   729fe4edf7d94a0d119f168e2552d8ac5ca3fd2d77e210f87375a7fe7f89d213321de2b4d1a0c8b2de834697e9f17f14
   6e45a7ea744bb4ca409fb4c81d1b303a1c7d7369a210cfa2902707f12e7cde6318fb596c0485d02e3587d753468b1f06
   68663f74d0de610c255731e5717c26609d930998080852021d0b82639a9d10db98ca1c841cb0658ceb45ca2b40b386b8
   6e8759c5c63b2d1b529e0aa4d71fb0205ddef44c22750ef548accf2c7ba2574144f58ea87b7fcfaa8097cd9110a74215
   1c616c66ecb776642ddfd9ff427c7da2fba2715ecc3c82bdcee9034ca379ca2cf22ed19718dfd11538140a6362493e14
   7a9fd281192ece0db6ebb447d5684cf284a33ad84b7b2438ab23b3f942d0306340e76929d88996b3faba2f70ba6a5a9c
   4368190ba8931e0281665508878525d6a862db32b505b08e4d23b059515187835b3d1d606249f0e34ea71c3d48546a0f
   d320a18b26cfe20e57b72c15c01eeb3897b564f90e9b5bee1db2812c686ca3a8020205172532e829f72fd7333e0ac4d2
   1a6dc7c3267495ed1d42e037828a5fcc80214c9233224b8ba660fde0f2d475fb3d40c75fdaa51acbbc086d998d6f2f42
   75f9e72250f83ed52281fab56e2ac0d3aa6584686924910a4f304c2cddeb4a9934c502ac8a090e490e4794a4991c32e4
   3ec5a7adae2577729b43e0fb45095ea240a82b07366c600c5057fe2cb26d4b7f820cab444896dd61f2cd0df257625593
   7f7fb4dc47479b6b99aa650c195887eb9798df7772e3b84356ed2437881047df22477bd01c7c46b5f01ead578454b468
   5997446348c86fe75e4413374c28e199ed665d34ab328167ba3de995ab01ae205ba5abac7e3aa173a05f1e8a260a9157
   61acf64016ca7be39ba3171787e2ddb667daedf603d2ba00e8b50b07f3f9f73b6635342862e63cf8cc927e1df25fb0e3
   ca7f1d65d484fc4234146924c15244230be5e790123af4da8365c923b28373f07fe49b43c7cc2ba704b01ca16a0eb201
   955385ff5387d126928ddcf31a40395300a7eed9a9f45affc70878d0d66cff692471b53d524b273a489e9d7f1a2e26e7
   733e30dc052273d1a6b55dfb9f0133b052149887b2f6e48986019d19ae073dbadd66f4cfdc9db3a5d3b3a03a04f111c0
   39f58666205b9ba75dc553e3c0ee331449bef2a8bea0a8939eb07d9d7b523c1bb022e5af937a749abb5e4ee9a0fdae6b
   d9035a641cc56510047afbb58d5687660e304ea5b040a34f3d02f852ee750666230cf5bb3721ad226313596ef0b34149
   358032fb3a9b6d507b159510de2bb88352cbc50585af5a212519dfb688e035953bbed23d562e8aea8cbd212cf4552f23
   7dc980b78f9b84917f1e88ae38ac8a7836748d94dd8d2724a261fe376681b3be29ea2490570a95ef25a679f611122878
   25090b89a167daeaa54be10fb4e1a00e3fcb6fce91f59a35d6d7d2d600ad7982ab90a9af7ddc1e7f3a53cd85b08f3259
   9296fa035f185d219372fa54519eaaed25fbb2aef95f16bdca0206f130876b947a991d7a97cb89a15142445f327824ab
   8b164796971832e45465baaa5c047433dbd40c4915c8d14d65c31aade3b355286a0064ee1fc82d2a01cc246db5f08023
   af69b36d916c6b04446f22ab92ae45622578eb7222a581e46ec73e8bf65da7239efa7122a93c3058bd156a449cdfd521
   3cd0f542f06d0f6a346b2ece70098ad43d45d2c49272f2f8e6b3ba5af0d2987c31135c9759309ed28c1fab6d09ef42e3
   488148f1b54495942c2e413fc238b732d2ee50cef76ad7497c3538279e7600ea47620dc24c17fc6feb25387a5d8093b5
   b352317f719c09e1c58eaaee41b544495f61ad144ff28e2677a6fc957a5f4625efbb6c2760455c3a22e41393782f05a5
   b6277c31e164b289a9fbb264143708c59d271af1fd6370855a8bb84c2ec365ba7195ebbbeab186f157eb70720fc578af
   6e089316068b43529411bb78f0ac25d9d86fe0497ccb1ac63a76ec1a4db6383468975953060cfc90469738740ad05ee7
   319c1d44e12723a20c4977178d566f679193f7735364797e30e541745416cdc8d18340e8e95d053cc900f7beb4898e17
   8e24455d5151c56bc0e15c726e3700b26d029edf472c1c541bd342713f9d77e46b2a7fae4a7916abd699f88ba4692c40
   e74b98db5f417c24ec4ac44d36ec28888fdd7da8124f1583a4ef126d80937d513d604aa3f746498a50b771bfbde44bcc
   36398f4b4d7d00a00b5e2e9c31e18d4fc67a78c38498ca8fd07137713d8975739c06c43a0cc500711f92447e90d0298e
   f49183abcc4a8bb0d336efcb4bf552df70aeb89e1af59fe2ba27f639e1acbab7724bb24210b8c8a4269657c6a183855c
   2f46f20b323a8d22ef36ae3690128a81576f11ae3c9204ab2aae2205ca892fb7558eacfdf0af3971ef51f798b7a26829
   574c73b750831e72b6baaf5e71fe251ccab6e8fea8c6cc1884dbdd15c3fac34419f26fb18343773338a0ca43ee6ad303
   720ffa78920b94d5bf7b318a0f5cac3b1b26e60d92b302e718aebbee0fd32f9de84888acd76b459ab751187d2a6cab67
   4abf5c20f7218ef15fcbb1be1f6261eb50b118f12ef9aa1d74fbbbbedb5629e0c28117681b77434673f21976964a8f9c
   e4c47703eadde112cd7359bf48e2c5163ca72ae99dc1f4608e962554cfb5e6b67543713d56583f4c48e76128041910e4
   adedd8eed24a49f9e8040b0f14803e4c0630baa2a171dd6e4bdfb1e65c6b8b84178573b38a674d6ebb46ca66b89676ab
   4dc4b5e6a03ddc8cfe04285beb19ae714448ccfa35dbe57d67449d36687b05c8c6c86a48eb484949c06425e4b0c8f0fc
   1b759d8bef73b15d7726ad42f4fecb5bfab8f88b3c14115f566fcd718ec7bd16abae9b4fd446517aac45e166ba8dbda5
   037cfb5c4f6d837f6e016f843260a104a2bb9e483240e7444da9c67a7155f72a8cb54ce84790dbd0d21ad7c64385ca37
   a261b8fca49af9df4b1c0abcca5b198e958f7e649b9d5254f3e5ce8e57903a9d21196c03b35b5aa8634d498247d2dcc5
   f167825d724535206ce1191477c08f170bea9dbb13fc775e71dab0191dc8cbd1056c95960d72e03e5c86716fb350c1ce
   08b8815c49b5a9bfdf4af2345f74b942f9bd6ee1de329d93ed331f53f4a927930d035ce75df78a7f5c059e79d2524696
   8caaa5db2f9f28dac2c1efbc8f9ce48160ed5723e0e65a53be2942bdb6b2c844a9f5285a79bf2af940a225faf9d1873c
   649ad266026749202a793826137a7210df28f5b902eba8282bb84906b17e38f7a75f7837c4db9905b7027263a8fd7588
   f1f2446df5a1fe5bb1e0415e7222f40f4a3d98de4e16fef2482ce95e456221a353fa1861d04a9f250a0313a37ddbc5d9
   e24b915f9bd021eb8acf3379600374ba7c062863e1357a90fc585ca8d44e3c2c1675adead6f9a50ed6ae09deceff31a7
   59c55d09ba2c13d8c9f90a2d74e39c08ce889177fca6b72245e7901cc5018d4a93b9d75afafdb99a503cbcb7a46adde5
   325051d5668252a75739bdd08eaf0a14d409b9c9210b6728b58af62927b97b7922dcb2721428692ac411fcf068adc753
   185ad54df9311eadc9ea9fc1594fc551f001979cdbc6943ac18c0b7eaf97fba9ea7f89c59ce90035b79e2da8d2b45304
   d823bc5ae9ac3f3ade254e7a967d58096d06eab5e397a5c2ce5b55277bddfc19872c592ce33922c56d9b3808cc5c7649
   c9d3ff4bc67461027a710ac516bb758d20bd85bf68ceec82172c559656fd6e88a244ad7591f4556320403bc7c7160050
   61401e934d625fcf9c21e7f5bef1d125eedf7257df867a996969f69a14c621478bde12f131d688b29781690b17904d1e
   816b4b20c784acb92accf81adbce02bd66be45deec1fdb9186e9fbc719d275750d6d26a4342a358b9fd1d1ca32f62f90
   5fcf11aea81fa875f5549fd29f76e72a714b91a904a08e106facaaaf4def4a6b3284553b7599a4a102c9315763a2f685
   15ae220c2a738ab6ac7d051a533c2e29f81e74db1a91b045b4a2d7d65b4093ccdd5735a12f71799307ef91d817ef32f7
   51d5f68751a396bf776045335c8b99b450b5614dfa761907dba23210fc14d87e64caf8cca1d57d98b89ac65bed8e3a34
   e789f55a39c942127f207773fd4a89267a7eaeb85c800fe899905620d6c534f707cbfbaa3e233460075d643a16680579
   a5e14c6ea52155c665f26f4460ed07378a25fefed6458c4ab7e7c5db220f65277f6e1e0b4c9cd0c14d655727632e5c7d
   054f96045c7d549c585d24ff8d999f6101d82aab683b6148d09f1e7fe03085007fc6433ca9214219c499224f855aef14
   07c8e0b3da4d079d2a8d35d6baee02ec73671700481afccfbd9eb1efa245061387d7b0759ba267767887e343062be298
   4ebef2affc63792459765a7f8ef3db16c0ab662a0a61dbded438fcbc385e07f1bcc3b931c174fda82ac1103f00264369
   d94d6dff9e9d67604f26bc4f0f4c87ee8c394927407b884b6edff86f0997cd4ed378a2a0264a7235f6035309245d4563
   4f8f4490f4647fa2d7c426e71cef1b1d5a85ccf7bab620cd991a8d508a7fe2e771298675f9d75f788f3ec991147ba0eb
   24e6952cbb52f1114e4b1db6ba2e9f2605babd0b0fc8b91dae740939dc6d7cd7f64040ce88ec80234d249a8f9ccc60b8
   bc7872280f5314d4eab2dd38dfa0aa42cfda12156692ba220bdff63d689a244e102042134e113cb63b3576be459f060d
   9fd5c4712071a4c6f037899bc45d93680eb75968a89dd82c376130a7f08fa7e79351103bb24293ba3bc61cf6b9215106
   673bf785e53d0d71f3a82f0c24d16f16b2c6a3521dc14ba29f5440e83c99dc96f86db7e2356cf85287f85cd9781f6f54
   6bb93b7c3e9b1663484dcb9aba1feb322d4b92bcebbe45195b3ab58af3e0d117d2a65b237086c0f0d40e6ec6ba911e4e
   88985c341ac62549f50f184269b32e5ebc944edd6a7902312699801b6a2ae6b9be3b3cc6153715263f990635aa896a02
   4616997934ef3a7313d18b9a087d53fb3ce6073f4521fb3f445b53ec781fe90f5eff8e6f164b48e559e215a8e0c34e4f
   e7078670fd1c68c6d9979aa6155f4032a9c992410edd2610df3ec8b3bb6644ada6ac35b078a36705b546a3f4cdb1f4d4
   35e9d720713864aa236b0ebdb8987841e97fac7dd2326f628d3ae56dc4a4969eeee3c2a1214ab9634c97fb80ed3925bc
   777343d5070641362fbc9db53dec4121a17e86b0eae1372b95882c0c40fb0cd25ff204da036939d66ba5f88ed3748d22
   907aa694391cfda776b797276ffbc6704b47d84918191ed0eec0b835ca5eadcf09a24e2f5fdd39f1980050c861ce3fa2
   cfc14ca405155ddf052f0108c0c1125e1a5c8701a5f01e8a1d25847b337924b7ae71527d933dd238b7322c3b6b968768
   4c8d07a57991d1bb5bcee7eec503791f5d450c90d37ea66dc7103e5f161823865c99d451b5249f6925146c8d5145b4cc
   ad54548d569f44170610f7cac1dc78f53455359b9039a0a6b921a00bf17ecb83e71010f517e2a4f2d5ae56dad68a6438
   c75289fd5b7d9cd4119e7777b18bce241d571bb9b75de0853d7357bc1c9272233a45752a3f0008d89465eafe94a1be7e
   386c0ff5a1d8ef20453b98bc9ab86199d8877cf5e2642b7fef3da25894056a7b59a072167d1e60858169a7149870e072
   00498ae76575cd15947c1e436d0b731a7f69075a3349ae4846c9937779e9f2acffbb77ce9f0b3115adf018dc4b11566c
   c8c48c389de215abc0da2264b6b839074ca4653dce4d61ae577fce80d46ad522ee745305531e49b7da86c24e9b5e24b2
   84513ba6009d36318843950c9903fe1fd31f293d7d83f03d729ecc1122fbb4ab797c895248f45fbf480d2e382a2bdbea
   9244846185bf16cc95bdaf620aa0b299e124661c41c31e3a6eba07"

/-- Python `zlib.compress(skewed random 10 KiB, 9)` (seed 1234): dynamic Huffman. -/
private def skew10kZ : ByteArray := ofHex
  "78da259ae9baa4281044fffb14bc5ab2094a8128e0f2f47db83ddf2c3db7bb54c8cc881358c6b9e0ceeee2d53eed7609
   7a9cae38977bd94b3da51bddbf1245ebf7edcd49b141975b1deedd863adfb0dd87e422a1075b3efd4577ac3fedbd2471
   a395f86aa76d549ba8fef85c472ce2f5e7b42bb2f9a8551b2325277b73a396e8bb563dad268af42e23d66ee25edc6ead
   f8d339b56667f7d7ed3fb7c52bf6533bd1fd7a637c16ab543c535956895aef4b522e3e678ad1af8e0ffaa2e2edb42ec7
   711423124a38d555a3d8b3a798a38adfbb2f7edfa51f32caa9f716f6504aeeaaa6e6aefb3a78a0278b449672fcce1216
   a3c2db65bbacb0de2ff6d89d595cba9e3756a59d5b7c33c1b337ba7ca7acf1167fab7a5a79a2ff19717d155b9a5a93ae
   4faf6774aa1477aa72ac0bdb2c2eb97d2f5db39e11dae8eb21caed49da5944a9f73bf55bf56fa9fcc978b2c943e4d2c5
   c532dabe4a75dc62edf5cb6dbf5de8eab95cb787eb2ff771628dddd7e7904ea515bb5caaeda94971bdc657a9b1897f5c
   3d9efc93c348f7dca34476c03989d2e3d65254c52bdded9b8bdb42fc7ab9d8e685ca3e97ffa93e2ebdf765d9b7504675
   5aba0bdf7794a87ae96b79dfc42a7cf2d22f776d4a6fcbd3bca8b4b9a2c7dacb5dddaaa2cddefe5c79538fc579ab69c2
   50bb12c7f36cabab72f6f07817c5e9c81253706ac8ba964e074b19fc7ce925ba3417106e179b5ddce64ed9449c77b310
   34f6aa520f3c5abe5c5cc3e7365659b62bdede983d75ede5505d16778833bdc767d55d6b979f144509658b47eeae51d0
   72c94a6f2f3ff648b64df7a2297ed45de5432dc9aa441b53cf787c4b2b5f695accafa4a5be9f8fbf743ff4a3e9bfe8e4
   8a656ef6eeb2d0485a5181b3453996b6ff5ad18b77dda9f88b348cfb785ae57e577f4efaa2b938eeb3327d2136f1b39e
   94e5588e358770f7ca27c41d6c85bb79c85b35f53dc79e5dd77440d7e7365653ccce4d6c8c9f4bad87434b38e7e275a3
   c6ce6ebeb3c5efe964dc6bab6ed6ccba32d27855d4362cc3a81fdd72d38d9926882cc0b1e1b773d1f24cbf733b44e4e8
   df8392985ee5d73b4f35f427310feb9c675f8d9752ce6628f26cf0cfa8d7882a37dd3c68590a5eb71196d493fcd01473
   6de5e76473cff32baa28fd15117d2163d4e59ca230e2f53dd2babe7ef14d0c0162f32ba84a3fd6ee9eb238db0fa63c85
   90c5afedfdb2f9e8eda8253d5d5d22ea7c8c503f790f7915cbd9f8fbb88b53fa95d505e9cbe3d8012422c686f0b5743c
   f6273a79d39f5f776e5f95eb6274b465f95e318147bf9146a5d730d4174a3ee431b1eefa0eea4445221735db2c0fd542
   ccdea24ff522b74b7ca780b0d090a8cd70311c2bc2d6dd27fdc700f4eb3be31c81ac7a1c99db38e9aa304ca5efeec7b8
   b93c9cb49b0a5ecf5996ca8cf1fb4b7999afa27084aef3d3258657d885a900e5941b6d72f22db1865d95c614e582b4d9
   d2e5aca88f6bfbf9440981e55f4d1dde5dec3d2d77fc5c288755f6e8ef2e653dae5252c11e7e12a49e45ad45d2ebf820
   422a977d3a1fabd67711f31c2a375c68a83b6bba54f419e390b0232a28657bacbc23b513e5dee568a25b0b4719c39587
   162ce7e68e4c6b5d6aa4c32f552d762cf13ebfbc24bda2791dad7b242d1b3b9add38b6b9a301d373373b6a4a91c3dd45
   f7d7747518b7e95af614e8618dfc30512deaa760026e5b93a5df779a2feaac91c87d71ab66c85cf4f471e372daa9dbb0
   b9d1ce1fe97269d711d3d872bcace59e3f3474f4eef5f2e478dfe8f6139dabaf961bebfdd0c72752225ab614d6cab60d
   04ed886eb9b59623c8670fedaf182326b7eebbbf1eac94699267bff48b6a19f691a5cafa899cb7766f08dd55b43de97b
   6754cb89b2232d077e1f7fd43bf842053d0eb7378ff6615cf266557e412226cfe0191f5e5febbd51af14dbab4d458fbe
   eb81235a5dbfcbc7c8366b344a3ce3afd3d7b7e5d83fec642b9ae67e683d65a88b64a861ad399ccf5e8ef019c6d8f070
   01a7a12778ae77ddcd35fbe4ed27ae39d8b1fa66ebff8c7e449ff42325d3bc4e96ed87ed327e2b6a5a97bef75f9da3d4
   1278c29a1807043ff31c8ead41e9601a89fb29064d63d0acfae9abf0ffe277e615d90da0cb2ca47af7491fb42d20b265
   c9417fbf493bee1c5def93a19cb1d896772048fda5a6cff34c871b9f9cda96b244739c7eb995b37a1f8c3078f573c81f
   1aa3ace9da763966b958f026f7ac0b8642ff20f8d4b2257f1d8521eb0b6bc6215585892e0c6351c27e9903f55d5e9ec3
   c7bc14ad21a8dfc3c56b5517cd83717ca0dd401ee4d06fca3ffa4f8715c3d2ab960b802a18cfc78008fdc092d5b67dfe
   422aae13b258bcd7d75dce84261677692cabc4874d37ac83edc5c94a3ab5aa16dcf8bca39b573606f7c260651bd3c3b1
   9cce2d2dee5d0a2668a52573c6f55c512644d6b7817d45bd15db6f94b36b1c4c9513d94487762c7c2bcf3d1db0b40720
   946d3e27fc27fb7d2946516b1363c2ae6f2e115de997ae78f8edd681029ba2820239b10d59329a27f786b8c8ab1947c7
   557a19d75aa6b00dfdbb2f016b993779039ff039dd4af32ccbb27de85c3f1c72020ee0dfa7f9b11636e6409fc193f2c4
   7b8d1687519777c31fbfc4bc4133b15f43caefd3b0a4df863c68c61ea7d8bbdfc0401617ef9e371482b546e737502e25
   cc334f61daf7a55c253189abfac5cc20670307aecb2b5b860f70830ad5dcd58ed6efedc3f4907516e0d62f2a866e02cc
   1574eef6dbadd7daaa05d5d731dd57260db48973f8453f7dc1c626cb14fcf99257aa2c3421cf75bf2bcc1ce2b43bcddc
   e95068497e4b78c4f2f83ddee54e55a136b4759cf881363eb19a32b753f8b46c0a0f94f2a9d2d53d51a0f4a3ee3b0527
   99d8eefb600602ea73a2346a4394c55d6a8d798deead3ea672bec02b62563e3cefe50e4fa0f80ddf41c5b3414df4fe12
   00f874e91fccb019dcefa0a354f60f24f5d5675fb6735bb0b80d2870b3d79e686e6acac3e9dfbad0537d82e56d9aa241
   7f88f6695bd8a2bb5c39c021155fd40bd670f859fff1f461070e19aa00d2f59767897bb2b1e854fb367a65185907eb75
   41cbf332faee26ff3cfaf912a22c147003fd5a79e32ba7b5a1a3add259df7e65f5064a0496dc4c6859efbd3a92083b1f
   c7fac670f9a3c3d134acbbf5d17f8e7ce0261aa88196e71f3a527a3a542592640324c3d0cf9071910ab8e346ad0db5d4
   9e8b50c0f24d2a76728c8322ed576c93a9d8a3ab1e378d3b32ab61c2568081e2eb1b3892fbd6bf0d75f8c9c30889ed4f
   f93687cddef78eee7df12149ba97f15fe24257bb9cdfbd7e64b8be06e71a85bee1b54bf59d1c03be0fbbfb738bcfd5bf
   d94a8aa0d5d129a93f51bfa3c76b2805192ac2a06a6659bfae0dbc0a961473bb7da6513c09fdedf2f52cbf5a0ee7c68f
   5f125d7117fe228a6d82bccbd6e30ba1a7b4c0d933b0b2ee8e2b6aa0857644b93e5860da7020998138851c0c0a97cbd2
   64139bb45ee4fa3975e8e8cb0e41101e61e03da600383d8cb2432cd958b3f51664e5aeed92671d563b0f27db71c4a9f6
   57a74f62fd90a79ec14e791bb340bac8403628990c5ed3466083e74c266a6e28d89b3b632f35adec02d0c4ec4372a525
   6d119ca760e427cb401bf40bd728fa010682522b01fb65eb7936c696729684eb1ebff506d58fded4a5d2b1dceff6d1bb
   f8f8d326a11b85f846b6e425eeba9302a929599a29afce2486b904a4e4700974e549a6b94408967574b7c6d664432ad7
   454fe0283d283a9dbc84d4eedc765af3172b362660849b98d3afe8cffb057dd9636f2f64487f261fafece85c6fa001d0
   515b8d5fb3dd4417e658a31ab77de5a579f28e970c42a114e6d64207ab40f07dcf2cdb781f9f7b99c284f2745b5d9e9b
   858a5df6db18c3784a1de93a7dfc0f4db8c59877081459110a6668d1eadb95a9dda755edd81e66867174809b6e796fc2
   3ee49d944b5e978dcc445822969d9839ab23c0ff2984acb01df3097eefaabfd7edfb4188befb583d1584b0d2497f5bb2
   e2f0717cf1fe4deda5b1ae0c74051da97e6c6c5e8afdf00f053436d6419d492c87eb5b3fa81bc3196889abcf043eb600
   bd31278b733fcba4fb448aa6bd10d9039d91f1d9c6763d782f343747675cd6103f7b2e091eb644443b3560527cec9f2b
   190c866ec12896327d60c0f86c34dded3c64836d9b3d8ec93b6f5a96587223c7c8b75337294bb001701558ecc71e681a
   5b75c6ed34fd30f47fb95dbb6eb312c8abb887466703d93c3b0308bb7711309edf2e97d35fe55fe0317ac2ea6459af5d
   af1d243f651e70ecb0ef025364b44c2bfdfb0d4a4bf6ea3cb846dd9afab994aad060b4ae5d6fb4e370df7c344714d3e6
   5da1beb4c8ba330214d299689240aa7ac21935ed269c6e4e5acf33f93779e6d1cefa3e195fd27a025cff629cd6bbcf68
   7711321815653f4deaf929f81b87da4abbc8c85cf734c03348c45cdf2c14dd03fbddac84bca85673e4867becd2962275
   dd0b91fa9e06ddac5ef40cdb540f504649575485ffb8a448dd68ddb1ac901d37ff91aa4035a5aa3ecbd8c11cf93b0501
   99d50d275e7fae4de3219bbad45adf5780e1184e0a5bb48a77e213cf9c9249451bb2bf4b58e31abb0d26f2436a7b3361
   ef661671ac3ef3472bb584803620f46eed01bdee91eeb0b07612600053bade7e99ed36f5d056eb6cc6b99468a8929b61
   83dc4cd71e5bebbea21cb4583e7337176e71ad18f1f1448f8fc5998e0619d2ad2b1d80604bbe321a866426cf5ac97d8b
   1cea1aedf3062bbd11a144ee7334ce83bac246c9cd90e2769d82a1eb8e537ece70b1f70954519341cdd0d4ad8189eaf7
   ccf3b08b3faf7bee2cb3f96c98e582c3977bdc16cfe6b63ecf333636bacaee948ce5ad3d05fb765616c215a170f6840b
   1cd6fdae7a3bf33dc75f3c30342a0aa4d55e62aaa71ef4df89927e7254e327832dd1ee0a91eebd929c2a8d09abfea0c1
   4e0f5b9e32ee0a86caa2d6ee97c005e2feab8db8b358613c9a0251ae5f70e9ed8b865f86d641a68963337d2753802f8c
   170843d65827040fe44eabe39387426f68b32926c73c8e1fc517a71e92817dd7dbefddffa65fcd878f95409b7208f361
   1db451d416bff5f8e176c7de4a58967234ae7dc4382d8cb91da20927ebb4aef72b7176998ca75c51ec8662383cd90d3a
   76d797f1a05834151a9e891838d67f879c0772bc6bf9f9ac2025800ca102eebbc6b6013909161d72da8cf2cc93c45835
   aeb14e3c241ebeab7648b287beb6850eed83f2d7a3cfd95493c13b36731b250b2e2a5374945b408d5a7e3a6c3ae3e0fc
   7058f961aa6e41597c5339a6b9015dfe0e3fdde22ca90009ac3fac835f2208d82798e1ae3b666e3ece1905219133d252
   6c3fe1822a7aa2fbe82f51fbdca62a23126265ac17ab478e51d2e91d741f6b89a4d8e6944a6db21f2a27337741902636
   38643f76ddfbfd20e6ee26a7400b0cfb457cd1e17bd5a2a13fbc1dcb8b8404a24e5bf5fd28058741f9a57a1dda556d9c
   09d34f8672fc56c7773c43bffcb52ffab01c18fd133f7351a7f531a94ed0c7828046c2ce29eb9adf773f23a0f298d5fa
   7314f29172fe98b450c7a9661c71376040ae2a3ff42ee857e195aecc0df170a73ad6b1b6dc5ff0b15c475bae72672841
   35c196f5790c26996b7454c19e1d65683ece73c4a853dbfcf3f3f2118e101efd49a987f2e82460446dbb3fcb54b3de34
   51f59c47a5006f29bb269b8b5ff5ba2e660b68cbdf49e265c2a4b8ee502daed9aeafb9cffbdd69ba962cb4a8352def5a
   faf2cc83e29fc17a48a1b56b7bccf37c539f510e066dee9f7da0581799df07d4c1bf96943fc6b5bfcbd87e80c08a43cf
   7715f3f087d82b595188182cc211d3dfd946ee93bd94c43afd909cc73dce1b1fcaa9543048d6df43dfe33fc50a20cd68
   75d2326346129225ec32c41a3feb351ba12f3818ea63b2d9b67cdd321b147513c01d7242d0864ed30f7a7d7f8747c5d2
   767dc7ec47acc95f2f823c0f0ea24a75b11b89555683e3dbdbdcd1cd2d4438a27add5931071652f6bee9826732c14c18
   ea3093a4e4b116649c2dd1934c0b2bfce5f351cb172216a86849c654fb804ab2f717e9e05792cbf869697b3e040f82df
   69598b419a884a77e71178bb4b662f97a7ecc5cb7400c03f3686dffa6c9f19582032a42843ef57c7f8a675b20b86eccc
   f5e599f07b54ae19c32f39e4e0585156f004279f444590db94ea3325cd04de5be3d9cb95ce0544d9bad9c6a7370223a8
   51129c4d8e7f6306bd01f41edc77abcb8e777635953c6eedfb3cd4ee8d256ff74de493df57f43c6e8c88e74fa7ebb8e7
   994125fa354b487954bdcf7b21623f6121f58bfd3dea015271c4b7d220a8f67713983ff7bd422d40519e5bbefb14dcea
   52ea3c59180ed278381eef99c7a13f94d5a21e4fd3156c426ce19c9d41abe956f53d110322f1f569dd48512e1acd820f
   2894794379db3c8c40b908e2bf902f8ff5936fc36f25a61d089b423cbf39fe332291f2629c4492ef8f1d1fd1fdf04fd1
   2b499b46a9b30a9dde5cabdde6287eec54596b51fb7e27e49ef01ef59ff8ada60908a4894fedf75eb2f1e19d71b051ae
   79c6b191e5da56eeb73f0bcddcd5000e7af6f36de4ee4c4696b4acf95946f069d39ea07275526152745bd0f3bdc933ad
   bc18a321f885dd7f5f9eb073c758d2a49e18eafaf384b679ceee2f5c5996e95a7d5f0b7f665aebef6af3852ce8588e58
   aeb38f03c53683e6d02e28d91ee693f17ca0fc19a3f06a0b934f4adff237cf10310399679ad5e17cb913f47eee795e66
   7291c18d59daa996cd656d6b7c892e1a0082891e1c184cae88ae059c3a20b160c406934176bededf5773179636df06f7
   f24a98a0e976638e96f50cbf9f36ac81ec99e709b0b51b01d0e8f9a42b7b200abdf90de66a9df38d6d492120d9a05536
   34220982193737d6454ad9776e3f9c1aa1df53addf8d7531f034842ef1e8dd9b799afc7c2f13404795fd89372c141987
   995ba4e2b552111c6db477d318093771f2e61dbfdf39556eec8a45141ab59cda84b5bb8d75c636b77b9ef5a4381153d2
   349fe1a0641c7057c75236a8c7f650ec6fa1e528069fb26441a7aea43fe2cc1f2b5007812ce55ba3dbfa1967c4f276be
   539c6f09a23ec66c6c02ee5c1994ddfa3eb4dae0482dedddd89230dfa9ca318f0fa212df2733c5758319d90a9470f2b0
   bed5baa3cc1b4805bca5c73d5c5adcb2f284ec33f17c23a1d872a4b5610b1381754dec14891d62c5abb795c42e6723fd
   23f80f3fd649e8d3759b671e610235b0ca540c5c56b10ba78a7e5b9ebe06b0eac4a3de7263675487155862e6c22cb83e
   493b3139f32c0c8f9befa97a58555cdd9a8cfa55d8139ebb2d41e6c685025aa82dbc64723b74055eb119a547ce5f6975
   81968a2f6a02301bbb1102706b9508e58bbde6e142bf8ffbfccdb77b7d1e4bca55dddcf0d90a2c9b8fd941d66831b8e5
   fdfd55a8cb79926f72f889896a4e2e210add8e6f84982aed4a335c6bf95d208df8790e3acf76861bc41ad7a4e65f26d1
   98bccb3c8c0de5352af2a3a7020f762ff59b8fd0cb3a9d4b353df66e2c3d055b76f7b18f71a71754d20e1c5c3e15407d
   0090ebb2df8cd44d2adca6a223e735a18b33969fe13dc67c6dc53fb481db0e22c48727f5789ca1f74c981a8222955fc6
   3b50a2f4d8f9fd0bae0b475dc9dd4aaf62b67edbddf956033043368f3ff9188bb53ad9777b463abe4c372ccae64e9414
   b281be88840e3f9f424702e9fa225ff034f405d35cb4212fbbd06884a962b13c702feecaf045bd89794d7f6fc7bcb773
   e85e25de33ebcd77ff4d56d662655765cb6d35320ef5b27cb4e24ce8689fe7134abd75b637900f37e07f288aacae10aa
   79a09f6acc2666f083a11349db41d6ab3e7882eb9cefee883b3e795a1da1a0bc2391b0335ba85c9c6f9f7f52da147ee5
   ea4599973bc383e75b321a7e55fc71e00403ae93f9a58fbbf7be6f9f9eabc45874ca5e1646727e07a0ccd361d0ee6cf7
   378f54b1d2c5b8fc864eea1cf173fb9d97c5136e27ee67d5186308aafd6eb08740a16282af25da4e5ccdb4f373b98168
   13cff37d3f6ef7fbabe1bf3ce9476f85901178887d7d3fca6c2f7e463b527d744202c2a352dcb6c321a8c22d2f7daa83
   115ab7b3eaf0d3919e8c731ffb563a717ac72ff43b5d8ae021160d8d00ab53dc19ddbedafd7ba5db250256ea61ca4117
   f91866f61b95609c3b1245d9419e707b5fa23fbd1c3bce95a8986e601f3652e6b7222a3639d99585ac255d927f981a62
   3e1551312d6db099fcdf5a35ee82ab2bc2442fdb4115fa01fdd4d12189cfbe61df134f88752c6df7618dbaeef3eb4224
   6cd5ef9ae5725c9b08c588aba3cc7322bcc0e6d0fd61a783a2bb6a3f81168205495401e24e73879cfb52e40ebfdbccb7
   14443aaaf29d8da17e4847e92d8eeed218be99ca318fea02f833fb95e6c5f70c29f4f83ea51eaf9eb49eebddcb52be11
   2102140951f9111d6d2f8758f2797b922cfd7303feb658e96a0e1fe9b33a532d4570be5cf3cdd3e6e5b91d6110a69def
   4f81755a28eb896e6af6114efe7cbdd21c7a79757563be9b05e14bbc2ff072090c3a96fe00e77a878a2c5b022fc0e0f9
   6eb72db9f093279c9d3daf1e1c78e3b325c036ec5f5d36f13699dda4beff9419a998548e6e09cdf9f8c5a50b9436bf21
   96eb7bf4bccf0398797883630d65eafd43dd4f0c362f6efc4ebd0682799f2fea237be329f80e6fdb6255a7ff4f75cde1
   edd1c31504dd281be3adc2721260a745d249dc10984b4008cd8cf8887e7c731709a464c2069ee112a16d9c962d7be637
   e77eb511e05ea4b75319ae8029e8374194e66b7abad7350f50f739ea400b14a0c1030d0973b50ce8c5a6b694dd8b6bec
   f36b244dd322ea3d9b2acb33bf9ff70cebf2fc82db826ee7aa4ff3cdef6accd7bf31512fcbecbdf8be8ca96533f47a3d
   7ef7a20986042cb5d46e1fad0f3f8f6eff01d2ace69e"


#guard okSum (zlibDecode big text1kL0Z) 1024 445868594
#guard okSum (zlibDecode big uni10kZ) 10240 980335111
#guard okSum (zlibDecode big skew10kZ) 10240 3534546590
#guard okSum (zlibDecode big zeros1mZ) 1048576 15728641

/-- 70000 bytes `i % 251` as two stored blocks (65535 + 4465 bytes, the first one not final)
in a zlib stream whose trailer is Python's `zlib.adler32` of the data (`0x4ee37ee9`). -/
private def stored70000Z : ByteArray :=
  let data := ByteArray.mk ((List.range 70000).map (fun i => (i % 251).toUInt8)).toArray
  (ofHex "780100ffff0000" ++ data.extract 0 65535 ++ ofHex "0171118eee" ++
    data.extract 65535 70000 ++ ofHex "4ee37ee9")

#guard okSum (zlibDecode big stored70000Z) 70000 1323532009

-- Output limit: exact fit succeeds, one byte less is `limitExceeded`.
#guard okEq (zlibDecode 5 (ofHex "789ccb48cdc9c90700062c0215")) "hello".toUTF8
#guard isLimit (zlibDecode 4 (ofHex "789ccb48cdc9c90700062c0215"))
#guard isLimit (zlibDecode 4 (ofHex "7801010500faff68656c6c6f062c0215"))
#guard isLimit (zlibDecode 69999 stored70000Z)
-- Decompression bomb: 1 MiB of zeros from 1039 bytes, limit 1000.
#guard isLimit (zlibDecode 1000 zeros1mZ)
#guard isLimit (flateDecode { maxDecodedStreamBytes := 1000 } zeros1mZ)
#guard isLimit (zlibDecode 0 zeros1mZ)

-- Bad zlib headers: FCHECK, CM = 7, CINFO = 8, FDICT set (unsupported), too short.
#guard isMalformed (zlibDecode big (ofHex "789dcb48cdc9c90700062c0215"))
#guard isMalformed (zlibDecode big (ofHex "77"))
#guard isMalformed (zlibDecode big (ofHex "7701"))
#guard isMalformed (zlibDecode big (ofHex "881c030000000001"))
#guard isUnsupported (zlibDecode big (ofHex "78bb0000000000030000000001"))
-- Adler-32 mismatch (strict) vs. relaxed; missing trailer (strict) vs. relaxed.
#guard isMalformed (zlibDecode big (ofHex "789ccb48cdc9c90700062c0216"))
#guard okEq (zlibDecode big (ofHex "789ccb48cdc9c90700062c0216") (checkAdler := false))
  "hello".toUTF8
#guard isMalformed (zlibDecode big (ofHex "789ccb48cdc9c90700"))
#guard okEq (zlibDecode big (ofHex "789ccb48cdc9c90700") (checkAdler := false)) "hello".toUTF8
-- Truncated input.
#guard isMalformed (inflate big (ofHex "cb48cdc9c9"))
#guard isMalformed (inflate big ByteArray.empty)
#guard isMalformed (zlibDecode big (ofHex "789ccb48cd"))
-- Stored block: LEN/NLEN mismatch; data shorter than LEN.
#guard isMalformed (inflate big (ofHex "010500000068656c6c6f"))
#guard isMalformed (inflate big (ofHex "010500faff68656c"))
-- Distance too far back (distance 2 after one byte).
#guard isMalformed (inflate big (ofHex "4b044200"))
-- Fixed code: distance symbol 30, literal/length symbol 286.
#guard isMalformed (inflate big (ofHex "4b043e00"))
#guard isMalformed (inflate big (ofHex "4b1c0300"))
-- A non-final empty fixed block followed by a final one.
#guard okEq (inflate big (ofHex "022c1100")) "a".toUTF8
-- Invalid block type 3.
#guard isMalformed (inflate big (ofHex "07"))
-- Over-subscribed code-length code (19 codes of length 1).
#guard isMalformed (inflate big (ofHex "05e093244992244992000000000000000000"))
-- HLIT = 287 > 286.
#guard isMalformed (inflate big (ofHex "f500000000000000000000"))
-- Repeat code 16 with no previous length.
#guard isMalformed (inflate big (ofHex "050002240000000000000000"))
-- Missing end-of-block code (length of symbol 256 is zero).
#guard isMalformed (inflate big (ofHex "05c081000000000010feab010000000000000000"))
-- The fixed codes were built (not the `default` fallback).
#guard fixedLit.symbols.size == 288 && fixedLit.counts[7]? == some 24
#guard fixedDist.symbols.size == 32 && fixedDist.counts[5]? == some 32
-- Code construction: over-subscribed and incomplete codes, one-bit exception.
#guard (build .litOrDist #[1, 1, 1]).toBool == false
#guard (build .litOrDist #[1, 2]).toBool == false
#guard (build .codeLengths #[1]).toBool == false
#guard (build .litOrDist #[0, 1]).toBool
#guard (build .litOrDist #[0, 0]).toBool
#guard (build .litOrDist #[2, 2, 2, 2]).toBool
#guard (build .codeLengths #[2, 2, 2, 2]).toBool

end Tests

end SafePdf.Core.Filter.Flate
