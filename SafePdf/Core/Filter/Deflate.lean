import SafePdf.Core.Filter.Flate

/-!
# A small DEFLATE encoder, for round-trip testing of inflate (Plan.md §6 Phase 3)

Plan.md §6 Phase 3: "Correctness via round-trip with a Lean deflate on random data". This
module is the Lean deflate: it is used only to check `Flate.inflate` / `Flate.flateDecode`,
never on the viewing path.

* `deflateStored`: raw DEFLATE (RFC 1951 §3.2.4) as stored blocks of at most 65535 bytes
  (an empty input is one empty final stored block).
* `deflateFixed`: raw DEFLATE as one fixed-Huffman block (RFC 1951 §3.2.6), with optional
  greedy LZ77 (one hash candidate per position, window 32768, matches 3..258).
* `zlibWrap`: the zlib wrapper (RFC 1950): header `78 01`, body, big-endian Adler-32.

## Theorems

* `inflate_deflateStored`: `inflate limit (deflateStored bs) = .ok bs` whenever
  `bs.size ≤ limit` (all sizes, any number of blocks).
* `zlibDecode_zlibStored`: the same through the zlib wrapper with the Adler-32 check on.
* The fixed-Huffman encoder is checked by `#guard` here and by the property suite
  `Tests/FlateRoundTrip.lean` (not proved).

## Not done here: the Flate work bound

A mechanised bound "steps ≤ c·(input bits + output)" needs a cost model: an instrumented copy
of `Flate.decodeGo`/`codes`/`stored`/`readLengths`/`readDynamic`/`blocks` that also returns a
step count, a theorem that its first component equals the real decoder, and the bound on the
count. That copy and its equality proofs belong in `Flate.lean` (they unfold its definitions
one by one), so the work bound stays argued in `Flate.lean`'s module doc.

`deflateStoredFrom` appends blocks right-nested, so it copies O(n²/65535) bytes; it is a test
encoder, not a production one.
-/

set_option autoImplicit false

namespace SafePdf.Core.Filter.Deflate

open SafePdf
open SafePdf.Core.Filter.Flate

/-! ## Stored blocks -/

/-- The 5-byte header of a stored block: `BFINAL`, `BTYPE = 00` (padded to a byte), then
`LEN` and `NLEN` little-endian. -/
def storedHeader (final : Bool) (len : Nat) : ByteArray :=
  ⟨#[if final then 1 else 0, (len % 256).toUInt8, (len / 256).toUInt8,
     ((65535 - len) % 256).toUInt8, ((65535 - len) / 256).toUInt8]⟩

/-- One stored block holding `chunk` (which must have at most 65535 bytes). -/
def storedBlock (final : Bool) (chunk : ByteArray) : ByteArray :=
  storedHeader final chunk.size ++ chunk

/-- Stored blocks for the bytes of `bs` from `start` on, at most 65535 bytes each; the last
one is final. -/
def deflateStoredFrom (bs : ByteArray) (start : Nat) : ByteArray :=
  if bs.size ≤ start + 65535 then storedBlock true (bs.extract start bs.size)
  else storedBlock false (bs.extract start (start + 65535)) ++ deflateStoredFrom bs (start + 65535)
termination_by bs.size - start

/-- Raw DEFLATE of `bs` with stored blocks only. -/
def deflateStored (bs : ByteArray) : ByteArray := deflateStoredFrom bs 0

/-! ## Fixed Huffman blocks -/

/-- A little-endian bit writer: whole bytes in `buf`, then `n < 8` pending bits in `acc`. -/
structure BitWriter where
  /-- Completed bytes. -/
  buf : ByteArray
  /-- Pending bits (the low `n` bits). -/
  acc : Nat
  /-- Number of pending bits. -/
  n : Nat

/-- The empty writer. -/
def BitWriter.empty : BitWriter := ⟨ByteArray.empty, 0, 0⟩

/-- Move `k` whole bytes from `acc` to `buf`. -/
def BitWriter.flush : Nat → ByteArray → Nat → ByteArray × Nat
  | 0, buf, acc => (buf, acc)
  | k + 1, buf, acc => flush k (buf.push (acc % 256).toUInt8) (acc / 256)

/-- Append the low `nbits` bits of `v`, least significant first. -/
def BitWriter.put (w : BitWriter) (v nbits : Nat) : BitWriter :=
  let acc := w.acc ||| ((v % 2 ^ nbits) <<< w.n)
  let n := w.n + nbits
  let (buf, acc) := flush (n / 8) w.buf acc
  ⟨buf, acc, n % 8⟩

/-- The bytes written, the last one padded with zero bits. -/
def BitWriter.finish (w : BitWriter) : ByteArray :=
  if w.n == 0 then w.buf else w.buf.push (w.acc % 256).toUInt8

/-- Reverse the low `len` bits of `c` (Huffman codes are sent most significant bit first). -/
def rev (c : Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => ((c % 2) <<< l) ||| rev (c / 2) l

/-- Write a Huffman code `code` of length `len`. -/
def BitWriter.putCode (w : BitWriter) (code len : Nat) : BitWriter :=
  w.put (rev code len) len

/-- Write a literal/length symbol `0..287` with the fixed code (RFC 1951 §3.2.6). -/
def BitWriter.putLit (w : BitWriter) (s : Nat) : BitWriter :=
  if s < 144 then w.putCode (0x30 + s) 8
  else if s < 256 then w.putCode (0x190 + (s - 144)) 9
  else if s < 280 then w.putCode (s - 256) 7
  else w.putCode (0xC0 + (s - 280)) 8

/-- The largest index `i < n` with `table[i] ≤ v` (0 if none). -/
def findBase (table : Array Nat) (n v : Nat) : Nat :=
  (List.range n).foldl (fun best i => if table[i]?.getD 0 ≤ v then i else best) 0

/-- Write a match of length `len ∈ 3..258` at distance `d ∈ 1..32768` (fixed codes). -/
def BitWriter.putMatch (w : BitWriter) (len d : Nat) : BitWriter :=
  let li := if len == 258 then 28 else findBase lenBase 28 len
  let di := findBase distBase 30 d
  let w := w.putLit (257 + li)
  let w := w.put (len - lenBase[li]?.getD 0) (lenExtra[li]?.getD 0)
  let w := w.putCode di 5
  w.put (d - distBase[di]?.getD 0) (distExtra[di]?.getD 0)

/-- Hash of the three bytes at `i` (12 bits). -/
def hash3 (bs : ByteArray) (i : Nat) : Nat :=
  (((bs[i]?.getD 0).toNat <<< 8) ^^^ ((bs[i + 1]?.getD 0).toNat <<< 4) ^^^
    (bs[i + 2]?.getD 0).toNat) % 4096

/-- Length of the common run of `bs` at `a` and at `b` (`a < b`), starting from `k`, at most
`k + fuel`, stopping at the end of `bs`. -/
def matchLen (bs : ByteArray) (a b : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k =>
    if b + k < bs.size ∧ bs[a + k]? == bs[b + k]? then matchLen bs a b fuel (k + 1) else k

/-- The LZ77 candidate at position `i`: `(length, distance)` of the match with the last
position of the same hash (`table[h]` is `1 +` that position, 0 for none), or `(0, 0)`. -/
def findMatch (bs : ByteArray) (table : Array Nat) (i : Nat) : Nat × Nat :=
  let cand := table[hash3 bs i]?.getD 0
  if 0 < cand ∧ cand ≤ i ∧ i + 1 - cand ≤ 32768 then
    (matchLen bs (cand - 1) i 258 0, i + 1 - cand)
  else (0, 0)

/-- The greedy LZ77 + fixed-Huffman loop from position `i`. -/
def fixedGo (bs : ByteArray) (lz : Bool) (table : Array Nat) (w : BitWriter) (i : Nat) :
    BitWriter :=
  if h : i < bs.size then
    if lz ∧ i + 3 ≤ bs.size then
      if hm : 3 ≤ (findMatch bs table i).1 then
        fixedGo bs lz (table.setIfInBounds (hash3 bs i) (i + 1))
          (w.putMatch (findMatch bs table i).1 (findMatch bs table i).2)
          (i + (findMatch bs table i).1)
      else fixedGo bs lz (table.setIfInBounds (hash3 bs i) (i + 1)) (w.putLit bs[i].toNat)
        (i + 1)
    else fixedGo bs lz table (w.putLit bs[i].toNat) (i + 1)
  else w
termination_by bs.size - i
decreasing_by all_goals omega

/-- Raw DEFLATE of `bs` as one final fixed-Huffman block; `lz77 := false` gives literals
only. -/
def deflateFixed (bs : ByteArray) (lz77 : Bool := true) : ByteArray :=
  let w := BitWriter.empty.put 3 3
  let w := fixedGo bs lz77 (Array.replicate 4096 0) w 0
  (w.putLit 256).finish

/-! ## Zlib wrapper -/

/-- The zlib header `78 01`: CM = 8, CINFO = 7 (32 KiB window), no dictionary, FCHECK
valid. -/
def zlibHeader : ByteArray := ⟨#[0x78, 0x01]⟩

/-- The Adler-32 trailer: `a` as four big-endian bytes. -/
def adlerTrailer (a : Nat) : ByteArray :=
  ⟨#[(a / 16777216 % 256).toUInt8, (a / 65536 % 256).toUInt8, (a / 256 % 256).toUInt8,
    (a % 256).toUInt8]⟩

/-- Wrap raw DEFLATE `body` (of the bytes `data`) as a zlib stream (RFC 1950): header, body,
big-endian Adler-32 of `data`. -/
def zlibWrap (body data : ByteArray) : ByteArray :=
  zlibHeader ++ body ++ adlerTrailer (adler32 data)

/-- A zlib stream of `bs` with stored blocks. -/
def zlibStored (bs : ByteArray) : ByteArray := zlibWrap (deflateStored bs) bs

/-- A zlib stream of `bs` with one fixed-Huffman block. -/
def zlibFixed (bs : ByteArray) (lz77 : Bool := true) : ByteArray :=
  zlibWrap (deflateFixed bs lz77) bs

/-! ## Round trip for stored blocks -/

/-- The low three bits of the 32-bit window read by `readBits` are those of its first byte. -/
theorem or4_and_seven (x0 x1 x2 x3 : Nat) :
    (x0 ||| (x1 <<< 8) ||| (x2 <<< 16) ||| (x3 <<< 24)) &&& 7 = x0 &&& 7 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 3
  · simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
    have h8 : ¬ (i ≥ 8) := by omega
    have h16 : ¬ (i ≥ 16) := by omega
    have h24 : ¬ (i ≥ 24) := by omega
    simp [h8, h16, h24]
  · have h7 : Nat.testBit 7 i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 7 < 2 ^ 3)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [Nat.testBit_and, h7]

/-- Two little-endian bytes of `n < 65536` recombine to `n`. -/
theorem le16 (n : Nat) (h : n < 65536) : n % 256 ||| (n / 256 % 256) <<< 8 = n := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : n % 256 < 2 ^ 8),
    Nat.shiftLeft_eq]
  omega

/-- A byte of the middle part of `pre ++ s ++ post`. -/
theorem getElem_mid (pre s post : ByteArray) (k : Nat) (hk : k < s.size)
    (h : pre.size + k < (pre ++ s ++ post).size) :
    (pre ++ s ++ post)[pre.size + k] = s[k] := by
  rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append]; omega),
    ByteArray.getElem_append_right (by omega)]
  simp

/-- Size of a stored block. -/
theorem storedBlock_size (final : Bool) (chunk : ByteArray) :
    (storedBlock final chunk).size = 5 + chunk.size := by
  simp [storedBlock, storedHeader, ByteArray.size_append]
  rfl

/-- The block header of a stored block reads as `BFINAL` and `BTYPE = 0`. -/
theorem readBits_storedBlock (pre post chunk : ByteArray) (final : Bool) :
    readBits (pre ++ storedBlock final chunk ++ post) (pre.size * 8) 3 =
      .ok (if final then 1 else 0, pre.size * 8 + 3) := by
  have hs := storedBlock_size final chunk
  have hsz : (pre ++ storedBlock final chunk ++ post).size =
      pre.size + (5 + chunk.size) + post.size := by
    simp [ByteArray.size_append, hs]
  have hb : (pre ++ storedBlock final chunk ++ post)[pre.size]? =
      some (if final then 1 else 0) := by
    rw [getElem?_pos _ _ (by omega)]
    have := getElem_mid pre (storedBlock final chunk) post 0 (by omega) (by omega)
    simp only [Nat.add_zero] at this
    rw [this]
    cases final <;> rfl
  unfold readBits
  have h1 : pre.size * 8 + 3 ≤ (pre ++ storedBlock final chunk ++ post).size * 8 := by omega
  simp only [h1, ↓reduceIte, show (3 : Nat) ≤ 24 by decide, Nat.mul_mod_left,
    Nat.shiftRight_zero, Nat.mul_div_cancel _ (by decide : 0 < 8), hb]
  rw [show (1 <<< 3) - 1 = 7 by decide, or4_and_seven]
  cases final <;> rfl

/-- A stored block decodes to its chunk. -/
theorem stored_storedBlock (limit : Nat) (pre post chunk : ByteArray) (final : Bool)
    (hc : chunk.size ≤ 65535) (out : Out limit) (hl : out.1.size + chunk.size ≤ limit) :
    stored (pre ++ storedBlock final chunk ++ post) limit out (pre.size * 8 + 3) =
      .ok (⟨out.1 ++ chunk, by simp [ByteArray.size_append]; omega⟩,
        (pre.size + 5 + chunk.size) * 8) := by
  have hs := storedBlock_size final chunk
  have hsz : (pre ++ storedBlock final chunk ++ post).size =
      pre.size + (5 + chunk.size) + post.size := by
    simp [ByteArray.size_append, hs]
  have hbyte : (pre.size * 8 + 3 + 7) / 8 = pre.size + 1 := by omega
  have hhs : (storedHeader final chunk.size).size = 5 := rfl
  have hin : ∀ (k : Nat) (hk : k < 5)
      (h' : pre.size + k < (pre ++ storedBlock final chunk ++ post).size),
      (pre ++ storedBlock final chunk ++ post)[pre.size + k] =
        (storedHeader final chunk.size)[k]'(by omega) := by
    intro k hk h'
    rw [getElem_mid pre _ post k (by omega) h']
    simp only [storedBlock]
    rw [ByteArray.getElem_append_left (by omega)]
  have e1 : ((pre ++ storedBlock final chunk ++ post)[pre.size + 1]'(by omega)).toNat =
      chunk.size % 256 := by
    rw [hin 1 (by omega)]
    all_goals show ((chunk.size % 256).toUInt8).toNat = _
    all_goals simp
  have e2 : ((pre ++ storedBlock final chunk ++ post)[pre.size + 1 + 1]'(by omega)).toNat =
      chunk.size / 256 % 256 := by
    rw [hin 2 (by omega)]
    all_goals show ((chunk.size / 256).toUInt8).toNat = _
    all_goals simp
  have e3 : ((pre ++ storedBlock final chunk ++ post)[pre.size + 1 + 2]'(by omega)).toNat =
      (65535 - chunk.size) % 256 := by
    rw [hin 3 (by omega)]
    all_goals show (((65535 - chunk.size) % 256).toUInt8).toNat = _
    all_goals simp
  have e4 : ((pre ++ storedBlock final chunk ++ post)[pre.size + 1 + 3]'(by omega)).toNat =
      (65535 - chunk.size) / 256 % 256 := by
    rw [hin 4 (by omega)]
    all_goals show (((65535 - chunk.size) / 256).toUInt8).toNat = _
    all_goals simp
  have hx : (pre ++ storedBlock final chunk ++ post).extract (pre.size + 1 + 4)
      (pre.size + 1 + 4 + chunk.size) = chunk := by
    have ha : pre ++ storedBlock final chunk ++ post =
        (pre ++ storedHeader final chunk.size) ++ chunk ++ post := by
      simp [storedBlock, ByteArray.append_assoc]
    rw [ha, ByteArray.extract_append,
      ByteArray.extract_append_eq_right (by simp [ByteArray.size_append, hhs] <;> omega)
        (by simp [ByteArray.size_append, hhs] <;> omega)]
    have h0 : pre.size + 1 + 4 + chunk.size - (pre ++ storedHeader final chunk.size ++ chunk).size
        = pre.size + 1 + 4 - (pre ++ storedHeader final chunk.size ++ chunk).size := by
      simp [ByteArray.size_append, hhs] <;> omega
    rw [h0, ByteArray.extract_same, ByteArray.append_empty]
  unfold stored
  simp only [hbyte]
  rw [dite_eq_left_of_eq_true (eq_true (by omega))]
  simp only [e1, e2, e3, e4]
  have l1 := le16 chunk.size (by omega)
  have l2 := le16 (65535 - chunk.size) (by omega)
  simp only [l1, l2]
  have hn : (chunk.size + (65535 - chunk.size) != 65535) = false := by
    simp; omega
  have ht : ¬ (pre ++ storedBlock final chunk ++ post).size < pre.size + 1 + 4 + chunk.size := by
    omega
  simp only [hn, ht, Bool.false_eq_true, ↓reduceIte]
  rw [dite_eq_left_of_eq_true (eq_true hl)]
  simp only [hx]

/-- One step of the block loop over a stored block. -/
theorem blocks_storedBlock (limit : Nat) (pre post chunk : ByteArray) (final : Bool)
    (hc : chunk.size ≤ 65535) (out : Out limit) (hl : out.1.size + chunk.size ≤ limit) :
    blocks (pre ++ storedBlock final chunk ++ post) limit out (pre.size * 8) =
      if final then .ok (⟨out.1 ++ chunk, by simp [ByteArray.size_append]; omega⟩,
        (pre.size + 5 + chunk.size) * 8)
      else blocks (pre ++ storedBlock final chunk ++ post) limit
        ⟨out.1 ++ chunk, by simp [ByteArray.size_append]; omega⟩
        ((pre.size + 5 + chunk.size) * 8) := by
  have hs := storedBlock_size final chunk
  have hsz : (pre ++ storedBlock final chunk ++ post).size =
      pre.size + (5 + chunk.size) + post.size := by
    simp [ByteArray.size_append, hs]
  rw [blocks, readBits_storedBlock]
  have hst := stored_storedBlock limit pre post chunk
  cases final
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.reduceShiftRight, Nat.reduceAnd,
      Nat.reduceBEq, hst false hc out hl]
    have hp : pre.size * 8 < (pre.size + 5 + chunk.size) * 8 ∧
        (pre.size + 5 + chunk.size) * 8 ≤ (pre ++ storedBlock false chunk ++ post).size * 8 := by
      omega
    rw [dite_eq_left_of_eq_true (eq_true hp)]
  · simp only [↓reduceIte, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBEq,
      hst true hc out hl]

/-- The block loop over the stored blocks of `bs` from `start`, inside any surrounding
bytes, appends `bs[start:]` to the output and stops right after the last block. -/
theorem blocks_deflateStoredFrom (limit : Nat) (bs : ByteArray) (start : Nat)
    (pre post : ByteArray) (out : Out limit) (hl : out.1.size + (bs.size - start) ≤ limit) :
    blocks (pre ++ deflateStoredFrom bs start ++ post) limit out (pre.size * 8) =
      .ok (⟨out.1 ++ bs.extract start bs.size, by simp [ByteArray.size_append]; omega⟩,
        (pre.size + (deflateStoredFrom bs start).size) * 8) := by
  by_cases h : bs.size ≤ start + 65535
  · have hd : deflateStoredFrom bs start = storedBlock true (bs.extract start bs.size) := by
      rw [deflateStoredFrom]; simp [h]
    simp only [hd]
    rw [blocks_storedBlock limit pre post _ true (by simp; omega) out (by simp; omega)]
    simp only [↓reduceIte, storedBlock_size, Except.ok.injEq, Prod.mk.injEq, true_and]
    omega
  · have hd : deflateStoredFrom bs start =
        storedBlock false (bs.extract start (start + 65535)) ++
          deflateStoredFrom bs (start + 65535) := by
      rw [deflateStoredFrom]; simp [h]
    have hc : (bs.extract start (start + 65535)).size = 65535 := by simp; omega
    have hin : pre ++ (storedBlock false (bs.extract start (start + 65535)) ++
          deflateStoredFrom bs (start + 65535)) ++ post =
        pre ++ storedBlock false (bs.extract start (start + 65535)) ++
          (deflateStoredFrom bs (start + 65535) ++ post) := by
      simp [ByteArray.append_assoc]
    simp only [hd]
    rw [hin, blocks_storedBlock limit pre _ _ false (by omega) out (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← ByteArray.append_assoc,
      show (pre.size + 5 + (bs.extract start (start + 65535)).size) * 8 =
        (pre ++ storedBlock false (bs.extract start (start + 65535))).size * 8 by
          simp only [ByteArray.size_append, storedBlock_size]; omega,
      blocks_deflateStoredFrom limit bs (start + 65535) _ post _ (by simp; omega)]
    simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq, ByteArray.append_assoc,
      ByteArray.extract_append_extract, ByteArray.size_append, storedBlock_size]
    constructor
    · congr 2 <;> omega
    · omega
termination_by bs.size - start
decreasing_by omega

/-- **Round trip, stored blocks**: raw inflate undoes `deflateStored` for every input that
fits the output limit (any size, so any number of 65535-byte blocks). -/
theorem inflate_deflateStored (limit : Nat) (bs : ByteArray) (h : bs.size ≤ limit) :
    inflate limit (deflateStored bs) = .ok bs := by
  have := blocks_deflateStoredFrom limit bs 0 ByteArray.empty ByteArray.empty
    ⟨ByteArray.empty, by simp [ByteArray.size_empty]⟩ (by simp [ByteArray.size_empty]; omega)
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    Nat.zero_mul, Nat.zero_add, ByteArray.extract_zero_size] at this
  unfold inflate inflateAt deflateStored
  rw [this]
  rfl

/-- `y <<< k ||| x = y * 2 ^ k + x` when `x < 2 ^ k`. -/
theorem shl_or_eq (y x k : Nat) (hx : x < 2 ^ k) : y <<< k ||| x = y * 2 ^ k + x := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]

/-- Four big-endian bytes of `a < 2 ^ 32` recombine to `a` (the Adler-32 trailer). -/
theorem be32 (a : Nat) (h : a < 2 ^ 32) :
    (a / 16777216 % 256) <<< 24 ||| (a / 65536 % 256) <<< 16 ||| (a / 256 % 256) <<< 8 |||
      a % 256 = a := by
  rw [show (24 : Nat) = 8 + 16 from rfl, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib,
    shl_or_eq _ _ 8 (by omega), show (16 : Nat) = 8 + 8 from rfl, Nat.shiftLeft_add,
    ← Nat.shiftLeft_or_distrib, shl_or_eq _ _ 8 (by omega), shl_or_eq _ _ 8 (by omega)]
  have : (2 : Nat) ^ 8 = 256 := rfl
  rw [this]
  omega

/-- An invariant preserved by each step of a `ByteArray.foldl` holds of its result. -/
theorem foldl_inv {β : Type} (P : β → Prop) (f : β → UInt8 → β) (init : β) (as : ByteArray)
    (h0 : P init) (hf : ∀ b x, P b → P (f b x)) : P (as.foldl f init) := by
  unfold ByteArray.foldl ByteArray.foldlM
  simp only [Nat.le_refl, ↓reduceDIte]
  suffices hl : ∀ (n j : Nat) (b : β), P b →
      P (ByteArray.foldlM.loop (m := Id) (fun x1 x2 => pure (f x1 x2)) as as.size
        (Nat.le_refl _) n j b).run from hl _ _ _ h0
  intro n
  induction n with
  | zero =>
    intro j b hb
    unfold ByteArray.foldlM.loop
    split <;> exact hb
  | succ n ih =>
    intro j b hb
    unfold ByteArray.foldlM.loop
    split
    · exact ih _ _ (hf _ _ hb)
    · exact hb

/-- Adler-32 fits in 32 bits. -/
theorem adler32_lt (data : ByteArray) : adler32 data < 2 ^ 32 := by
  unfold adler32
  have hP := foldl_inv (fun st : Nat × Nat => st.1 < 65521 ∧ st.2 < 65521)
    (fun (st : Nat × Nat) x =>
      let a := (st.1 + x.toNat) % 65521
      (a, (st.2 + a) % 65521)) (1, 0) data (by decide)
    (fun _ _ _ => ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩)
  split
  rename_i a b heq
  rw [heq] at hP
  simp only at hP
  omega

/-- **Round trip through zlib, stored blocks**: `zlibDecode` (Adler-32 check on, the strict
`/FlateDecode` path) undoes `zlibStored` for every input that fits the output limit. -/
theorem zlibDecode_zlibStored (limit : Nat) (bs : ByteArray) (h : bs.size ≤ limit) :
    zlibDecode limit (zlibStored bs) = .ok bs := by
  have hb := blocks_deflateStoredFrom limit bs 0 zlibHeader (adlerTrailer (adler32 bs))
    ⟨ByteArray.empty, by simp [ByteArray.size_empty]⟩ (by simp [ByteArray.size_empty]; omega)
  simp only [ByteArray.empty_append, ByteArray.extract_zero_size] at hb
  unfold zlibDecode zlibDecodeOut zlibStored zlibWrap inflateAt deflateStored
  generalize deflateStoredFrom bs 0 = D at hb ⊢
  have hHs : zlibHeader.size = 2 := rfl
  have hTs : (adlerTrailer (adler32 bs)).size = 4 := rfl
  have hsz : (zlibHeader ++ D ++ adlerTrailer (adler32 bs)).size = 2 + D.size + 4 := by
    simp only [ByteArray.size_append, hHs, hTs]
  have e0 : ((zlibHeader ++ D ++ adlerTrailer (adler32 bs))[0]'(by omega)).toNat = 120 := by
    rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append]; omega),
      ByteArray.getElem_append_left (by omega)]
    rfl
  have e1 : ((zlibHeader ++ D ++ adlerTrailer (adler32 bs))[1]'(by omega)).toNat = 1 := by
    rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append]; omega),
      ByteArray.getElem_append_left (by omega)]
    rfl
  have tk : ∀ (k : Nat) (hk : k < 4),
      ((zlibHeader ++ D ++ adlerTrailer (adler32 bs))[2 + D.size + k]'(by omega)) =
        (adlerTrailer (adler32 bs))[k]'(by omega) := by
    intro k hk
    rw [ByteArray.getElem_append_right (by simp [ByteArray.size_append]; omega)]
    simp only [ByteArray.size_append, hHs]
    congr 1
    omega
  have hb' : blocks (zlibHeader ++ D ++ adlerTrailer (adler32 bs)) limit
      ⟨ByteArray.empty, by simp [ByteArray.size_empty]⟩ 16 =
      .ok (⟨bs, by omega⟩, (2 + D.size) * 8) := by
    rw [show (16 : Nat) = zlibHeader.size * 8 by omega, hb, hHs]
  rw [dite_eq_left_of_eq_true (eq_true (by omega))]
  simp (config := { decide := true }) only [e0, e1, hb']
  simp only [↓reduceIte]
  have hpos : ((2 + D.size) * 8 + 7) / 8 = 2 + D.size := by omega
  simp only [hpos]
  rw [dite_eq_left_of_eq_true (eq_true (by omega))]
  have t0 := tk 0 (by omega)
  simp only [Nat.add_zero] at t0
  have a0 : ((adlerTrailer (adler32 bs))[0]'(by omega)).toNat = adler32 bs / 16777216 % 256 := by
    show ((adler32 bs / 16777216 % 256).toUInt8).toNat = _
    simp
  have a1 : ((adlerTrailer (adler32 bs))[1]'(by omega)).toNat = adler32 bs / 65536 % 256 := by
    show ((adler32 bs / 65536 % 256).toUInt8).toNat = _
    simp
  have a2 : ((adlerTrailer (adler32 bs))[2]'(by omega)).toNat = adler32 bs / 256 % 256 := by
    show ((adler32 bs / 256 % 256).toUInt8).toNat = _
    simp
  have a3 : ((adlerTrailer (adler32 bs))[3]'(by omega)).toNat = adler32 bs % 256 := by
    show ((adler32 bs % 256).toUInt8).toNat = _
    simp
  simp only [t0, tk 1 (by omega), tk 2 (by omega), tk 3 (by omega), a0, a1, a2, a3,
    be32 _ (adler32_lt bs), beq_self_eq_true, ↓reduceIte]
  rfl

/-! ## Round-trip checks on fixed vectors (the property suite is `Tests/FlateRoundTrip.lean`) -/

section Tests

/-- `n` pseudo-random bytes (LCG, fixed seed) over an alphabet of `k` symbols (test helper). -/
private def pseudo (n k : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut x := 12345
  for _ in [0:n] do
    x := (x * 1103515245 + 12345) % 2147483648
    b := b.push ((x / 65536) % k).toUInt8
  return b

/-- All 256 byte values in order (test helper). -/
private def allBytes : ByteArray := ⟨(List.range 256).toArray.map (·.toUInt8)⟩

/-- The fixed vectors: empty, 1 byte, 65535, 65536, 100 000 bytes, all 256 byte values. -/
private def vectors : List ByteArray :=
  [ByteArray.empty, ⟨#[42]⟩, pseudo 65535 256, pseudo 65536 7, pseudo 100000 3, allBytes]

/-- `r` is `.ok` with exactly the bytes of `bs` (test helper). -/
private def okEq (r : Except Error ByteArray) (bs : ByteArray) : Bool :=
  match r with
  | .ok o => o.data == bs.data
  | .error _ => false

/-- `r` is `Error.limitExceeded .decodedStreamBytes` (test helper). -/
private def isLimit (r : Except Error ByteArray) : Bool :=
  match r with
  | .error (.limitExceeded .decodedStreamBytes) => true
  | _ => false

#guard vectors.all fun v => okEq (inflate v.size (deflateStored v)) v
#guard vectors.all fun v => okEq (inflate v.size (deflateFixed v)) v
#guard vectors.all fun v => okEq (inflate v.size (deflateFixed v false)) v
#guard vectors.all fun v => okEq (zlibDecode v.size (zlibStored v)) v
#guard vectors.all fun v => okEq (zlibDecode v.size (zlibFixed v)) v
#guard vectors.all fun v => okEq (zlibDecode v.size (zlibFixed v false)) v
-- One byte under the size is a limit error.
#guard (vectors.filter (0 < ·.size)).all fun v =>
  isLimit (zlibDecode (v.size - 1) (zlibStored v)) &&
    isLimit (zlibDecode (v.size - 1) (zlibFixed v)) &&
    isLimit (zlibDecode (v.size - 1) (zlibFixed v false))
-- Block structure: an empty input is one 5-byte block; 65536 bytes need two blocks.
#guard (deflateStored ByteArray.empty).data == #[1, 0, 0, 0xff, 0xff]
#guard (deflateStored (pseudo 65536 7)).size == 65536 + 10
-- LZ77 compresses long runs (64 KiB of zeros: about 254 matches of length 258).
#guard (deflateFixed (ByteArray.mk (Array.replicate 65536 0))).size < 1000
-- Matches Python's `zlib.compress(b"hello", 0)` byte for byte.
#guard (zlibStored "hello".toUTF8).data ==
  #[0x78, 0x01, 0x01, 0x05, 0x00, 0xfa, 0xff, 0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x06, 0x2c, 0x02, 0x15]

end Tests

end SafePdf.Core.Filter.Deflate
