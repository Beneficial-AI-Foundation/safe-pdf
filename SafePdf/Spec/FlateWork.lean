import SafePdf.Core.Filter.Flate

/-!
# Flate work bound (Plan.md §3 S3, §5.2, §6 Phase 3; task 3.8b)

`SafePdf/Core/Filter/Flate.lean` bounds the *output* of inflate by construction. This module
bounds its *work*, so that a decompression bomb is rejected in bounded time, not only with
bounded output.

## Approach: counted twins

Each loop of the decoder gets a twin that returns `(result, steps)`:
`decodeGoW`, `codesW`, `storedW`, `readLengthsW`, `readDynamicW`, `blocksW` (with the block
body factored out as `blockBodyW`), and the entry points `inflateAtW`, `inflateW`,
`zlibDecodeOutW`, `flateDecodeW`. Each twin has an `…W_fst` theorem stating that its first
component **is** the real function (`(flateDecodeW limits input checkAdler).1 =
flateDecode limits input checkAdler`), so the count is attached to the real decoder and the
definitions in `Flate.lean` are unchanged (the round-trip proofs in `Deflate.lean` unfold
them).

## Cost model (what a step is)

* one bit read by the Huffman decoder (`decodeGo` iteration, at most 15 per symbol);
* one per `readBits` call (at most 24 bits, constant time);
* one per iteration of `codes`, `readLengths`, `blocks` (plus one for the block header read);
* one per byte appended: literal, back-reference copy (`len` steps), stored block (`len`
  steps), repeat code in a dynamic header (`n` steps), and one per output byte for the
  Adler-32 check;
* one per 3-bit code-length code length read by `readClLengths` (counted as the list length);
* `buildCost n = 4 n + 64` per Huffman table built from `n` lengths. This one is a model,
  not a count: `build` is straight-line code (folds over the `n ≤ 286` lengths and loops of
  15 or 16 steps) and is not twinned. The fixed tables `fixedLit`/`fixedDist` are global
  constants built once, so they cost nothing per block.

## Results

With `N = input.size * 8` (input bits):

* `inflateAtW_steps_le`: in **every** outcome (success, malformed, truncated, limit
  exceeded), `steps ≤ 67·(N - pos) + 2·limit + 1922`.
* `inflateAtW_steps_le_of_ok`: on success ending at bit `p`,
  `steps + 67·(N - p) ≤ 67·(N - pos) + 2·out.size + 1922`, i.e. 67 per bit consumed plus 2 per
  byte produced.
* `flateDecodeW_steps_le`: `steps ≤ 536·input.size + 3·maxDecodedStreamBytes + 1923`, any
  outcome; `flateDecodeW_steps_le_of_ok`: `steps ≤ 536·input.size + 3·out.size + 1923`.

## Proof: a potential

Every block-level twin satisfies `steps + Φ(after) ≤ Φ(before) + c`, where
`Φ = 67·(unread bits) + 2·(bytes still allowed)` and `Φ(after) = 0` after an error (`postW`).
In `codes`, a literal costs `1 + k` steps for a `k`-bit code and lowers `Φ` by `67k + 2`; a
copy costs `3 + k₁ + k₃ + len` and lowers `Φ` by at least `67(k₁ + k₃) + 2 len`; an error
costs at most `33` (two 15-bit decodes and three more steps). A dynamic header costs at most
`1887` beyond its bits (`buildCost` of 19, ≤ 286 and ≤ 30 lengths, ≤ 316 repeat steps, 19
code-length reads, 17 for an error), and reads at least 26 header bits besides the 3-bit
block header, so a block with a dynamic header pays its constant out of `67·29` potential.
The coefficient 67 is that amortisation (`⌈(1887 + 33 + 2) / 29⌉`); for stored and fixed
blocks alone 12 would do. The bound is honest but loose by design: it charges the dynamic
table construction to the header bits, as the number of blocks is not known in advance.
-/

set_option autoImplicit false

namespace SafePdf.Spec.FlateWork

open SafePdf SafePdf.Core.Filter.Flate

/-- Counted twin of `decodeGo`: one step per bit read. -/
def decodeGoW (input : ByteArray) (h : Huffman) :
    Nat → Nat → Nat → Nat → Nat → Nat → Except Error (Nat × Nat) × Nat
  | 0, _, _, _, _, p => (.error (.malformed (p / 8) "flate: invalid Huffman code"), 0)
  | fuel + 1, len, code, first, index, p =>
    match bitAt input p with
    | none => (.error (truncated p), 1)
    | some b =>
      let code := code ||| b
      let count := h.counts[len]?.getD 0
      if code < first + count then
        match h.symbols[index + (code - first)]? with
        | some s => (.ok (s, p + 1), 1)
        | none => (.error (.malformed (p / 8) "flate: internal: Huffman table"), 1)
      else
        let r := decodeGoW input h fuel (len + 1) (code <<< 1) ((first + count) <<< 1)
          (index + count) (p + 1)
        (r.1, r.2 + 1)

/-- The twin computes exactly `decodeGo`. -/
theorem decodeGoW_fst (input : ByteArray) (h : Huffman) (fuel len code first index p : Nat) :
    (decodeGoW input h fuel len code first index p).1 =
      decodeGo input h fuel len code first index p := by
  induction fuel generalizing len code first index p with
  | zero => rfl
  | succ fuel ih =>
    rw [decodeGoW, decodeGo]
    cases bitAt input p with
    | none => rfl
    | some b =>
      dsimp only
      split
      · cases h.symbols[index + ((code ||| b) - first)]? <;> rfl
      · exact ih ..

/-- `decodeGoW` takes at most `fuel` steps. -/
theorem decodeGoW_snd_le (input : ByteArray) (h : Huffman) (fuel len code first index p : Nat) :
    (decodeGoW input h fuel len code first index p).2 ≤ fuel := by
  induction fuel generalizing len code first index p with
  | zero => simp [decodeGoW]
  | succ fuel ih =>
    rw [decodeGoW]
    split
    · simp
    · dsimp only
      split
      · split <;> simp
      · exact Nat.succ_le_succ (ih ..)

/-- A bit that exists lies before the end of the input. -/
theorem bitAt_some {input : ByteArray} {i b : Nat} (h : bitAt input i = some b) :
    i + 1 ≤ input.size * 8 := by
  unfold bitAt at h
  split at h
  · omega
  · simp at h

/-- On success `decodeGoW` takes exactly one step per bit consumed, consumes at least one
bit and stays within the input. -/
theorem decodeGoW_ok (input : ByteArray) (h : Huffman) (fuel len code first index p s p' : Nat)
    (hr : (decodeGoW input h fuel len code first index p).1 = .ok (s, p')) :
    (decodeGoW input h fuel len code first index p).2 + p = p' ∧ p < p' ∧
      p' ≤ input.size * 8 := by
  induction fuel generalizing len code first index p with
  | zero => simp [decodeGoW] at hr
  | succ fuel ih =>
    rw [decodeGoW] at hr ⊢
    split at hr
    · simp at hr
    · rename_i b hb
      have := bitAt_some hb
      dsimp only at hr ⊢
      split at hr
      · rename_i hlt
        simp only [hlt, ↓reduceIte]
        split at hr
        · simp at hr; omega
        · simp at hr
      · rename_i hlt
        simp only [hlt, ↓reduceIte]
        have := ih _ _ _ _ _ hr
        omega

/-- Counted twin of `decodeSym`. -/
@[inline] def decodeSymW (input : ByteArray) (h : Huffman) (pos : Nat) :
    Except Error (Nat × Nat) × Nat :=
  decodeGoW input h 15 1 0 0 0 pos

/-- The twin computes exactly `decodeSym`. -/
theorem decodeSymW_fst (input : ByteArray) (h : Huffman) (pos : Nat) :
    (decodeSymW input h pos).1 = decodeSym input h pos :=
  decodeGoW_fst ..

/-- A symbol decode takes at most 15 steps. -/
theorem decodeSymW_snd_le (input : ByteArray) (h : Huffman) (pos : Nat) :
    (decodeSymW input h pos).2 ≤ 15 :=
  decodeGoW_snd_le ..

/-- On success a symbol decode takes one step per bit consumed (at least one). -/
theorem decodeSymW_ok {input : ByteArray} {h : Huffman} {pos s p' : Nat}
    (hr : (decodeSymW input h pos).1 = .ok (s, p')) :
    (decodeSymW input h pos).2 + pos = p' ∧ pos < p' ∧ p' ≤ input.size * 8 :=
  decodeGoW_ok _ _ _ _ _ _ _ _ _ _ hr

/-- A successful `readBits` advances by exactly `n` bits and stays within the input. -/
theorem readBits_ok {input : ByteArray} {pos n v p' : Nat}
    (hr : readBits input pos n = .ok (v, p')) : p' = pos + n ∧ p' ≤ input.size * 8 := by
  unfold readBits at hr
  split at hr
  · split at hr
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hr; omega
    · simp at hr
  · simp at hr

set_option maxRecDepth 4000 in
/-- Counted twin of `codes`: one step per iteration, plus the bit steps of the two symbol
decodes, one step per `readBits`, and `len` steps per back-reference copy. -/
def codesW (input : ByteArray) (limit : Nat) (lit dist : Huffman) (out : Out limit)
    (pos : Nat) : Except Error (Out limit × Nat) × Nat :=
  let q1 := decodeSymW input lit pos
  match q1.1 with
  | .error e => (.error e, 1 + q1.2)
  | .ok (sym, p1) =>
    if sym < 256 then
      if h : out.1.size < limit then
        let r := codesW input limit lit dist
          ⟨out.1.push sym.toUInt8, by simp [ByteArray.size_push]; omega⟩ p1
        (r.1, 1 + q1.2 + r.2)
      else (.error limitErr, 1 + q1.2)
    else if sym == 256 then (.ok (out, p1), 1 + q1.2)
    else if 29 ≤ sym - 257 then
      (.error (.malformed (pos / 8) "flate: invalid length symbol"), 1 + q1.2)
    else
      match readBits input p1 (lenExtra[sym - 257]?.getD 0) with
      | .error e => (.error e, 2 + q1.2)
      | .ok (le, p2) =>
        let len := lenBase[sym - 257]?.getD 0 + le
        let q3 := decodeSymW input dist p2
        match q3.1 with
        | .error e => (.error e, 2 + q1.2 + q3.2)
        | .ok (ds, p3) =>
          if 30 ≤ ds then
            (.error (.malformed (p2 / 8) "flate: invalid distance symbol"), 2 + q1.2 + q3.2)
          else
            match readBits input p3 (distExtra[ds]?.getD 0) with
            | .error e => (.error e, 3 + q1.2 + q3.2)
            | .ok (de, p4) =>
              let d := distBase[ds]?.getD 0 + de
              if hd : 0 < d ∧ d ≤ out.1.size then
                if hl : 0 < len ∧ out.1.size + len ≤ limit then
                  let r := codesW input limit lit dist
                    ⟨copyBack d hd.1 len out.1 hd.2, by rw [copyBack_size]; omega⟩ p4
                  (r.1, 3 + q1.2 + q3.2 + len + r.2)
                else (.error limitErr, 3 + q1.2 + q3.2)
              else
                (.error (.malformed (p3 / 8) "flate: invalid distance too far back"),
                  3 + q1.2 + q3.2)
termination_by limit - out.1.size
decreasing_by
  all_goals simp only [ByteArray.size_push, copyBack_size]
  all_goals omega

set_option maxRecDepth 4000 in
/-- The twin computes exactly `codes`. -/
theorem codesW_fst (input : ByteArray) (limit : Nat) (lit dist : Huffman) (out : Out limit)
    (pos : Nat) : (codesW input limit lit dist out pos).1 = codes input limit lit dist out pos := by
  rw [codesW.eq_def, codes.eq_def]
  dsimp only
  rw [decodeSymW_fst]
  rcases decodeSym input lit pos with e | ⟨sym, p1⟩
  · rfl
  · dsimp only
    split
    · split
      · exact codesW_fst ..
      · rfl
    · split
      · rfl
      · split
        · rfl
        · rcases readBits input p1 (lenExtra[sym - 257]?.getD 0) with e | ⟨le, p2⟩
          · rfl
          · dsimp only
            rw [decodeSymW_fst]
            rcases decodeSym input dist p2 with e | ⟨ds, p3⟩
            · rfl
            · dsimp only
              split
              · rfl
              · rcases readBits input p3 (distExtra[ds]?.getD 0) with e | ⟨de, p4⟩
                · rfl
                · dsimp only
                  split
                  · split
                    · exact codesW_fst ..
                    · rfl
                  · rfl
termination_by limit - out.1.size
decreasing_by
  all_goals simp only [ByteArray.size_push, copyBack_size]
  all_goals omega

/-- The potential left after a successful block-level call: `67` per unread input bit plus
`2` per byte of output still allowed; `0` after an error. -/
def postW (N limit : Nat) : Except Error (Out limit × Nat) → Nat
  | .ok (o, p) => 67 * (N - p) + 2 * (limit - o.1.size)
  | .error _ => 0

set_option maxRecDepth 4000 in
/-- **Work of the literal/length loop**: the steps of `codesW` plus the potential left
afterwards are at most the potential before plus `33`. -/
theorem codesW_bound (input : ByteArray) (limit : Nat) (lit dist : Huffman) (out : Out limit)
    (pos : Nat) :
    (codesW input limit lit dist out pos).2 +
        postW (input.size * 8) limit (codesW input limit lit dist out pos).1 ≤
      67 * (input.size * 8 - pos) + 2 * (limit - out.1.size) + 33 := by
  rw [codesW.eq_def]
  dsimp only
  have hk1 := decodeSymW_snd_le input lit pos
  have hok1 := @decodeSymW_ok input lit pos
  generalize decodeSymW input lit pos = q1 at hk1 hok1 ⊢
  rcases q1 with ⟨_ | ⟨sym, p1⟩, k1⟩
  · simp only [postW]; omega
  · obtain ⟨e1, e2, e3⟩ := hok1 rfl
    dsimp only at hk1 e1 ⊢
    split
    · split
      · rename_i h
        have ih := codesW_bound input limit lit dist
          ⟨out.1.push sym.toUInt8, by simp [ByteArray.size_push]; omega⟩ p1
        simp only [ByteArray.size_push] at ih; dsimp only
        omega
      · simp only [postW]; omega
    · split
      · simp only [postW]; omega
      · split
        · simp only [postW]; omega
        · have hb2 := @readBits_ok input p1 (lenExtra[sym - 257]?.getD 0)
          generalize readBits input p1 (lenExtra[sym - 257]?.getD 0) = rb at hb2 ⊢
          rcases rb with _ | ⟨le, p2⟩
          · simp only [postW]; omega
          · obtain ⟨f1, f2⟩ := hb2 rfl
            dsimp only
            have hk3 := decodeSymW_snd_le input dist p2
            have hok3 := @decodeSymW_ok input dist p2
            generalize decodeSymW input dist p2 = q3 at hk3 hok3 ⊢
            rcases q3 with ⟨_ | ⟨ds, p3⟩, k3⟩
            · simp only [postW]; omega
            · obtain ⟨g1, g2, g3⟩ := hok3 rfl
              dsimp only at hk3 g1 ⊢
              split
              · simp only [postW]; omega
              · have hb4 := @readBits_ok input p3 (distExtra[ds]?.getD 0)
                generalize readBits input p3 (distExtra[ds]?.getD 0) = rb4 at hb4 ⊢
                rcases rb4 with _ | ⟨de, p4⟩
                · simp only [postW]; omega
                · obtain ⟨h1, h2⟩ := hb4 rfl
                  dsimp only
                  split
                  · split
                    · rename_i hd hl
                      have ih := codesW_bound input limit lit dist
                        ⟨copyBack (distBase[ds]?.getD 0 + de) hd.1 (lenBase[sym - 257]?.getD 0 + le) out.1 hd.2,
                          by rw [copyBack_size]; omega⟩ p4
                      simp only [copyBack_size] at ih; dsimp only
                      omega
                    · simp only [postW]; omega
                  · simp only [postW]; omega
termination_by limit - out.1.size
decreasing_by
  all_goals simp only [ByteArray.size_push, copyBack_size]
  all_goals omega

/-! ## Stored blocks -/

/-- Counted twin of `stored`: one step, plus one per byte copied. -/
def storedW (input : ByteArray) (limit : Nat) (out : Out limit) (pos : Nat) :
    Except Error (Out limit × Nat) × Nat :=
  let byte := (pos + 7) / 8
  if h : byte + 4 ≤ input.size then
    let len := input[byte].toNat ||| (input[byte + 1].toNat <<< 8)
    let nlen := input[byte + 2].toNat ||| (input[byte + 3].toNat <<< 8)
    if len + nlen != 65535 then
      (.error (.malformed byte "flate: invalid stored block lengths"), 1)
    else if input.size < byte + 4 + len then (.error (truncated ((byte + 4) * 8)), 1)
    else if hl : out.1.size + len ≤ limit then
      let chunk := input.extract (byte + 4) (byte + 4 + len)
      (.ok (⟨out.1 ++ chunk, by
          simp only [ByteArray.size_append, chunk, ByteArray.size_extract]; omega⟩,
        (byte + 4 + len) * 8), 1 + len)
    else (.error limitErr, 1)
  else (.error (truncated pos), 1)

/-- The twin computes exactly `stored`. -/
theorem storedW_fst (input : ByteArray) (limit : Nat) (out : Out limit) (pos : Nat) :
    (storedW input limit out pos).1 = stored input limit out pos := by
  unfold storedW stored
  dsimp only
  split
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rfl

/-- **Work of a stored block**: at most the potential before plus `1`. -/
theorem storedW_bound (input : ByteArray) (limit : Nat) (out : Out limit) (pos : Nat) :
    (storedW input limit out pos).2 + postW (input.size * 8) limit (storedW input limit out pos).1 ≤
      67 * (input.size * 8 - pos) + 2 * (limit - out.1.size) + 1 := by
  unfold storedW
  dsimp only
  split
  · split
    · simp only [postW]; omega
    · split
      · simp only [postW]; omega
      · split
        · simp only [postW, ByteArray.size_append, ByteArray.size_extract]; omega
        · simp only [postW]; omega
  · simp only [postW]; omega

/-! ## Dynamic block headers -/

/-- Counted twin of `readLengths`: one step per iteration, the bit steps of the symbol
decode, one step per `readBits`, and `n` steps per repeat of length `n`. -/
def readLengthsW (input : ByteArray) (cl : Huffman) (total : Nat) (acc : Array Nat)
    (pos : Nat) : Except Error (Array Nat × Nat) × Nat :=
  if _hdone : total ≤ acc.size then (.ok (acc, pos), 0)
  else
    let q1 := decodeSymW input cl pos
    match q1.1 with
    | .error e => (.error e, 1 + q1.2)
    | .ok (sym, p1) =>
      if sym < 16 then
        let r := readLengthsW input cl total (acc.push sym) p1
        (r.1, 1 + q1.2 + r.2)
      else
        let r : Except Error (Nat × Nat × Nat) :=
          if sym == 16 then
            match acc.back? with
            | none => .error (.malformed (pos / 8) "flate: invalid bit length repeat")
            | some prev => (readBits input p1 2).map fun (e, p) => (prev, 3 + e, p)
          else if sym == 17 then (readBits input p1 3).map fun (e, p) => (0, 3 + e, p)
          else (readBits input p1 7).map fun (e, p) => (0, 11 + e, p)
        match r with
        | .error e => (.error e, 2 + q1.2)
        | .ok (v, n, p2) =>
          if h : 0 < n ∧ acc.size + n ≤ total then
            let r' := readLengthsW input cl total (acc ++ Array.replicate n v) p2
            (r'.1, 2 + q1.2 + n + r'.2)
          else (.error (.malformed (pos / 8) "flate: invalid bit length repeat"), 2 + q1.2)
termination_by total - acc.size
decreasing_by
  all_goals simp only [Array.size_push, Array.size_append, Array.size_replicate]
  all_goals omega

/-- The twin computes exactly `readLengths`. -/
theorem readLengthsW_fst (input : ByteArray) (cl : Huffman) (total : Nat) (acc : Array Nat)
    (pos : Nat) : (readLengthsW input cl total acc pos).1 = readLengths input cl total acc pos := by
  rw [readLengthsW.eq_def, readLengths.eq_def]
  split
  · rfl
  · dsimp only
    rw [decodeSymW_fst]
    rcases decodeSym input cl pos with e | ⟨sym, p1⟩
    · rfl
    · dsimp only
      split
      · exact readLengthsW_fst ..
      · by_cases h16 : (sym == 16) = true
        · simp only [h16, ↓reduceIte]
          rcases acc.back? with _ | prev
          · rfl
          · rcases readBits input p1 2 with _ | ⟨x, p2⟩
            · rfl
            · dsimp only [Except.map]
              split
              · exact readLengthsW_fst ..
              · rfl
        · simp only [h16, ↓reduceIte, Bool.false_eq_true]
          by_cases h17 : (sym == 17) = true
          · simp only [h17, ↓reduceIte]
            rcases readBits input p1 3 with _ | ⟨x, p2⟩
            · rfl
            · dsimp only [Except.map]
              split
              · exact readLengthsW_fst ..
              · rfl
          · simp only [h17, ↓reduceIte, Bool.false_eq_true]
            rcases readBits input p1 7 with _ | ⟨x, p2⟩
            · rfl
            · dsimp only [Except.map]
              split
              · exact readLengthsW_fst ..
              · rfl
termination_by total - acc.size
decreasing_by
  all_goals simp only [Array.size_push, Array.size_append, Array.size_replicate]
  all_goals omega

/-- The potential left after a successful `readLengths`: `67` per unread input bit. -/
def postL (N : Nat) : Except Error (Array Nat × Nat) → Nat
  | .ok (_, p) => 67 * (N - p)
  | .error _ => 0

/-- **Work of the code-length loop**: the steps plus the potential left are at most `67` per
input bit, plus one per code length still to read, plus `17`. -/
theorem readLengthsW_bound (input : ByteArray) (cl : Huffman) (total : Nat) (acc : Array Nat)
    (pos : Nat) :
    (readLengthsW input cl total acc pos).2 +
        postL (input.size * 8) (readLengthsW input cl total acc pos).1 ≤
      67 * (input.size * 8 - pos) + (total - acc.size) + 17 := by
  rw [readLengthsW.eq_def]
  split
  · simp only [postL]; omega
  · dsimp only
    have hk1 := decodeSymW_snd_le input cl pos
    have hok1 := @decodeSymW_ok input cl pos
    generalize decodeSymW input cl pos = q1 at hk1 hok1 ⊢
    rcases q1 with ⟨_ | ⟨sym, p1⟩, k1⟩
    · simp only [postL]; omega
    · obtain ⟨e1, e2, e3⟩ := hok1 rfl
      dsimp only at hk1 e1 ⊢
      split
      · have ih := readLengthsW_bound input cl total (acc.push sym) p1
        simp only [Array.size_push] at ih; dsimp only
        omega
      · -- In every repeat case, `r = .ok (v, n, p2)` implies `p1 < p2 ≤ N`.
        have key : ∀ (r : Except Error (Nat × Nat × Nat)),
            (∀ v n p2, r = .ok (v, n, p2) → p1 < p2 ∧ p2 ≤ input.size * 8) →
            (match r with
              | .error e => ((.error e : Except Error (Array Nat × Nat)), 2 + k1)
              | .ok (v, n, p2) =>
                if h : 0 < n ∧ acc.size + n ≤ total then
                  let r' := readLengthsW input cl total (acc ++ Array.replicate n v) p2
                  (r'.1, 2 + k1 + n + r'.2)
                else (.error (.malformed (pos / 8) "flate: invalid bit length repeat"), 2 + k1)).2 +
              postL (input.size * 8) (match r with
              | .error e => ((.error e : Except Error (Array Nat × Nat)), 2 + k1)
              | .ok (v, n, p2) =>
                if h : 0 < n ∧ acc.size + n ≤ total then
                  let r' := readLengthsW input cl total (acc ++ Array.replicate n v) p2
                  (r'.1, 2 + k1 + n + r'.2)
                else (.error (.malformed (pos / 8) "flate: invalid bit length repeat"), 2 + k1)).1 ≤
              67 * (input.size * 8 - pos) + (total - acc.size) + 17 := by
          intro r hr
          rcases r with _ | ⟨v, n, p2⟩
          · simp only [postL]; omega
          · obtain ⟨f1, f2⟩ := hr v n p2 rfl
            dsimp only
            split
            · have ih := readLengthsW_bound input cl total (acc ++ Array.replicate n v) p2
              simp only [Array.size_append, Array.size_replicate] at ih; dsimp only
              omega
            · simp only [postL]; omega
        apply key
        intro v n p2 hr
        by_cases h16 : (sym == 16) = true
        · simp only [h16, ↓reduceIte] at hr
          split at hr
          · cases hr
          · rcases hb : readBits input p1 2 with _ | ⟨x, p⟩ <;> rw [hb] at hr
            · simp [Except.map] at hr
            · simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
              have := readBits_ok hb; omega
        · simp only [h16, ↓reduceIte, Bool.false_eq_true] at hr
          by_cases h17 : (sym == 17) = true
          · simp only [h17, ↓reduceIte] at hr
            rcases hb : readBits input p1 3 with _ | ⟨x, p⟩ <;> rw [hb] at hr
            · simp [Except.map] at hr
            · simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
              have := readBits_ok hb; omega
          · simp only [h17, ↓reduceIte, Bool.false_eq_true] at hr
            rcases hb : readBits input p1 7 with _ | ⟨x, p⟩ <;> rw [hb] at hr
            · simp [Except.map] at hr
            · simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
              have := readBits_ok hb; omega
termination_by total - acc.size
decreasing_by
  all_goals simp only [Array.size_push, Array.size_append, Array.size_replicate]
  all_goals omega

/-- `readClLengths` keeps the array size and reads exactly 3 bits per listed symbol. -/
theorem readClLengths_ok (input : ByteArray) (l : List Nat) (acc : Array Nat) (p : Nat)
    {cll : Array Nat} {p' : Nat} (hp : p ≤ input.size * 8)
    (h : readClLengths input l acc p = .ok (cll, p')) :
    cll.size = acc.size ∧ p' = p + 3 * l.length ∧ p' ≤ input.size * 8 := by
  induction l generalizing acc p with
  | nil =>
    simp only [readClLengths, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp, hp⟩
  | cons s ss ih =>
    rw [readClLengths] at h
    rcases hb : readBits input p 3 with e | ⟨v, q⟩ <;> rw [hb] at h
    · cases h
    · obtain ⟨hq1, hq2⟩ := readBits_ok hb
      dsimp only at h
      obtain ⟨g1, g2, g3⟩ := ih _ _ hq2 h
      simp only [Array.size_setIfInBounds] at g1
      simp only [List.length_cons]
      omega

/-- Cost charged for one `build` over `n` code lengths: the `any` check, the counting fold,
`leftOver` and `offsets` (15 steps each), the symbol table and the sorting fold. A model,
not a mechanised count: `build` is straight-line code made of folds over arrays of size `n`
(at most 286 here) and loops of 15 or 16 steps. -/
def buildCost (n : Nat) : Nat := 4 * n + 64

/-- Counted twin of `readDynamic`: one step per `readBits` (three header fields, one per
code-length code length), `buildCost` per table built, and the steps of `readLengthsW`. -/
def readDynamicW (input : ByteArray) (pos : Nat) :
    Except Error (Huffman × Huffman × Nat) × Nat :=
  match readBits input pos 5 with
  | .error e => (.error e, 1)
  | .ok (hlit, p1) =>
  match readBits input p1 5 with
  | .error e => (.error e, 2)
  | .ok (hdist, p2) =>
  match readBits input p2 4 with
  | .error e => (.error e, 3)
  | .ok (hclen, p3) =>
  if 286 < hlit + 257 ∨ 30 < hdist + 1 then
    (.error (.malformed (pos / 8) "flate: too many length or distance symbols"), 3)
  else
  let c1 := 3 + (clOrder.take (hclen + 4)).length
  match readClLengths input (clOrder.take (hclen + 4)) (Array.replicate 19 0) p3 with
  | .error e => (.error e, c1)
  | .ok (cll, p4) =>
  let c2 := c1 + buildCost cll.size
  match build .codeLengths cll with
  | .error _ => (.error (.malformed (p3 / 8) "flate: invalid code lengths set"), c2)
  | .ok cl =>
  let q := readLengthsW input cl (hlit + 257 + (hdist + 1)) #[] p4
  match q.1 with
  | .error e => (.error e, c2 + q.2)
  | .ok (lens, p5) =>
  if lens[256]?.getD 0 == 0 then
    (.error (.malformed (p4 / 8) "flate: invalid code -- missing end-of-block"), c2 + q.2)
  else
  let c3 := c2 + q.2 + buildCost (lens.extract 0 (hlit + 257)).size
  match build .litOrDist (lens.extract 0 (hlit + 257)) with
  | .error _ => (.error (.malformed (p4 / 8) "flate: invalid literal/lengths set"), c3)
  | .ok lit =>
  let c4 := c3 + buildCost (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1))).size
  match build .litOrDist (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1))) with
  | .error _ => (.error (.malformed (p4 / 8) "flate: invalid distances set"), c4)
  | .ok dist => (.ok (lit, dist, p5), c4)

/-- The twin computes exactly `readDynamic`. -/
theorem readDynamicW_fst (input : ByteArray) (pos : Nat) :
    (readDynamicW input pos).1 = readDynamic input pos := by
  unfold readDynamicW readDynamic
  simp only [bind, Except.bind]
  rcases readBits input pos 5 with e | ⟨hlit, p1⟩
  · rfl
  dsimp only
  rcases readBits input p1 5 with e | ⟨hdist, p2⟩
  · rfl
  dsimp only
  rcases readBits input p2 4 with e | ⟨hclen, p3⟩
  · rfl
  dsimp only
  split
  · rfl
  rcases readClLengths input (clOrder.take (hclen + 4)) (Array.replicate 19 0) p3 with
    e | ⟨cll, p4⟩
  · rfl
  dsimp only
  rcases build .codeLengths cll with e | cl
  · rfl
  dsimp only [Except.mapError]
  rw [readLengthsW_fst]
  rcases readLengths input cl (hlit + 257 + (hdist + 1)) #[] p4 with e | ⟨lens, p5⟩
  · rfl
  dsimp only
  split
  · rfl
  rcases build .litOrDist (lens.extract 0 (hlit + 257)) with e | lit
  · rfl
  dsimp only [Except.mapError]
  rcases build .litOrDist (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1))) with e | dist
  · rfl
  rfl

/-- The potential left after a successful dynamic header: `67` per unread input bit, plus a
bonus of `67 · 26` for the at least 26 header bits (HLIT, HDIST, HCLEN and at least four
3-bit code-length code lengths) that were read. -/
def postD (N : Nat) : Except Error (Huffman × Huffman × Nat) → Nat
  | .ok (_, _, p) => 67 * (N - p) + 67 * 26
  | .error _ => 0

/-- Between 4 and 19 code-length code lengths are read. -/
theorem clOrder_take_length (n : Nat) : 4 ≤ (clOrder.take (n + 4)).length ∧
    (clOrder.take (n + 4)).length ≤ 19 := by
  simp only [List.length_take, clOrder, List.length_cons, List.length_nil]
  omega

/-- **Work of a dynamic header**: steps plus the potential left are at most the potential
before plus `1887` (= 3 + 19 + `buildCost 19` + 316 + 17 + `buildCost 286` + `buildCost 30`). -/
theorem readDynamicW_bound (input : ByteArray) (pos : Nat) :
    (readDynamicW input pos).2 + postD (input.size * 8) (readDynamicW input pos).1 ≤
      67 * (input.size * 8 - pos) + 1887 := by
  unfold readDynamicW
  rcases hb1 : readBits input pos 5 with e | ⟨hlit, p1⟩
  · simp only [postD]; omega
  obtain ⟨a1, a2⟩ := readBits_ok hb1
  dsimp only
  rcases hb2 : readBits input p1 5 with e | ⟨hdist, p2⟩
  · simp only [postD]; omega
  obtain ⟨b1, b2⟩ := readBits_ok hb2
  dsimp only
  rcases hb3 : readBits input p2 4 with e | ⟨hclen, p3⟩
  · simp only [postD]; omega
  obtain ⟨c1, c2⟩ := readBits_ok hb3
  dsimp only
  split
  · simp only [postD]; omega
  rename_i hsym
  have hord := clOrder_take_length hclen
  rcases hcl : readClLengths input (clOrder.take (hclen + 4)) (Array.replicate 19 0) p3 with
    e | ⟨cll, p4⟩
  · simp only [postD]; omega
  obtain ⟨d1, d2, d3⟩ := readClLengths_ok input _ _ p3 c2 hcl
  simp only [Array.size_replicate] at d1
  dsimp only
  rw [d1]
  rcases build .codeLengths cll with e | cl
  · simp only [postD, buildCost]; omega
  dsimp only
  have hL := readLengthsW_bound input cl (hlit + 257 + (hdist + 1)) #[] p4
  generalize readLengthsW input cl (hlit + 257 + (hdist + 1)) #[] p4 = q at hL ⊢
  rcases q with ⟨_ | ⟨lens, p5⟩, k⟩
  · simp only [postD, buildCost]; simp only [postL, List.size_toArray, List.length_nil] at hL
    omega
  simp only [postL, List.size_toArray, List.length_nil] at hL
  dsimp only
  have hx1 : (lens.extract 0 (hlit + 257)).size ≤ 286 := by
    simp only [Array.size_extract]; omega
  have hx2 : (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1))).size ≤ 30 := by
    simp only [Array.size_extract]; omega
  split
  · simp only [postD, buildCost]; omega
  rcases build .litOrDist (lens.extract 0 (hlit + 257)) with e | lit
  · simp only [postD, buildCost]; omega
  dsimp only
  rcases build .litOrDist (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1))) with e | dist
  · simp only [postD, buildCost]; omega
  simp only [postD, buildCost]
  omega

/-! ## The block loop and the entry points -/

/-- Counted twin of the body of one `blocks` iteration (after the 3-bit header). -/
def blockBodyW (input : ByteArray) (limit : Nat) (out : Out limit) (pos p1 btype : Nat) :
    Except Error (Out limit × Nat) × Nat :=
  if btype == 0 then storedW input limit out p1
  else if btype == 1 then codesW input limit fixedLit fixedDist out p1
  else if btype == 2 then
    let q := readDynamicW input p1
    match q.1 with
    | .error e => (.error e, q.2)
    | .ok (lit, dist, p2) =>
      let c := codesW input limit lit dist out p2
      (c.1, q.2 + c.2)
  else (.error (.malformed (pos / 8) "flate: invalid block type"), 0)

/-- Counted twin of `blocks`: two steps per block (iteration and header read) plus the steps
of the block body. The fixed codes `fixedLit`/`fixedDist` are global constants, built once,
and cost nothing per block. -/
def blocksW (input : ByteArray) (limit : Nat) (out : Out limit) (pos : Nat) :
    Except Error (Out limit × Nat) × Nat :=
  match readBits input pos 3 with
  | .error e => (.error e, 1)
  | .ok (hdr, p1) =>
    let final := hdr &&& 1
    let r := blockBodyW input limit out pos p1 (hdr >>> 1)
    match r.1 with
    | .error e => (.error e, 2 + r.2)
    | .ok (out', p') =>
      if final == 1 then (.ok (out', p'), 2 + r.2)
      else if _h : pos < p' ∧ p' ≤ input.size * 8 then
        let q := blocksW input limit out' p'
        (q.1, 2 + r.2 + q.2)
      else (.error (.malformed (pos / 8) "flate: internal: no progress"), 2 + r.2)
termination_by input.size * 8 - pos

/-- The block-body twin computes exactly the body of `blocks`. -/
theorem blockBodyW_fst (input : ByteArray) (limit : Nat) (out : Out limit) (pos p1 btype : Nat) :
    (blockBodyW input limit out pos p1 btype).1 =
      (if btype == 0 then stored input limit out p1
      else if btype == 1 then codes input limit fixedLit fixedDist out p1
      else if btype == 2 then
        match readDynamic input p1 with
        | .error e => .error e
        | .ok (lit, dist, p2) => codes input limit lit dist out p2
      else .error (.malformed (pos / 8) "flate: invalid block type")) := by
  unfold blockBodyW
  split
  · exact storedW_fst ..
  split
  · exact codesW_fst ..
  split
  · dsimp only
    rw [readDynamicW_fst]
    rcases readDynamic input p1 with e | ⟨lit, dist, p2⟩
    · rfl
    · exact codesW_fst ..
  · rfl

/-- The twin computes exactly `blocks`. -/
theorem blocksW_fst (input : ByteArray) (limit : Nat) (out : Out limit) (pos : Nat) :
    (blocksW input limit out pos).1 = blocks input limit out pos := by
  rw [blocksW.eq_def, blocks.eq_def]
  rcases readBits input pos 3 with e | ⟨hdr, p1⟩
  · rfl
  dsimp only
  rw [blockBodyW_fst]
  generalize (if hdr >>> 1 == 0 then stored input limit out p1 else _) = r
  rcases r with e | ⟨out', p'⟩
  · rfl
  dsimp only
  split
  · rfl
  split
  · exact blocksW_fst ..
  · rfl
termination_by input.size * 8 - pos

/-- `k` on success, `0` on error. -/
def okExtra {α : Type} (k : Nat) : Except Error α → Nat
  | .ok _ => k
  | .error _ => 0

set_option maxRecDepth 4000 in
/-- **Work of one block body**: at most the potential before plus `1920`; a successful body
leaves `1721` of that unspent (so it costs at most `199` beyond the bits and bytes it
consumes). The dynamic case pays for its tables with the bonus of `readDynamicW_bound`. -/
theorem blockBodyW_bound (input : ByteArray) (limit : Nat) (out : Out limit)
    (pos p1 btype : Nat) :
    (blockBodyW input limit out pos p1 btype).2 +
        postW (input.size * 8) limit (blockBodyW input limit out pos p1 btype).1 +
        okExtra 1721 (blockBodyW input limit out pos p1 btype).1 ≤
      67 * (input.size * 8 - p1) + 2 * (limit - out.1.size) + 1920 := by
  unfold blockBodyW
  split
  · have h := storedW_bound input limit out p1
    generalize storedW input limit out p1 = r at h ⊢
    rcases r with ⟨_ | _, k⟩ <;> simp only [okExtra] at h ⊢ <;> omega
  split
  · have h := codesW_bound input limit fixedLit fixedDist out p1
    generalize codesW input limit fixedLit fixedDist out p1 = r at h ⊢
    rcases r with ⟨_ | _, k⟩ <;> simp only [okExtra] at h ⊢ <;> omega
  split
  · have hD := readDynamicW_bound input p1
    generalize readDynamicW input p1 = q at hD ⊢
    rcases q with ⟨_ | ⟨lit, dist, p2⟩, kD⟩
    · simp only [postD] at hD; simp only [postW, okExtra]; omega
    · simp only [postD] at hD
      dsimp only
      have h := codesW_bound input limit lit dist out p2
      generalize codesW input limit lit dist out p2 = r at h ⊢
      rcases r with ⟨_ | _, k⟩ <;> simp only [okExtra] at h ⊢ <;> omega
  · simp only [postW, okExtra]; omega

/-- **Work of the block loop**: steps plus the potential left are at most `67` per unread
input bit, plus `2` per byte of output still allowed, plus `1922`. -/
theorem blocksW_bound (input : ByteArray) (limit : Nat) (out : Out limit) (pos : Nat) :
    (blocksW input limit out pos).2 + postW (input.size * 8) limit (blocksW input limit out pos).1 ≤
      67 * (input.size * 8 - pos) + 2 * (limit - out.1.size) + 1922 := by
  rw [blocksW.eq_def]
  rcases hb : readBits input pos 3 with e | ⟨hdr, p1⟩
  · simp only [postW]; omega
  obtain ⟨a1, a2⟩ := readBits_ok hb
  dsimp only
  have hB := blockBodyW_bound input limit out pos p1 (hdr >>> 1)
  generalize blockBodyW input limit out pos p1 (hdr >>> 1) = r at hB ⊢
  rcases r with ⟨_ | ⟨out', p'⟩, k⟩
  · simp only [postW, okExtra] at hB ⊢; omega
  simp only [postW, okExtra] at hB
  dsimp only
  split
  · simp only [postW]; omega
  split
  · rename_i hp
    have ih := blocksW_bound input limit out' p'
    dsimp only
    omega
  · simp only [postW]; omega
termination_by input.size * 8 - pos

/-- Counted twin of `inflateAt`. -/
def inflateAtW (limit : Nat) (input : ByteArray) (pos : Nat) :
    Except Error (Out limit × Nat) × Nat :=
  blocksW input limit ⟨ByteArray.empty, by simp [ByteArray.size_empty]⟩ pos

/-- The twin computes exactly `inflateAt`. -/
theorem inflateAtW_fst (limit : Nat) (input : ByteArray) (pos : Nat) :
    (inflateAtW limit input pos).1 = inflateAt limit input pos :=
  blocksW_fst ..

/-- **Work bound for raw inflate (S3)**, any outcome: at most `67` steps per input bit from
`pos`, plus `2` per byte of the output limit, plus `1922`. -/
theorem inflateAtW_steps_le (limit : Nat) (input : ByteArray) (pos : Nat) :
    (inflateAtW limit input pos).2 ≤ 67 * (input.size * 8 - pos) + 2 * limit + 1922 := by
  have h := blocksW_bound input limit ⟨ByteArray.empty, by simp [ByteArray.size_empty]⟩ pos
  simp only [ByteArray.size_empty] at h
  unfold inflateAtW
  omega

/-- **Work bound for raw inflate (S3)**, on success: at most `67` steps per input bit
consumed, plus `2` per output byte produced, plus `1922`. -/
theorem inflateAtW_steps_le_of_ok {limit : Nat} {input : ByteArray} {pos p : Nat}
    {out : Out limit} (h : (inflateAtW limit input pos).1 = .ok (out, p)) :
    (inflateAtW limit input pos).2 + 67 * (input.size * 8 - p) ≤
      67 * (input.size * 8 - pos) + 2 * out.1.size + 1922 := by
  have hb := blocksW_bound input limit ⟨ByteArray.empty, by simp [ByteArray.size_empty]⟩ pos
  simp only [ByteArray.size_empty] at hb
  unfold inflateAtW at h ⊢
  rw [h] at hb
  simp only [postW] at hb
  have := out.2
  omega

/-- Counted twin of `inflate`. -/
def inflateW (limit : Nat) (input : ByteArray) : Except Error ByteArray × Nat :=
  let q := inflateAtW limit input 0
  (q.1.map (·.1.1), q.2)

/-- The twin computes exactly `inflate`. -/
theorem inflateW_fst (limit : Nat) (input : ByteArray) :
    (inflateW limit input).1 = inflate limit input := by
  simp only [inflateW, inflate, inflateAtW_fst]

/-- **Work bound for raw inflate (S3)**: at most `536` steps per input byte, plus `2` per byte
of the output limit, plus `1922`. -/
theorem inflateW_steps_le (limit : Nat) (input : ByteArray) :
    (inflateW limit input).2 ≤ 536 * input.size + 2 * limit + 1922 := by
  have := inflateAtW_steps_le limit input 0
  simp only [inflateW]
  omega

/-- Counted twin of `zlibDecodeOut`: one step for the header, the steps of `inflateAtW`, and
one step per output byte for the Adler-32 check when it runs. -/
def zlibDecodeOutW (limit : Nat) (input : ByteArray) (checkAdler : Bool) :
    Except Error (Out limit) × Nat :=
  if h : 2 ≤ input.size then
    let cmf := input[0].toNat
    let flg := input[1].toNat
    if cmf &&& 15 != 8 then (.error (.malformed 0 "zlib: unknown compression method"), 1)
    else if 7 < cmf >>> 4 then (.error (.malformed 0 "zlib: invalid window size"), 1)
    else if (cmf * 256 + flg) % 31 != 0 then
      (.error (.malformed 1 "zlib: incorrect header check"), 1)
    else if flg &&& 32 != 0 then (.error (.unsupported "zlib: preset dictionary (FDICT)"), 1)
    else
      let q := inflateAtW limit input 16
      match q.1 with
      | .error e => (.error e, 1 + q.2)
      | .ok (out, p) =>
        if !checkAdler then (.ok out, 1 + q.2)
        else
          let i := (p + 7) / 8
          if hi : i + 4 ≤ input.size then
            let stored := (input[i].toNat <<< 24) ||| (input[i + 1].toNat <<< 16) |||
              (input[i + 2].toNat <<< 8) ||| input[i + 3].toNat
            if stored == adler32 out.1 then (.ok out, 1 + q.2 + out.1.size)
            else (.error (.malformed i "zlib: incorrect data check"), 1 + q.2 + out.1.size)
          else (.error (.malformed i "zlib: missing Adler-32 trailer"), 1 + q.2)
  else (.error (.malformed 0 "zlib: truncated header"), 1)

/-- The twin computes exactly `zlibDecodeOut`. -/
theorem zlibDecodeOutW_fst (limit : Nat) (input : ByteArray) (checkAdler : Bool) :
    (zlibDecodeOutW limit input checkAdler).1 = zlibDecodeOut limit input checkAdler := by
  unfold zlibDecodeOutW zlibDecodeOut
  split
  · dsimp only
    split
    · rfl
    split
    · rfl
    split
    · rfl
    split
    · rfl
    rw [inflateAtW_fst]
    rcases inflateAt limit input 16 with e | ⟨out, p⟩
    · rfl
    dsimp only
    split
    · rfl
    split
    · split <;> rfl
    · rfl
  · rfl

/-- Steps of `zlibDecodeOutW` in terms of the inflate steps: on success at most one more
plus the output size, and in every case at most one more plus the limit. -/
theorem zlibDecodeOutW_snd (limit : Nat) (input : ByteArray) (checkAdler : Bool) :
    (zlibDecodeOutW limit input checkAdler).2 ≤ 1 + (inflateAtW limit input 16).2 + limit ∧
      ∀ out, (zlibDecodeOutW limit input checkAdler).1 = .ok out →
        ∃ p, (inflateAtW limit input 16).1 = .ok (out, p) ∧
          (zlibDecodeOutW limit input checkAdler).2 ≤
            1 + (inflateAtW limit input 16).2 + out.1.size := by
  unfold zlibDecodeOutW
  split
  · dsimp only
    split
    · simp; omega
    split
    · simp; omega
    split
    · simp; omega
    split
    · simp; omega
    rcases hq : (inflateAtW limit input 16).1 with e | ⟨out, p⟩
    · simp
    dsimp only
    have := out.2
    split
    · refine ⟨by omega, ?_⟩
      intro o ho
      simp only [Except.ok.injEq] at ho
      subst ho
      exact ⟨p, rfl, by omega⟩
    split
    · split
      · refine ⟨by omega, ?_⟩
        intro o ho
        simp only [Except.ok.injEq] at ho
        subst ho
        exact ⟨p, rfl, by omega⟩
      · refine ⟨by omega, ?_⟩
        intro o ho
        cases ho
    · refine ⟨by omega, ?_⟩
      intro o ho
      cases ho
  · simp; omega

/-- Counted twin of `flateDecode`. -/
def flateDecodeW (limits : Limits) (input : ByteArray) (checkAdler : Bool := true) :
    Except Error ByteArray × Nat :=
  let q := zlibDecodeOutW limits.maxDecodedStreamBytes input checkAdler
  (q.1.map (·.1), q.2)

/-- The twin computes exactly `flateDecode`. -/
theorem flateDecodeW_fst (limits : Limits) (input : ByteArray) (checkAdler : Bool) :
    (flateDecodeW limits input checkAdler).1 = flateDecode limits input checkAdler := by
  simp only [flateDecodeW, flateDecode, zlibDecode, zlibDecodeOutW_fst]

/-- **Work bound for `/FlateDecode` (S3)**, any outcome (success, malformed input, or limit
exceeded): at most `536` steps per input byte, plus `3` per byte of the output limit, plus
`1923`. -/
theorem flateDecodeW_steps_le (limits : Limits) (input : ByteArray) (checkAdler : Bool) :
    (flateDecodeW limits input checkAdler).2 ≤
      536 * input.size + 3 * limits.maxDecodedStreamBytes + 1923 := by
  have h1 := (zlibDecodeOutW_snd limits.maxDecodedStreamBytes input checkAdler).1
  have h2 := inflateAtW_steps_le limits.maxDecodedStreamBytes input 16
  simp only [flateDecodeW]
  omega

/-- **Work bound for `/FlateDecode` (S3)**, on success: at most `536` steps per input byte,
plus `3` per output byte, plus `1923` — linear in input plus output. -/
theorem flateDecodeW_steps_le_of_ok {limits : Limits} {input out : ByteArray}
    {checkAdler : Bool} (h : (flateDecodeW limits input checkAdler).1 = .ok out) :
    (flateDecodeW limits input checkAdler).2 ≤ 536 * input.size + 3 * out.size + 1923 := by
  simp only [flateDecodeW] at h ⊢
  rcases hz : (zlibDecodeOutW limits.maxDecodedStreamBytes input checkAdler).1 with e | o
  · rw [hz] at h; cases h
  · rw [hz] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨p, hp, hle⟩ := (zlibDecodeOutW_snd limits.maxDecodedStreamBytes input checkAdler).2 o hz
    have := inflateAtW_steps_le_of_ok hp
    omega

end SafePdf.Spec.FlateWork
