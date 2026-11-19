import SafePdf.Core.Filter.Ascii

/-!
# RunLengthDecode (Plan.md §6 Phase 3, task 3.3; §4 S2/S3/S7)

A total, bounded decoder for `/RunLengthDecode` (ISO 32000-2 §7.4.5).

## Rules

* A length byte `n` is followed by data:
  * `0 ≤ n ≤ 127`: the next `n + 1` bytes are copied literally;
  * `129 ≤ n ≤ 255`: the next byte is repeated `257 − n` times (2 to 128 copies);
  * `n = 128`: EOD; the rest of the input is ignored.
* **Missing EOD or a truncated run**: strict (`strict = true`, the default) gives
  `Error.malformed` at the input end; lenient (`strict = false`, for the repair path) stops
  there, keeping the bytes already produced (an incomplete repeat run produces nothing).
* The filter can expand 2 bytes into 128, so a decompression bomb is a real concern: every
  emission is checked against `limits.maxDecodedStreamBytes` *before* it is appended, and
  exceeding it is `Error.limitExceeded .decodedStreamBytes` (S3).

## Design

The decoder is a byte machine (`SafePdf.Core.Filter.Ascii.Machine`, defined with the ASCII
filters): the specification `runLengthSpec` (structural recursion over a list) and the
implementation `runLengthDecode` (index loop over a `ByteArray`) share the step function
`rlStep`, and the generic `decodeWith_spec` gives impl ≡ spec, including error values.

Proven here:

* `runLengthDecode_spec` — implementation = specification.
* `runLengthDecode_size_le` — output ≤ `limits.maxDecodedStreamBytes`.
* `runLengthDecode_size_le_input` — output ≤ 128 · input.
* `runLengthDecode_encode` — round trip with the literal-run encoder `runLengthEncode`
  (chunks of at most 128 literal bytes, then EOD), strict or lenient.
* `rlSpec_repeat` — a repeat run `[257 − n, b]` decodes to `n` copies of `b`.
-/

namespace SafePdf.Core.Filter.RunLength

open SafePdf
open SafePdf.Core.Filter.Ascii

/-- RunLength state. -/
inductive RLState where
  /-- Expecting a length byte. -/
  | idle
  /-- Copying literal bytes: `n + 1` remain. -/
  | copy (n : Nat)
  /-- Expecting the byte to repeat `n` times. -/
  | rep (n : Nat)

/-- One RunLength step. -/
def rlStep (s : RLState) (_pos : Nat) (c : UInt8) : Step RLState :=
  match s with
  | .idle =>
    if c < 128 then .cont (.copy c.toNat) []
    else if c == 128 then .done []
    else .cont (.rep (257 - c.toNat)) []
  | .copy n =>
    match n with
    | 0 => .cont .idle [c]
    | n + 1 => .cont (.copy n) [c]
  | .rep n => .cont .idle (List.replicate n c)

/-- End of input without EOD. -/
def rlEof (strict : Bool) (s : RLState) (pos : Nat) : Except Error (List UInt8) :=
  if strict then
    match s with
    | .idle => .error (.malformed pos "runlength: missing EOD (128)")
    | _ => .error (.malformed pos "runlength: truncated run")
  else .ok []

/-- The RunLength machine. -/
def rlMachine (strict : Bool) : Machine RLState where
  init := .idle
  step := rlStep
  eof := rlEof strict

/-- **Specification** of RunLengthDecode on a list of bytes. -/
def runLengthSpec (limit : Nat) (strict : Bool) (input : List UInt8) :
    Except Error (List UInt8) :=
  specWith (rlMachine strict) limit input

/-- **RunLengthDecode** (ISO 32000-2 §7.4.5), bounded by `limits.maxDecodedStreamBytes`. -/
def runLengthDecode (limits : Limits) (input : ByteArray) (strict : Bool := true) :
    Except Error ByteArray :=
  decodeWith (rlMachine strict) limits.maxDecodedStreamBytes input

/-- RunLengthDecode implementation = specification. -/
theorem runLengthDecode_spec (limits : Limits) (input : ByteArray) (strict : Bool) :
    (runLengthDecode limits input strict).map (·.data.toList) =
      runLengthSpec limits.maxDecodedStreamBytes strict input.data.toList :=
  decodeWith_spec _ _ _

/-- RunLengthDecode output is within the limit. -/
theorem runLengthDecode_size_le (limits : Limits) (input out : ByteArray) (strict : Bool)
    (h : runLengthDecode limits input strict = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes :=
  decodeWith_size_le _ _ _ _ h

/-- **RunLength length law**: output ≤ 128 · input. -/
theorem runLengthDecode_size_le_input (limits : Limits) (input out : ByteArray) (strict : Bool)
    (h : runLengthDecode limits input strict = .ok out) :
    out.size ≤ 128 * input.size := by
  have := decodeWith_law (rlMachine strict) _ 1 128 0
    (fun s => match s with | .rep n => n | _ => 0) ?_ ?_ ?_ input out h
  · simpa [rlMachine] using this
  · intro s pos c s' e hs
    simp only [rlMachine, rlStep] at hs
    split at hs
    · split at hs
      · cases hs; simp
      · split at hs
        · cases hs
        · next h1 h2 =>
          cases hs
          have h3 : 128 ≤ c.toNat := by simpa [UInt8.lt_iff_toNat_lt] using h1
          have h4 : c.toNat ≠ 128 := by
            intro e; apply h2; simp only [beq_iff_eq]; exact UInt8.toNat_inj.mp (by simpa using e)
          simp; omega
    · split at hs <;> (cases hs; simp)
    · cases hs; simp
  · intro s pos c e hs
    simp only [rlMachine, rlStep] at hs
    split at hs
    · split at hs
      · cases hs
      · split at hs
        · cases hs; simp
        · cases hs
    · split at hs <;> cases hs
    · cases hs
  · intro s pos e hs
    cases strict <;> cases s <;> simp_all [rlMachine, rlEof]

/-! ## Round trips -/

/-- Literal-run encoder on lists: chunks of at most 128 bytes, each preceded by its length
minus one, then EOD. -/
def rlEncodeList : List UInt8 → List UInt8
  | [] => [128]
  | x :: xs =>
    (((x :: xs).take 128).length - 1).toUInt8 ::
      (((x :: xs).take 128) ++ rlEncodeList ((x :: xs).drop 128))
termination_by l => l.length
decreasing_by simp; omega

/-- Literal-run RunLength encoder (used for the round-trip theorem and tests). -/
def runLengthEncode (bs : ByteArray) : ByteArray := ⟨(rlEncodeList bs.data.toList).toArray⟩

/-- Copying a literal chunk. -/
theorem rlSpec_copy (strict : Bool) (limit : Nat) :
    ∀ (xs rest acc : List UInt8) (pos : Nat), xs ≠ [] → acc.length + xs.length ≤ limit →
      runSpec (rlMachine strict) limit (xs ++ rest) pos (.copy (xs.length - 1)) acc =
        runSpec (rlMachine strict) limit rest (pos + xs.length) .idle (acc ++ xs)
  | [], _, _, _, h, _ => absurd rfl h
  | [x], rest, acc, pos, _, hl => by
    have hs : (rlMachine strict).step (.copy 0) pos x = .cont .idle [x] := rfl
    simpa using runSpec_cont _ _ _ _ _ _ _ _ _ hs (by simpa using hl)
  | x :: y :: ys, rest, acc, pos, _, hl => by
    have hs : (rlMachine strict).step (.copy (ys.length + 1)) pos x =
        .cont (.copy ys.length) [x] := rfl
    have := runSpec_cont (rlMachine strict) limit x ((y :: ys) ++ rest) pos _ _ acc _ hs
      (by simp at hl ⊢; omega)
    simp only [List.length_cons, Nat.add_sub_cancel, List.cons_append] at this ⊢
    rw [this]
    have ih := rlSpec_copy strict limit (y :: ys) rest (acc ++ [x]) (pos + 1) (by simp)
      (by simp at hl ⊢; omega)
    simp only [List.length_cons, Nat.add_sub_cancel, List.cons_append] at ih
    rw [ih]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    congr 1
    omega

/-- Round trip on the specification, generalised over the accumulator. -/
theorem rlSpec_encode (strict : Bool) (limit : Nat) (bs acc : List UInt8) (pos : Nat)
    (h : acc.length + bs.length ≤ limit) :
    runSpec (rlMachine strict) limit (rlEncodeList bs) pos .idle acc = .ok (acc ++ bs) := by
  fun_induction rlEncodeList bs generalizing acc pos with
  | case1 =>
    have hs : (rlMachine strict).step .idle pos 128 = .done [] := rfl
    rw [runSpec_done _ _ _ _ _ _ _ _ hs (by simpa using h)]
  | case2 x xs ih =>
    have hlen : ((x :: xs).take 128).length = min 128 (xs.length + 1) := by simp; omega
    have hc : (((x :: xs).take 128).length - 1).toUInt8 < 128 := by
      rw [UInt8.lt_iff_toNat_lt, hlen]; simp; omega
    have hn : (((x :: xs).take 128).length - 1).toUInt8.toNat =
        ((x :: xs).take 128).length - 1 := by
      rw [hlen]; simp; omega
    have hs : (rlMachine strict).step .idle pos (((x :: xs).take 128).length - 1).toUInt8 =
        .cont (.copy (((x :: xs).take 128).length - 1)) [] := by
      simp only [rlMachine, rlStep, hc, ↓reduceIte, hn]
    have htk : (x :: xs).take 128 ≠ [] := by simp
    have htot : ((x :: xs).take 128).length + ((x :: xs).drop 128).length = xs.length + 1 := by
      simp; omega
    rw [runSpec_cont _ _ _ _ _ _ _ _ _ hs (by simp at h ⊢; omega), List.append_nil,
      rlSpec_copy strict limit _ _ _ _ htk (by simp at h ⊢; omega),
      ih _ _ (by simp at h htot ⊢; omega), List.append_assoc, List.take_append_drop]

/-- **RunLength round trip**: decoding the encoding gives the input back (strict or lenient),
whenever it fits in the limit. -/
theorem runLengthDecode_encode (limits : Limits) (bs : ByteArray) (strict : Bool)
    (h : bs.size ≤ limits.maxDecodedStreamBytes) :
    runLengthDecode limits (runLengthEncode bs) strict = .ok bs := by
  have := decodeWith_ok_of_spec (rlMachine strict) limits.maxDecodedStreamBytes
    (runLengthEncode bs) bs.data.toList
    (by simpa [specWith, rlMachine, runLengthEncode] using
      rlSpec_encode strict _ bs.data.toList [] 0 (by simpa using h))
  simpa [runLengthDecode] using this

/-- A repeat run `[257 − n, b]` (2 ≤ n ≤ 128) followed by EOD decodes to `n` copies of `b`. -/
theorem rlSpec_repeat (strict : Bool) (limit n : Nat) (b : UInt8) (h2 : 2 ≤ n) (h128 : n ≤ 128)
    (hl : n ≤ limit) :
    runLengthSpec limit strict [(257 - n).toUInt8, b, 128] = .ok (List.replicate n b) := by
  have hn : (257 - n).toUInt8.toNat = 257 - n := by simp; omega
  have hc1 : ¬ (257 - n).toUInt8 < 128 := by rw [UInt8.lt_iff_toNat_lt, hn]; simp; omega
  have hc2 : ((257 - n).toUInt8 == 128) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro he; have := congrArg UInt8.toNat he; rw [hn] at this; simp at this; omega
  have hs1 : (rlMachine strict).step .idle 0 (257 - n).toUInt8 = .cont (.rep n) [] := by
    simp only [rlMachine, rlStep, hc1, hc2, ↓reduceIte, hn, Bool.false_eq_true]
    congr; omega
  have hs2 : (rlMachine strict).step (.rep n) (0 + 1) b = .cont .idle (List.replicate n b) := rfl
  have hs3 : (rlMachine strict).step .idle (0 + 1 + 1) 128 = .done [] := rfl
  show runSpec (rlMachine strict) limit _ 0 .idle [] = _
  rw [runSpec_cont _ _ _ _ _ _ _ _ _ hs1 (by simp <;> omega),
    runSpec_cont _ _ _ _ _ _ _ _ _ hs2 (by simp <;> omega),
    runSpec_done _ _ _ _ _ _ _ _ hs3 (by simp <;> omega)]
  simp

/-! ## Tests -/

/-- Success with exactly these bytes. -/
private def okBytes (r : Except Error ByteArray) (expected : List UInt8) : Bool :=
  match r with
  | .ok o => o.data.toList == expected
  | .error _ => false

/-- Failure with `Error.malformed` at this offset. -/
private def malformedAt (r : Except Error ByteArray) (off : Nat) : Bool :=
  match r with
  | .error (.malformed o _) => o == off
  | _ => false

/-- Failure with `Error.limitExceeded .decodedStreamBytes`. -/
private def isLimit (r : Except Error ByteArray) : Bool :=
  match r with
  | .error (.limitExceeded .decodedStreamBytes) => true
  | _ => false

/-- Bytes from a list. -/
private def B (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- Default limits. -/
private def dl : Limits := {}

/-- Limits with a tiny per-stream output cap. -/
private def tiny (n : Nat) : Limits := { maxDecodedStreamBytes := n }

#guard okBytes (runLengthDecode dl (B [2, 65, 66, 67, 128])) [65, 66, 67]
#guard okBytes (runLengthDecode dl (B [254, 7, 128])) [7, 7, 7]
#guard okBytes (runLengthDecode dl (B [129, 9, 128])) (List.replicate 128 9)
#guard okBytes (runLengthDecode dl (B [0, 1, 255, 2, 1, 3, 4, 128, 99, 99])) [1, 2, 2, 3, 4]
#guard okBytes (runLengthDecode dl (B [128])) []
#guard malformedAt (runLengthDecode dl (B [2, 65])) 2
#guard malformedAt (runLengthDecode dl (B [254])) 1
#guard malformedAt (runLengthDecode dl (B [0, 65])) 2
#guard okBytes (runLengthDecode dl (B [0, 65]) (strict := false)) [65]
#guard okBytes (runLengthDecode dl (B [1, 65]) (strict := false)) [65]
#guard isLimit (runLengthDecode (tiny 127) (B [129, 9, 128]))
#guard okBytes (runLengthDecode (tiny 128) (B [129, 9, 128])) (List.replicate 128 9)
#guard okBytes (runLengthDecode dl (runLengthEncode (B (List.replicate 300 5))))
  (List.replicate 300 5)
-- Bomb: 2 MiB of `[129, 0]` (128 MiB of zeros) against a 1 MiB cap stops at the cap.
#guard isLimit (runLengthDecode (tiny (1 <<< 20))
  ⟨(Array.replicate (1 <<< 20) [129, (0 : UInt8)]).toList.flatten.toArray⟩)

end SafePdf.Core.Filter.RunLength
