import SafePdf.Core.Error
import SafePdf.Core.Limits

/-!
# ASCIIHexDecode and ASCII85Decode (Plan.md §6 Phase 3, task 3.3; §4 S2/S3/S7)

Total, bounded decoders for the two ASCII filters of ISO 32000-2: `/ASCIIHexDecode`
(§7.4.2) and `/ASCII85Decode` (§7.4.3).

## Structure: byte machines

Both filters are *byte machines* (`Machine`): a state, a step function fed one input byte at
a time (with its offset), and an end-of-input function. A step continues (possibly emitting
bytes), stops at the end-of-data marker (emitting bytes; the rest of the input is ignored), or
fails. One machine drives both

* the **specification** `runSpec`, structural recursion over a `List UInt8`, and
* the **implementation** `run`, an index loop over a `ByteArray` (`termination_by`).

Every emission is checked against `limit` *before* it is appended: exceeding it returns
`Error.limitExceeded .decodedStreamBytes` (S3). The theorem `run_spec` states impl ≡ spec
for every machine, including error values; `runSpec_le_limit` gives the limit bound and
`runSpec_law` a weighted output-length law from per-step bounds.

## ASCIIHexDecode (ISO 32000-2 §7.4.2)

* Hex digits `0-9 A-F a-f`; white space (NUL, HT, LF, FF, CR, SP; §7.2.3) is ignored.
* `>` is EOD; the rest of the input is ignored. An odd number of digits before EOD is padded
  with a final `0` digit (§7.4.2).
* Any other byte is `Error.malformed` at its offset.
* **Missing `>`**: strict (`strict = true`, the default) gives `Error.malformed` at the input
  end; lenient (`strict = false`, for the repair path) treats the input end as EOD.
* Laws: `asciiHexDecode_size_le` (≤ limit), `asciiHexDecode_size_le_input`
  (`2 · out ≤ in` strict, `2 · out ≤ in + 1` lenient, i.e. `out ≤ ⌈in/2⌉`).

## ASCII85Decode (ISO 32000-2 §7.4.3)

* Digits `!`..`u` (33–117) are base-85 digits; groups of 5 give 4 bytes (big-endian). A
  group value above `2^32 − 1` is `Error.malformed`.
* `z` (122) stands for 4 zero bytes and is only valid between groups; inside a group it is
  `Error.malformed`.
* White space is ignored everywhere, except between `~` and `>`: EOD is exactly `~>`, and a
  `~` followed by anything else is `Error.malformed`. The rest of the input after `~>` is
  ignored. A leading `<~` is not part of the PDF filter and is rejected (`<` is a digit, and
  the `~` after it is not followed by `>`).
* A final partial group of `k` digits (2 ≤ k ≤ 4) is padded with `u` and gives `k − 1`
  bytes; a final group of one digit is `Error.malformed`.
* **Missing `~>`**: strict gives `Error.malformed`; lenient finishes the pending group as if
  `~>` had been read (a dangling `~` at the end is then accepted too).
* Laws: `ascii85Decode_size_le` (≤ limit), `ascii85Decode_size_le_input` (`out ≤ 4 · in`;
  tight because `z` expands 1 → 4).

## Round trips

`asciiHexDecode_encode` and `ascii85Decode_encode`: for the simple encoders
`asciiHexEncode` (two upper-case digits per byte, then `>`) and `ascii85Encode` (groups of
5 digits, no `z`, standard final partial group, then `~>`), decoding gives back the input
whenever it fits in the limit, in both strict and lenient mode.
-/

namespace SafePdf.Core.Filter.Ascii

open SafePdf

/-- The error for an output that would exceed the limit. -/
def limitErr : Error := .limitExceeded .decodedStreamBytes

/-! ## Byte machines -/

/-- Result of feeding one input byte to a byte machine. -/
inductive Step (σ : Type) where
  /-- Continue in state `s`, appending `emit` to the output. -/
  | cont (s : σ) (emit : List UInt8)
  /-- End of data: append `emit` and stop (the rest of the input is ignored). -/
  | done (emit : List UInt8)
  /-- Malformed input. -/
  | fail (e : Error)

/-- A byte-at-a-time decoder. -/
structure Machine (σ : Type) where
  /-- Initial state. -/
  init : σ
  /-- Feed the byte at offset `pos`. -/
  step : σ → Nat → UInt8 → Step σ
  /-- End of input reached (no end-of-data marker) at offset `pos`: final bytes or error. -/
  eof : σ → Nat → Except Error (List UInt8)

/-- Append a list of bytes. -/
def pushAll (out : ByteArray) : List UInt8 → ByteArray
  | [] => out
  | b :: bs => pushAll (out.push b) bs

/-- **Specification** of a machine run over the list of remaining input bytes, starting at
offset `pos` in state `s` with output so far `acc`; every emission is checked against
`limit` before it is appended. -/
def runSpec {σ : Type} (m : Machine σ) (limit : Nat) :
    List UInt8 → Nat → σ → List UInt8 → Except Error (List UInt8)
  | [], pos, s, acc =>
    match m.eof s pos with
    | .ok e => if acc.length + e.length ≤ limit then .ok (acc ++ e) else .error limitErr
    | .error err => .error err
  | c :: cs, pos, s, acc =>
    match m.step s pos c with
    | .cont s' e =>
      if acc.length + e.length ≤ limit then runSpec m limit cs (pos + 1) s' (acc ++ e)
      else .error limitErr
    | .done e => if acc.length + e.length ≤ limit then .ok (acc ++ e) else .error limitErr
    | .fail err => .error err

/-- **Implementation** of a machine run over a `ByteArray` from index `i`, in state `s`
with output so far `out`. -/
def run {σ : Type} (m : Machine σ) (limit : Nat) (input : ByteArray) (i : Nat) (s : σ)
    (out : ByteArray) : Except Error ByteArray :=
  if h : i < input.size then
    match m.step s i input[i] with
    | .cont s' e =>
      if out.size + e.length ≤ limit then run m limit input (i + 1) s' (pushAll out e)
      else .error limitErr
    | .done e => if out.size + e.length ≤ limit then .ok (pushAll out e) else .error limitErr
    | .fail err => .error err
  else
    match m.eof s i with
    | .ok e => if out.size + e.length ≤ limit then .ok (pushAll out e) else .error limitErr
    | .error err => .error err
termination_by input.size - i

/-- Decode a whole `ByteArray` with machine `m` under output limit `limit`. -/
def decodeWith {σ : Type} (m : Machine σ) (limit : Nat) (input : ByteArray) :
    Except Error ByteArray :=
  run m limit input 0 m.init ByteArray.empty

/-- Specification of `decodeWith` on a list of bytes. -/
def specWith {σ : Type} (m : Machine σ) (limit : Nat) (input : List UInt8) :
    Except Error (List UInt8) :=
  runSpec m limit input 0 m.init []

/-! ### Generic theorems -/

/-- `pushAll` appends. -/
theorem pushAll_toList (out : ByteArray) (l : List UInt8) :
    (pushAll out l).data.toList = out.data.toList ++ l := by
  induction l generalizing out with
  | nil => simp [pushAll]
  | cons b bs ih => simp [pushAll, ih]

/-- **Implementation = specification** for every machine, from any index, including the
error values. -/
theorem run_spec {σ : Type} (m : Machine σ) (limit : Nat) (input : ByteArray) (i : Nat) (s : σ)
    (out : ByteArray) :
    (run m limit input i s out).map (·.data.toList) =
      runSpec m limit (input.data.toList.drop i) i s out.data.toList := by
  fun_induction run m limit input i s out with
  | case1 i s out h s' e hs hle ih =>
    have hlen : i < input.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hlen, runSpec]
    have hc : input.data.toList[i] = input[i] := by simp; rfl
    rw [hc, hs]
    simp only [show out.data.toList.length + e.length ≤ limit by simpa using hle, ↓reduceIte]
    rw [← pushAll_toList]; exact ih
  | case2 i s out h s' e hs hle =>
    have hlen : i < input.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hlen, runSpec]
    have hc : input.data.toList[i] = input[i] := by simp; rfl
    rw [hc, hs]
    simp [hle, Except.map]
  | case3 i s out h e hs hle =>
    have hlen : i < input.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hlen, runSpec]
    have hc : input.data.toList[i] = input[i] := by simp; rfl
    rw [hc, hs]
    simp [hle, Except.map, pushAll_toList]
  | case4 i s out h e hs hle =>
    have hlen : i < input.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hlen, runSpec]
    have hc : input.data.toList[i] = input[i] := by simp; rfl
    rw [hc, hs]
    simp [hle, Except.map]
  | case5 i s out h err hs =>
    have hlen : i < input.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hlen, runSpec]
    have hc : input.data.toList[i] = input[i] := by simp; rfl
    rw [hc, hs]
    rfl
  | case6 i s out h e hs hle =>
    have : input.data.toList.drop i = [] := by simp; omega
    rw [this, runSpec, hs]
    simp [hle, Except.map, pushAll_toList]
  | case7 i s out h e hs hle =>
    have : input.data.toList.drop i = [] := by simp; omega
    rw [this, runSpec, hs]
    simp [hle, Except.map]
  | case8 i s out h err hs =>
    have : input.data.toList.drop i = [] := by simp; omega
    rw [this, runSpec, hs]
    rfl

/-- **Implementation = specification** for whole inputs. -/
theorem decodeWith_spec {σ : Type} (m : Machine σ) (limit : Nat) (input : ByteArray) :
    (decodeWith m limit input).map (·.data.toList) = specWith m limit input.data.toList := by
  have := run_spec m limit input 0 m.init ByteArray.empty
  simpa [decodeWith, specWith] using this

/-- A successful specification run is a successful implementation run with the same bytes. -/
theorem decodeWith_ok_of_spec {σ : Type} (m : Machine σ) (limit : Nat) (input : ByteArray)
    (l : List UInt8) (h : specWith m limit input.data.toList = .ok l) :
    decodeWith m limit input = .ok ⟨l.toArray⟩ := by
  have hs := decodeWith_spec m limit input
  rw [h] at hs
  cases hd : decodeWith m limit input with
  | error e => rw [hd] at hs; cases hs
  | ok b =>
    rw [hd] at hs
    have hb : b.data.toList = l := by cases hs; rfl
    cases b with
    | mk d => cases d; simp_all

/-- One continuing step of the specification. -/
theorem runSpec_cont {σ : Type} (m : Machine σ) (limit : Nat) (c : UInt8) (cs : List UInt8)
    (pos : Nat) (s s' : σ) (acc e : List UInt8) (h : m.step s pos c = .cont s' e)
    (hl : acc.length + e.length ≤ limit) :
    runSpec m limit (c :: cs) pos s acc = runSpec m limit cs (pos + 1) s' (acc ++ e) := by
  rw [runSpec, h]; simp only [hl, ↓reduceIte]

/-- One final step of the specification. -/
theorem runSpec_done {σ : Type} (m : Machine σ) (limit : Nat) (c : UInt8) (cs : List UInt8)
    (pos : Nat) (s : σ) (acc e : List UInt8) (h : m.step s pos c = .done e)
    (hl : acc.length + e.length ≤ limit) :
    runSpec m limit (c :: cs) pos s acc = .ok (acc ++ e) := by
  rw [runSpec, h]; simp only [hl, ↓reduceIte]

/-- The specification never produces more than `limit` bytes. -/
theorem runSpec_le_limit {σ : Type} (m : Machine σ) (limit : Nat) (cs : List UInt8) (pos : Nat)
    (s : σ) (acc l : List UInt8) (h : runSpec m limit cs pos s acc = .ok l) : l.length ≤ limit := by
  induction cs generalizing pos s acc with
  | nil =>
    rw [runSpec] at h
    split at h
    · split at h
      · cases h; simpa using ‹_›
      · cases h
    · cases h
  | cons c cs ih =>
    rw [runSpec] at h
    split at h
    · split at h
      · exact ih _ _ _ h
      · cases h
    · split at h
      · cases h; simpa using ‹_›
      · cases h
    · cases h

/-- **Generic output-length law.** If every step and the end of input satisfy weighted
bounds with potential `φ` (weight `w` per output byte, `K` per input byte, `E` once at the
end of input), then so does the whole run. -/
theorem runSpec_law {σ : Type} (m : Machine σ) (limit w K E : Nat) (φ : σ → Nat)
    (hc : ∀ s pos c s' e, m.step s pos c = .cont s' e → w * e.length + φ s' ≤ φ s + K)
    (hd : ∀ s pos c e, m.step s pos c = .done e → w * e.length ≤ φ s + K)
    (he : ∀ s pos e, m.eof s pos = .ok e → w * e.length ≤ φ s + E)
    (cs : List UInt8) (pos : Nat) (s : σ) (acc l : List UInt8)
    (h : runSpec m limit cs pos s acc = .ok l) :
    w * l.length ≤ w * acc.length + φ s + K * cs.length + E := by
  induction cs generalizing pos s acc with
  | nil =>
    rw [runSpec] at h
    split at h
    · next e he' =>
      split at h
      · cases h
        have := he _ _ _ he'
        simp only [List.length_append, Nat.mul_add]; omega
      · cases h
    · cases h
  | cons c cs ih =>
    rw [runSpec] at h
    split at h
    · next s' e hs =>
      split at h
      · have h1 := ih _ _ _ h
        have h2 := hc _ _ _ _ _ hs
        simp only [List.length_append, Nat.mul_add, List.length_cons, Nat.mul_succ] at h1 ⊢
        omega
      · cases h
    · next e hs =>
      split at h
      · cases h
        have := hd _ _ _ _ hs
        simp only [List.length_append, Nat.mul_add, List.length_cons, Nat.mul_succ]
        omega
      · cases h
    · cases h

/-- The implementation never produces more than `limit` bytes. -/
theorem decodeWith_size_le {σ : Type} (m : Machine σ) (limit : Nat) (input out : ByteArray)
    (h : decodeWith m limit input = .ok out) : out.size ≤ limit := by
  have hs := decodeWith_spec m limit input
  rw [h] at hs
  have := runSpec_le_limit m limit _ _ _ _ _ hs.symm
  simpa using this

/-- The generic output-length law for the implementation. -/
theorem decodeWith_law {σ : Type} (m : Machine σ) (limit w K E : Nat) (φ : σ → Nat)
    (hc : ∀ s pos c s' e, m.step s pos c = .cont s' e → w * e.length + φ s' ≤ φ s + K)
    (hd : ∀ s pos c e, m.step s pos c = .done e → w * e.length ≤ φ s + K)
    (he : ∀ s pos e, m.eof s pos = .ok e → w * e.length ≤ φ s + E)
    (input out : ByteArray) (h : decodeWith m limit input = .ok out) :
    w * out.size ≤ φ m.init + K * input.size + E := by
  have hs := decodeWith_spec m limit input
  rw [h] at hs
  have := runSpec_law m limit w K E φ hc hd he _ _ _ _ _ hs.symm
  simpa using this

/-! ## Shared character classes -/

/-- PDF white space (ISO 32000-2 §7.2.3, Table 1): NUL, HT, LF, FF, CR, SP. -/
def isWhite (c : UInt8) : Bool :=
  c == 0 || c == 9 || c == 10 || c == 12 || c == 13 || c == 32

/-! ## ASCIIHexDecode -/

/-- Value of a hexadecimal digit. -/
def hexVal (c : UInt8) : Option UInt8 :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

/-- Bytes emitted at EOD: a pending high digit is padded with `0`. -/
def hexFlush : Option UInt8 → List UInt8
  | none => []
  | some h => [h * 16]

/-- One ASCIIHex step; the state is the pending high digit. -/
def hexStep (s : Option UInt8) (pos : Nat) (c : UInt8) : Step (Option UInt8) :=
  if c == 62 then .done (hexFlush s)
  else if isWhite c then .cont s []
  else
    match hexVal c with
    | none => .fail (.malformed pos "asciihex: invalid character")
    | some v =>
      match s with
      | none => .cont (some v) []
      | some h => .cont none [h * 16 + v]

/-- The ASCIIHex machine; `strict` decides whether a missing `>` is an error. -/
def hexMachine (strict : Bool) : Machine (Option UInt8) where
  init := none
  step := hexStep
  eof s pos :=
    if strict then .error (.malformed pos "asciihex: missing EOD '>'") else .ok (hexFlush s)

/-- **Specification** of ASCIIHexDecode on a list of bytes. -/
def asciiHexSpec (limit : Nat) (strict : Bool) (input : List UInt8) :
    Except Error (List UInt8) :=
  specWith (hexMachine strict) limit input

/-- **ASCIIHexDecode** (ISO 32000-2 §7.4.2), bounded by `limits.maxDecodedStreamBytes`. -/
def asciiHexDecode (limits : Limits) (input : ByteArray) (strict : Bool := true) :
    Except Error ByteArray :=
  decodeWith (hexMachine strict) limits.maxDecodedStreamBytes input

/-- ASCIIHexDecode implementation = specification. -/
theorem asciiHexDecode_spec (limits : Limits) (input : ByteArray) (strict : Bool) :
    (asciiHexDecode limits input strict).map (·.data.toList) =
      asciiHexSpec limits.maxDecodedStreamBytes strict input.data.toList :=
  decodeWith_spec _ _ _

/-- ASCIIHexDecode output is within the limit. -/
theorem asciiHexDecode_size_le (limits : Limits) (input out : ByteArray) (strict : Bool)
    (h : asciiHexDecode limits input strict = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes :=
  decodeWith_size_le _ _ _ _ h

/-- **ASCIIHex length law**: `2 · out ≤ in` (strict) and `2 · out ≤ in + 1` (lenient). -/
theorem asciiHexDecode_size_le_input (limits : Limits) (input out : ByteArray) (strict : Bool)
    (h : asciiHexDecode limits input strict = .ok out) :
    2 * out.size ≤ input.size + (if strict then 0 else 1) := by
  have := decodeWith_law (hexMachine strict) _ 2 1 (if strict then 0 else 1)
    (fun s => match s with | none => 0 | some _ => 1) ?_ ?_ ?_ input out h
  · simpa [hexMachine] using this
  · intro s pos c s' e hs
    simp only [hexMachine, hexStep] at hs
    split at hs
    · cases hs
    · split at hs
      · cases hs; simp
      · split at hs
        · cases hs
        · split at hs <;> cases hs <;> simp
  · intro s pos c e hs
    simp only [hexMachine, hexStep] at hs
    split at hs
    · cases hs; cases s <;> simp [hexFlush]
    · split at hs
      · cases hs
      · split at hs
        · cases hs
        · split at hs <;> cases hs
  · intro s pos e hs
    simp only [hexMachine] at hs
    cases strict
    · cases hs; cases s <;> simp [hexFlush]
    · cases hs

/-- Upper-case hexadecimal digit for a value below 16. -/
def hexDigit (n : UInt8) : UInt8 := if n < 10 then n + 48 else n + 55

/-- Simple ASCIIHex encoder on lists: two digits per byte, then `>`. -/
def hexEncodeList : List UInt8 → List UInt8
  | [] => [62]
  | b :: bs => hexDigit (b / 16) :: hexDigit (b % 16) :: hexEncodeList bs

/-- Simple ASCIIHex encoder (used for the round-trip theorem and tests). -/
def asciiHexEncode (bs : ByteArray) : ByteArray := ⟨(hexEncodeList bs.data.toList).toArray⟩

set_option maxRecDepth 100000 in
/-- Byte-level facts about the encoder digits, checked for all 256 bytes. -/
theorem hexDigit_facts : ∀ b : UInt8,
    hexVal (hexDigit (b / 16)) = some (b / 16) ∧ hexVal (hexDigit (b % 16)) = some (b % 16) ∧
    isWhite (hexDigit (b / 16)) = false ∧ isWhite (hexDigit (b % 16)) = false ∧
    (hexDigit (b / 16) == 62) = false ∧ (hexDigit (b % 16) == 62) = false ∧
    b / 16 * 16 + b % 16 = b := by decide

/-- Round trip on the specification, generalised over the accumulator. -/
theorem hexSpec_encode (strict : Bool) (limit : Nat) :
    ∀ (bs acc : List UInt8) (pos : Nat), acc.length + bs.length ≤ limit →
      runSpec (hexMachine strict) limit (hexEncodeList bs) pos none acc = .ok (acc ++ bs)
  | [], acc, pos, h => by
    rw [hexEncodeList, runSpec_done _ _ _ _ _ _ _ [] (by simp [hexMachine, hexStep, hexFlush])
      (by simpa using h)]
  | b :: bs, acc, pos, h => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hexDigit_facts b
    rw [hexEncodeList,
      runSpec_cont _ _ _ _ _ _ (some (b / 16)) _ [] (by simp [hexMachine, hexStep, h1, h3, h5])
        (by simp at h ⊢; omega),
      runSpec_cont _ _ _ _ _ _ none _ [b] (by simp [hexMachine, hexStep, h2, h4, h6, h7])
        (by simp at h ⊢; omega),
      hexSpec_encode strict limit bs _ _ (by simp at h ⊢; omega)]
    simp

/-- **ASCIIHex round trip**: decoding the encoding gives the input back (strict or lenient),
whenever it fits in the limit. -/
theorem asciiHexDecode_encode (limits : Limits) (bs : ByteArray) (strict : Bool)
    (h : bs.size ≤ limits.maxDecodedStreamBytes) :
    asciiHexDecode limits (asciiHexEncode bs) strict = .ok bs := by
  have := decodeWith_ok_of_spec (hexMachine strict) limits.maxDecodedStreamBytes
    (asciiHexEncode bs) bs.data.toList
    (by simpa [specWith, hexMachine, asciiHexEncode] using
      hexSpec_encode strict _ bs.data.toList [] 0 (by simpa using h))
  simpa [asciiHexDecode] using this

/-! ## ASCII85Decode -/

/-- ASCII85 state: `cnt` digits (0–4) of the current group read so far, their base-85 value
`val`, and whether a `~` was just read. -/
structure A85 where
  /-- Digits of the current group read so far. -/
  cnt : Nat
  /-- Base-85 value of those digits. -/
  val : Nat
  /-- A `~` was just read (the next byte must be `>`). -/
  tilde : Bool

/-- The four big-endian bytes of a 32-bit value. -/
def bytes4 (v : Nat) : List UInt8 :=
  [(v / 16777216).toUInt8, (v / 65536).toUInt8, (v / 256).toUInt8, v.toUInt8]

/-- Finish at EOD with `cnt` pending digits of value `val`: pad with `u` (84), i.e. the
value becomes `val · 85^(5−cnt) + 85^(5−cnt) − 1`, and keep `cnt − 1` bytes. -/
def a85Finish (cnt val pos : Nat) : Except Error (List UInt8) :=
  if cnt = 0 then .ok []
  else if cnt = 1 then .error (.malformed pos "ascii85: final group of one character")
  else if val * 85 ^ (5 - cnt) + (85 ^ (5 - cnt) - 1) < 4294967296 then
    .ok ((bytes4 (val * 85 ^ (5 - cnt) + (85 ^ (5 - cnt) - 1))).take (cnt - 1))
  else .error (.malformed pos "ascii85: group value exceeds 2^32 - 1")

/-- One ASCII85 step. -/
def a85Step (s : A85) (pos : Nat) (c : UInt8) : Step A85 :=
  if s.tilde then
    if c == 62 then
      match a85Finish s.cnt s.val pos with
      | .ok e => .done e
      | .error err => .fail err
    else .fail (.malformed pos "ascii85: '~' not followed by '>'")
  else if c == 126 then .cont ⟨s.cnt, s.val, true⟩ []
  else if isWhite c then .cont s []
  else if c == 122 then
    if s.cnt = 0 then .cont s [0, 0, 0, 0]
    else .fail (.malformed pos "ascii85: 'z' inside a group")
  else if 33 ≤ c ∧ c ≤ 117 then
    if s.cnt = 4 then
      if s.val * 85 + (c - 33).toNat < 4294967296 then
        .cont ⟨0, 0, false⟩ (bytes4 (s.val * 85 + (c - 33).toNat))
      else .fail (.malformed pos "ascii85: group value exceeds 2^32 - 1")
    else .cont ⟨s.cnt + 1, s.val * 85 + (c - 33).toNat, false⟩ []
  else .fail (.malformed pos "ascii85: invalid character")

/-- The ASCII85 machine; `strict` decides whether a missing `~>` is an error. -/
def a85Machine (strict : Bool) : Machine A85 where
  init := ⟨0, 0, false⟩
  step := a85Step
  eof s pos :=
    if strict then .error (.malformed pos "ascii85: missing EOD '~>'")
    else a85Finish s.cnt s.val pos

/-- **Specification** of ASCII85Decode on a list of bytes. -/
def ascii85Spec (limit : Nat) (strict : Bool) (input : List UInt8) :
    Except Error (List UInt8) :=
  specWith (a85Machine strict) limit input

/-- **ASCII85Decode** (ISO 32000-2 §7.4.3), bounded by `limits.maxDecodedStreamBytes`. -/
def ascii85Decode (limits : Limits) (input : ByteArray) (strict : Bool := true) :
    Except Error ByteArray :=
  decodeWith (a85Machine strict) limits.maxDecodedStreamBytes input

/-- ASCII85Decode implementation = specification. -/
theorem ascii85Decode_spec (limits : Limits) (input : ByteArray) (strict : Bool) :
    (ascii85Decode limits input strict).map (·.data.toList) =
      ascii85Spec limits.maxDecodedStreamBytes strict input.data.toList :=
  decodeWith_spec _ _ _

/-- ASCII85Decode output is within the limit. -/
theorem ascii85Decode_size_le (limits : Limits) (input out : ByteArray) (strict : Bool)
    (h : ascii85Decode limits input strict = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes :=
  decodeWith_size_le _ _ _ _ h

/-- A finished group has at most `cnt − 1` bytes. -/
theorem a85Finish_length (cnt val pos : Nat) (e : List UInt8)
    (h : a85Finish cnt val pos = .ok e) : e.length + 1 ≤ cnt ∨ e = [] := by
  unfold a85Finish at h
  split at h
  · cases h; simp
  · split at h
    · cases h
    · split at h
      · cases h; left; simp [bytes4]; omega
      · cases h

/-- **ASCII85 length law**: `out ≤ 4 · in` (`z` expands 1 → 4, a group 5 → 4). -/
theorem ascii85Decode_size_le_input (limits : Limits) (input out : ByteArray) (strict : Bool)
    (h : ascii85Decode limits input strict = .ok out) :
    out.size ≤ 4 * input.size := by
  have := decodeWith_law (a85Machine strict) _ 1 4 0 (fun s => s.cnt) ?_ ?_ ?_ input out h
  · simpa [a85Machine] using this
  · intro s pos c s' e hs
    simp only [a85Machine, a85Step] at hs
    split at hs
    · split at hs
      · split at hs <;> cases hs
      · cases hs
    · split at hs
      · cases hs; simp
      · split at hs
        · cases hs; simp
        · split at hs
          · split at hs
            · cases hs; simp; omega
            · cases hs
          · split at hs
            · split at hs
              · split at hs
                · cases hs; simp [bytes4]
                · cases hs
              · cases hs; simp
            · cases hs
  · intro s pos c e hs
    simp only [a85Machine, a85Step] at hs
    split at hs
    · split at hs
      · split at hs
        · next e' hf =>
          cases hs
          rcases a85Finish_length _ _ _ _ hf with h1 | h1
          · simp; omega
          · simp [h1]
        · cases hs
      · cases hs
    · split at hs
      · cases hs
      · split at hs
        · cases hs
        · split at hs
          · split at hs <;> cases hs
          · split at hs
            · split at hs
              · split at hs <;> cases hs
              · cases hs
            · cases hs
  · intro s pos e hs
    simp only [a85Machine] at hs
    cases strict
    · rcases a85Finish_length _ _ _ _ hs with h1 | h1
      · simp; omega
      · simp [h1]
    · cases hs

/-- The ASCII85 digit character for a digit value below 85. -/
def ch (d : Nat) : UInt8 := (d + 33).toUInt8

/-- The five digit characters of a value below `85^5`, most significant first. -/
def enc5 (v : Nat) : List UInt8 :=
  [ch (v / 85 / 85 / 85 / 85 % 85), ch (v / 85 / 85 / 85 % 85), ch (v / 85 / 85 % 85),
    ch (v / 85 % 85), ch (v % 85)]

/-- Big-endian 32-bit value of four bytes. -/
def word (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat

/-- Simple ASCII85 encoder on lists: groups of 5 digits (no `z`), the standard final partial
group (`k` bytes padded with zeros, first `k + 1` digits), then `~>`. -/
def a85EncodeList : List UInt8 → List UInt8
  | b0 :: b1 :: b2 :: b3 :: rest => enc5 (word b0 b1 b2 b3) ++ a85EncodeList rest
  | [b0, b1, b2] => (enc5 (word b0 b1 b2 0)).take 4 ++ [126, 62]
  | [b0, b1] => (enc5 (word b0 b1 0 0)).take 3 ++ [126, 62]
  | [b0] => (enc5 (word b0 0 0 0)).take 2 ++ [126, 62]
  | [] => [126, 62]

/-- Simple ASCII85 encoder (used for the round-trip theorem and tests). -/
def ascii85Encode (bs : ByteArray) : ByteArray := ⟨(a85EncodeList bs.data.toList).toArray⟩

set_option maxRecDepth 100000 in
/-- Facts about digit characters, checked for all 256 bytes. -/
theorem digit_facts : ∀ c : UInt8, 33 ≤ c → c ≤ 117 →
    (c == 126) = false ∧ isWhite c = false ∧ (c == 122) = false := by
  decide

/-- Range and value of a digit character. -/
theorem ch_range (d : Nat) (hd : d < 85) :
    33 ≤ ch d ∧ ch d ≤ 117 ∧ (ch d - 33).toNat = d := by
  have hn : (ch d).toNat = d + 33 := by simp [ch]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt8.le_iff_toNat_le, hn]; simp
  · rw [UInt8.le_iff_toNat_le, hn]; simp; omega
  · rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, hn]; simp), hn]; simp

/-- A digit inside a group (specification step). -/
theorem spec_ch (strict : Bool) (limit d cnt val pos : Nat) (cs acc : List UInt8)
    (hd : d < 85) (hc : cnt ≠ 4) (hl : acc.length ≤ limit) :
    runSpec (a85Machine strict) limit (ch d :: cs) pos ⟨cnt, val, false⟩ acc =
      runSpec (a85Machine strict) limit cs (pos + 1) ⟨cnt + 1, val * 85 + d, false⟩ acc := by
  obtain ⟨h1, h2, h3⟩ := ch_range d hd
  obtain ⟨f1, f2, f3⟩ := digit_facts _ h1 h2
  have hs : (a85Machine strict).step ⟨cnt, val, false⟩ pos (ch d) =
      .cont ⟨cnt + 1, val * 85 + d, false⟩ [] := by
    simp [a85Machine, a85Step, f1, f2, f3, h1, h2, h3, hc]
  rw [runSpec_cont _ _ _ _ _ _ _ _ _ hs (by simpa using hl), List.append_nil]

/-- The digit completing a group (specification step). -/
theorem spec_ch4 (strict : Bool) (limit d val pos : Nat) (cs acc : List UInt8)
    (hd : d < 85) (hv : val * 85 + d < 4294967296) (hl : acc.length + 4 ≤ limit) :
    runSpec (a85Machine strict) limit (ch d :: cs) pos ⟨4, val, false⟩ acc =
      runSpec (a85Machine strict) limit cs (pos + 1) ⟨0, 0, false⟩
        (acc ++ bytes4 (val * 85 + d)) := by
  obtain ⟨h1, h2, h3⟩ := ch_range d hd
  obtain ⟨f1, f2, f3⟩ := digit_facts _ h1 h2
  have hs : (a85Machine strict).step ⟨4, val, false⟩ pos (ch d) =
      .cont ⟨0, 0, false⟩ (bytes4 (val * 85 + d)) := by
    simp [a85Machine, a85Step, f1, f2, f3, h1, h2, h3, hv]
  exact runSpec_cont _ _ _ _ _ _ _ _ _ hs (by simpa [bytes4] using hl)

/-- `~` (specification step). -/
theorem spec_tilde (strict : Bool) (limit cnt val pos : Nat) (cs acc : List UInt8)
    (hl : acc.length ≤ limit) :
    runSpec (a85Machine strict) limit (126 :: cs) pos ⟨cnt, val, false⟩ acc =
      runSpec (a85Machine strict) limit cs (pos + 1) ⟨cnt, val, true⟩ acc := by
  have hs : (a85Machine strict).step ⟨cnt, val, false⟩ pos 126 = .cont ⟨cnt, val, true⟩ [] := by
    simp [a85Machine, a85Step]
  rw [runSpec_cont _ _ _ _ _ _ _ _ _ hs (by simpa using hl), List.append_nil]

/-- `>` after `~` (specification step). -/
theorem spec_eod (strict : Bool) (limit cnt val pos : Nat) (cs acc e : List UInt8)
    (hf : a85Finish cnt val pos = .ok e) (hl : acc.length + e.length ≤ limit) :
    runSpec (a85Machine strict) limit (62 :: cs) pos ⟨cnt, val, true⟩ acc = .ok (acc ++ e) := by
  have hs : (a85Machine strict).step ⟨cnt, val, true⟩ pos 62 = .done e := by
    simp [a85Machine, a85Step, hf]
  exact runSpec_done _ _ _ _ _ _ _ _ hs hl

/-- A natural number as a byte, given its value modulo 256. -/
theorem toUInt8_eq (n : Nat) (b : UInt8) (h : n % 256 = b.toNat) : n.toUInt8 = b :=
  UInt8.toNat_inj.mp (by simp; omega)

/-- A byte of `V`, given the range of `V / n`. -/
theorem byte_of_range (V q n : Nat) (b : UInt8) (lo : q * n ≤ V) (hi : V < (q + 1) * n)
    (hq : q % 256 = b.toNat) : (V / n).toUInt8 = b :=
  toUInt8_eq _ _ (by rw [Nat.div_eq_of_lt_le lo hi]; exact hq)

/-- The bytes of a word. -/
theorem bytes4_word (b0 b1 b2 b3 : UInt8) : bytes4 (word b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  simp only [bytes4, word, List.cons.injEq, and_true]
  refine ⟨toUInt8_eq _ _ ?_, toUInt8_eq _ _ ?_, toUInt8_eq _ _ ?_, toUInt8_eq _ _ ?_⟩ <;> omega

/-- A finished partial group, by its padded value `V`. -/
theorem a85Finish_ok (cnt val pos V : Nat) (h2 : 2 ≤ cnt)
    (hV : val * 85 ^ (5 - cnt) + (85 ^ (5 - cnt) - 1) = V) (hlt : V < 4294967296) :
    a85Finish cnt val pos = .ok ((bytes4 V).take (cnt - 1)) := by
  unfold a85Finish
  rw [hV]
  simp only [show cnt ≠ 0 by omega, show cnt ≠ 1 by omega, hlt, ↓reduceIte]

/-- Round trip on the specification, generalised over the accumulator. -/
theorem a85Spec_encode (strict : Bool) (limit : Nat) :
    ∀ (bs acc : List UInt8) (pos : Nat), acc.length + bs.length ≤ limit →
      runSpec (a85Machine strict) limit (a85EncodeList bs) pos ⟨0, 0, false⟩ acc =
        .ok (acc ++ bs)
  | b0 :: b1 :: b2 :: b3 :: rest, acc, pos, h => by
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have hw : word b0 b1 b2 b3 < 4294967296 := by simp only [word]; omega
    generalize hv : word b0 b1 b2 b3 = v at hw
    simp only [List.length_cons] at h
    rw [a85EncodeList, hv, enc5]
    simp only [List.cons_append, List.nil_append]
    have hh : ((((0 * 85 + v / 85 / 85 / 85 / 85 % 85) * 85 + v / 85 / 85 / 85 % 85) * 85 +
        v / 85 / 85 % 85) * 85 + v / 85 % 85) * 85 + v % 85 = v := by omega
    rw [spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_, spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_,
      spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_, spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_,
      spec_ch4 _ _ _ _ _ _ _ ?_ ?_ ?_, hh, ← hv, bytes4_word,
      a85Spec_encode strict limit rest _ _ ?_]
    all_goals first | omega | (simp; omega) | simp
  | [b0, b1, b2], acc, pos, h => by
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt
    have hw' : word b0 b1 b2 0 = b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 := by
      simp [word]
    generalize hv : word b0 b1 b2 0 = v at hw'
    simp only [List.length_cons, List.length_nil] at h
    rw [a85EncodeList, hv, enc5]
    simp only [List.take, List.cons_append, List.nil_append]
    have hval : (((0 * 85 + v / 85 / 85 / 85 / 85 % 85) * 85 + v / 85 / 85 / 85 % 85) * 85 +
        v / 85 / 85 % 85) * 85 + v / 85 % 85 = v / 85 := by omega
    have hf : a85Finish (0 + 1 + 1 + 1 + 1) (v / 85) (pos + 1 + 1 + 1 + 1 + 1) =
        .ok [b0, b1, b2] := by
      have hk : v ≤ v / 85 * 85 + 84 ∧ v / 85 * 85 + 84 ≤ v + 84 := by omega
      generalize hV : v / 85 * 85 + 84 = V at hk
      rw [a85Finish_ok _ (v / 85) _ V (by omega) (by simp [← hV]) (by omega)]
      rw [show (bytes4 V).take (0 + 1 + 1 + 1 + 1 - 1) =
        [(V / 16777216).toUInt8, (V / 65536).toUInt8, (V / 256).toUInt8] from rfl]
      simp only [Except.ok.injEq, List.cons.injEq, and_true]
      exact ⟨byte_of_range V b0.toNat _ _ (by omega) (by omega) (by omega),
        byte_of_range V (b0.toNat * 256 + b1.toNat) _ _ (by omega) (by omega) (by omega),
        byte_of_range V (b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) _ _ (by omega) (by omega)
          (by omega)⟩
    rw [spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_, spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_,
      spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_, spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_,
      spec_tilde _ _ _ _ _ _ _ ?_, hval, spec_eod _ _ _ _ _ _ _ _ hf ?_]
    all_goals first | omega | (simp; omega) | simp
  | [b0, b1], acc, pos, h => by
    have := b0.toNat_lt; have := b1.toNat_lt
    have hw' : word b0 b1 0 0 = b0.toNat * 16777216 + b1.toNat * 65536 := by simp [word]
    generalize hv : word b0 b1 0 0 = v at hw'
    simp only [List.length_cons, List.length_nil] at h
    rw [a85EncodeList, hv, enc5]
    simp only [List.take, List.cons_append, List.nil_append]
    have hval : ((0 * 85 + v / 85 / 85 / 85 / 85 % 85) * 85 + v / 85 / 85 / 85 % 85) * 85 +
        v / 85 / 85 % 85 = v / 85 / 85 := by omega
    have hf : a85Finish (0 + 1 + 1 + 1) (v / 85 / 85) (pos + 1 + 1 + 1 + 1) = .ok [b0, b1] := by
      have hk : v ≤ v / 85 / 85 * 7225 + 7224 ∧ v / 85 / 85 * 7225 + 7224 ≤ v + 7224 := by omega
      generalize hV : v / 85 / 85 * 7225 + 7224 = V at hk
      rw [a85Finish_ok _ (v / 85 / 85) _ V (by omega) (by simp [← hV]) (by omega)]
      rw [show (bytes4 V).take (0 + 1 + 1 + 1 - 1) =
        [(V / 16777216).toUInt8, (V / 65536).toUInt8] from rfl]
      simp only [Except.ok.injEq, List.cons.injEq, and_true]
      exact ⟨byte_of_range V b0.toNat _ _ (by omega) (by omega) (by omega),
        byte_of_range V (b0.toNat * 256 + b1.toNat) _ _ (by omega) (by omega) (by omega)⟩
    rw [spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_, spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_,
      spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_, spec_tilde _ _ _ _ _ _ _ ?_, hval,
      spec_eod _ _ _ _ _ _ _ _ hf ?_]
    all_goals first | omega | (simp; omega) | simp
  | [b0], acc, pos, h => by
    have := b0.toNat_lt
    have hw' : word b0 0 0 0 = b0.toNat * 16777216 := by simp [word]
    generalize hv : word b0 0 0 0 = v at hw'
    simp only [List.length_cons, List.length_nil] at h
    rw [a85EncodeList, hv, enc5]
    simp only [List.take, List.cons_append, List.nil_append]
    have hval : (0 * 85 + v / 85 / 85 / 85 / 85 % 85) * 85 + v / 85 / 85 / 85 % 85 =
        v / 85 / 85 / 85 := by omega
    have hf : a85Finish (0 + 1 + 1) (v / 85 / 85 / 85) (pos + 1 + 1 + 1) = .ok [b0] := by
      have hk : v ≤ v / 85 / 85 / 85 * 614125 + 614124 ∧
          v / 85 / 85 / 85 * 614125 + 614124 ≤ v + 614124 := by omega
      generalize hV : v / 85 / 85 / 85 * 614125 + 614124 = V at hk
      rw [a85Finish_ok _ (v / 85 / 85 / 85) _ V (by omega) (by simp [← hV]) (by omega)]
      rw [show (bytes4 V).take (0 + 1 + 1 - 1) = [(V / 16777216).toUInt8] from rfl]
      simp only [Except.ok.injEq, List.cons.injEq, and_true]
      exact byte_of_range V b0.toNat _ _ (by omega) (by omega) (by omega)
    rw [spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_, spec_ch _ _ _ _ _ _ _ _ ?_ ?_ ?_,
      spec_tilde _ _ _ _ _ _ _ ?_, hval, spec_eod _ _ _ _ _ _ _ _ hf ?_]
    all_goals first | omega | (simp; omega) | simp
  | [], acc, pos, h => by
    simp only [List.length_nil] at h
    rw [a85EncodeList, spec_tilde _ _ _ _ _ _ _ (by omega),
      spec_eod _ _ _ _ _ _ _ [] (by simp [a85Finish]) (by simpa using h)]

/-- **ASCII85 round trip**: decoding the encoding gives the input back (strict or lenient),
whenever it fits in the limit. -/
theorem ascii85Decode_encode (limits : Limits) (bs : ByteArray) (strict : Bool)
    (h : bs.size ≤ limits.maxDecodedStreamBytes) :
    ascii85Decode limits (ascii85Encode bs) strict = .ok bs := by
  have := decodeWith_ok_of_spec (a85Machine strict) limits.maxDecodedStreamBytes
    (ascii85Encode bs) bs.data.toList
    (by simpa [specWith, a85Machine, ascii85Encode] using
      a85Spec_encode strict _ bs.data.toList [] 0 (by simpa using h))
  simpa [ascii85Decode] using this

/-! ## Tests

ASCII85 vectors were produced with Python's `base64.a85encode` (standard library). -/

/-- Success with exactly the bytes of this string. -/
private def okStr (r : Except Error ByteArray) (expected : String) : Bool :=
  match r with
  | .ok o => o.data == expected.toUTF8.data
  | .error _ => false

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

/-- Default limits. -/
private def dl : Limits := {}

/-- Limits with a tiny per-stream output cap. -/
private def tiny (n : Nat) : Limits := { maxDecodedStreamBytes := n }

-- ASCIIHexDecode
#guard okStr (asciiHexDecode dl "48656C6C6F>".toUTF8) "Hello"
#guard okStr (asciiHexDecode dl "48 65\n6c\t6C\r6f\x0c>".toUTF8) "Hello"
#guard okBytes (asciiHexDecode dl "7>".toUTF8) [0x70]
#guard okBytes (asciiHexDecode dl ">".toUTF8) []
#guard okBytes (asciiHexDecode dl "486>garbage after EOD".toUTF8) [0x48, 0x60]
#guard malformedAt (asciiHexDecode dl "4G>".toUTF8) 1
#guard malformedAt (asciiHexDecode dl "4848".toUTF8) 4
#guard okBytes (asciiHexDecode dl "484".toUTF8 (strict := false)) [0x48, 0x40]
#guard isLimit (asciiHexDecode (tiny 1) "4848>".toUTF8)
#guard okBytes (asciiHexDecode (tiny 1) "48>".toUTF8) [0x48]
#guard okStr (asciiHexDecode dl (asciiHexEncode "round trip \x00\xff".toUTF8)) "round trip \x00\xff"

-- ASCII85Decode
#guard okStr (ascii85Decode dl "87cURD_*#TDfTZ)+T~>".toUTF8) "Hello, world!"
#guard okStr (ascii85Decode dl "87cUR D_*#T\nDfTZ)\r+T~>".toUTF8) "Hello, world!"
#guard okBytes (ascii85Decode dl "z@:E^~>".toUTF8) [0, 0, 0, 0, 97, 98, 99]
#guard okStr (ascii85Decode dl "5l~>".toUTF8) "A"
#guard okStr (ascii85Decode dl "5sb~>".toUTF8) "AB"
#guard okStr (ascii85Decode dl "5sdp~>".toUTF8) "ABC"
#guard okBytes (ascii85Decode dl "s8W-!~>".toUTF8) [255, 255, 255, 255]
#guard okBytes (ascii85Decode dl "~>".toUTF8) []
#guard okBytes (ascii85Decode dl "5l~>trailing".toUTF8) [65]
#guard malformedAt (ascii85Decode dl "s8W-\"~>".toUTF8) 4
#guard malformedAt (ascii85Decode dl "5~>".toUTF8) 2
#guard malformedAt (ascii85Decode dl "5z~>".toUTF8) 1
#guard malformedAt (ascii85Decode dl "5l~ >".toUTF8) 3
#guard malformedAt (ascii85Decode dl "5lv~>".toUTF8) 2
#guard malformedAt (ascii85Decode dl "<~5l~>".toUTF8) 2
#guard malformedAt (ascii85Decode dl "5sb".toUTF8) 3
#guard okStr (ascii85Decode dl "5sb".toUTF8 (strict := false)) "AB"
#guard okStr (ascii85Decode dl "5sb~".toUTF8 (strict := false)) "AB"
#guard isLimit (ascii85Decode (tiny 8) "zzz~>".toUTF8)
#guard okBytes (ascii85Decode (tiny 8) "zz~>".toUTF8) [0, 0, 0, 0, 0, 0, 0, 0]
#guard okStr (ascii85Decode dl (ascii85Encode "Hello, world!".toUTF8)) "Hello, world!"
#guard okStr (ascii85Decode dl (ascii85Encode "\x00\x00\x00\x00\xff\xfe".toUTF8))
  "\x00\x00\x00\x00\xff\xfe"
-- Bomb: 4 MiB of `z` (16 MiB of zeros) against a 1 MiB cap stops at the cap.
#guard isLimit (ascii85Decode (tiny (1 <<< 20))
  (ByteArray.mk ((Array.replicate (1 <<< 22) (122 : UInt8)).push 126 |>.push 62)))

end SafePdf.Core.Filter.Ascii
