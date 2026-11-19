import SafePdf.Core.Error
import SafePdf.Core.Limits
import SafePdf.Core.Filter.Predictor

/-!
# LZWDecode (Plan.md §6 Phase 3, task 3.4; §4 S2/S3/S7; ISO 32000-2 §7.4.4)

A total, bounded decoder for the `/LZWDecode` filter.

## Format

* Codes are packed most-significant-bit first, with a variable width of 9 to 12 bits.
* Codes 0–255 stand for single bytes, 256 is *clear-table*, 257 is *EOD*; codes from 258 on
  are table entries, at most 4096 codes in all.
* After every data code except the first one following a clear, the decoder adds the entry
  "previous string + first byte of the current string". The code `next` (the entry being
  added) is legal — the `KwKwK` case — and stands for "previous string + its first byte".
* `/EarlyChange` (Table 9; default 1, else 0): the width is 9 bits while
  `next + earlyChange < 512`, 10 while `< 1024`, 11 while `< 2048`, then 12 (`codeWidth`).
  So with the default, the width grows one code early.

## Behaviour chosen here

* **Missing EOD**: when fewer bits remain than the current width, decoding stops and the
  output so far is returned, in strict and lenient mode alike (as most readers do;
  the trailing bits are the encoder's padding). Bytes after EOD are ignored.
* **Invalid code** (a code above `next`, the `KwKwK` code right after a clear or with a full
  table): strict mode (`strict = true`, the default) gives `Error.malformed` at the code's
  byte offset; lenient mode (`strict = false`, for the repair path) stops there and keeps the
  output so far. An out-of-range `/EarlyChange` is `Error.malformed`.
* **Full table**: once 4096 codes are defined, no entry is added until the next clear (the
  encoder is expected to emit one); the width stays 12.
* **Bombs (S3)**: LZW output grows up to quadratically in the input per table cycle
  (a run of `KwKwK` codes emits 1, 2, 3, … bytes), so every emission is checked against
  `limits.maxDecodedStreamBytes` *before* it is appended; exceeding it is
  `Error.limitExceeded .decodedStreamBytes` in both modes.

## Design

* The table stores, per code `≥ 258`, only `(prefix code, last byte)`: adding an entry is
  O(1), there are no string copies. A code is expanded by walking its prefix chain
  (`expand`, well-founded on the code: every stored prefix is checked to be smaller than its
  entry, so a corrupted table cannot loop). Expansion builds at most 4096 bytes before the
  limit check.
* Output is carried as `Out limit := {b : ByteArray // b.size ≤ limit}` as in Flate, so the
  bound is structural.
* The main loop `loop` recurses structurally on a fuel argument. `lzwDecode` passes
  `input.size * 8 / 9 + 1`, an explicit **work bound** on the number of codes read: every
  code consumes at least 9 bits. `loop_fuel_irrel` proves this fuel is never what stops the
  decoder (more fuel gives the same result).

Proven here:

* `lzwDecode_size_le` — output ≤ `limits.maxDecodedStreamBytes`.
* `loop_fuel_irrel`, `lzwDecode_fuel_enough` — the work bound `input.size * 8 / 9 + 1`
  iterations is sufficient: the result equals the result with any larger fuel.
* `codeWidth_ge`, `codeWidth_le` — widths are 9–12 bits.
* Table invariants: `addEntry_size_le` (at most 4096 codes), `step_wf` (`TableWF`, every
  prefix is a valid code below its own entry, is preserved, together with the validity of
  the previous code), and `expand_ok` (on a well-formed table every valid code expands
  without an internal error, to a non-empty string).

Work (argued from the above, not mechanised as a cost model): at most
`input.size * 8 / 9 + 1` loop iterations; each expands one code in O(length of its string)
steps, and that string is appended to the output, so total work is
O(input.size + limit).
-/

namespace SafePdf.Core.Filter.LZW

open SafePdf

/-! ## Bit reader and widths -/

/-- An output buffer whose size is at most `limit` (Plan.md §4 S3). -/
abbrev Out (limit : Nat) := { b : ByteArray // b.size ≤ limit }

/-- The error for an output that would exceed the limit. -/
def limitErr : Error := .limitExceeded .decodedStreamBytes

/-- The `w`-bit code (`w ≤ 17`) at bit position `pos`, most significant bit first; bytes past
the end read as `0` (the caller checks `pos + w ≤ input.size * 8`). -/
def codeAt (input : ByteArray) (pos w : Nat) : Nat :=
  let i := pos / 8
  let x := ((input[i]?.getD 0).toNat <<< 16) ||| ((input[i + 1]?.getD 0).toNat <<< 8) |||
    (input[i + 2]?.getD 0).toNat
  (x >>> (24 - pos % 8 - w)) &&& ((1 <<< w) - 1)

/-- The code width for the next code read, when the next table entry to be defined is `next`
(ISO 32000-2 §7.4.4.2, `/EarlyChange`). -/
def codeWidth (early : Bool) (next : Nat) : Nat :=
  if next + (if early then 1 else 0) < 512 then 9
  else if next + (if early then 1 else 0) < 1024 then 10
  else if next + (if early then 1 else 0) < 2048 then 11
  else 12

/-- Widths are at least 9 bits (so every code consumes input). -/
theorem codeWidth_ge (early : Bool) (next : Nat) : 9 ≤ codeWidth early next := by
  unfold codeWidth; repeat' split
  all_goals omega

/-- Widths are at most 12 bits. -/
theorem codeWidth_le (early : Bool) (next : Nat) : codeWidth early next ≤ 12 := by
  unfold codeWidth; repeat' split
  all_goals omega

/-! ## Table -/

/-- A table entry for a code `≥ 258`: the string of `pre` followed by `last`. -/
structure Entry where
  /-- The code whose string this entry extends. -/
  pre : Nat
  /-- The final byte. -/
  last : UInt8
  deriving Repr, Inhabited

/-- Maximum number of codes (12 bits). -/
def maxCodes : Nat := 4096

/-- A code is valid for a table whose next free code is `next`: a byte, or a defined entry
(never clear or EOD). -/
def ValidCode (c next : Nat) : Prop := c < 256 ∨ (258 ≤ c ∧ c < next)

/-- The table invariant: entry `i` (code `258 + i`) has a valid prefix below its own code,
and the table holds at most `maxCodes - 258` entries. -/
def TableWF (tab : Array Entry) : Prop :=
  tab.size ≤ maxCodes - 258 ∧ ∀ i (h : i < tab.size), ValidCode tab[i].pre (258 + i)

/-- Add the entry `(p, b)` unless the table is full. -/
def addEntry (tab : Array Entry) (p : Nat) (b : UInt8) : Array Entry :=
  if 258 + tab.size < maxCodes then tab.push ⟨p, b⟩ else tab

/-- The table never holds more than 4096 codes. -/
theorem addEntry_size_le (tab : Array Entry) (p : Nat) (b : UInt8)
    (h : tab.size ≤ maxCodes - 258) : (addEntry tab p b).size ≤ maxCodes - 258 := by
  unfold addEntry maxCodes at *
  split
  · simp only [Array.size_push]; omega
  · omega

/-- The internal error for a corrupted table (unreachable on a well-formed table, see
`expand_ok`). -/
def internalErr : Error := .malformed 0 "lzw: internal: bad table"

/-- Expand code `c`, prepending its bytes to `acc`: walks the prefix chain, which strictly
decreases (checked), so at most `c` steps. -/
def expand (tab : Array Entry) (c : Nat) (acc : List UInt8) : Except Error (List UInt8) :=
  if c < 256 then .ok (c.toUInt8 :: acc)
  else if c < 258 then .error internalErr
  else
    match tab[c - 258]? with
    | none => .error internalErr
    | some e => if e.pre < c then expand tab e.pre (e.last :: acc) else .error internalErr
termination_by c

/-- **Table invariant ⇒ expansion succeeds**: on a well-formed table every valid code
expands, without an internal error, to a non-empty string. -/
theorem expand_ok (tab : Array Entry) (hwf : TableWF tab) (c : Nat) (acc : List UInt8)
    (hc : ValidCode c (258 + tab.size)) : ∃ b rest, expand tab c acc = .ok (b :: rest) := by
  unfold expand
  by_cases h1 : c < 256
  · simp only [h1, ↓reduceIte]; exact ⟨_, _, rfl⟩
  · have h2 : 258 ≤ c ∧ c < 258 + tab.size := by unfold ValidCode at hc; omega
    have h3 : ¬ c < 258 := by omega
    have hi : c - 258 < tab.size := by omega
    have hv := hwf.2 (c - 258) hi
    have hc' : 258 + (c - 258) = c := by omega
    rw [hc'] at hv
    simp only [h1, h3, ↓reduceIte]
    rw [Array.getElem?_eq_getElem hi]
    have hlt : tab[c - 258].pre < c := by unfold ValidCode at hv; omega
    simp only [hlt, ↓reduceIte]
    exact expand_ok tab hwf _ _ (by unfold ValidCode at hv ⊢; omega)
termination_by c

/-! ## Decoder state and one step -/

/-- Decoder state: the table, the previous data code (`none` at the start and after a
clear), and the output so far. -/
structure State (limit : Nat) where
  /-- Entries for codes `258 …`. -/
  tab : Array Entry
  /-- The previous data code. -/
  prev : Option Nat
  /-- Output so far. -/
  out : Out limit

/-- The state invariant: a well-formed table, and a previous code that is valid for it. -/
def State.WF {limit : Nat} (st : State limit) : Prop :=
  TableWF st.tab ∧ ∀ p, st.prev = some p → ValidCode p (258 + st.tab.size)

/-- The result of one step. -/
inductive Action (limit : Nat) where
  /-- EOD seen. -/
  | done
  /-- Continue with this state. -/
  | cont (st : State limit)

/-- Append `s` to `out`, or fail with `limitErr` if that would exceed `limit`. -/
def emit {limit : Nat} (out : Out limit) (s : List UInt8) : Except Error (Out limit) :=
  if h : out.1.size + s.length ≤ limit then
    .ok ⟨out.1 ++ ⟨s.toArray⟩, by
      have hs : (ByteArray.mk s.toArray).size = s.length := by
        simp [ByteArray.size]
      rw [ByteArray.size_append, hs]; exact h⟩
  else .error limitErr

/-- Process one code read at byte offset `off`. -/
def step {limit : Nat} (st : State limit) (code off : Nat) : Except Error (Action limit) :=
  if code = 256 then .ok (.cont { tab := #[], prev := none, out := st.out })
  else if code = 257 then .ok .done
  else
    match st.prev with
    | none =>
      if code < 256 then
        match emit st.out [code.toUInt8] with
        | .error e => .error e
        | .ok out => .ok (.cont { tab := st.tab, prev := some code, out })
      else .error (.malformed off s!"lzw: code {code} after a clear is not a literal")
    | some p =>
      if code < 258 + st.tab.size then
        match expand st.tab code [] with
        | .error e => .error e
        | .ok [] => .error internalErr
        | .ok (b :: rest) =>
          match emit st.out (b :: rest) with
          | .error e => .error e
          | .ok out => .ok (.cont { tab := addEntry st.tab p b, prev := some code, out })
      else if code = 258 + st.tab.size ∧ 258 + st.tab.size < maxCodes then
        match expand st.tab p [] with
        | .error e => .error e
        | .ok [] => .error internalErr
        | .ok (b :: rest) =>
          match emit st.out (b :: rest ++ [b]) with
          | .error e => .error e
          | .ok out => .ok (.cont { tab := addEntry st.tab p b, prev := some code, out })
      else .error (.malformed off s!"lzw: invalid code {code}")

/-- Adding a valid prefix keeps the table well-formed. -/
theorem addEntry_wf (tab : Array Entry) (p : Nat) (b : UInt8) (hwf : TableWF tab)
    (hp : ValidCode p (258 + tab.size)) : TableWF (addEntry tab p b) := by
  unfold addEntry
  split
  · refine ⟨?_, ?_⟩
    · have := hwf.1; unfold maxCodes at *; simp only [Array.size_push]; omega
    · intro i hi
      simp only [Array.size_push] at hi
      by_cases hlt : i < tab.size
      · rw [Array.getElem_push_lt hlt]; exact hwf.2 i hlt
      · have hieq : i = tab.size := by omega
        subst hieq
        rw [Array.getElem_push_eq]; exact hp
  · exact hwf

/-- The table only grows (or stays) under `addEntry`. -/
theorem addEntry_size_ge (tab : Array Entry) (p : Nat) (b : UInt8) :
    tab.size ≤ (addEntry tab p b).size := by
  unfold addEntry; split
  · simp only [Array.size_push]; omega
  · omega

/-- `addEntry` defines code `258 + tab.size` whenever the table is not full. -/
theorem addEntry_size_eq (tab : Array Entry) (p : Nat) (b : UInt8)
    (h : 258 + tab.size < maxCodes) : (addEntry tab p b).size = tab.size + 1 := by
  unfold addEntry; simp only [h, ↓reduceIte, Array.size_push]

/-- **Table invariant preserved**: a step from a well-formed state yields a well-formed
state (valid prefixes below their entries, at most 4096 codes, a valid previous code). -/
theorem step_wf {limit : Nat} (st st' : State limit) (code off : Nat) (hwf : st.WF)
    (h : step st code off = .ok (.cont st')) : st'.WF := by
  unfold step at h
  by_cases h256 : code = 256
  · simp only [h256, ↓reduceIte, Except.ok.injEq, Action.cont.injEq] at h
    subst h
    refine ⟨⟨by unfold maxCodes; simp, fun i hi => by simp at hi⟩, fun p hp => by simp at hp⟩
  simp only [h256, ↓reduceIte] at h
  by_cases h257 : code = 257
  · simp [h257] at h
  simp only [h257, ↓reduceIte] at h
  cases hprev : st.prev with
  | none =>
    simp only [hprev] at h
    by_cases hlt : code < 256
    · simp only [hlt, ↓reduceIte] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq, Action.cont.injEq] at h
        subst h
        refine ⟨hwf.1, fun p hp => ?_⟩
        simp only [Option.some.injEq] at hp
        subst hp; left; exact hlt
    · simp [hlt] at h
  | some p =>
    simp only [hprev] at h
    have hp : ValidCode p (258 + st.tab.size) := hwf.2 p hprev
    by_cases hlt : code < 258 + st.tab.size
    · simp only [hlt, ↓reduceIte] at h
      split at h
      · simp at h
      · simp at h
      · rename_i b rest _
        split at h
        · simp at h
        · simp only [Except.ok.injEq, Action.cont.injEq] at h
          subst h
          refine ⟨addEntry_wf _ _ _ hwf.1 hp, fun q hq => ?_⟩
          simp only [Option.some.injEq] at hq
          subst hq
          have := addEntry_size_ge st.tab p b
          dsimp only; unfold ValidCode; omega
    · simp only [hlt, ↓reduceIte] at h
      by_cases hk : code = 258 + st.tab.size ∧ 258 + st.tab.size < maxCodes
      · simp only [hk, and_self, ↓reduceIte] at h
        split at h
        · simp at h
        · simp at h
        · rename_i b rest _
          split at h
          · simp at h
          · simp only [Except.ok.injEq, Action.cont.injEq] at h
            subst h
            refine ⟨addEntry_wf _ _ _ hwf.1 hp, fun q hq => ?_⟩
            simp only [Option.some.injEq] at hq
            subst hq
            have := addEntry_size_eq st.tab p b hk.2
            dsimp only; unfold ValidCode; omega
      · simp only [hk, ↓reduceIte] at h
        simp at h

/-! ## Main loop -/

/-- The error returned if the fuel runs out (never happens with the fuel `lzwDecode` passes,
see `loop_fuel_irrel`). -/
def fuelErr : Error := .malformed 0 "lzw: internal: out of fuel"

/-- Decode codes from bit position `pos`, at most `fuel` of them. Stops at EOD or when fewer
bits remain than the current width (missing EOD). On an invalid code, `strict` fails and
lenient mode returns the output so far; exceeding the limit always fails. -/
def loop (input : ByteArray) (limit : Nat) (early strict : Bool) :
    Nat → Nat → State limit → Except Error (Out limit)
  | 0, _, _ => .error fuelErr
  | fuel + 1, pos, st =>
    if pos + codeWidth early (258 + st.tab.size) ≤ input.size * 8 then
      match step st (codeAt input pos (codeWidth early (258 + st.tab.size))) (pos / 8) with
      | .ok .done => .ok st.out
      | .ok (.cont st') => loop input limit early strict fuel
          (pos + codeWidth early (258 + st.tab.size)) st'
      | .error e =>
        if strict then .error e
        else match e with
          | .limitExceeded k => .error (.limitExceeded k)
          | _ => .ok st.out
    else .ok st.out

/-- **Work bound is sufficient**: with fuel `f` such that the remaining input bits are fewer
than `9 * f`, adding fuel does not change the result, so the decoder is never stopped by
fuel. -/
theorem loop_fuel_irrel (input : ByteArray) (limit : Nat) (early strict : Bool) :
    ∀ (f k pos : Nat) (st : State limit), input.size * 8 - pos < 9 * f →
      loop input limit early strict f pos st = loop input limit early strict (f + k) pos st := by
  intro f
  induction f with
  | zero => intro k pos st h; omega
  | succ f ih =>
    intro k pos st h
    rw [show f + 1 + k = (f + k) + 1 by omega]
    simp only [loop]
    split
    · rename_i hpos
      have h9 := codeWidth_ge early (258 + st.tab.size)
      split
      · rfl
      · apply ih; omega
      · rfl
    · rfl

/-- The initial state. -/
def init (limit : Nat) : State limit :=
  { tab := #[], prev := none, out := ⟨ByteArray.empty, by simp [ByteArray.size_empty]⟩ }

/-- The initial state is well-formed. -/
theorem init_wf (limit : Nat) : (init limit).WF :=
  ⟨⟨by unfold maxCodes; simp [init], fun i hi => by simp [init] at hi⟩,
    fun p hp => by simp [init] at hp⟩

/-- The number of codes `lzwDecode` reads at most: every code takes at least 9 bits. -/
def workBound (input : ByteArray) : Nat := input.size * 8 / 9 + 1

/-- Decode within `limit`, keeping the output's size proof. -/
def lzwDecodeOut (limit : Nat) (input : ByteArray) (early : Bool := true)
    (strict : Bool := true) : Except Error (Out limit) :=
  loop input limit early strict (workBound input) 0 (init limit)

/-- `/LZWDecode` (ISO 32000-2 §7.4.4): decode `input` with `/EarlyChange` = `early`
(`true` = 1, the default), failing with `Error.limitExceeded .decodedStreamBytes` as soon as
the output would exceed `limits.maxDecodedStreamBytes`. A missing EOD is accepted; invalid
codes are errors when `strict`, otherwise the output so far is returned. -/
def lzwDecode (limits : Limits) (input : ByteArray) (early : Bool := true)
    (strict : Bool := true) : Except Error ByteArray :=
  (lzwDecodeOut limits.maxDecodedStreamBytes input early strict).map (·.1)

/-- **Output bound (S3)**: a successful decode produces at most
`limits.maxDecodedStreamBytes` bytes. -/
theorem lzwDecode_size_le {limits : Limits} {input out : ByteArray} {early strict : Bool}
    (h : lzwDecode limits input early strict = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes := by
  unfold lzwDecode at h
  cases hr : lzwDecodeOut limits.maxDecodedStreamBytes input early strict with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    simp only [hr, Except.map, Except.ok.injEq] at h
    subst h; exact r.2

/-- **Work bound**: `lzwDecode` reads at most `workBound input = input.size * 8 / 9 + 1`
codes (its loop is structural on that fuel), and that fuel is enough: any larger fuel gives
the same result. -/
theorem lzwDecode_fuel_enough (limit : Nat) (input : ByteArray) (early strict : Bool)
    (k : Nat) :
    lzwDecodeOut limit input early strict =
      loop input limit early strict (workBound input + k) 0 (init limit) := by
  unfold lzwDecodeOut workBound
  apply loop_fuel_irrel
  omega

/-! ## Parameters -/

/-- Read `/EarlyChange` from `/DecodeParms` (default 1; only 0 and 1 are legal). -/
def earlyOfDict (d : Dict) : Except Error Bool := do
  let v ← Predictor.getNat d "EarlyChange" 1
  if v = 1 then .ok true
  else if v = 0 then .ok false
  else .error (.malformed 0 s!"/DecodeParms /EarlyChange {v} is not 0 or 1")

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

/-- Test helper: pack codes MSB-first, tracking the table size as the decoder does
(`next` grows after each data code but the first after a clear) to pick each width. -/
private def pack (early : Bool) (codes : List Nat) : ByteArray :=
  let (bits, _, _) := codes.foldl (fun (st : List Bool × Nat × Bool) c =>
    let (bits, next, fresh) := st
    let w := codeWidth early next
    let bits := bits ++ (List.range w).map (fun i => (c >>> (w - 1 - i)) % 2 == 1)
    if c = 256 then (bits, 258, true)
    else if fresh then (bits, next, false)
    else (bits, if next < maxCodes then next + 1 else next, false)) ([], 258, true)
  let padded := bits ++ List.replicate ((8 - bits.length % 8) % 8) false
  let bytes := (List.range (padded.length / 8)).map fun j =>
    ((List.range 8).foldl (fun acc i => acc * 2 + (if padded[8 * j + i]?.getD false then 1 else 0))
      0).toUInt8
  ⟨bytes.toArray⟩

-- ISO 32000-2 §7.4.4.2 example: "-----A---B" (45 = '-', 65 = 'A', 66 = 'B').
#guard okBytes (lzwDecode dl (B [0x80, 0x0B, 0x60, 0x50, 0x22, 0x0C, 0x0C, 0x85, 0x01]))
  [45, 45, 45, 45, 45, 65, 45, 45, 45, 66]
-- The same codes packed by the helper give the same bytes.
#guard (pack true [256, 45, 258, 258, 65, 259, 66, 257]).data.toList ==
  [0x80, 0x0B, 0x60, 0x50, 0x22, 0x0C, 0x0C, 0x85, 0x01]
-- Missing EOD (strict and lenient): the output so far.
#guard okBytes (lzwDecode dl (pack true [45, 258, 258, 65])) [45, 45, 45, 45, 45, 65]
#guard okBytes (lzwDecode dl (B [])) []
-- Clear code in the middle resets the table: after it, 258 is again the first new entry.
#guard okBytes (lzwDecode dl (pack true [65, 66, 258, 256, 67, 67, 258, 257]))
  [65, 66, 65, 66, 67, 67, 67, 67]
-- KwKwK: code = next.
#guard okBytes (lzwDecode dl (pack true [7, 258, 259, 257])) [7, 7, 7, 7, 7, 7]
-- Invalid code (above next): strict error at the code's byte, lenient keeps the output.
#guard malformedAt (lzwDecode dl (pack true [65, 300, 257])) 1
#guard okBytes (lzwDecode dl (pack true [65, 300, 257]) (strict := false)) [65]
-- KwKwK right after a clear is invalid.
#guard malformedAt (lzwDecode dl (pack true [256, 258, 257])) 1
-- EarlyChange 0 vs 1: 254 literals define entries up to 510; the width change to 10 bits
-- comes one code earlier with EarlyChange 1, so each packing decodes only with its own flag.
private def wideCodes : List Nat := (List.range 254).map (· % 256) ++ [511 - 1, 65, 66, 257]
private def wideOut : List UInt8 :=
  ((List.range 254).map (fun i => (i % 256).toUInt8)) ++ [252, 253, 65, 66]
#guard okBytes (lzwDecode dl (pack true wideCodes) (early := true)) wideOut
#guard okBytes (lzwDecode dl (pack false wideCodes) (early := false)) wideOut
#guard !okBytes (lzwDecode dl (pack false wideCodes) (early := true)) wideOut
#guard !okBytes (lzwDecode dl (pack true wideCodes) (early := false)) wideOut
-- Full table cycle round: 4000 literals then EOD, with and without EarlyChange.
private def longCodes : List Nat := (List.range 4000).map (· % 256) ++ [257]
private def longOut : List UInt8 := (List.range 4000).map (fun i => (i % 256).toUInt8)
#guard okBytes (lzwDecode dl (pack true longCodes)) longOut
#guard okBytes (lzwDecode dl (pack false longCodes) (early := false)) longOut
-- /EarlyChange parameter.
#guard (match earlyOfDict [] with | .ok b => b | .error _ => false)
#guard (match earlyOfDict [(Name.ofString "EarlyChange", .int 0)] with
  | .ok b => !b | .error _ => false)
#guard (match earlyOfDict [(Name.ofString "EarlyChange", .int 2)] with
  | .ok _ => false | .error _ => true)
-- Bomb: KwKwK chain 0, 258, 259, … emits 1 + 2 + 3 + … bytes (quadratic): 3800 codes
-- (≈ 5 KiB) would give ≈ 7.2 MB; against a 100 000-byte cap it stops with limitExceeded,
-- in strict and lenient mode.
private def bomb : ByteArray := pack true (0 :: (List.range 3800).map (· + 258) ++ [257])
#guard isLimit (lzwDecode (tiny 100000) bomb)
#guard isLimit (lzwDecode (tiny 100000) bomb (strict := false))
-- A smaller chain fits exactly: 1 + 2 + … + 100 = 5050 bytes.
#guard okBytes (lzwDecode (tiny 5050) (pack true (0 :: (List.range 99).map (· + 258) ++ [257])))
  (List.replicate 5050 0)
#guard isLimit (lzwDecode (tiny 5049) (pack true (0 :: (List.range 99).map (· + 258) ++ [257])))

end SafePdf.Core.Filter.LZW
