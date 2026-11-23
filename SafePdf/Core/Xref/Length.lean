import SafePdf.Core.Xref
import SafePdf.Core.ObjParse

/-!
# Indirect stream `/Length` resolution (Plan.md §5.2, task 2.3)

ISO 32000-2 §7.3.8.2 allows the `/Length` entry of a stream dictionary to be an indirect
reference to an integer object. Resolving it means reading another object, which may itself
need resolution, so a hostile file can make the reader chase references forever. The
classic attack (Bogk & Schöpl 2014, "The Pitfalls of Protocol Design") is a stream whose
`/Length` is a reference to the stream itself, or to an object whose parsing needs the stream.

Plan.md §5.2: "resolve through a resolution function with fuel = number of objects; a
`/Length` that transitively needs its own stream is an error". This module does that,
abstracted over the cross-reference data (a `lookup : Nat → Option XrefEntry`), so it does
not depend on how the xref chain is merged (task 2.2).

## Rules

* L1. `resolveLength lookup limits bytes fuel visiting (n, g)`: if `n ∈ visiting` the result
  is `Error.malformed _ "cyclic /Length"` (checked first, whatever the fuel).
* L2. Fuel `0` is `Error.limitExceeded .objects`. Callers pass the number of objects in the
  cross-reference data; since every hop adds a distinct object number to `visiting`, a chain
  longer than that revisits an object (L1) or misses the table (L3), so the limit only fires
  when a caller passes less fuel than the object count.
* L3. The entry for `n` must be `inUse off g` with the generation of the reference; a missing
  or free entry or a generation mismatch is `malformed`; a `compressed` entry (object stream)
  is `unsupported` until task 2.4.
* L4. The object at `off` is parsed (`n g obj <object> endobj`, header numbers must match the
  reference). An integer `l ≥ 0` is the length; a reference is followed with `fuel - 1` and
  `n` added to `visiting`; anything else (negative integer, other object, a stream) is an
  error.
* L5. `parseIndirectResolved` parses `n g obj …` like `ObjParse.parseIndirect`, but an indirect
  stream `/Length` is resolved by L1–L4 with `visiting = [n]` from the start, so a stream whose
  `/Length` refers to itself is rejected at once. The stream's dictionary is kept as written
  (the `/Length` stays a reference); the data is exactly the resolved number of bytes.
  Header and body are `ObjParse.parseHeader` and `ObjParse.parseIndirectBodyWith` with the
  resolver `lengthOf` (task 2.10), so the framing rules are exactly those of `parseIndirect`.
  The resolver runs after the `stream` keyword's EOL is checked (as `streamLength` does).

## Bounds

* `resolveLength_calls_le`: the number of object parses performed is at most `fuel`.
* `resolveLength_self`: a reference to an object being resolved is an error.
* `parseIndirectResolved_data`: stream data lies within the input.
* `parseIndirectResolved_pos`: progress, `pos < r ≤ bytes.size`.

Everything is pure and total (structural recursion on the fuel).
-/

namespace SafePdf.Core.Xref.Length

open SafePdf
open SafePdf.Core.Xref (XrefEntry)

/-! ## Resolution of an indirect `/Length` -/

/-- The object `n g obj <object> endobj` at `off` (rule L4): the header must name object `n`
generation `g`; a stream object is an error (`endobj` expected). One object parse. -/
def parseLengthObj (limits : Limits) (bytes : ByteArray) (off n g : Nat) :
    Except Error PdfObject :=
  match ObjParse.parseHeader bytes off with
  | .error e => .error e
  | .ok (n', g', q) =>
    if n' = (n : Int) ∧ g' = (g : Int) then
      match ObjParse.parseObject limits bytes q with
      | .error e => .error e
      | .ok (o, r) =>
        match ObjParse.expectKeyword bytes r ObjParse.kwEndobj "expected endobj" with
        | .ok _ => .ok o
        | .error e => .error e
    else .error (.malformed off "object header does not match the cross-reference entry")

/-- Byte offset used in an error about object `n`: its xref offset when in use, else `0`. -/
def errOffset (lookup : Nat → Option XrefEntry) (n : Nat) : Nat :=
  match lookup n with
  | some (.inUse off _) => off
  | _ => 0

/-- Instrumented resolution (rules L1–L4): the number of object parses performed, and the
length or an error. `resolveLength` is its second component; `resolveLength_calls_le` bounds
the first. Structural recursion on `fuel`. -/
def resolveLengthAux (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) : Nat × Except Error Nat :=
  if ref.1 ∈ visiting then (0, .error (.malformed (errOffset lookup ref.1) "cyclic /Length"))
  else
    match fuel with
    | 0 => (0, .error (.limitExceeded .objects))
    | fuel + 1 =>
      match lookup ref.1 with
      | none => (0, .error (.malformed 0 s!"/Length refers to object {ref.1}, not in the xref"))
      | some (.free _ _) => (0, .error (.malformed 0 s!"/Length refers to free object {ref.1}"))
      | some (.compressed _ _) => (0, .error (.unsupported "object in object stream (task 2.4)"))
      | some (.inUse off g') =>
        if g' = ref.2 then
          match parseLengthObj limits bytes off ref.1 ref.2 with
          | .error e => (1, .error e)
          | .ok (.int l) =>
            (1, if 0 ≤ l then .ok l.toNat else .error (.malformed off "negative /Length"))
          | .ok (.ref m h) =>
            let r := resolveLengthAux lookup limits bytes fuel (ref.1 :: visiting) (m, h)
            (r.1 + 1, r.2)
          | .ok _ => (1, .error (.malformed off "/Length is not an integer"))
        else (0, .error (.malformed off "/Length reference generation mismatch"))

/-- **Entry point.** The value of the indirect `/Length` reference `ref` (object number,
generation), following a chain of references at most `fuel` hops (rules L1–L4). Objects in
`visiting` are being resolved: referring to one is a cycle error. Callers pass the number of
objects in the cross-reference data as `fuel`. -/
def resolveLength (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) : Except Error Nat :=
  (resolveLengthAux lookup limits bytes fuel visiting ref).2

/-- The number of object parses `resolveLength` performs on these arguments. -/
def resolveLengthCalls (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) : Nat :=
  (resolveLengthAux lookup limits bytes fuel visiting ref).1

/-! ## Indirect objects with resolved `/Length` -/

/-- The stream dictionary `d` of object `self` with a direct `/Length` for
`ObjParse.parseStreamBody`: unchanged when `/Length` is not a reference; otherwise the
resolved length (with `visiting = [self]`) is put in front, shadowing the reference for
`Dict.lookup`. -/
def lengthDict (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel self : Nat) (d : Dict) : Except Error Dict :=
  match Dict.lookup d ObjParse.nameLength with
  | some (.ref m h) =>
    match resolveLength lookup limits bytes fuel [self] (m, h) with
    | .ok len => .ok ((ObjParse.nameLength, .int len) :: d)
    | .error e => .error e
  | _ => .ok d

/-- The length resolver of rule L5 for object `self`: the stream data length from `d`
(an indirect `/Length` resolved through `lengthDict`, then the direct rule
`ObjParse.streamLength`). Passed to `ObjParse.parseIndirectBodyWith`. -/
def lengthOf (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel self : Nat) : ObjParse.LengthResolver := fun d at_ =>
  match lengthDict lookup limits bytes fuel self d with
  | .error e => .error e
  | .ok d' => ObjParse.streamLength d' at_

/-- **Entry point.** The indirect object `n g obj … endobj` (or stream object) at the next
token at or after `pos`, like `ObjParse.parseIndirect` (same header, `ObjParse.parseHeader`)
but resolving an indirect stream `/Length` through `resolveLength` with fuel `fuel` (the
number of objects) and `visiting = [n]` (rule L5, `lengthOf`). Returns the object and the
position after `endobj`. -/
def parseIndirectResolved (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel pos : Nat) : Except Error (IndirectObject × Nat) :=
  match ObjParse.parseHeader bytes pos with
  | .error e => .error e
  | .ok (n, g, q) =>
    match ObjParse.parseIndirectBodyWith (lengthOf lookup limits bytes fuel n.toNat) limits
        bytes q with
    | .ok (b, r) => .ok (⟨n.toNat, g.toNat, b⟩, r)
    | .error e => .error e

/-! ## Bounds -/

/-- **Bounded work.** Resolving one `/Length` parses at most `fuel` objects. -/
theorem resolveLength_calls_le (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) :
    resolveLengthCalls lookup limits bytes fuel visiting ref ≤ fuel := by
  unfold resolveLengthCalls
  induction fuel generalizing visiting ref with
  | zero =>
    unfold resolveLengthAux
    split <;> simp
  | succ f ih =>
    unfold resolveLengthAux
    split
    · simp
    · simp only
      split
      · simp
      · simp
      · simp
      · split
        · split
          · simp
          · simp
          · rename_i m hh _
            have := ih (ref.1 :: visiting) (m, hh)
            simp only
            omega
          · simp
        · simp

/-- **Cycles are errors.** A `/Length` reference to an object already being resolved fails
with `cyclic /Length`, whatever the fuel. -/
theorem resolveLength_self (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat)
    (h : ref.1 ∈ visiting) :
    resolveLength lookup limits bytes fuel visiting ref =
      .error (.malformed (errOffset lookup ref.1) "cyclic /Length") := by
  unfold resolveLength resolveLengthAux
  simp [h]

/-- A stream whose `/Length` is a reference to the stream object itself is rejected by
`lengthDict` (Bogk's self-referential `/Length`). -/
theorem lengthDict_self (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel self g : Nat) (d : Dict)
    (h : Dict.lookup d ObjParse.nameLength = some (.ref self g)) :
    ∃ e, lengthDict lookup limits bytes fuel self d = .error e := by
  unfold lengthDict
  rw [h]
  simp only
  rw [resolveLength_self lookup limits bytes fuel [self] (self, g) (by simp)]
  exact ⟨_, rfl⟩

/-- **Progress** of `parseIndirectResolved`: the object ends strictly after `pos` and within
the input. -/
theorem parseIndirectResolved_pos {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel pos : Nat} {o : IndirectObject} {r : Nat}
    (h : parseIndirectResolved lookup limits bytes fuel pos = .ok (o, r)) :
    pos < r ∧ r ≤ bytes.size := by
  unfold parseIndirectResolved at h
  split at h
  · simp at h
  · rename_i n g q hq
    have p1 := ObjParse.parseHeader_pos hq
    split at h
    · rename_i b r' hb
      have p2 := ObjParse.parseIndirectBodyWith_ok hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨by omega, p2.2.1⟩
    · simp at h

/-- **Stream data within the file.** On success, a stream's data is the input slice
`[st, st + size)` for some `st > pos` with `st + size ≤ bytes.size`; for an indirect
`/Length` the size is the resolved length. -/
theorem parseIndirectResolved_data {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel pos : Nat} {o : IndirectObject} {r : Nat} {s : Stream}
    (h : parseIndirectResolved lookup limits bytes fuel pos = .ok (o, r))
    (hs : o.body = .stream s) :
    ∃ st, pos < st ∧ st + s.data.size ≤ bytes.size ∧
      s.data = bytes.extract st (st + s.data.size) := by
  unfold parseIndirectResolved at h
  split at h
  · simp at h
  · rename_i n g q hq
    have p1 := ObjParse.parseHeader_pos hq
    split at h
    · rename_i b r' hb
      have p2 := ObjParse.parseIndirectBodyWith_ok hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨st, h1, h2, h3⟩ := p2.2.2 s hs
      exact ⟨st, by omega, h2, h3⟩
    · simp at h

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}:{m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"

/-- Test helper: `parseIndirectResolved` summarised as (num, gen, stream data or none, end). -/
private def pir (lookup : Nat → Option XrefEntry) (b : ByteArray) (fuel pos : Nat) :
    Sum String (Nat × Nat × Option (List UInt8) × Nat) :=
  match parseIndirectResolved lookup Limits.default b fuel pos with
  | .ok (o, r) =>
    match o.body with
    | .stream s => .inr (o.num, o.gen, some s.data.toList, r)
    | .obj _ => .inr (o.num, o.gen, none, r)
  | .error e => .inl (errS e)

/-- Test helper: `resolveLength` summarised. -/
private def rl (lookup : Nat → Option XrefEntry) (b : ByteArray) (fuel : Nat)
    (visiting : List Nat) (ref : Nat × Nat) : Sum String Nat :=
  match resolveLength lookup Limits.default b fuel visiting ref with
  | .ok n => .inr n
  | .error e => .inl (errS e)

/-- Test helper: lookup and object count from the classic xref table at `startxref`. -/
private def tableLookup (b : ByteArray) : (Nat → Option XrefEntry) × Nat :=
  match findStartxref b with
  | .ok off =>
    match parseXrefTable Limits.default b off with
    | .ok (sec, _, _) => (fun n => sec.entries.lookup n, sec.entries.length)
    | .error _ => (fun _ => none, 0)
  | .error _ => (fun _ => none, 0)

/-- Test helper: lookup from an explicit list of entries. -/
private def mkLookup (l : List (Nat × XrefEntry)) : Nat → Option XrefEntry :=
  fun n => l.lookup n

/-- Bytes of `Tests/adversarial/length-self-ref.pdf` (590 B): object 4 is a stream with
`/Length 4 0 R`. -/
private def selfRefPdf : ByteArray := ⟨#[
  37, 80, 68, 70, 45, 49, 46, 55, 10, 37, 226, 227, 207, 211, 10, 49, 32, 48, 32, 111, 98, 106,
  10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103, 32, 47, 80, 97,
  103, 101, 115, 32, 50, 32, 48, 32, 82, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 50,
  32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101,
  115, 32, 47, 75, 105, 100, 115, 32, 91, 51, 32, 48, 32, 82, 93, 32, 47, 67, 111, 117, 110,
  116, 32, 49, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 51, 32, 48, 32, 111, 98, 106,
  10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 32, 47, 80, 97, 114, 101,
  110, 116, 32, 50, 32, 48, 32, 82, 32, 47, 77, 101, 100, 105, 97, 66, 111, 120, 32, 91, 48, 32,
  48, 32, 54, 49, 50, 32, 55, 57, 50, 93, 32, 47, 67, 111, 110, 116, 101, 110, 116, 115, 32, 52,
  32, 48, 32, 82, 32, 47, 82, 101, 115, 111, 117, 114, 99, 101, 115, 32, 60, 60, 32, 47, 70,
  111, 110, 116, 32, 60, 60, 32, 47, 70, 49, 32, 53, 32, 48, 32, 82, 32, 62, 62, 32, 62, 62, 32,
  62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 52, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 32,
  47, 76, 101, 110, 103, 116, 104, 32, 52, 32, 48, 32, 82, 32, 62, 62, 10, 115, 116, 114, 101,
  97, 109, 10, 66, 84, 32, 47, 70, 49, 32, 50, 52, 32, 84, 102, 32, 55, 50, 32, 55, 48, 48, 32,
  84, 100, 32, 40, 72, 101, 108, 108, 111, 41, 32, 84, 106, 32, 69, 84, 10, 101, 110, 100, 115,
  116, 114, 101, 97, 109, 10, 101, 110, 100, 111, 98, 106, 10, 53, 32, 48, 32, 111, 98, 106, 10,
  60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 70, 111, 110, 116, 32, 47, 83, 117, 98, 116, 121,
  112, 101, 32, 47, 84, 121, 112, 101, 49, 32, 47, 66, 97, 115, 101, 70, 111, 110, 116, 32, 47,
  72, 101, 108, 118, 101, 116, 105, 99, 97, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10,
  120, 114, 101, 102, 10, 48, 32, 54, 10, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 32, 54, 53,
  53, 51, 53, 32, 102, 32, 10, 48, 48, 48, 48, 48, 48, 48, 48, 49, 53, 32, 48, 48, 48, 48, 48,
  32, 110, 32, 10, 48, 48, 48, 48, 48, 48, 48, 48, 54, 52, 32, 48, 48, 48, 48, 48, 32, 110, 32,
  10, 48, 48, 48, 48, 48, 48, 48, 49, 50, 49, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48,
  48, 48, 48, 48, 48, 50, 52, 55, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48, 48,
  48, 48, 51, 51, 55, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 116, 114, 97, 105, 108, 101, 114,
  10, 60, 60, 32, 47, 83, 105, 122, 101, 32, 54, 32, 47, 82, 111, 111, 116, 32, 49, 32, 48, 32,
  82, 32, 62, 62, 10, 115, 116, 97, 114, 116, 120, 114, 101, 102, 10, 52, 48, 55, 10, 37, 37,
  69, 79, 70, 10
]⟩

/-- Bytes of `Tests/adversarial/length-mutual.pdf` (550 B): object 4 has `/Length 6 0 R`,
object 6 is in object stream 5, whose `/Length` is `4 0 R`. -/
private def mutualPdf : ByteArray := ⟨#[
  37, 80, 68, 70, 45, 49, 46, 55, 10, 37, 226, 227, 207, 211, 10, 49, 32, 48, 32, 111, 98, 106,
  10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103, 32, 47, 80, 97,
  103, 101, 115, 32, 50, 32, 48, 32, 82, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 50,
  32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101,
  115, 32, 47, 75, 105, 100, 115, 32, 91, 51, 32, 48, 32, 82, 93, 32, 47, 67, 111, 117, 110,
  116, 32, 49, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 51, 32, 48, 32, 111, 98, 106,
  10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 32, 47, 80, 97, 114, 101,
  110, 116, 32, 50, 32, 48, 32, 82, 32, 47, 77, 101, 100, 105, 97, 66, 111, 120, 32, 91, 48, 32,
  48, 32, 54, 49, 50, 32, 55, 57, 50, 93, 32, 47, 67, 111, 110, 116, 101, 110, 116, 115, 32, 52,
  32, 48, 32, 82, 32, 47, 82, 101, 115, 111, 117, 114, 99, 101, 115, 32, 60, 60, 32, 62, 62, 32,
  62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 52, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 32,
  47, 76, 101, 110, 103, 116, 104, 32, 54, 32, 48, 32, 82, 32, 62, 62, 10, 115, 116, 114, 101,
  97, 109, 10, 48, 32, 48, 32, 109, 32, 49, 48, 32, 49, 48, 32, 108, 32, 83, 10, 101, 110, 100,
  115, 116, 114, 101, 97, 109, 10, 101, 110, 100, 111, 98, 106, 10, 53, 32, 48, 32, 111, 98,
  106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 79, 98, 106, 83, 116, 109, 32, 47, 78, 32,
  49, 32, 47, 70, 105, 114, 115, 116, 32, 52, 32, 47, 76, 101, 110, 103, 116, 104, 32, 52, 32,
  48, 32, 82, 32, 62, 62, 10, 115, 116, 114, 101, 97, 109, 10, 54, 32, 48, 32, 49, 53, 10, 101,
  110, 100, 115, 116, 114, 101, 97, 109, 10, 101, 110, 100, 111, 98, 106, 10, 55, 32, 48, 32,
  111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 88, 82, 101, 102, 32, 47, 83,
  105, 122, 101, 32, 56, 32, 47, 87, 32, 91, 49, 32, 52, 32, 50, 93, 32, 47, 82, 111, 111, 116,
  32, 49, 32, 48, 32, 82, 32, 47, 76, 101, 110, 103, 116, 104, 32, 53, 54, 32, 62, 62, 10, 115,
  116, 114, 101, 97, 109, 10, 0, 0, 0, 0, 0, 255, 255, 1, 0, 0, 0, 15, 0, 0, 1, 0, 0, 0, 64, 0,
  0, 1, 0, 0, 0, 121, 0, 0, 1, 0, 0, 0, 225, 0, 0, 1, 0, 0, 1, 38, 0, 0, 2, 0, 0, 0, 5, 0, 0, 1,
  0, 0, 1, 125, 0, 0, 10, 101, 110, 100, 115, 116, 114, 101, 97, 109, 10, 101, 110, 100, 111,
  98, 106, 10, 115, 116, 97, 114, 116, 120, 114, 101, 102, 10, 51, 56, 49, 10, 37, 37, 69, 79,
  70, 10
]⟩

-- length-self-ref.pdf: the classic table has 6 entries; objects 1, 2, 3, 5 parse, object 4
-- (offset 247, `/Length 4 0 R`) is rejected at once as a cycle.
#guard (tableLookup selfRefPdf).2 == 6
#guard (tableLookup selfRefPdf).1 4 == some (.inUse 247 0)
#guard (pir (tableLookup selfRefPdf).1 selfRefPdf 6 247) == .inl "malformed@247:cyclic /Length"
#guard (pir (tableLookup selfRefPdf).1 selfRefPdf 6 15).isRight
#guard (pir (tableLookup selfRefPdf).1 selfRefPdf 6 337).isRight
-- with any fuel, including 0
#guard (pir (tableLookup selfRefPdf).1 selfRefPdf 0 247) == .inl "malformed@247:cyclic /Length"

/-- Lookup for `length-mutual.pdf`, built by hand: its xref is a stream (task 2.4). Offsets are
those `Tests/adversarial/generate.py` (`length_mutual`) wrote: objects 1–5 and the xref stream 7
in use, object 6 at index 0 of object stream 5. -/
private def mutualLookup : Nat → Option XrefEntry :=
  mkLookup [(1, .inUse 15 0), (2, .inUse 64 0), (3, .inUse 121 0), (4, .inUse 225 0),
    (5, .inUse 294 0), (6, .compressed 5 0), (7, .inUse 381 0)]

-- length-mutual.pdf: stream 4 needs object 6 (in object stream 5): unsupported until 2.4.
#guard (pir mutualLookup mutualPdf 8 225) == .inl "unsupported:object in object stream (task 2.4)"
-- object stream 5 needs `4 0 R`, a stream object, not an integer object: rejected where
-- `endobj` was expected (the `stream` keyword of object 4, offset 254).
#guard (pir mutualLookup mutualPdf 8 294) == .inl "malformed@254:expected endobj"
-- the xref stream 7 has a direct /Length and parses.
#guard (pir mutualLookup mutualPdf 8 381).isRight

/-- A stream with `/Length 5 0 R` and `5 0 obj 11 endobj` (one hop). -/
private def oneHopHead : String := "1 0 obj\n<< /Length 5 0 R >>\nstream\nhello world\nendstream\nendobj\n"

/-- `oneHopHead` followed by the length object. -/
private def oneHop : ByteArray := (oneHopHead ++ "5 0 obj 11 endobj\n").toUTF8

/-- Lookup for `oneHop`. -/
private def oneHopLookup : Nat → Option XrefEntry :=
  mkLookup [(1, .inUse 0 0), (5, .inUse oneHopHead.utf8ByteSize 0)]

#guard (pir oneHopLookup oneHop 2 0) ==
  .inr (1, 0, some "hello world".toUTF8.toList, oneHopHead.utf8ByteSize - 1)
#guard rl oneHopLookup oneHop 2 [1] (5, 0) == .inr 11
#guard resolveLengthCalls oneHopLookup Limits.default oneHop 2 [1] (5, 0) == 1
-- the dictionary keeps the reference as written
#guard (match parseIndirectResolved oneHopLookup Limits.default oneHop 2 0 with
  | .ok (⟨_, _, .stream s⟩, _) => s.dict.length == 1
  | _ => false)
-- ObjParse.parseIndirect still rejects the indirect /Length
#guard (match ObjParse.parseIndirect Limits.default oneHop 0 with
  | .error (.unsupported _) => true
  | _ => false)

/-- Two hops: `/Length 5 0 R`, `5 0 obj 6 0 R endobj`, `6 0 obj 11 endobj`. -/
private def twoHopObjs : String := "5 0 obj 6 0 R endobj\n"

/-- `oneHopHead`, then objects 5 and 6. -/
private def twoHop : ByteArray := (oneHopHead ++ twoHopObjs ++ "6 0 obj 11 endobj\n").toUTF8

/-- Lookup for `twoHop`. -/
private def twoHopLookup : Nat → Option XrefEntry :=
  mkLookup [(1, .inUse 0 0), (5, .inUse oneHopHead.utf8ByteSize 0),
    (6, .inUse (oneHopHead.utf8ByteSize + twoHopObjs.utf8ByteSize) 0)]

#guard (pir twoHopLookup twoHop 3 0) ==
  .inr (1, 0, some "hello world".toUTF8.toList, oneHopHead.utf8ByteSize - 1)
#guard resolveLengthCalls twoHopLookup Limits.default twoHop 3 [1] (5, 0) == 2
-- fuel exhaustion: two hops with fuel 1
#guard (pir twoHopLookup twoHop 1 0) == .inl "limit:SafePdf.LimitKind.objects"
#guard resolveLengthCalls twoHopLookup Limits.default twoHop 1 [1] (5, 0) == 1

/-- A cycle between two integer-less objects: `5 0 obj 6 0 R endobj`, `6 0 obj 5 0 R endobj`. -/
private def cyc : ByteArray := (oneHopHead ++ twoHopObjs ++ "6 0 obj 5 0 R endobj\n").toUTF8

#guard (pir twoHopLookup cyc 100 0) == .inl s!"malformed@{oneHopHead.utf8ByteSize}:cyclic /Length"

-- generation mismatch: the reference says generation 1, the entry generation 0
#guard (pir oneHopLookup
  (oneHopHead.replace "5 0 R" "5 1 R" ++ "5 0 obj 11 endobj\n").toUTF8 2 0) ==
  .inl s!"malformed@{oneHopHead.utf8ByteSize}:/Length reference generation mismatch"
-- header mismatch: the entry points at an object with another number
#guard rl (mkLookup [(5, .inUse 0 0)]) oneHop 2 [] (5, 0) ==
  .inl "malformed@0:object header does not match the cross-reference entry"
-- negative, non-integer, free, missing
#guard rl (mkLookup [(5, .inUse 0 0)]) "5 0 obj -3 endobj".toUTF8 1 [] (5, 0) ==
  .inl "malformed@0:negative /Length"
#guard rl (mkLookup [(5, .inUse 0 0)]) "5 0 obj /X endobj".toUTF8 1 [] (5, 0) ==
  .inl "malformed@0:/Length is not an integer"
#guard (rl (mkLookup [(5, .free 0 1)]) oneHop 1 [] (5, 0)).isLeft
#guard (rl (mkLookup []) oneHop 1 [] (5, 0)).isLeft

-- a direct /Length behaves as in ObjParse.parseIndirect
#guard (pir (mkLookup []) "1 0 obj << /Length 2 >> stream\nab\nendstream endobj".toUTF8 0 0) ==
  .inr (1, 0, some [97, 98], 50)
#guard (match ObjParse.parseIndirect Limits.default
    "1 0 obj << /Length 2 >> stream\nab\nendstream endobj".toUTF8 0 with
  | .ok (o, r) => o.num == 1 && r == 50 &&
    (match o.body with
     | .stream s => s.data.toList == [97, 98]
     | .obj _ => false)
  | .error _ => false)

end Tests

end SafePdf.Core.Xref.Length
