import SafePdf.Core.Xref
import SafePdf.Core.Xref.ObjStmDecode
import SafePdf.Core.ObjParse
import SafePdf.Core.Lex
import SafePdf.Core.Filter.Structural

/-!
# Indirect stream `/Length` resolution (Plan.md §5.2, tasks 2.3, 2.14)

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

* L1. `resolveLength pre lookup limits bytes fuel visiting (n, g)`: if `n ∈ visiting` the result
  is `Error.cycle _ "cyclic /Length"` (checked first, whatever the fuel; task 2.13 made it a
  `cycle` rather than `malformed`, so `Core.Open.openFile` does not try repair on it).
* L2. Fuel `0` is `Error.limitExceeded .objects`. The fuel is a budget of object parses
  (length objects and object-stream containers) for the whole resolution. Callers pass the
  number of objects in the cross-reference data; along a chain of `inUse` objects every hop
  adds a distinct object number to `visiting`, so a chain longer than that revisits an object
  (L1) or misses the table (L3). Through object streams (L6) the budget is shared between the
  container's `/Length` and the member's value, so pathological files that need the same
  objects on both paths can run out of budget (`limitExceeded`, never unbounded work).
* L3. The entry for `n` must be `inUse off g` with the generation of the reference, or
  `compressed c idx` (L6); a missing or free entry or a generation mismatch is `malformed`.
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
* L6. (Task 2.14.) `n` is `compressed c idx` (ISO 32000-2 §7.5.7): if `c = n` or `c` is in
  `visiting` the result is `Error.cycle` (an object stream whose decoding needs itself). The
  entry of `c` must be `inUse off 0` (as in `ObjStm.fetchCompressed`: a compressed container
  is an error, `Error.cycle` when it lies in `n` or in an object being resolved). The head of
  `c` is parsed (`parseContainerHead`: `c 0 obj << … >> stream`, one parse); the container's
  own `/Length`, if a reference, is resolved recursively with `c` and `n` added to
  `visiting` (`containerLength`), so a `/Length` cycle through the object stream, such as
  `length-mutual.pdf` (stream 4 → object 6 in object stream 5 → `/Length 4 0 R`), is an
  `Error.cycle`. Then the body, `ObjStm.decodeObjStm`, `ObjStm.findObject` (must be `idx`)
  and `ObjStm.getObject` (`containerMember`); the member is then treated as in L4, a
  reference being followed with the budget left over and `n` added to `visiting`.
  (Task 4.6.) Between the body and `decodeObjStm` the container passes through the pre-pass
  `pre` (`ObjStm.Pre`, rule O7 of `Core.Xref.ObjStm`): `Core.Open` passes the decryption of
  an encrypted file's object streams (`OpenDoc.pre`), so a `/Length` stored in an object
  stream of an encrypted file resolves; `Pre.id` otherwise. Every resolver function takes
  `pre`; `parseIndirectResolved` takes it as an optional last argument (default `Pre.id`,
  for the repair scan and the raw inspector views, which have no decryption state). The
  pass performs no object parse, so the bounds below hold for every `pre`.

Module structure: `ObjStm.lean` imports this module (its containers may have an indirect
`/Length`), so the decoding of object streams lives in `Core.Xref.ObjStmDecode`, which both
import (task 2.14).

## Bounds

* `resolveLength_calls_le`: the number of object parses performed is at most `fuel` (strong
  induction on the fuel; the second recursive call of L6 gets `fuel - used`).
* `resolveLength_self`: a reference to an object being resolved is an error.
* `resolveLength_container_cycle`: with non-zero fuel, an object in an object stream that is
  being resolved (or in itself) is a cycle error.
* `parseIndirectResolved_data`: stream data lies within the input.
* `parseIndirectResolved_pos`: progress, `pos < r ≤ bytes.size`.

## Budgeted resolution (task 4.5, Plan.md §4 S3)

* L7. `resolveLengthAuxB`, `lengthOfB`, `parseIndirectResolvedB` are the functions above with a
  `Filter.Budget` threaded through: every object stream decoded by rule L6 (including those
  needed for a container's own `/Length`) is charged by `ObjStm.decodeObjStmB` (defined here,
  `ObjStm` imports this module). Rules L1–L6 are unchanged. Nothing is cached: each
  resolution that needs a container decodes (and pays for) it again.
* Bounds restated over the budgeted resolver: `resolveLengthB_calls_le` (at most `fuel`
  parses), `resolveLengthB_self`, `resolveLengthB_container_cycle`, `containerLengthB_calls_le`;
  `resolveLengthB_le` (the budget never grows), `resolveLengthB_cost` (at most one
  `allowance` per parse, so `fuel · allowance`), `ObjStm.decodeObjStmB_charge` (a decoded
  container is charged at least its bytes).
* `resolveLengthB_eq`, `lengthOfB_eq`, `parseIndirectResolvedB_eq`: **a-posteriori
  equality** — if at least one `allowance` is left after the budgeted call, it returned
  exactly what the unbudgeted call returns (the budget only decreases, so every decode on the
  way ran with an allowance left, where `decodeObjStmB` is `decodeObjStm`).
* `parseIndirectWith`, `callPoint`, `parseIndirectWith_congr`: the object parse is generic in
  its length resolver, which is called at most once, at `callPoint`; so
  `parseIndirectResolvedB` resolves the length there first and then parses with it
  (`parseIndirectResolvedB_with`, `_pos`, `_data`).

Everything is pure and total (well-founded recursion on the fuel, `termination_by fuel`).
-/
namespace SafePdf.Core.Xref.ObjStm

open SafePdf
open SafePdf.Core.Filter (Budget)

/-! ## Budgeted object-stream decoding (task 3.13)

`decodeObjStmB` is `decodeObjStm` with its decode charged against the document budget
(`Filter.decodeBytesB`). It lives here (it was in `Core.Xref.ObjStm` until task 4.5) so that
the budgeted `/Length` resolver below (rule L6) can charge the object streams it decodes;
`Core.Xref.ObjStm` imports this module. Names are unchanged. -/

/-- `decodeObjStm` with the budget: the decode is `Filter.decodeBytesB` (rules O1–O4). -/
def decodeObjStmB (limits : Limits) (budget : Budget) (st : Stream) :
    (Except Error ObjStm) × Budget :=
  match checkType st.dict, getCount limits st.dict, getFirst st.dict, getExtends st.dict with
  | .ok (), .ok n, .ok first, .ok ext =>
    let p := Filter.decodeBytesB limits budget st.dict st.data
      (.malformed 0 "object stream: image filter")
    (match p.1 with
     | .error e => .error e
     | .ok data =>
       if first ≤ data.size then
         match parsePairs (data.extract 0 first) n 0 [] with
         | .error e => .error e
         | .ok entries => mkObjStm first ext data entries
       else .error (.malformed 0 "object stream: /First beyond the decoded data"), p.2)
  | .error e, _, _, _ => (.error e, budget)
  | _, .error e, _, _ => (.error e, budget)
  | _, _, .error e, _ => (.error e, budget)
  | _, _, _, .error e => (.error e, budget)

/-- `decodeObjStmB` never increases the budget. -/
theorem decodeObjStmB_le (limits : Limits) (budget : Budget) (st : Stream) :
    (decodeObjStmB limits budget st).2.remaining ≤ budget.remaining := by
  unfold decodeObjStmB
  split
  · exact Filter.decodeBytesB_le limits budget st.dict st.data
      (.malformed 0 "object stream: image filter") true
  all_goals exact Nat.le_refl _

/-- Cost of `decodeObjStmB`: at most one structural decode. -/
theorem decodeObjStmB_cost (limits : Limits) (budget : Budget) (st : Stream) :
    budget.remaining ≤ (decodeObjStmB limits budget st).2.remaining +
      (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + st.data.size) := by
  unfold decodeObjStmB
  split
  · exact Filter.decodeBytesB_cost limits budget st.dict st.data
      (.malformed 0 "object stream: image filter") true
  all_goals exact Nat.le_add_right _ _

/-- Budget large enough ⇒ `decodeObjStmB` returns what `decodeObjStm` returns. -/
theorem decodeObjStmB_eq {limits : Limits} {budget : Budget} {st : Stream}
    (h : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + st.data.size) ≤
      budget.remaining) :
    (decodeObjStmB limits budget st).1 = decodeObjStm limits st := by
  unfold decodeObjStmB decodeObjStm decodeData
  cases h1 : checkType st.dict <;> cases h2 : getCount limits st.dict <;>
    cases h3 : getFirst st.dict <;> cases h4 : getExtends st.dict <;> simp only
  rw [Filter.decodeBytesB_eq h]
  generalize Filter.decodeBytes limits st.dict st.data _ = x
  cases x <;> rfl

/-- `mkObjStm` keeps the data it was given. -/
theorem mkObjStm_data {first : Nat} {ext : Option (Nat × Nat)} {data : ByteArray}
    {entries : List (Nat × Nat)} {os : ObjStm} (h : mkObjStm first ext data entries = .ok os) :
    os.data = data := by
  unfold mkObjStm at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- **Charge law** of `decodeObjStmB` (task 4.5): a decoded object stream's data plus the
budget left are at most the budget before (its bytes were charged). -/
theorem decodeObjStmB_charge {limits : Limits} {budget : Budget} {st : Stream} {os : ObjStm}
    (h : (decodeObjStmB limits budget st).1 = .ok os) :
    os.data.size + (decodeObjStmB limits budget st).2.remaining ≤ budget.remaining := by
  unfold decodeObjStmB at h ⊢
  split at h
  · simp only at h ⊢
    generalize hp : Filter.decodeBytesB limits budget st.dict st.data
      (.malformed 0 "object stream: image filter") = p at h ⊢
    rcases p with ⟨r, b⟩
    rcases r with e | data
    · cases h
    · simp only at h ⊢
      have hc := Filter.decodeBytesB_charge (limits := limits) (budget := budget) (d := st.dict)
        (raw := st.data) (imageErr := .malformed 0 "object stream: image filter")
        (strict := true) (out := data) (by rw [hp])
      rw [hp] at hc
      simp only at hc
      split at h
      · split at h
        · cases h
        · rw [mkObjStm_data h]; exact hc
      · cases h
  all_goals cases h

end SafePdf.Core.Xref.ObjStm

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

/-- The length denoted by the integer `l` found at `off` (rule L4): `l ≥ 0`, else an error. -/
def intLength (off : Nat) (l : Int) : Except Error Nat :=
  if 0 ≤ l then .ok l.toNat else .error (.malformed off "negative /Length")

/-- The head of object-stream container `c` at `off` (rule L6): `c 0 obj`, a dictionary, and
the `stream` keyword. Returns the dictionary and the position after `stream`. One object
parse; the framing is that of `ObjParse.parseIndirectBodyWith`. -/
def parseContainerHead (limits : Limits) (bytes : ByteArray) (off c : Nat) :
    Except Error (Dict × Nat) :=
  match ObjParse.parseHeader bytes off with
  | .error e => .error e
  | .ok (n', g', q) =>
    if n' = (c : Int) ∧ g' = 0 then
      match ObjParse.parseObject limits bytes q with
      | .error e => .error e
      | .ok (o, r) =>
        match Lex.next bytes r with
        | .error e => .error (ObjParse.lexErr e)
        | .ok (some (.keyword k, r2)) =>
          if k = ObjParse.kwStream then
            match o with
            | .dict d => .ok (d, r2)
            | _ => .error (ObjParse.errAt bytes r "stream without a dictionary")
          else .error (.malformed off "object stream container is not a stream")
        | .ok _ => .error (.malformed off "object stream container is not a stream")
    else .error (.malformed off "object header does not match the cross-reference entry")

/-- The container's own data length (rule L6): a reference `/Length` is resolved by `res`
(the recursive resolver, with the visiting list `vis`), anything else by the direct rule
`ObjParse.streamLength` (no object parse). -/
def containerLength (res : List Nat → Nat × Nat → Nat × Except Error Nat) (vis : List Nat)
    (d : Dict) (p : Nat) : Nat × Except Error Nat :=
  match Dict.lookup d ObjParse.nameLength with
  | some (.ref m h) => res vis (m, h)
  | _ => (0, ObjParse.streamLength d p)

/-- Member `num` (index `idx`) of the object-stream container whose head was read at `off`
(dictionary `d`, `stream` keyword ending at `p`) with data length `len` (rule L6): the stream
body, the container pre-pass `pre` (decryption of an encrypted file's container, task 4.6),
`ObjStm.decodeObjStm`, the header index check `ObjStm.findObject`, `ObjStm.getObject`.
Not recursive. -/
def containerMember (pre : ObjStm.Pre) (limits : Limits) (bytes : ByteArray)
    (off c num idx : Nat) (d : Dict) (p : Nat) (len : Except Error Nat) :
    Except Error PdfObject :=
  match len with
  | .error e => .error e
  | .ok len =>
    match ObjParse.parseStreamBodyWith (fun _ _ => .ok len) bytes p d with
    | .error e => .error e
    | .ok (st0, _) =>
      match pre.f c st0 with
      | .error e => .error e
      | .ok st =>
        match ObjStm.decodeObjStm limits st with
        | .error e => .error e
        | .ok os =>
          if ObjStm.findObject os num = some idx then ObjStm.getObject os limits idx
          else .error (.malformed off s!"object {num} is not at index {idx} of object stream {c}")

/-- Instrumented resolution (rules L1–L4, L6): the number of object parses performed, and the
length or an error. `resolveLength` is its second component; `resolveLength_calls_le` bounds
the first by `fuel`. The fuel is a work budget: a hop through an object stream makes two
recursive calls (the container's `/Length`, then the member's value if it is a reference),
and the second gets what the first left (`fuel - used`), so the total stays below `fuel`.
Well-founded recursion on `fuel`. -/
def resolveLengthAux (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) :
    Nat × Except Error Nat :=
  if ref.1 ∈ visiting then (0, .error (.cycle (errOffset lookup ref.1) "cyclic /Length"))
  else
    match fuel with
    | 0 => (0, .error (.limitExceeded .objects))
    | fuel + 1 =>
      match lookup ref.1 with
      | none => (0, .error (.malformed 0 s!"/Length refers to object {ref.1}, not in the xref"))
      | some (.free _ _) => (0, .error (.malformed 0 s!"/Length refers to free object {ref.1}"))
      | some (.compressed c idx) =>
        if c = ref.1 ∨ c ∈ visiting then
          (0, .error (.cycle (errOffset lookup c)
            s!"cyclic /Length through object stream {c}"))
        else
          match lookup c with
          | some (.inUse off g) =>
            if g = 0 then
              match parseContainerHead limits bytes off c with
              | .error e => (1, .error e)
              | .ok (d, p) =>
                let r1 := containerLength
                  (fun v r => resolveLengthAux pre lookup limits bytes fuel v r)
                  (c :: ref.1 :: visiting) d p
                match containerMember pre limits bytes off c ref.1 idx d p r1.2 with
                | .error e => (r1.1 + 1, .error e)
                | .ok (.int l) => (r1.1 + 1, intLength off l)
                | .ok (.ref m h) =>
                  let r2 := resolveLengthAux pre lookup limits bytes (fuel - r1.1)
                    (ref.1 :: visiting) (m, h)
                  (r1.1 + 1 + r2.1, r2.2)
                | .ok _ => (r1.1 + 1, .error (.malformed off "/Length is not an integer"))
            else (0, .error (.malformed off s!"object stream {c} has a non-zero generation"))
          | some (.compressed c' _) =>
            (0, .error (if c' = ref.1 ∨ c' ∈ visiting then
              .cycle 0 s!"cyclic /Length through object stream {c}"
              else .malformed 0 s!"object stream {c} is itself in an object stream"))
          | some (.free _ _) => (0, .error (.malformed 0 s!"object stream {c} is free"))
          | none => (0, .error (.malformed 0 s!"object stream {c} is not in the xref"))
      | some (.inUse off g') =>
        if g' = ref.2 then
          match parseLengthObj limits bytes off ref.1 ref.2 with
          | .error e => (1, .error e)
          | .ok (.int l) => (1, intLength off l)
          | .ok (.ref m h) =>
            let r := resolveLengthAux pre lookup limits bytes fuel (ref.1 :: visiting) (m, h)
            (r.1 + 1, r.2)
          | .ok _ => (1, .error (.malformed off "/Length is not an integer"))
        else (0, .error (.malformed off "/Length reference generation mismatch"))
termination_by fuel
decreasing_by all_goals omega

/-- **Entry point.** The value of the indirect `/Length` reference `ref` (object number,
generation), following a chain of references at most `fuel` hops (rules L1–L4). Objects in
`visiting` are being resolved: referring to one is a cycle error. Callers pass the number of
objects in the cross-reference data as `fuel`. -/
def resolveLength (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) :
    Except Error Nat :=
  (resolveLengthAux pre lookup limits bytes fuel visiting ref).2

/-- The number of object parses `resolveLength` performs on these arguments. -/
def resolveLengthCalls (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) : Nat :=
  (resolveLengthAux pre lookup limits bytes fuel visiting ref).1

/-! ## Indirect objects with resolved `/Length` -/

/-- The stream dictionary `d` of object `self` with a direct `/Length` for
`ObjParse.parseStreamBody`: unchanged when `/Length` is not a reference; otherwise the
resolved length (with `visiting = [self]`) is put in front, shadowing the reference for
`Dict.lookup`. -/
def lengthDict (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel self : Nat) (d : Dict) : Except Error Dict :=
  match Dict.lookup d ObjParse.nameLength with
  | some (.ref m h) =>
    match resolveLength pre lookup limits bytes fuel [self] (m, h) with
    | .ok len => .ok ((ObjParse.nameLength, .int len) :: d)
    | .error e => .error e
  | _ => .ok d

/-- The length resolver of rule L5 for object `self`: the stream data length from `d`
(an indirect `/Length` resolved through `lengthDict`, then the direct rule
`ObjParse.streamLength`). Passed to `ObjParse.parseIndirectBodyWith`. -/
def lengthOf (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel self : Nat) : ObjParse.LengthResolver := fun d at_ =>
  match lengthDict pre lookup limits bytes fuel self d with
  | .error e => .error e
  | .ok d' => ObjParse.streamLength d' at_

/-- **Entry point.** The indirect object `n g obj … endobj` (or stream object) at the next
token at or after `pos`, like `ObjParse.parseIndirect` (same header, `ObjParse.parseHeader`)
but resolving an indirect stream `/Length` through `resolveLength` with fuel `fuel` (the
number of objects) and `visiting = [n]` (rule L5, `lengthOf`). Returns the object and the
position after `endobj`. -/
def parseIndirectResolved (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel pos : Nat) (pre : ObjStm.Pre := ObjStm.Pre.id) :
    Except Error (IndirectObject × Nat) :=
  match ObjParse.parseHeader bytes pos with
  | .error e => .error e
  | .ok (n, g, q) =>
    match ObjParse.parseIndirectBodyWith (lengthOf pre lookup limits bytes fuel n.toNat) limits
        bytes q with
    | .ok (b, r) => .ok (⟨n.toNat, g.toNat, b⟩, r)
    | .error e => .error e

/-! ## Bounds -/

/-- `containerLength` performs no more parses than its resolver does. -/
theorem containerLength_calls_le {res : List Nat → Nat × Nat → Nat × Except Error Nat}
    {B : Nat} (h : ∀ v r, (res v r).1 ≤ B) (vis : List Nat) (d : Dict) (p : Nat) :
    (containerLength res vis d p).1 ≤ B := by
  unfold containerLength
  split
  · exact h _ _
  · simp

/-- **Bounded work.** Resolving one `/Length` parses at most `fuel` objects (length objects
and object-stream containers), also through object streams (task 2.14). -/
theorem resolveLength_calls_le (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) :
    resolveLengthCalls pre lookup limits bytes fuel visiting ref ≤ fuel := by
  unfold resolveLengthCalls
  induction fuel using Nat.strongRecOn generalizing visiting ref with
  | _ fuel ih =>
    rw [resolveLengthAux.eq_def]
    split
    · simp
    · split
      · simp
      · rename_i f
        have h1 : ∀ v r, (resolveLengthAux pre lookup limits bytes f v r).1 ≤ f :=
          fun v r => ih f (by omega) v r
        split
        · simp
        · simp
        · rename_i c idx _
          split
          · simp
          · split
            · split
              · split
                · simp
                · rename_i d p _
                  have hc : (containerLength
                      (fun v r => resolveLengthAux pre lookup limits bytes f v r)
                      (c :: ref.1 :: visiting) d p).1 ≤ f := containerLength_calls_le h1 _ d p
                  dsimp only
                  split
                  · omega
                  · omega
                  · rename_i m hh _
                    have h2 := ih (f - (containerLength
                      (fun v r => resolveLengthAux pre lookup limits bytes f v r)
                      (c :: ref.1 :: visiting) d p).1) (by omega) (ref.1 :: visiting) (m, hh)
                    omega
                  · omega
              · simp
            · simp
            · simp
            · simp
        · split
          · split
            · simp
            · simp
            · rename_i m hh _
              have := h1 (ref.1 :: visiting) (m, hh)
              simp only
              omega
            · simp
          · simp

/-- **Cycles are errors.** A `/Length` reference to an object already being resolved fails
with `cyclic /Length`, whatever the fuel. -/
theorem resolveLength_self (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat)
    (h : ref.1 ∈ visiting) :
    resolveLength pre lookup limits bytes fuel visiting ref =
      .error (.cycle (errOffset lookup ref.1) "cyclic /Length") := by
  unfold resolveLength resolveLengthAux
  simp [h]

/-- **Cycles through object streams are errors** (rule L6, task 2.14): with any non-zero
fuel, resolving a reference to an object stored in an object stream that is itself being
resolved (or in itself) fails with `Error.cycle`, before any parse. -/
theorem resolveLength_container_cycle (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (visiting : List Nat) (ref : Nat × Nat) (c idx : Nat)
    (hl : lookup ref.1 = some (.compressed c idx)) (hc : c = ref.1 ∨ c ∈ visiting) :
    ∃ o w, resolveLength pre lookup limits bytes (fuel + 1) visiting ref = .error (.cycle o w) := by
  unfold resolveLength
  rw [resolveLengthAux.eq_def]
  by_cases hv : ref.1 ∈ visiting
  · simp [hv]
  · simp [hv, hl, hc]

/-- A stream whose `/Length` is a reference to the stream object itself is rejected by
`lengthDict` (Bogk's self-referential `/Length`). -/
theorem lengthDict_self (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel self g : Nat) (d : Dict)
    (h : Dict.lookup d ObjParse.nameLength = some (.ref self g)) :
    ∃ e, lengthDict pre lookup limits bytes fuel self d = .error e := by
  unfold lengthDict
  rw [h]
  simp only
  rw [resolveLength_self pre lookup limits bytes fuel [self] (self, g) (by simp)]
  exact ⟨_, rfl⟩

/-- **Progress** of `parseIndirectResolved`: the object ends strictly after `pos` and within
the input. -/
theorem parseIndirectResolved_pos {pre : ObjStm.Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel pos : Nat} {o : IndirectObject} {r : Nat}
    (h : parseIndirectResolved lookup limits bytes fuel pos pre = .ok (o, r)) :
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
theorem parseIndirectResolved_data {pre : ObjStm.Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel pos : Nat} {o : IndirectObject} {r : Nat} {s : Stream}
    (h : parseIndirectResolved lookup limits bytes fuel pos pre = .ok (o, r))
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

/-! ## Budgeted resolution (task 4.5, Plan.md §4 S3)

`resolveLengthAuxB` is `resolveLengthAux` with the object-stream decodes of rule L6 charged
against a `Filter.Budget` (`ObjStm.decodeObjStmB`, in `containerMemberB`): the budget is
threaded through both recursive calls of a hop through an object stream and returned with the
parse count and the result. Rules L1–L6, the fuel and the visiting list are exactly those of
`resolveLengthAux`. Nothing is cached: a container decoded during one resolution is decoded
(and charged) again by the next resolution that needs it. `lengthOfB` and
`parseIndirectResolvedB` are `lengthOf` and `parseIndirectResolved` with this resolver.

* `resolveLengthB_calls_le`, `containerLengthB_calls_le`, `resolveLengthB_self`,
  `resolveLengthB_container_cycle`: the bounds of the unbudgeted resolver, restated over the
  budgeted one.
* `resolveLengthB_le`: the budget never grows. `resolveLengthB_cost`: a resolution costs at
  most one `allowance` per object parse it performs, so at most `fuel · allowance`.
  `ObjStm.decodeObjStmB_charge`: every decoded container was charged at least its bytes.
* `resolveLengthB_eq`: **if at least one `allowance` is left at the end** (an a-posteriori
  condition, checkable at run time), the budgeted resolver performed exactly the parses and
  returned exactly the result of `resolveLengthAux`: the budget only decreases, so every decode
  on the way ran with at least one allowance left, where `decodeObjStmB` is `decodeObjStm`.
* `parseIndirectResolvedB_le`, `_cost`, `_eq` (same a-posteriori condition), `_with` (the
  result is `parseIndirectWith` of some resolver, so the framing lemmas
  `parseIndirectWith_pos`, `parseIndirectWith_data` apply to it).
-/

open SafePdf.Core.Filter (Budget)

/-- The most one object-stream decode of a container read from `bytes` can charge:
`(maxFilters + 1) · (maxDecodedStreamBytes + bytes.size)` (`ObjStm.decodeObjStmB_cost`; the
container's data lies within the input). The same number as `Chain.decodeAllowance`. -/
def allowance (limits : Limits) (bytes : ByteArray) : Nat :=
  (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + bytes.size)

/-- `containerMember` with the container decode charged against `budget`
(`ObjStm.decodeObjStmB`). Not recursive. -/
def containerMemberB (pre : ObjStm.Pre) (limits : Limits) (bytes : ByteArray)
    (off c num idx : Nat) (d : Dict) (p : Nat) (len : Except Error Nat) (budget : Budget) :
    (Except Error PdfObject) × Budget :=
  match len with
  | .error e => (.error e, budget)
  | .ok len =>
    match ObjParse.parseStreamBodyWith (fun _ _ => .ok len) bytes p d with
    | .error e => (.error e, budget)
    | .ok (st0, _) =>
      match pre.f c st0 with
      | .error e => (.error e, budget)
      | .ok st =>
        match ObjStm.decodeObjStmB limits budget st with
        | (.error e, b1) => (.error e, b1)
        | (.ok os, b1) =>
          (if ObjStm.findObject os num = some idx then ObjStm.getObject os limits idx
           else .error (.malformed off s!"object {num} is not at index {idx} of object stream {c}"),
           b1)

/-- `containerMemberB` never increases the budget. -/
theorem containerMemberB_le (pre : ObjStm.Pre) (limits : Limits) (bytes : ByteArray)
    (off c num idx : Nat) (d : Dict) (p : Nat) (len : Except Error Nat) (budget : Budget) :
    (containerMemberB pre limits bytes off c num idx d p len budget).2.remaining ≤
      budget.remaining := by
  unfold containerMemberB
  rcases len with e | len
  · exact Nat.le_refl _
  · simp only
    rcases ObjParse.parseStreamBodyWith (fun _ _ => .ok len) bytes p d with e | ⟨st0, r⟩
    · exact Nat.le_refl _
    · simp only
      rcases pre.f c st0 with e | st
      · exact Nat.le_refl _
      · simp only
        have h := ObjStm.decodeObjStmB_le limits budget st
        rcases hd : ObjStm.decodeObjStmB limits budget st with ⟨r1, b1⟩
        rw [hd] at h
        rcases r1 with e | os <;> exact h

/-- `containerMemberB` costs at most one `allowance`. -/
theorem containerMemberB_cost (pre : ObjStm.Pre) (limits : Limits) (bytes : ByteArray)
    (off c num idx : Nat) (d : Dict) (p : Nat) (len : Except Error Nat) (budget : Budget) :
    budget.remaining ≤
      (containerMemberB pre limits bytes off c num idx d p len budget).2.remaining +
        allowance limits bytes := by
  unfold containerMemberB allowance
  rcases len with e | len
  · exact Nat.le_add_right _ _
  · simp only
    rcases hs : ObjParse.parseStreamBodyWith (fun _ _ => .ok len) bytes p d with e | ⟨st0, r⟩
    · exact Nat.le_add_right _ _
    · simp only
      obtain ⟨s0, -, hs0, -⟩ := ObjParse.parseStreamBodyWith_ok hs
      rcases hpre : pre.f c st0 with e | st
      · exact Nat.le_add_right _ _
      · simp only
        have hk : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + st.data.size) ≤
            (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + bytes.size) :=
          Nat.mul_le_mul_left _ (by have := pre.le c st0 st hpre; omega)
        have h := ObjStm.decodeObjStmB_cost limits budget st
        rcases hd : ObjStm.decodeObjStmB limits budget st with ⟨r1, b1⟩
        rw [hd] at h
        rcases r1 with e | os <;> (simp only at h ⊢; omega)

/-- With one `allowance` left, `containerMemberB` returns what `containerMember` returns. -/
theorem containerMemberB_eq {pre : ObjStm.Pre} {limits : Limits} {bytes : ByteArray}
    {off c num idx : Nat} {d : Dict} {p : Nat} {len : Except Error Nat} {budget : Budget}
    (h : allowance limits bytes ≤ budget.remaining) :
    (containerMemberB pre limits bytes off c num idx d p len budget).1 =
      containerMember pre limits bytes off c num idx d p len := by
  unfold containerMemberB containerMember
  rcases len with e | len
  · rfl
  · simp only
    rcases hs : ObjParse.parseStreamBodyWith (fun _ _ => .ok len) bytes p d with e | ⟨st0, r⟩
    · rfl
    · simp only
      obtain ⟨s0, -, hs0, -⟩ := ObjParse.parseStreamBodyWith_ok hs
      rcases hpre : pre.f c st0 with e | st
      · rfl
      · simp only
        have hle : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + st.data.size) ≤
            budget.remaining :=
          Nat.le_trans (Nat.mul_le_mul_left _ (by have := pre.le c st0 st hpre; omega)) h
        have he := ObjStm.decodeObjStmB_eq (budget := budget) hle
        rcases hd : ObjStm.decodeObjStmB limits budget st with ⟨r1, b1⟩
        rw [hd] at he
        simp only at he
        rw [← he]
        rcases r1 with e | os <;> rfl

/-- `containerLength` with a budgeted resolver `res` (which takes and returns the budget). -/
def containerLengthB (res : Budget → List Nat → Nat × Nat → Nat × Except Error Nat × Budget)
    (budget : Budget) (vis : List Nat) (d : Dict) (p : Nat) : Nat × Except Error Nat × Budget :=
  match Dict.lookup d ObjParse.nameLength with
  | some (.ref m h) => res budget vis (m, h)
  | _ => (0, ObjParse.streamLength d p, budget)

/-- `containerLengthB` performs no more parses than its resolver does. -/
theorem containerLengthB_calls_le
    {res : Budget → List Nat → Nat × Nat → Nat × Except Error Nat × Budget}
    {B : Nat} (h : ∀ b v r, (res b v r).1 ≤ B) (budget : Budget) (vis : List Nat) (d : Dict)
    (p : Nat) : (containerLengthB res budget vis d p).1 ≤ B := by
  unfold containerLengthB
  split
  · exact h _ _ _
  · simp

/-- `containerLengthB` never increases the budget if its resolver does not. -/
theorem containerLengthB_le
    {res : Budget → List Nat → Nat × Nat → Nat × Except Error Nat × Budget}
    (h : ∀ b v r, (res b v r).2.2.remaining ≤ b.remaining) (budget : Budget) (vis : List Nat)
    (d : Dict) (p : Nat) : (containerLengthB res budget vis d p).2.2.remaining ≤ budget.remaining := by
  unfold containerLengthB
  split
  · exact h _ _ _
  · exact Nat.le_refl _

/-- `containerLengthB` costs what its resolver costs. -/
theorem containerLengthB_cost
    {res : Budget → List Nat → Nat × Nat → Nat × Except Error Nat × Budget} {K : Nat}
    (h : ∀ b v r, b.remaining ≤ (res b v r).2.2.remaining + (res b v r).1 * K)
    (budget : Budget) (vis : List Nat) (d : Dict) (p : Nat) :
    budget.remaining ≤ (containerLengthB res budget vis d p).2.2.remaining +
      (containerLengthB res budget vis d p).1 * K := by
  unfold containerLengthB
  split
  · exact h _ _ _
  · simp

/-- `containerLengthB` agrees with `containerLength` when its resolver agrees with the
unbudgeted one under the a-posteriori condition `K ≤` budget left. -/
theorem containerLengthB_eq
    {res : Budget → List Nat → Nat × Nat → Nat × Except Error Nat × Budget}
    {res' : List Nat → Nat × Nat → Nat × Except Error Nat} {K : Nat}
    (h : ∀ b v r, K ≤ (res b v r).2.2.remaining →
      (res b v r).1 = (res' v r).1 ∧ (res b v r).2.1 = (res' v r).2)
    {budget : Budget} {vis : List Nat} {d : Dict} {p : Nat}
    (hk : K ≤ (containerLengthB res budget vis d p).2.2.remaining) :
    (containerLengthB res budget vis d p).1 = (containerLength res' vis d p).1 ∧
    (containerLengthB res budget vis d p).2.1 = (containerLength res' vis d p).2 := by
  unfold containerLengthB at hk ⊢
  unfold containerLength
  split
  · rename_i m hh hl
    rw [hl] at hk
    exact h _ _ _ hk
  · exact ⟨rfl, rfl⟩

/-- **Budgeted resolution** (task 4.5): `resolveLengthAux` (rules L1–L4, L6) with the
container decodes of rule L6 charged against `budget` (`containerMemberB`). Returns the number
of object parses, the length or an error, and the budget left. Well-founded recursion on
`fuel`, exactly as `resolveLengthAux`. -/
def resolveLengthAuxB (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel : Nat) (budget : Budget) (visiting : List Nat) (ref : Nat × Nat) :
    Nat × Except Error Nat × Budget :=
  if ref.1 ∈ visiting then
    (0, .error (.cycle (errOffset lookup ref.1) "cyclic /Length"), budget)
  else
    match fuel with
    | 0 => (0, .error (.limitExceeded .objects), budget)
    | fuel + 1 =>
      match lookup ref.1 with
      | none =>
        (0, .error (.malformed 0 s!"/Length refers to object {ref.1}, not in the xref"), budget)
      | some (.free _ _) =>
        (0, .error (.malformed 0 s!"/Length refers to free object {ref.1}"), budget)
      | some (.compressed c idx) =>
        if c = ref.1 ∨ c ∈ visiting then
          (0, .error (.cycle (errOffset lookup c)
            s!"cyclic /Length through object stream {c}"), budget)
        else
          match lookup c with
          | some (.inUse off g) =>
            if g = 0 then
              match parseContainerHead limits bytes off c with
              | .error e => (1, .error e, budget)
              | .ok (d, p) =>
                let r1 := containerLengthB
                  (fun b v r => resolveLengthAuxB pre lookup limits bytes fuel b v r)
                  budget (c :: ref.1 :: visiting) d p
                let m := containerMemberB pre limits bytes off c ref.1 idx d p r1.2.1 r1.2.2
                match m.1 with
                | .error e => (r1.1 + 1, .error e, m.2)
                | .ok (.int l) => (r1.1 + 1, intLength off l, m.2)
                | .ok (.ref m' h) =>
                  let r2 := resolveLengthAuxB pre lookup limits bytes (fuel - r1.1) m.2
                    (ref.1 :: visiting) (m', h)
                  (r1.1 + 1 + r2.1, r2.2.1, r2.2.2)
                | .ok _ => (r1.1 + 1, .error (.malformed off "/Length is not an integer"), m.2)
            else
              (0, .error (.malformed off s!"object stream {c} has a non-zero generation"),
                budget)
          | some (.compressed c' _) =>
            (0, .error (if c' = ref.1 ∨ c' ∈ visiting then
              .cycle 0 s!"cyclic /Length through object stream {c}"
              else .malformed 0 s!"object stream {c} is itself in an object stream"), budget)
          | some (.free _ _) => (0, .error (.malformed 0 s!"object stream {c} is free"), budget)
          | none => (0, .error (.malformed 0 s!"object stream {c} is not in the xref"), budget)
      | some (.inUse off g') =>
        if g' = ref.2 then
          match parseLengthObj limits bytes off ref.1 ref.2 with
          | .error e => (1, .error e, budget)
          | .ok (.int l) => (1, intLength off l, budget)
          | .ok (.ref m h) =>
            let r := resolveLengthAuxB pre lookup limits bytes fuel budget (ref.1 :: visiting)
              (m, h)
            (r.1 + 1, r.2.1, r.2.2)
          | .ok _ => (1, .error (.malformed off "/Length is not an integer"), budget)
        else (0, .error (.malformed off "/Length reference generation mismatch"), budget)
termination_by fuel
decreasing_by all_goals omega

/-- **Bounded work** (budgeted): at most `fuel` object parses, as `resolveLength_calls_le`. -/
theorem resolveLengthB_calls_le (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry)
    (limits : Limits) (bytes : ByteArray) (fuel : Nat) (budget : Budget) (visiting : List Nat)
    (ref : Nat × Nat) :
    (resolveLengthAuxB pre lookup limits bytes fuel budget visiting ref).1 ≤ fuel := by
  induction fuel using Nat.strongRecOn generalizing budget visiting ref with
  | _ fuel ih =>
    rw [resolveLengthAuxB.eq_def]
    split
    · simp
    · split
      · simp
      · rename_i f
        have h1 : ∀ b v r, (resolveLengthAuxB pre lookup limits bytes f b v r).1 ≤ f :=
          fun b v r => ih f (by omega) b v r
        split
        · simp
        · simp
        · rename_i c idx _
          split
          · simp
          · split
            · rename_i off g _
              split
              · split
                · simp
                · rename_i d p _
                  have hc := containerLengthB_calls_le h1 budget (c :: ref.1 :: visiting) d p
                  generalize containerLengthB
                    (fun b v r => resolveLengthAuxB pre lookup limits bytes f b v r)
                    budget (c :: ref.1 :: visiting) d p = X at hc ⊢
                  dsimp only
                  generalize containerMemberB pre limits bytes off c ref.1 idx d p X.2.1 X.2.2
                    = M
                  split
                  · omega
                  · omega
                  · rename_i m' hh _
                    have h2 := ih (f - X.1) (by omega) M.2 (ref.1 :: visiting) (m', hh)
                    omega
                  · omega
              · simp
            · simp
            · simp
            · simp
        · split
          · split
            · simp
            · simp
            · rename_i m hh _
              have := h1 budget (ref.1 :: visiting) (m, hh)
              simp only
              omega
            · simp
          · simp

/-- **Budget monotone**: `resolveLengthAuxB` never increases the budget. -/
theorem resolveLengthB_le (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry)
    (limits : Limits) (bytes : ByteArray) (fuel : Nat) (budget : Budget) (visiting : List Nat)
    (ref : Nat × Nat) :
    (resolveLengthAuxB pre lookup limits bytes fuel budget visiting ref).2.2.remaining ≤
      budget.remaining := by
  induction fuel using Nat.strongRecOn generalizing budget visiting ref with
  | _ fuel ih =>
    rw [resolveLengthAuxB.eq_def]
    split
    · simp
    · split
      · simp
      · rename_i f
        have h1 : ∀ b v r, (resolveLengthAuxB pre lookup limits bytes f b v r).2.2.remaining ≤
            b.remaining := fun b v r => ih f (by omega) b v r
        split
        · simp
        · simp
        · rename_i c idx _
          split
          · simp
          · split
            · rename_i off g _
              split
              · split
                · simp
                · rename_i d p _
                  have hc := containerLengthB_le h1 budget (c :: ref.1 :: visiting) d p
                  generalize containerLengthB
                    (fun b v r => resolveLengthAuxB pre lookup limits bytes f b v r)
                    budget (c :: ref.1 :: visiting) d p = X at hc ⊢
                  dsimp only
                  have hm := containerMemberB_le pre limits bytes off c ref.1 idx d p X.2.1 X.2.2
                  generalize containerMemberB pre limits bytes off c ref.1 idx d p X.2.1 X.2.2
                    = M at hm ⊢
                  split
                  · dsimp only; omega
                  · dsimp only; omega
                  · rename_i m' hh _
                    have h2 := ih (f - X.1) (by omega) M.2 (ref.1 :: visiting) (m', hh)
                    dsimp only; omega
                  · dsimp only; omega
              · simp
            · simp
            · simp
            · simp
        · split
          · split
            · simp
            · simp
            · rename_i m hh _
              exact h1 budget (ref.1 :: visiting) (m, hh)
            · simp
          · simp

/-- **Cost** of a budgeted resolution: at most one `allowance` per object parse performed
(`calls · allowance ≤ fuel · allowance`, `resolveLengthB_calls_le`). -/
theorem resolveLengthB_cost (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry)
    (limits : Limits) (bytes : ByteArray) (fuel : Nat) (budget : Budget) (visiting : List Nat)
    (ref : Nat × Nat) :
    budget.remaining ≤
      (resolveLengthAuxB pre lookup limits bytes fuel budget visiting ref).2.2.remaining +
      (resolveLengthAuxB pre lookup limits bytes fuel budget visiting ref).1 *
        allowance limits bytes := by
  induction fuel using Nat.strongRecOn generalizing budget visiting ref with
  | _ fuel ih =>
    rw [resolveLengthAuxB.eq_def]
    split
    · simp
    · split
      · simp
      · rename_i f
        have h1 : ∀ b v r, b.remaining ≤
            (resolveLengthAuxB pre lookup limits bytes f b v r).2.2.remaining +
            (resolveLengthAuxB pre lookup limits bytes f b v r).1 * allowance limits bytes :=
          fun b v r => ih f (by omega) b v r
        split
        · simp
        · simp
        · rename_i c idx _
          split
          · simp
          · split
            · rename_i off g _
              split
              · split
                · simp
                · rename_i d p _
                  have hc := containerLengthB_cost h1 budget (c :: ref.1 :: visiting) d p
                  generalize containerLengthB
                    (fun b v r => resolveLengthAuxB pre lookup limits bytes f b v r)
                    budget (c :: ref.1 :: visiting) d p = X at hc ⊢
                  dsimp only
                  have hm := containerMemberB_cost pre limits bytes off c ref.1 idx d p X.2.1 X.2.2
                  generalize containerMemberB pre limits bytes off c ref.1 idx d p X.2.1 X.2.2
                    = M at hm ⊢
                  split
                  · simp only [Nat.add_mul, Nat.one_mul]; omega
                  · simp only [Nat.add_mul, Nat.one_mul]; omega
                  · rename_i m' hh _
                    have h2 := ih (f - X.1) (by omega) M.2 (ref.1 :: visiting) (m', hh)
                    simp only [Nat.add_mul, Nat.one_mul]; omega
                  · simp only [Nat.add_mul, Nat.one_mul]; omega
              · simp
            · simp
            · simp
            · simp
        · split
          · split
            · simp
            · simp
            · rename_i m hh _
              have h2 := h1 budget (ref.1 :: visiting) (m, hh)
              simp only [Nat.add_mul, Nat.one_mul]; omega
            · simp
          · simp

/-- **Cycles are errors** (budgeted): as `resolveLength_self`; nothing is charged. -/
theorem resolveLengthB_self (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry)
    (limits : Limits) (bytes : ByteArray) (fuel : Nat) (budget : Budget) (visiting : List Nat)
    (ref : Nat × Nat) (h : ref.1 ∈ visiting) :
    resolveLengthAuxB pre lookup limits bytes fuel budget visiting ref =
      (0, .error (.cycle (errOffset lookup ref.1) "cyclic /Length"), budget) := by
  rw [resolveLengthAuxB.eq_def]
  simp [h]

/-- **Cycles through object streams are errors** (budgeted): as
`resolveLength_container_cycle`, before any parse or decode. -/
theorem resolveLengthB_container_cycle (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry)
    (limits : Limits) (bytes : ByteArray) (fuel : Nat) (budget : Budget) (visiting : List Nat)
    (ref : Nat × Nat) (c idx : Nat)
    (hl : lookup ref.1 = some (.compressed c idx)) (hc : c = ref.1 ∨ c ∈ visiting) :
    ∃ o w, resolveLengthAuxB pre lookup limits bytes (fuel + 1) budget visiting ref =
      (0, .error (.cycle o w), budget) := by
  rw [resolveLengthAuxB.eq_def]
  by_cases hv : ref.1 ∈ visiting
  · simp [hv]
  · simp [hv, hl, hc]

/-- **Budget large enough ⇒ same resolution** (task 4.5, a-posteriori): if at least one
`allowance` is left after a budgeted resolution, it performed exactly the parses of
`resolveLengthAux` and returned exactly its result. -/
theorem resolveLengthB_eq (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry)
    (limits : Limits) (bytes : ByteArray) (fuel : Nat) (budget : Budget) (visiting : List Nat)
    (ref : Nat × Nat) :
    allowance limits bytes ≤
      (resolveLengthAuxB pre lookup limits bytes fuel budget visiting ref).2.2.remaining →
    (resolveLengthAuxB pre lookup limits bytes fuel budget visiting ref).1 =
      (resolveLengthAux pre lookup limits bytes fuel visiting ref).1 ∧
    (resolveLengthAuxB pre lookup limits bytes fuel budget visiting ref).2.1 =
      (resolveLengthAux pre lookup limits bytes fuel visiting ref).2 := by
  induction fuel using Nat.strongRecOn generalizing budget visiting ref with
  | _ fuel ih =>
    rw [resolveLengthAuxB.eq_def, resolveLengthAux.eq_def]
    by_cases hv : ref.1 ∈ visiting
    · simp [hv]
    · simp only [hv, ↓reduceIte]
      rcases fuel with _ | f
      · simp
      · simp only
        rcases hl : lookup ref.1 with _ | (⟨_, _⟩ | ⟨off, g'⟩ | ⟨c, idx⟩)
        · simp
        · simp
        · simp only
          by_cases hg : g' = ref.2
          · simp only [hg, ↓reduceIte]
            rcases hp : parseLengthObj limits bytes off ref.1 ref.2 with e | o
            · simp
            · cases o <;> try simp
              rename_i m hh
              intro hA
              obtain ⟨e1, e2⟩ := ih f (by omega) budget (ref.1 :: visiting) (m, hh) hA
              exact ⟨by rw [e1], e2⟩
          · simp [hg]
        · by_cases hcv : c = ref.1 ∨ c ∈ visiting
          · simp [hcv]
          · simp only [hcv, ↓reduceIte]
            rcases hlc : lookup c with _ | (⟨_, _⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
            · simp
            · simp
            · by_cases hg : g = 0
              · simp only [hg, ↓reduceIte]
                rcases hh : parseContainerHead limits bytes off c with e | ⟨d, p⟩
                · simp
                · simp only
                  have hXle := containerLengthB_le
                    (res := fun b v r => resolveLengthAuxB pre lookup limits bytes f b v r)
                    (fun b v r => resolveLengthB_le pre lookup limits bytes f b v r)
                    budget (c :: ref.1 :: visiting) d p
                  have hXeq := fun hk => containerLengthB_eq
                    (res := fun b v r => resolveLengthAuxB pre lookup limits bytes f b v r)
                    (res' := fun v r => resolveLengthAux pre lookup limits bytes f v r)
                    (fun b v r hk => ih f (by omega) b v r hk)
                    (budget := budget) (vis := c :: ref.1 :: visiting) (d := d) (p := p) hk
                  generalize containerLengthB
                    (fun b v r => resolveLengthAuxB pre lookup limits bytes f b v r)
                    budget (c :: ref.1 :: visiting) d p = X at hXle hXeq ⊢
                  generalize containerLength
                    (fun v r => resolveLengthAux pre lookup limits bytes f v r)
                    (c :: ref.1 :: visiting) d p = Y at hXeq ⊢
                  have hMle := containerMemberB_le pre limits bytes off c ref.1 idx d p X.2.1 X.2.2
                  have hMeq := fun hk => containerMemberB_eq (pre := pre) (limits := limits) (bytes := bytes) (off := off) (c := c)
                    (num := ref.1) (idx := idx) (d := d) (p := p) (len := X.2.1)
                    (budget := X.2.2) hk
                  generalize containerMemberB pre limits bytes off c ref.1 idx d p X.2.1 X.2.2
                    = M at hMle hMeq ⊢
                  intro hA
                  have hAM : allowance limits bytes ≤ M.2.remaining := by
                    revert hA
                    split
                    · exact id
                    · exact id
                    · rename_i m' hh' _
                      have := resolveLengthB_le pre lookup limits bytes (f - X.1) M.2
                        (ref.1 :: visiting) (m', hh')
                      dsimp only
                      omega
                    · exact id
                  obtain ⟨hx1, hx2⟩ := hXeq (by omega)
                  have hm := hMeq (by omega)
                  rw [hx2] at hm
                  rw [← hm, ← hx1]
                  revert hA
                  split
                  · simp
                  · simp
                  · rename_i m' hh' _
                    intro hA
                    obtain ⟨e1, e2⟩ := ih (f - X.1) (by omega) M.2 (ref.1 :: visiting) (m', hh') hA
                    exact ⟨by rw [e1], e2⟩
                  · simp
              · simp [hg]
            · simp

/-- `lengthOf` with the budgeted resolver: the stream length for object `self` with
dictionary `d`, and the budget left. -/
def lengthOfB (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel self : Nat) (budget : Budget) (d : Dict) (at_ : Nat) :
    (Except Error Nat) × Budget :=
  match Dict.lookup d ObjParse.nameLength with
  | some (.ref m h) =>
    let r := resolveLengthAuxB pre lookup limits bytes fuel budget [self] (m, h)
    (match r.2.1 with
     | .ok len => ObjParse.streamLength ((ObjParse.nameLength, .int len) :: d) at_
     | .error e => .error e, r.2.2)
  | _ => (ObjParse.streamLength d at_, budget)

/-- `lengthOfB` never increases the budget. -/
theorem lengthOfB_le (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel self : Nat) (budget : Budget) (d : Dict) (at_ : Nat) :
    (lengthOfB pre lookup limits bytes fuel self budget d at_).2.remaining ≤
      budget.remaining := by
  unfold lengthOfB
  split
  · exact resolveLengthB_le _ _ _ _ _ _ _ _
  · exact Nat.le_refl _

/-- `lengthOfB` costs at most `fuel · allowance`. -/
theorem lengthOfB_cost (pre : ObjStm.Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel self : Nat) (budget : Budget) (d : Dict) (at_ : Nat) :
    budget.remaining ≤ (lengthOfB pre lookup limits bytes fuel self budget d at_).2.remaining +
      fuel * allowance limits bytes := by
  unfold lengthOfB
  split
  · rename_i m h _
    have h1 := resolveLengthB_cost pre lookup limits bytes fuel budget [self] (m, h)
    have h2 := Nat.mul_le_mul_right (allowance limits bytes)
      (resolveLengthB_calls_le pre lookup limits bytes fuel budget [self] (m, h))
    dsimp only
    omega
  · exact Nat.le_add_right _ _

/-- With one `allowance` left at the end, `lengthOfB` returns what `lengthOf` returns. -/
theorem lengthOfB_eq {pre : ObjStm.Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel self : Nat} {budget : Budget} {d : Dict} {at_ : Nat}
    (h : allowance limits bytes ≤
      (lengthOfB pre lookup limits bytes fuel self budget d at_).2.remaining) :
    (lengthOfB pre lookup limits bytes fuel self budget d at_).1 =
      lengthOf pre lookup limits bytes fuel self d at_ := by
  unfold lengthOfB at h ⊢
  unfold lengthOf lengthDict resolveLength
  split
  · rename_i m hh hl
    rw [hl] at h
    have he := (resolveLengthB_eq pre lookup limits bytes fuel budget [self] (m, hh) h).2
    dsimp only
    rw [he]
    cases (resolveLengthAux pre lookup limits bytes fuel [self] (m, hh)).2 <;> rfl
  · rfl

/-- `parseIndirectResolved` with an arbitrary length resolver `lenF n` for object `n`: the
header (`ObjParse.parseHeader`), then `ObjParse.parseIndirectBodyWith`. -/
def parseIndirectWith (lenF : Nat → ObjParse.LengthResolver) (limits : Limits)
    (bytes : ByteArray) (pos : Nat) : Except Error (IndirectObject × Nat) :=
  match ObjParse.parseHeader bytes pos with
  | .error e => .error e
  | .ok (n, g, q) =>
    match ObjParse.parseIndirectBodyWith (lenF n.toNat) limits bytes q with
    | .ok (b, r) => .ok (⟨n.toNat, g.toNat, b⟩, r)
    | .error e => .error e

/-- `parseIndirectResolved` is `parseIndirectWith` of `lengthOf`. -/
theorem parseIndirectResolved_eq_with (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel pos : Nat) (pre : ObjStm.Pre) :
    parseIndirectResolved lookup limits bytes fuel pos pre =
      parseIndirectWith (lengthOf pre lookup limits bytes fuel) limits bytes pos := rfl

/-- **Where the length resolver is called**: `parseIndirectWith lenF limits bytes pos` calls
`lenF n d p` only when this is `some (n, d, p)` (a stream object `n` with dictionary `d`
whose `stream` keyword, ending at `p`, is followed by an end-of-line), and never otherwise
(`parseIndirectWith_congr`). -/
def callPoint (limits : Limits) (bytes : ByteArray) (pos : Nat) : Option (Nat × Dict × Nat) :=
  match ObjParse.parseHeader bytes pos with
  | .error _ => none
  | .ok (n, _, q) =>
    match ObjParse.parseObject limits bytes q with
    | .error _ => none
    | .ok (o, r) =>
      match Lex.next bytes r with
      | .ok (some (.keyword k, r2)) =>
        if k = ObjParse.kwEndobj then none
        else if k = ObjParse.kwStream then
          match o with
          | .dict d =>
            match ObjParse.streamDataStart bytes r2 with
            | some _ => some (n.toNat, d, r2)
            | none => none
          | _ => none
        else none
      | _ => none

/-- `parseStreamBodyWith` only calls its resolver on `d p`, and only after the end-of-line
check. -/
theorem parseStreamBodyWith_congr {len len' : ObjParse.LengthResolver} {bytes : ByteArray}
    {p : Nat} {d : Dict}
    (h : ∀ s, ObjParse.streamDataStart bytes p = some s → len d p = len' d p) :
    ObjParse.parseStreamBodyWith len bytes p d = ObjParse.parseStreamBodyWith len' bytes p d := by
  unfold ObjParse.parseStreamBodyWith
  rcases hs : ObjParse.streamDataStart bytes p with _ | s
  · rfl
  · simp only
    rw [h s hs]

/-- `parseIndirectBodyWith` only calls its resolver at the stream point. -/
theorem parseIndirectBodyWith_congr {len len' : ObjParse.LengthResolver} {limits : Limits}
    {bytes : ByteArray} {q : Nat}
    (h : ∀ o r k r2 d s, ObjParse.parseObject limits bytes q = .ok (o, r) →
      Lex.next bytes r = .ok (some (.keyword k, r2)) → k ≠ ObjParse.kwEndobj →
      k = ObjParse.kwStream → o = .dict d → ObjParse.streamDataStart bytes r2 = some s →
      len d r2 = len' d r2) :
    ObjParse.parseIndirectBodyWith len limits bytes q =
      ObjParse.parseIndirectBodyWith len' limits bytes q := by
  unfold ObjParse.parseIndirectBodyWith
  rcases ho : ObjParse.parseObject limits bytes q with e | ⟨o, r⟩
  · rfl
  · simp only
    rcases hk : Lex.next bytes r with e | _ | ⟨t, r2⟩
    · rfl
    · rfl
    · cases t <;> try rfl
      rename_i k
      simp only
      by_cases h1 : k = ObjParse.kwEndobj
      · simp only [h1, ↓reduceIte]
      · by_cases h2 : k = ObjParse.kwStream
        · simp only [h2, ↓reduceIte]
          cases o <;> try rfl
          rename_i d
          simp only
          rw [parseStreamBodyWith_congr (fun s hs => h _ _ _ _ d s ho hk h1 h2 rfl hs)]
        · simp only [h1, h2, ↓reduceIte]

/-- **Only the call point matters**: two resolvers that agree where `parseIndirectWith`
calls them give the same result. -/
theorem parseIndirectWith_congr {lenF lenG : Nat → ObjParse.LengthResolver} {limits : Limits}
    {bytes : ByteArray} {pos : Nat}
    (h : ∀ n d p, callPoint limits bytes pos = some (n, d, p) → lenF n d p = lenG n d p) :
    parseIndirectWith lenF limits bytes pos = parseIndirectWith lenG limits bytes pos := by
  unfold parseIndirectWith
  rcases hh : ObjParse.parseHeader bytes pos with e | ⟨n, g, q⟩
  · rfl
  · simp only
    rw [parseIndirectBodyWith_congr (len' := lenG n.toNat)]
    intro o r k r2 d s ho hk h1 h2 hd hs
    apply h
    unfold callPoint
    rw [hh]
    simp only
    rw [ho]
    simp only
    rw [hk]
    subst hd h2
    simp only [h1, ↓reduceIte, hs]

/-- **Progress** of `parseIndirectWith`, for every resolver. -/
theorem parseIndirectWith_pos {lenF : Nat → ObjParse.LengthResolver} {limits : Limits}
    {bytes : ByteArray} {pos : Nat} {o : IndirectObject} {r : Nat}
    (h : parseIndirectWith lenF limits bytes pos = .ok (o, r)) :
    pos < r ∧ r ≤ bytes.size := by
  unfold parseIndirectWith at h
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

/-- **Stream data within the file** for `parseIndirectWith`, for every resolver. -/
theorem parseIndirectWith_data {lenF : Nat → ObjParse.LengthResolver} {limits : Limits}
    {bytes : ByteArray} {pos : Nat} {o : IndirectObject} {r : Nat} {s : Stream}
    (h : parseIndirectWith lenF limits bytes pos = .ok (o, r)) (hs : o.body = .stream s) :
    ∃ st, pos < st ∧ st + s.data.size ≤ bytes.size ∧
      s.data = bytes.extract st (st + s.data.size) := by
  unfold parseIndirectWith at h
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

/-- **Budgeted entry point** (task 4.5): `parseIndirectResolved` with an indirect stream
`/Length` resolved by `lengthOfB` (rule L5 with the budgeted resolver: the decodes of rule L6
are charged against `budget`). The length is resolved at the call point (`callPoint`) and the
object is then parsed with that length (`parseIndirectWith`); an object that is not a stream
with an end-of-line after `stream` resolves no length and costs nothing. Returns the result
and the budget left. -/
def parseIndirectResolvedB (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel pos : Nat) (pre : ObjStm.Pre) (budget : Budget) :
    (Except Error (IndirectObject × Nat)) × Budget :=
  match callPoint limits bytes pos with
  | none => (parseIndirectWith (fun _ => ObjParse.streamLength) limits bytes pos, budget)
  | some (n, d, p) =>
    let r := lengthOfB pre lookup limits bytes fuel n budget d p
    (parseIndirectWith (fun _ _ _ => r.1) limits bytes pos, r.2)

/-- `parseIndirectResolvedB` is `parseIndirectWith` of some resolver. -/
theorem parseIndirectResolvedB_with (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel pos : Nat) (pre : ObjStm.Pre) (budget : Budget) :
    ∃ lenF, (parseIndirectResolvedB lookup limits bytes fuel pos pre budget).1 =
      parseIndirectWith lenF limits bytes pos := by
  unfold parseIndirectResolvedB
  split
  · exact ⟨fun _ => ObjParse.streamLength, rfl⟩
  · rename_i n d p _
    exact ⟨fun _ _ _ => (lengthOfB pre lookup limits bytes fuel n budget d p).1, rfl⟩

/-- `parseIndirectResolvedB` never increases the budget. -/
theorem parseIndirectResolvedB_le (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel pos : Nat) (pre : ObjStm.Pre) (budget : Budget) :
    (parseIndirectResolvedB lookup limits bytes fuel pos pre budget).2.remaining ≤
      budget.remaining := by
  unfold parseIndirectResolvedB
  split
  · exact Nat.le_refl _
  · exact lengthOfB_le _ _ _ _ _ _ _ _ _

/-- **Cost** of `parseIndirectResolvedB`: at most `fuel · allowance` (one `/Length`
resolution). -/
theorem parseIndirectResolvedB_cost (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel pos : Nat) (pre : ObjStm.Pre) (budget : Budget) :
    budget.remaining ≤
      (parseIndirectResolvedB lookup limits bytes fuel pos pre budget).2.remaining +
        fuel * allowance limits bytes := by
  unfold parseIndirectResolvedB
  split
  · exact Nat.le_add_right _ _
  · exact lengthOfB_cost _ _ _ _ _ _ _ _ _

/-- **Budget large enough ⇒ same object** (a-posteriori): with one `allowance` left after
the parse, `parseIndirectResolvedB` returns exactly what `parseIndirectResolved` returns. -/
theorem parseIndirectResolvedB_eq {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel pos : Nat} {pre : ObjStm.Pre} {budget : Budget}
    (h : allowance limits bytes ≤
      (parseIndirectResolvedB lookup limits bytes fuel pos pre budget).2.remaining) :
    (parseIndirectResolvedB lookup limits bytes fuel pos pre budget).1 =
      parseIndirectResolved lookup limits bytes fuel pos pre := by
  rw [parseIndirectResolved_eq_with]
  unfold parseIndirectResolvedB at h ⊢
  split
  · rename_i hc
    dsimp only
    exact parseIndirectWith_congr fun n d p h' => by rw [hc] at h'; cases h'
  · rename_i n d p hc
    rw [hc] at h
    dsimp only at h ⊢
    apply parseIndirectWith_congr
    intro n' d' p' h'
    rw [hc] at h'
    cases h'
    exact lengthOfB_eq h

/-- **Progress** of `parseIndirectResolvedB`. -/
theorem parseIndirectResolvedB_pos {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel pos : Nat} {pre : ObjStm.Pre} {budget : Budget}
    {o : IndirectObject} {r : Nat}
    (h : (parseIndirectResolvedB lookup limits bytes fuel pos pre budget).1 = .ok (o, r)) :
    pos < r ∧ r ≤ bytes.size := by
  obtain ⟨lenF, he⟩ := parseIndirectResolvedB_with lookup limits bytes fuel pos pre budget
  rw [he] at h
  exact parseIndirectWith_pos h

/-- **Stream data within the file** for `parseIndirectResolvedB`. -/
theorem parseIndirectResolvedB_data {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel pos : Nat} {pre : ObjStm.Pre} {budget : Budget}
    {o : IndirectObject} {r : Nat} {s : Stream}
    (h : (parseIndirectResolvedB lookup limits bytes fuel pos pre budget).1 = .ok (o, r))
    (hs : o.body = .stream s) :
    ∃ st, pos < st ∧ st + s.data.size ≤ bytes.size ∧
      s.data = bytes.extract st (st + s.data.size) := by
  obtain ⟨lenF, he⟩ := parseIndirectResolvedB_with lookup limits bytes fuel pos pre budget
  rw [he] at h
  exact parseIndirectWith_data h hs

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}:{m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o w => s!"cycle@{o}:{w}"
  | .encryption w => s!"encryption:{w}"

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
  match resolveLength ObjStm.Pre.id lookup Limits.default b fuel visiting ref with
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
#guard (pir (tableLookup selfRefPdf).1 selfRefPdf 6 247) == .inl "cycle@247:cyclic /Length"
#guard (pir (tableLookup selfRefPdf).1 selfRefPdf 6 15).isRight
#guard (pir (tableLookup selfRefPdf).1 selfRefPdf 6 337).isRight
-- with any fuel, including 0
#guard (pir (tableLookup selfRefPdf).1 selfRefPdf 0 247) == .inl "cycle@247:cyclic /Length"

/-- Lookup for `length-mutual.pdf`, built by hand: its xref is a stream (task 2.4). Offsets are
those `Tests/adversarial/generate.py` (`length_mutual`) wrote: objects 1–5 and the xref stream 7
in use, object 6 at index 0 of object stream 5. -/
private def mutualLookup : Nat → Option XrefEntry :=
  mkLookup [(1, .inUse 15 0), (2, .inUse 64 0), (3, .inUse 121 0), (4, .inUse 225 0),
    (5, .inUse 294 0), (6, .compressed 5 0), (7, .inUse 381 0)]

-- length-mutual.pdf: stream 4 needs object 6, in object stream 5, whose own /Length is
-- `4 0 R`: a cycle through an object stream (task 2.14), found after one container parse.
#guard (pir mutualLookup mutualPdf 8 225) == .inl "cycle@225:cyclic /Length"
#guard resolveLengthCalls ObjStm.Pre.id mutualLookup Limits.default mutualPdf 8 [4] (6, 0) == 1
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
#guard resolveLengthCalls ObjStm.Pre.id oneHopLookup Limits.default oneHop 2 [1] (5, 0) == 1
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
#guard resolveLengthCalls ObjStm.Pre.id twoHopLookup Limits.default twoHop 3 [1] (5, 0) == 2
-- fuel exhaustion: two hops with fuel 1
#guard (pir twoHopLookup twoHop 1 0) == .inl "limit:SafePdf.LimitKind.objects"
#guard resolveLengthCalls ObjStm.Pre.id twoHopLookup Limits.default twoHop 1 [1] (5, 0) == 1

/-- A cycle between two integer-less objects: `5 0 obj 6 0 R endobj`, `6 0 obj 5 0 R endobj`. -/
private def cyc : ByteArray := (oneHopHead ++ twoHopObjs ++ "6 0 obj 5 0 R endobj\n").toUTF8

#guard (pir twoHopLookup cyc 100 0) == .inl s!"cycle@{oneHopHead.utf8ByteSize}:cyclic /Length"

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

/-! ### `/Length` through object streams (rule L6, task 2.14) -/

/-- A stream with `/Length 7 0 R`, object 7 being in an object stream. -/
private def osHead : String :=
  "1 0 obj\n<< /Length 7 0 R >>\nstream\nhello world\nendstream\nendobj\n"

/-- Object stream `2 0 obj` with `/Length` `len` holding `7 0 <member>` (`/First 4`). -/
private def osCont (len member : String) : String :=
  s!"2 0 obj\n<< /Type /ObjStm /N 1 /First 4 /Length {len} >>\nstream\n7 0 {member}" ++
    "\nendstream\nendobj\n"

/-- `osHead`, the container, then `tail` (further objects). -/
private def osFile (len member tail : String) : ByteArray :=
  (osHead ++ osCont len member ++ tail).toUTF8

/-- Lookup for `osFile`: 1 and 2 in use, 7 in object stream 2, `extra` entries. -/
private def osLookup (len member : String) (extra : List (Nat × XrefEntry) := []) :
    Nat → Option XrefEntry :=
  mkLookup ([(1, .inUse 0 0), (2, .inUse osHead.utf8ByteSize 0), (7, .compressed 2 0)] ++
    extra.map (fun e => match e.2 with
      | .inUse o g => (e.1, .inUse (osHead.utf8ByteSize + (osCont len member).utf8ByteSize + o) g)
      | x => (e.1, x)))

/-- Expected result of `pir` on `osFile`: object 1 with data `hello world`. -/
private def osOk : Sum String (Nat × Nat × Option (List UInt8) × Nat) :=
  .inr (1, 0, some "hello world".toUTF8.toList, osHead.utf8ByteSize - 1)

-- the member is the integer 11: resolves, one parse (the container)
#guard (pir (osLookup "6" "11") (osFile "6" "11" "") 3 0) == osOk
#guard resolveLengthCalls ObjStm.Pre.id (osLookup "6" "11") Limits.default (osFile "6" "11" "") 3 [1] (7, 0) == 1
-- the container's own /Length is indirect (`3 0 R`, an integer object): two parses
#guard (pir (osLookup "3 0 R" "11" [(3, .inUse 0 0)])
  (osFile "3 0 R" "11" "3 0 obj 6 endobj\n") 3 0) == osOk
#guard resolveLengthCalls ObjStm.Pre.id (osLookup "3 0 R" "11" [(3, .inUse 0 0)]) Limits.default
  (osFile "3 0 R" "11" "3 0 obj 6 endobj\n") 3 [1] (7, 0) == 2
-- the member is a reference to an integer object: two parses
#guard (pir (osLookup "9" "8 0 R" [(8, .inUse 0 0)])
  (osFile "9" "8 0 R" "8 0 obj 11 endobj\n") 3 0) == osOk
#guard resolveLengthCalls ObjStm.Pre.id (osLookup "9" "8 0 R" [(8, .inUse 0 0)]) Limits.default
  (osFile "9" "8 0 R" "8 0 obj 11 endobj\n") 3 [1] (7, 0) == 2
-- the budget is shared: container /Length and member reference with fuel 2 (three parses needed)
#guard (pir (osLookup "3 0 R" "8 0 R" [(3, .inUse 0 0), (8, .inUse 17 0)])
  (osFile "3 0 R" "8 0 R" "3 0 obj 9 endobj\n8 0 obj 11 endobj\n") 3 0) == osOk
#guard (pir (osLookup "3 0 R" "8 0 R" [(3, .inUse 0 0), (8, .inUse 17 0)])
  (osFile "3 0 R" "8 0 R" "3 0 obj 9 endobj\n8 0 obj 11 endobj\n") 2 0) ==
  .inl "limit:SafePdf.LimitKind.objects"
-- the container's /Length is its own member 7: a cycle
#guard (pir (osLookup "7 0 R" "11") (osFile "7 0 R" "11" "") 3 0) == .inl "cycle@0:cyclic /Length"
-- the member refers back to the stream being parsed: a cycle
#guard (pir (osLookup "9" "1 0 R") (osFile "9" "1 0 R" "") 3 0) == .inl "cycle@0:cyclic /Length"
-- the container's /Length is the stream being parsed: a cycle
#guard (pir (osLookup "1 0 R" "11") (osFile "1 0 R" "11" "") 3 0) == .inl "cycle@0:cyclic /Length"
-- object 7 claims to be its own container / an object stream inside an object stream
#guard (pir (mkLookup [(1, .inUse 0 0), (7, .compressed 7 0)]) (osFile "6" "11" "") 3 0) ==
  .inl "cycle@0:cyclic /Length through object stream 7"
#guard (pir (mkLookup [(1, .inUse 0 0), (7, .compressed 2 0), (2, .compressed 9 0)])
  (osFile "6" "11" "") 3 0) == .inl "malformed@0:object stream 2 is itself in an object stream"
#guard (pir (mkLookup [(1, .inUse 0 0), (7, .compressed 2 0), (2, .compressed 7 0)])
  (osFile "6" "11" "") 3 0) == .inl "cycle@0:cyclic /Length through object stream 2"
-- the xref index disagrees with the stream header
#guard (pir (mkLookup [(1, .inUse 0 0), (2, .inUse osHead.utf8ByteSize 0), (7, .compressed 2 1)])
  (osFile "6" "11" "") 3 0) ==
  .inl s!"malformed@{osHead.utf8ByteSize}:object 7 is not at index 1 of object stream 2"
-- the member is not an integer; the container is not a stream
#guard (pir (osLookup "6" "/X") (osFile "6" "/X" "") 3 0) ==
  .inl s!"malformed@{osHead.utf8ByteSize}:/Length is not an integer"
#guard (pir (mkLookup [(1, .inUse 0 0), (2, .inUse oneHopHead.utf8ByteSize 0),
    (7, .compressed 2 0)]) (osHead ++ "2 0 obj 6 endobj\n").toUTF8 3 0) ==
  .inl s!"malformed@{osHead.utf8ByteSize}:object stream container is not a stream"

/-! ### Budgeted resolution (task 4.5) -/

/-- Test helper: `parseIndirectResolvedB` from a budget of `n` bytes, summarised as `pir`
does, with the budget left. -/
private def pirB (lookup : Nat → Option XrefEntry) (b : ByteArray) (fuel pos n : Nat) :
    Sum String (Nat × Nat × Option (List UInt8) × Nat) × Nat :=
  let r := parseIndirectResolvedB lookup Limits.default b fuel pos ObjStm.Pre.id ⟨n⟩
  ((match r.1 with
    | .ok (o, q) =>
      match o.body with
      | .stream s => .inr (o.num, o.gen, some s.data.toList, q)
      | .obj _ => .inr (o.num, o.gen, none, q)
    | .error e => .inl (errS e)), r.2.remaining)

-- the member is the integer 11: the container's data (`7 0 11`, 6 bytes, no filter) is charged
#guard pirB (osLookup "6" "11") (osFile "6" "11" "") 3 0 100 == (osOk, 94)
-- the container does not fit the budget: the total-budget error
#guard (pirB (osLookup "6" "11") (osFile "6" "11" "") 3 0 5).1 ==
  .inl "limit:SafePdf.LimitKind.decodedTotalBytes"
-- the member is a reference to an integer object (`7 0 8 0 R`, 9 bytes charged)
#guard pirB (osLookup "9" "8 0 R" [(8, .inUse 0 0)]) (osFile "9" "8 0 R" "8 0 obj 11 endobj\n")
  3 0 100 == (osOk, 91)
-- a /Length in a plain object, a direct /Length, a cycle: nothing decoded, nothing charged
#guard pirB oneHopLookup oneHop 2 0 0 == (pir oneHopLookup oneHop 2 0, 0)
#guard pirB (mkLookup []) "1 0 obj << /Length 2 >> stream\nab\nendstream endobj".toUTF8 0 0 7 ==
  (.inr (1, 0, some [97, 98], 50), 7)
#guard pirB (tableLookup selfRefPdf).1 selfRefPdf 6 247 3 == (.inl "cycle@247:cyclic /Length", 3)
-- length-mutual.pdf: the cycle is found before any decode
#guard pirB mutualLookup mutualPdf 8 225 10 == (.inl "cycle@225:cyclic /Length", 10)
-- with the budget left, the budgeted resolver performs the parses of the unbudgeted one
#guard (resolveLengthAuxB ObjStm.Pre.id (osLookup "3 0 R" "11" [(3, .inUse 0 0)]) Limits.default
  (osFile "3 0 R" "11" "3 0 obj 6 endobj\n") 3 ⟨100⟩ [1] (7, 0)).1 == 2


end Tests

end SafePdf.Core.Xref.Length
