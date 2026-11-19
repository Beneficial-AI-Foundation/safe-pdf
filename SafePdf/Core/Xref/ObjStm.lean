import SafePdf.Core.Xref
import SafePdf.Core.Xref.Length
import SafePdf.Core.ObjParse
import SafePdf.Core.Lex
import SafePdf.Core.Filter.Flate
import SafePdf.Core.Filter.Predictor

/-!
# Object streams (Plan.md §5.2, task 2.4b)

ISO 32000-2 §7.5.7: an object stream is a stream object (`/Type /ObjStm`) whose decoded data
holds `/N` direct objects. The first `/First` bytes are a header of `N` pairs
`objnum offset` (offsets relative to `/First`, in increasing order); the objects follow.
Cross-reference streams point at such objects with type-2 entries
`XrefEntry.compressed objStm index`.

Plan.md §5.2: "Object streams: an object inside an object stream may not itself be the
stream's container — rank argument on (generation of container, offset)." Here the rank is
simply the entry kind: an `inUse` entry has rank 0, a `compressed` one rank 1, and the
container of a compressed object must have rank 0 (§7.5.7: "the stream object itself shall
not be stored in an object stream"; generation 0). So the container chain has length exactly
one and `fetchCompressed` is not recursive at all (`fetchCompressed_no_recursion`).

## Rules

* O1. `decodeObjStm`: `/Type /ObjStm`; `/N` an integer `≥ 0` (above `limits.maxObjects` is
  `Error.limitExceeded .objects`); `/First` an integer `≥ 0`, at most the decoded size;
  `/Extends`, if present, a reference (recorded, not followed).
* O2. Data: no `/Filter` (or `[]`) is raw; `/FlateDecode` (or `[/FlateDecode]`) is inflated
  with `Filter.Flate.flateDecode limits`, then `/DecodeParms` (a dictionary or a one-element
  array) is applied with `Filter.Predictor`; any other filter or filter chain is
  `Error.unsupported`.
* O3. Header: exactly `N` pairs of non-negative integers, lexed by `Lex.next` from the decoded
  bytes `[0, /First)` only, and nothing else in that range.
* O4. Offsets strictly increasing; `/First + offset <` decoded size for every pair; object
  numbers `≥ 1`; object numbers pairwise distinct (S6). These are carried by `ObjStm` as
  proof fields, so `decodeObjStm_offsets_sorted` etc. hold by construction.
* O5. `getObject os limits k`: `ObjParse.parseObject` at `/First + off_k`; the object must end
  at or before the next object's start (`/First + off_{k+1}`, or the end of the data), and
  only white space or comments may follow it in its slice: objects in object streams are
  direct objects (no `n g obj` wrapper, no `stream`), generation implicitly 0.
* O6. `fetchCompressed lookup limits bytes fuel num`: the entry of `num` must be
  `compressed c idx` with `c ≠ num` (else `Error.cycle`); the entry of `c` must be
  `inUse off 0` (a compressed container is "nested", an error: `Error.cycle` when it is
  `compressed num _`, the two-object cycle, else `malformed`); the object at `off` is parsed with
  `Length.parseIndirectResolved` (indirect `/Length` resolved with `fuel`), its header must be
  `c 0` and its body a stream; it is decoded by O1–O4; `findObject os num` must equal `idx`
  (the xref index and the stream header agree); then O5 with `k = idx`.

Error offsets for header and object errors are positions in the *decoded* data; dictionary
errors use offset 0, container errors the container's file offset.

## Theorems

* Totality by construction: no recursion except `parsePairs` (structural on the pair count).
* `decodeObjStm_offsets_sorted`, `decodeObjStm_bounds`, `decodeObjStm_nums_pos`,
  `decodeObjStm_nums_nodup`, `decodeObjStm_first_le`, `decodeObjStm_count_le`.
* `getObject_depth`, `fetchCompressed_depth`: depth at most `limits.maxObjectDepth`.
* `fetchCompressed_self`, `fetchCompressed_nested`: a self-container or a compressed
  container is an error; `fetchCompressed_self_cycle`, `fetchCompressed_mutual_cycle`: for a
  self-container and for two object streams containing each other it is `Error.cycle`.
* `fetchCompressed_no_recursion`, `fetchCompressed_rank`: success implies the chain
  `num ↦ compressed c ↦ inUse off 0` with `c ≠ num` (rank 1 → rank 0).
* `fetchCompressed_work`: at most one container parse and one decode
  (`fetchCompressedTrace` counts them; `fetchCompressed` is its result).
-/

namespace SafePdf.Core.Xref.ObjStm

open SafePdf
open SafePdf.Core.Xref (XrefEntry)
open SafePdf.Core.ObjParse (errAt lexErr)

/-! ## Strictly ascending lists -/

/-- Adjacent elements strictly ascending (linear-time check). -/
def adjLt : List Nat → Bool
  | a :: b :: rest => decide (a < b) && adjLt (b :: rest)
  | _ => true

/-- Adjacent-strict implies pairwise strict. -/
theorem pairwise_of_adjLt : (l : List Nat) → adjLt l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [adjLt, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_adjLt (b :: rest) h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst hx; exact h.1
    · exact Nat.lt_trans h.1 ((List.pairwise_cons.mp ih).1 x hx)

/-- Distinctness check in `O(n log n)`: sort, then compare neighbours. -/
def numsDistinct (nums : List Nat) : Bool :=
  adjLt (nums.mergeSort (fun a b => decide (a ≤ b)))

/-- `numsDistinct` is sound. -/
theorem nodup_of_numsDistinct (nums : List Nat) (h : numsDistinct nums = true) : nums.Nodup := by
  have hp := pairwise_of_adjLt _ h
  have hn : (nums.mergeSort (fun a b => decide (a ≤ b))).Nodup := hp.imp Nat.ne_of_lt
  exact (List.mergeSort_perm nums _).nodup_iff.mp hn

/-! ## The decoded object stream -/

/-- A decoded object stream (ISO 32000-2 §7.5.7) with its header invariants (O4). -/
structure ObjStm where
  /-- `/First`: offset of the first object in `data`. -/
  first : Nat
  /-- `/Extends`, if present: the reference `(num, gen)` to another object stream. -/
  extends? : Option (Nat × Nat)
  /-- The decoded stream data. -/
  data : ByteArray
  /-- The header pairs `(object number, offset relative to first)`, in header order. -/
  entries : List (Nat × Nat)
  /-- `/First` lies within the data. -/
  first_le : first ≤ data.size
  /-- Offsets strictly increasing (§7.5.7). -/
  sorted : (entries.map Prod.snd).Pairwise (· < ·)
  /-- Every object starts inside the data. -/
  bounded : ∀ e ∈ entries, first + e.2 < data.size
  /-- Object numbers are at least 1. -/
  numPos : ∀ e ∈ entries, 1 ≤ e.1
  /-- Object numbers are distinct (S6). -/
  distinct : (entries.map Prod.fst).Nodup

/-- Check the invariants of O4 and build the `ObjStm`. -/
def mkObjStm (first : Nat) (ext : Option (Nat × Nat)) (data : ByteArray)
    (entries : List (Nat × Nat)) : Except Error ObjStm :=
  if hf : first ≤ data.size then
    if hs : adjLt (entries.map Prod.snd) = true then
      if hb : entries.all (fun e => decide (first + e.2 < data.size)) = true then
        if hp : entries.all (fun e => decide (1 ≤ e.1)) = true then
          if hn : numsDistinct (entries.map Prod.fst) = true then
            .ok { first, extends? := ext, data, entries
                  first_le := hf
                  sorted := pairwise_of_adjLt _ hs
                  bounded := fun e he => of_decide_eq_true (List.all_eq_true.mp hb e he)
                  numPos := fun e he => of_decide_eq_true (List.all_eq_true.mp hp e he)
                  distinct := nodup_of_numsDistinct _ hn }
          else .error (.malformed 0 "object stream: duplicate object number")
        else .error (.malformed 0 "object stream: object number 0")
      else .error (.malformed 0 "object stream: object offset beyond the data")
    else .error (.malformed 0 "object stream: offsets not increasing")
  else .error (.malformed 0 "object stream: /First beyond the decoded data")

/-! ## Dictionary entries (O1, O2) -/

/-- `/Type` must be `/ObjStm`. -/
def checkType (d : Dict) : Except Error Unit :=
  match d.get? (Name.ofString "Type") with
  | some (.name n) =>
    if n = Name.ofString "ObjStm" then .ok ()
    else .error (.malformed 0 "object stream: /Type is not /ObjStm")
  | _ => .error (.malformed 0 "object stream: /Type is not /ObjStm")

/-- `/N`: an integer, `0 ≤ N ≤ limits.maxObjects`. -/
def getCount (limits : Limits) (d : Dict) : Except Error Nat :=
  match d.get? (Name.ofString "N") with
  | some (.int n) =>
    if n < 0 then .error (.malformed 0 "object stream: negative /N")
    else if n.toNat ≤ limits.maxObjects then .ok n.toNat
    else .error (.limitExceeded .objects)
  | _ => .error (.malformed 0 "object stream: /N missing or not an integer")

/-- `/First`: a non-negative integer. -/
def getFirst (d : Dict) : Except Error Nat :=
  match d.get? (Name.ofString "First") with
  | some (.int n) =>
    if n < 0 then .error (.malformed 0 "object stream: negative /First") else .ok n.toNat
  | _ => .error (.malformed 0 "object stream: /First missing or not an integer")

/-- `/Extends`: absent, or a reference (recorded, not followed). -/
def getExtends (d : Dict) : Except Error (Option (Nat × Nat)) :=
  match d.get? (Name.ofString "Extends") with
  | none => .ok none
  | some (.ref n g) => .ok (some (n, g))
  | some _ => .error (.malformed 0 "object stream: /Extends is not a reference")

/-- The single filter name, if any: `/F`, `[/F]`, absent or `[]`; chains are unsupported. -/
def filterName (d : Dict) : Except Error (Option Name) :=
  match d.get? (Name.ofString "Filter") with
  | none => .ok none
  | some (.name n) => .ok (some n)
  | some (.array []) => .ok none
  | some (.array [.name n]) => .ok (some n)
  | some _ => .error (.unsupported "object stream: filter chain")

/-- The predictor parameters dictionary: absent, a dictionary, or a one-element array. -/
def decodeParms (d : Dict) : Except Error Dict :=
  match d.get? (Name.ofString "DecodeParms") with
  | none => .ok []
  | some (.dict p) => .ok p
  | some (.array []) => .ok []
  | some (.array [.null]) => .ok []
  | some (.array [.dict p]) => .ok p
  | some _ => .error (.malformed 0 "object stream: /DecodeParms is not a dictionary")

/-- Decode the stream data (O2). -/
def decodeData (limits : Limits) (d : Dict) (raw : ByteArray) : Except Error ByteArray :=
  match filterName d with
  | .error e => .error e
  | .ok none => .ok raw
  | .ok (some n) =>
    if n = Name.ofString "FlateDecode" then
      match Filter.Flate.flateDecode limits raw with
      | .error e => .error e
      | .ok out =>
        match decodeParms d with
        | .error e => .error e
        | .ok parms =>
          match Filter.Predictor.Params.ofDict parms with
          | .error e => .error e
          | .ok p => Filter.Predictor.decode p out
    else .error (.unsupported "object stream: filter other than /FlateDecode")

/-! ## Header (O3) -/

/-- Read `k` more pairs `objnum offset` from the header bytes at `pos`, then require the end
of the header. Structural on `k`. -/
def parsePairs (hdr : ByteArray) : Nat → Nat → List (Nat × Nat) →
    Except Error (List (Nat × Nat))
  | 0, pos, acc =>
    match Lex.next hdr pos with
    | .ok none => .ok acc.reverse
    | .ok (some _) => .error (errAt hdr pos "object stream: header longer than /N pairs")
    | .error e => .error (lexErr e)
  | k + 1, pos, acc =>
    match Lex.next hdr pos with
    | .ok (some (.int n, q)) =>
      match Lex.next hdr q with
      | .ok (some (.int off, q2)) =>
        if 0 ≤ n ∧ 0 ≤ off then parsePairs hdr k q2 ((n.toNat, off.toNat) :: acc)
        else .error (errAt hdr pos "object stream: negative number in header")
      | .error e => .error (lexErr e)
      | .ok _ => .error (errAt hdr q "object stream: expected an offset in header")
    | .error e => .error (lexErr e)
    | .ok _ => .error (errAt hdr pos "object stream: expected an object number in header")

/-- **Entry point.** Decode an object stream (rules O1–O4). Does not follow `/Extends`. -/
def decodeObjStm (limits : Limits) (st : Stream) : Except Error ObjStm :=
  match checkType st.dict, getCount limits st.dict, getFirst st.dict, getExtends st.dict with
  | .ok (), .ok n, .ok first, .ok ext =>
    match decodeData limits st.dict st.data with
    | .error e => .error e
    | .ok data =>
      if first ≤ data.size then
        match parsePairs (data.extract 0 first) n 0 [] with
        | .error e => .error e
        | .ok entries => mkObjStm first ext data entries
      else .error (.malformed 0 "object stream: /First beyond the decoded data")
  | .error e, _, _, _ => .error e
  | _, .error e, _, _ => .error e
  | _, _, .error e, _ => .error e
  | _, _, _, .error e => .error e

/-! ## Objects (O5) -/

/-- End of the slice of the `k`-th object: the next object's start, or the end of the data. -/
def sliceEnd (os : ObjStm) (k : Nat) : Nat :=
  match os.entries[k + 1]? with
  | some (_, off') => os.first + off'
  | none => os.data.size

/-- **Entry point.** The `k`-th object of the stream (rule O5); generation implicitly 0. -/
def getObject (os : ObjStm) (limits : Limits) (k : Nat) : Except Error PdfObject :=
  match os.entries[k]? with
  | none => .error (.malformed 0 s!"object stream: index {k} out of range")
  | some (_, off) =>
    match ObjParse.parseObject limits os.data (os.first + off) with
    | .error e => .error e
    | .ok (o, r) =>
      if r ≤ sliceEnd os k then
        if sliceEnd os k ≤ Lex.skipWs os.data r false then .ok o
        else .error (.malformed r "object stream: data after the object (not a direct object)")
      else .error (.malformed r "object stream: object runs past the next object's offset")

/-- The index of object number `num` in the header, if present (unique, by `os.distinct`). -/
def findObject (os : ObjStm) (num : Nat) : Option Nat :=
  os.entries.findIdx? (fun e => e.1 == num)

/-! ## Fetching a compressed object (O6) -/

/-- An instrumented result: container parses and decodes performed, and the result. -/
structure Trace where
  /-- Number of `Length.parseIndirectResolved` calls on a container. -/
  parses : Nat
  /-- Number of `decodeObjStm` calls. -/
  decodes : Nat
  /-- The fetched object or an error. -/
  result : Except Error PdfObject

/-- `fetchCompressed` with its work counted (rule O6). Not recursive. -/
def fetchCompressedTrace (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel num : Nat) : Trace :=
  match lookup num with
  | some (.compressed c idx) =>
    if c = num then ⟨0, 0, .error (.cycle 0 s!"object {num} is its own object stream")⟩
    else
      match lookup c with
      | some (.inUse off g) =>
        if g = 0 then
          match Length.parseIndirectResolved lookup limits bytes fuel off with
          | .error e => ⟨1, 0, .error e⟩
          | .ok (io, _) =>
            if io.num = c ∧ io.gen = 0 then
              match io.body with
              | .obj _ =>
                ⟨1, 0, .error (.malformed off "object stream container is not a stream")⟩
              | .stream st =>
                match decodeObjStm limits st with
                | .error e => ⟨1, 1, .error e⟩
                | .ok os =>
                  if findObject os num = some idx then ⟨1, 1, getObject os limits idx⟩
                  else ⟨1, 1, .error (.malformed off
                    s!"object {num} is not at index {idx} of object stream {c}")⟩
            else ⟨1, 0, .error (.malformed off
              "object header does not match the cross-reference entry")⟩
        else ⟨0, 0, .error (.malformed off s!"object stream {c} has a non-zero generation")⟩
      | some (.compressed c' _) =>
        ⟨0, 0, .error (if c' = num then
          .cycle 0 s!"object streams {num} and {c} contain each other"
          else .malformed 0 s!"object stream {c} is itself in an object stream")⟩
      | some (.free _ _) => ⟨0, 0, .error (.malformed 0 s!"object stream {c} is free")⟩
      | none => ⟨0, 0, .error (.malformed 0 s!"object stream {c} is not in the xref")⟩
  | _ => ⟨0, 0, .error (.malformed 0 s!"object {num} is not in an object stream")⟩

/-- **Entry point.** Object `num`, stored in an object stream according to `lookup` (rule
O6). `fuel` bounds indirect `/Length` resolution of the container (callers pass the object
count). -/
def fetchCompressed (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel num : Nat) : Except Error PdfObject :=
  (fetchCompressedTrace lookup limits bytes fuel num).result

/-! ## Theorems -/

/-- **Sorted offsets** (§7.5.7 "in increasing order"), by construction. -/
theorem decodeObjStm_offsets_sorted {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : (os.entries.map Prod.snd).Pairwise (· < ·) :=
  os.sorted

/-- **Header bounds**: every object starts inside the decoded data. -/
theorem decodeObjStm_bounds {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : ∀ e ∈ os.entries, os.first + e.2 < os.data.size :=
  os.bounded

/-- `/First` lies within the decoded data. -/
theorem decodeObjStm_first_le {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : os.first ≤ os.data.size :=
  os.first_le

/-- Object numbers in the header are at least 1. -/
theorem decodeObjStm_nums_pos {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : ∀ e ∈ os.entries, 1 ≤ e.1 :=
  os.numPos

/-- Object numbers in the header are distinct (S6). -/
theorem decodeObjStm_nums_nodup {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : (os.entries.map Prod.fst).Nodup :=
  os.distinct

/-- `parsePairs` reads exactly `k` pairs. -/
theorem parsePairs_length (hdr : ByteArray) :
    (k pos : Nat) → (acc l : List (Nat × Nat)) → parsePairs hdr k pos acc = .ok l →
    l.length = k + acc.length
  | 0, pos, acc, l, h => by
    unfold parsePairs at h
    split at h
    · cases h; simp
    · cases h
    · cases h
  | k + 1, pos, acc, l, h => by
    unfold parsePairs at h
    split at h
    · split at h
      · split at h
        · have := parsePairs_length hdr k _ _ l h
          simp at this; omega
        · cases h
      · cases h
      · cases h
    · cases h
    · cases h

/-- `getCount` respects `limits.maxObjects`. -/
theorem getCount_le {limits : Limits} {d : Dict} {n : Nat} (h : getCount limits d = .ok n) :
    n ≤ limits.maxObjects := by
  unfold getCount at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h; assumption
      · cases h
  · cases h

/-- `mkObjStm` keeps the entries it was given. -/
theorem mkObjStm_entries {first : Nat} {ext : Option (Nat × Nat)} {data : ByteArray}
    {entries : List (Nat × Nat)} {os : ObjStm} (h : mkObjStm first ext data entries = .ok os) :
    os.entries = entries := by
  unfold mkObjStm at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- **Count bound**: at most `limits.maxObjects` objects (exactly `/N`). -/
theorem decodeObjStm_count_le {limits : Limits} {st : Stream} {os : ObjStm}
    (h : decodeObjStm limits st = .ok os) : os.entries.length ≤ limits.maxObjects := by
  unfold decodeObjStm at h
  split at h
  · next n first ext _ hn _ _ =>
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · next entries he =>
          have h1 := parsePairs_length _ _ _ _ _ he
          have h2 := mkObjStm_entries h
          have h3 := getCount_le hn
          rw [h2, h1]
          simpa using h3
      · cases h
  all_goals cases h

/-- **Depth bound**: an object from an object stream nests at most `limits.maxObjectDepth`. -/
theorem getObject_depth {os : ObjStm} {limits : Limits} {k : Nat} {o : PdfObject}
    (h : getObject os limits k = .ok o) : o.depth ≤ limits.maxObjectDepth := by
  unfold getObject at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hp
      split at h
      · split at h
        · cases h; exact ObjParse.parseObject_depth hp
        · cases h
      · cases h

/-- **Rank lemma / non-recursion** (Plan.md §5.2): a successful fetch went through exactly one
container `c ≠ num` whose entry is `inUse off 0`; a container is never itself compressed, so
the container chain has length one and no recursion is needed. -/
theorem fetchCompressed_no_recursion {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed lookup limits bytes fuel num = .ok o) :
    ∃ c idx off, lookup num = some (.compressed c idx) ∧ c ≠ num ∧
      lookup c = some (.inUse off 0) := by
  unfold fetchCompressed fetchCompressedTrace at h
  split at h
  · rename_i c idx hl
    split at h
    · cases h
    · rename_i hne
      split at h
      · rename_i off g hc
        split at h
        · rename_i hg
          subst hg
          exact ⟨c, idx, off, hl, hne, hc⟩
        · cases h
      · cases h
      · cases h
      · cases h
  · cases h

/-- The rank of an entry: 1 for an object in an object stream, 0 otherwise. -/
def entryRank : Option XrefEntry → Nat
  | some (.compressed _ _) => 1
  | _ => 0

/-- **Rank decreases**: on success the container's rank is strictly below the object's. -/
theorem fetchCompressed_rank {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed lookup limits bytes fuel num = .ok o) :
    ∃ c idx, lookup num = some (.compressed c idx) ∧
      entryRank (lookup c) < entryRank (lookup num) := by
  obtain ⟨c, idx, off, h1, _, h2⟩ := fetchCompressed_no_recursion h
  exact ⟨c, idx, h1, by simp [entryRank, h1, h2]⟩

/-- **Self-container**: an object claiming to live in an object stream with its own number
is an error. -/
theorem fetchCompressed_self (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num idx : Nat) (h : lookup num = some (.compressed num idx)) :
    ∃ e, fetchCompressed lookup limits bytes fuel num = .error e := by
  simp [fetchCompressed, fetchCompressedTrace, h]

/-- **Self-container is a cycle** (task 2.13): the error of `fetchCompressed_self` is
`Error.cycle`. -/
theorem fetchCompressed_self_cycle (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num idx : Nat) (h : lookup num = some (.compressed num idx)) :
    fetchCompressed lookup limits bytes fuel num =
      .error (.cycle 0 s!"object {num} is its own object stream") := by
  simp [fetchCompressed, fetchCompressedTrace, h]

/-- **Two object streams containing each other are a cycle** (task 2.13): `num` lies in
`c ≠ num` and `c` lies in `num`. -/
theorem fetchCompressed_mutual_cycle (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num c idx idx' : Nat)
    (h : lookup num = some (.compressed c idx)) (hc : lookup c = some (.compressed num idx'))
    (hne : c ≠ num) :
    fetchCompressed lookup limits bytes fuel num =
      .error (.cycle 0 s!"object streams {num} and {c} contain each other") := by
  simp [fetchCompressed, fetchCompressedTrace, h, hc, hne]

/-- **Nested container**: a container that is itself in an object stream is an error. -/
theorem fetchCompressed_nested (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num c idx c' idx' : Nat)
    (h : lookup num = some (.compressed c idx)) (hc : lookup c = some (.compressed c' idx')) :
    ∃ e, fetchCompressed lookup limits bytes fuel num = .error e := by
  by_cases hcn : c = num
  · subst hcn; exact fetchCompressed_self lookup limits bytes fuel c idx h
  · simp [fetchCompressed, fetchCompressedTrace, h, hc, hcn]

/-- **Work bound**: at most one container parse and one object-stream decode. -/
theorem fetchCompressed_work (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num : Nat) :
    (fetchCompressedTrace lookup limits bytes fuel num).parses ≤ 1 ∧
    (fetchCompressedTrace lookup limits bytes fuel num).decodes ≤ 1 := by
  unfold fetchCompressedTrace
  repeat' split
  all_goals simp

/-- **Depth bound** for fetched objects. -/
theorem fetchCompressed_depth {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed lookup limits bytes fuel num = .ok o) :
    o.depth ≤ limits.maxObjectDepth := by
  unfold fetchCompressed fetchCompressedTrace at h
  repeat' split at h
  all_goals first | cases h | exact getObject_depth h

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}:{m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o w => s!"cycle@{o}:{w}"

/-- Test helper: a stream from string keys. -/
private def mkSt (d : List (String × PdfObject)) (data : ByteArray) : Stream :=
  ⟨d.map (fun e => (Name.ofString e.1, e.2)), data⟩

/-- Test helper: `/Type /ObjStm /N n /First f` plus extra entries. -/
private def osDict (n first : Int) (extra : List (String × PdfObject) := []) :
    List (String × PdfObject) :=
  [("Type", PdfObject.nameOf "ObjStm"), ("N", .int n), ("First", .int first)] ++ extra

/-- Test helper: `decodeObjStm` summarised as its header entries. -/
private def dec (st : Stream) : Sum String (List (Nat × Nat)) :=
  match decodeObjStm Limits.default st with
  | .ok os => .inr os.entries
  | .error e => .inl (errS e)

/-- Test helper: decode, then fetch object `k`. -/
private def obj (st : Stream) (k : Nat) : Sum String PdfObject :=
  match decodeObjStm Limits.default st with
  | .ok os =>
    match getObject os Limits.default k with
    | .ok o => .inr o
    | .error e => .inl (errS e)
  | .error e => .inl (errS e)

/-- Test helper: `fetchCompressed` summarised. -/
private def fc (lookup : Nat → Option XrefEntry) (b : ByteArray) (num : Nat) :
    Sum String PdfObject :=
  match fetchCompressed lookup Limits.default b 100 num with
  | .ok o => .inr o
  | .error e => .inl (errS e)

/-- Test helper: lookup from an explicit list of entries. -/
private def mkLookup (l : List (Nat × XrefEntry)) : Nat → Option XrefEntry :=
  fun n => l.lookup n

/-- Three objects, uncompressed: header `10 0 11 11 12 19 `, `/First 17`. -/
private def raw3 : ByteArray := "10 0 11 11 12 19 << /A 1 >>\n[1 2 3]\n(hi)\n".toUTF8

/-- `raw3` compressed with Python's `zlib.compress` (scratch script, stdlib only). -/
private def z3 : ByteArray := ⟨#[120, 156, 51, 52, 80, 48, 80, 48, 52, 4, 35, 35, 5, 67, 75, 5,
  27, 27, 5, 125, 71, 5, 67, 5, 59, 59, 174, 104, 67, 5, 35, 5, 227, 88, 46, 141, 140, 76, 77,
  46, 0, 153, 183, 7, 166]⟩

/-- `raw3` padded with spaces to 44 bytes, PNG Up predictor (`/Columns 4`), then
`zlib.compress`. -/
private def zp : ByteArray := ⟨#[120, 156, 1, 55, 0, 200, 255, 2, 49, 48, 32, 48, 2, 239, 1, 17,
  240, 2, 17, 0, 239, 17, 2, 1, 239, 17, 8, 2, 238, 28, 11, 231, 2, 15, 5, 228, 17, 2, 241, 253,
  30, 217, 2, 59, 243, 226, 40, 2, 197, 2, 61, 216, 2, 8, 53, 12, 31, 2, 226, 184, 183, 247,
  190, 201, 18, 129]⟩

private def flate : List (String × PdfObject) := [("Filter", PdfObject.nameOf "FlateDecode")]

private def dictA : PdfObject := .dict [(Name.ofString "A", .int 1)]
private def arr123 : PdfObject := .array [.int 1, .int 2, .int 3]
private def strHi : PdfObject := .string "hi".toUTF8.toList

-- N = 3, raw
#guard dec (mkSt (osDict 3 17) raw3) == .inr [(10, 0), (11, 11), (12, 19)]
#guard obj (mkSt (osDict 3 17) raw3) 0 == .inr dictA
#guard obj (mkSt (osDict 3 17) raw3) 1 == .inr arr123
#guard obj (mkSt (osDict 3 17) raw3) 2 == .inr strHi
#guard obj (mkSt (osDict 3 17) raw3) 3 == .inl "malformed@0:object stream: index 3 out of range"
-- N = 3, Flate (also as a one-element filter array), and Flate + PNG predictor
#guard dec (mkSt (osDict 3 17 flate) z3) == .inr [(10, 0), (11, 11), (12, 19)]
#guard obj (mkSt (osDict 3 17 flate) z3) 2 == .inr strHi
#guard obj (mkSt (osDict 3 17 [("Filter", .array [PdfObject.nameOf "FlateDecode"])]) z3) 1 ==
  .inr arr123
#guard obj (mkSt (osDict 3 17 (flate ++ [("DecodeParms", .dict [(Name.ofString "Predictor",
  .int 12), (Name.ofString "Columns", .int 4)])])) zp) 2 == .inr strHi
-- N = 1 and N = 0
#guard dec (mkSt (osDict 1 4) "7 0 42".toUTF8) == .inr [(7, 0)]
#guard obj (mkSt (osDict 1 4) "7 0 42".toUTF8) 0 == .inr (.int 42)
#guard dec (mkSt (osDict 0 0) ByteArray.empty) == .inr []
#guard obj (mkSt (osDict 0 0) ByteArray.empty) 0 ==
  .inl "malformed@0:object stream: index 0 out of range"
-- /Extends is recorded
#guard (match decodeObjStm Limits.default
    (mkSt (osDict 1 4 [("Extends", .ref 9 0)]) "7 0 42".toUTF8) with
  | .ok os => os.extends? == some (9, 0)
  | .error _ => false)
-- decreasing offsets
#guard dec (mkSt (osDict 2 10) "10 5 11 0 42 43".toUTF8) ==
  .inl "malformed@0:object stream: offsets not increasing"
-- /First beyond the data; offset beyond the data
#guard dec (mkSt (osDict 3 100) raw3) ==
  .inl "malformed@0:object stream: /First beyond the decoded data"
#guard dec (mkSt (osDict 1 4) "7 9 42".toUTF8) ==
  .inl "malformed@0:object stream: object offset beyond the data"
-- object spilling past the next offset
#guard obj (mkSt (osDict 2 10) "10 0 11 3 [1 2 3]\n42".toUTF8) 0 ==
  .inl "malformed@17:object stream: object runs past the next object's offset"
#guard obj (mkSt (osDict 2 10) "10 0 11 8 [1 2 3]\n42".toUTF8) 1 == .inr (.int 42)
-- not a direct object: `n g obj` wrapper, `stream`
#guard obj (mkSt (osDict 1 4) "5 0 5 0 obj 1 endobj".toUTF8) 0 ==
  .inl "malformed@5:object stream: data after the object (not a direct object)"
#guard obj (mkSt (osDict 1 4) "5 0 << >> stream".toUTF8) 0 ==
  .inl "malformed@9:object stream: data after the object (not a direct object)"
-- duplicate object numbers; object number 0; header too short / too long
#guard dec (mkSt (osDict 2 10) "10 0 10 2 1 2".toUTF8) ==
  .inl "malformed@0:object stream: duplicate object number"
#guard dec (mkSt (osDict 1 4) "0 0 42".toUTF8) ==
  .inl "malformed@0:object stream: object number 0"
#guard (dec (mkSt (osDict 2 4) "7 0 42".toUTF8)).isLeft
#guard (dec (mkSt (osDict 1 8) "7 0 8 1 42".toUTF8)).isLeft
-- dictionary checks
#guard dec (mkSt [("Type", PdfObject.nameOf "XRef"), ("N", .int 0), ("First", .int 0)]
  ByteArray.empty) == .inl "malformed@0:object stream: /Type is not /ObjStm"
#guard dec (mkSt (osDict (-1) 0) ByteArray.empty) == .inl "malformed@0:object stream: negative /N"
#guard dec (mkSt (osDict 8388608 0) ByteArray.empty) == .inl "limit:SafePdf.LimitKind.objects"
#guard dec (mkSt (osDict 0 0 [("Filter", PdfObject.nameOf "ASCIIHexDecode")]) ByteArray.empty) ==
  .inl "unsupported:object stream: filter other than /FlateDecode"
#guard (dec (mkSt (osDict 3 17 flate) raw3)).isLeft

/-- A file holding object stream `20 0 obj` (Flate, the three objects of `raw3`) at offset 0. -/
private def file20 : ByteArray :=
  "20 0 obj\n<< /Type /ObjStm /N 3 /First 17 /Filter /FlateDecode /Length 45 >>\nstream\n".toUTF8
    ++ z3 ++ "\nendstream\nendobj\n".toUTF8

/-- Lookup for `file20`: objects 10–12 in stream 20. -/
private def lookup20 : Nat → Option XrefEntry :=
  mkLookup [(20, .inUse 0 0), (10, .compressed 20 0), (11, .compressed 20 1),
    (12, .compressed 20 2), (13, .compressed 20 1), (30, .compressed 31 0), (31, .compressed 20 0),
    (40, .compressed 41 0), (41, .inUse 0 0)]

-- valid fetches through the xref
#guard fc lookup20 file20 10 == .inr dictA
#guard fc lookup20 file20 11 == .inr arr123
#guard fc lookup20 file20 12 == .inr strHi
#guard (fetchCompressedTrace lookup20 Limits.default file20 100 12).parses == 1
#guard (fetchCompressedTrace lookup20 Limits.default file20 100 12).decodes == 1
-- xref index and stream header disagree (13 claims index 1, which holds object 11)
#guard fc lookup20 file20 13 == .inl "malformed@0:object 13 is not at index 1 of object stream 20"
-- nested container: 30 is in 31, which is itself in 20
#guard fc lookup20 file20 30 == .inl "malformed@0:object stream 31 is itself in an object stream"
-- two object streams containing each other: a cycle (task 2.13)
#guard fc (mkLookup [(50, .compressed 51 0), (51, .compressed 50 0)]) file20 50 ==
  .inl "cycle@0:object streams 50 and 51 contain each other"
-- container header mismatch: entry 41 points at `20 0 obj`
#guard fc lookup20 file20 40 ==
  .inl "malformed@0:object header does not match the cross-reference entry"
-- not compressed / missing
#guard (fc lookup20 file20 20).isLeft
#guard (fc lookup20 file20 99).isLeft
-- an uncompressed container, with an indirect /Length
#guard fc (mkLookup [(1, .inUse 0 0), (2, .inUse 87 0), (7, .compressed 1 0)])
  ("1 0 obj\n<< /Type /ObjStm /N 1 /First 4 /Length 2 0 R >>\nstream\n7 0 42\nendstream\nendobj\n"
    ++ "2 0 obj 6 endobj\n").toUTF8 7 == .inr (.int 42)

/-- Bytes of `Tests/adversarial/objstm-self-container.pdf` (378 B, SHA-256 `91dcdb06…41ea`):
the xref stream (object 4 at offset 223) marks object 5 as type 2 in object stream 5. -/
private def selfContainerPdf : ByteArray := ⟨#[
  37, 80, 68, 70, 45, 49, 46, 55, 10, 37, 226, 227, 207, 211, 10, 49, 32, 48, 32, 111, 98, 106,
  10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103, 32, 47, 80, 97,
  103, 101, 115, 32, 50, 32, 48, 32, 82, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 50, 32,
  48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 115, 32,
  47, 75, 105, 100, 115, 32, 91, 51, 32, 48, 32, 82, 93, 32, 47, 67, 111, 117, 110, 116, 32, 49,
  32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 51, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32,
  47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 32, 47, 80, 97, 114, 101, 110, 116, 32, 50,
  32, 48, 32, 82, 32, 47, 77, 101, 100, 105, 97, 66, 111, 120, 32, 91, 48, 32, 48, 32, 54, 49,
  50, 32, 55, 57, 50, 93, 32, 47, 82, 111, 116, 97, 116, 101, 32, 53, 32, 48, 32, 82, 32, 47, 82,
  101, 115, 111, 117, 114, 99, 101, 115, 32, 60, 60, 32, 62, 62, 32, 62, 62, 10, 101, 110, 100,
  111, 98, 106, 10, 52, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47,
  88, 82, 101, 102, 32, 47, 83, 105, 122, 101, 32, 54, 32, 47, 87, 32, 91, 49, 32, 52, 32, 50,
  93, 32, 47, 82, 111, 111, 116, 32, 49, 32, 48, 32, 82, 32, 47, 76, 101, 110, 103, 116, 104, 32,
  52, 50, 32, 62, 62, 10, 115, 116, 114, 101, 97, 109, 10, 0, 0, 0, 0, 0, 255, 255, 1, 0, 0, 0,
  15, 0, 0, 1, 0, 0, 0, 64, 0, 0, 1, 0, 0, 0, 121, 0, 0, 1, 0, 0, 0, 223, 0, 0, 2, 0, 0, 0, 5, 0,
  0, 10, 101, 110, 100, 115, 116, 114, 101, 97, 109, 10, 101, 110, 100, 111, 98, 106, 10, 115,
  116, 97, 114, 116, 120, 114, 101, 102, 10, 50, 50, 51, 10, 37, 37, 69, 79, 70, 10
]⟩

/-- Lookup decoded by hand from the file's xref stream (`/W [1 4 2]`, `/Size 6`). -/
private def selfContainerLookup : Nat → Option XrefEntry :=
  mkLookup [(0, .free 0 65535), (1, .inUse 15 0), (2, .inUse 64 0), (3, .inUse 121 0),
    (4, .inUse 223 0), (5, .compressed 5 0)]

#guard selfContainerPdf.size == 378
#guard fc selfContainerLookup selfContainerPdf 5 ==
  .inl "cycle@0:object 5 is its own object stream"
#guard (fetchCompressedTrace selfContainerLookup Limits.default selfContainerPdf 6 5).parses == 0
-- pointing object 5 at the xref stream instead: a container that is not /Type /ObjStm
#guard fc (mkLookup [(4, .inUse 223 0), (5, .compressed 4 0)]) selfContainerPdf 5 ==
  .inl "malformed@0:object stream: /Type is not /ObjStm"

end Tests

end SafePdf.Core.Xref.ObjStm
