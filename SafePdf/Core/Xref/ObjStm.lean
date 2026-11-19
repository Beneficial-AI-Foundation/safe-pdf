import SafePdf.Core.Xref
import SafePdf.Core.Xref.ObjStmDecode
import SafePdf.Core.Xref.Length
import SafePdf.Core.Filter.Structural

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

O1–O5 (dictionary, filters, header, offsets, objects) are in `Core.Xref.ObjStmDecode`
(`decodeObjStm`, `getObject`, `findObject`; split out in task 2.14 so that
`Core.Xref.Length` can follow a `/Length` into an object stream). This module adds:

* O6. `fetchCompressed pre lookup limits bytes fuel num`: the entry of `num` must be
  `compressed c idx` with `c ≠ num` (else `Error.cycle`); the entry of `c` must be
  `inUse off 0` (a compressed container is "nested", an error: `Error.cycle` when it is
  `compressed num _`, the two-object cycle, else `malformed`); the object at `off` is parsed with
  `Length.parseIndirectResolved` (indirect `/Length` resolved with `fuel`), its header must be
  `c 0` and its body a stream; it is decoded by O1–O4; `findObject os num` must equal `idx`
  (the xref index and the stream header agree); then O5 with `k = idx`.

* O7. (task 4.3b) Before O1–O4, the container stream passes through `pre.f c` (a `Pre`):
  the decryption of an encrypted file's object stream (ISO 32000-2 §7.6.2: the stream is
  encrypted, the objects inside are not encrypted again), `Pre.id` otherwise. A failing pass
  is the fetch's error. (`Pre` is defined in `Core.Xref.ObjStmDecode`, task 4.6, so that
  `Core.Xref.Length` applies the same pass to a container it decodes, rule L6.)

Error offsets for header and object errors are positions in the *decoded* data; dictionary
errors use offset 0, container errors the container's file offset.

## Theorems

* Totality by construction: `fetchCompressed` is not recursive (the `/Length` of its
  container is resolved by `Length.resolveLength`, bounded by its fuel).
* Decoding theorems (`decodeObjStm_*`, `getObject_depth`): `Core.Xref.ObjStmDecode`.
* `fetchCompressed_depth`: depth at most `limits.maxObjectDepth`.
* `fetchCompressed_self`, `fetchCompressed_nested`: a self-container or a compressed
  container is an error; `fetchCompressed_self_cycle`, `fetchCompressed_mutual_cycle`: for a
  self-container and for two object streams containing each other it is `Error.cycle`.
* `fetchCompressed_no_recursion`, `fetchCompressed_rank`: success implies the chain
  `num ↦ compressed c ↦ inUse off 0` with `c ≠ num` (rank 1 → rank 0).
* `fetchCompressed_work`: at most one container parse and one decode
  (`fetchCompressedTrace` counts them; `fetchCompressed` is its result).
* Task 3.13: `decodeObjStmB` and `fetchCompressedB` charge the decode against a
  `Filter.Budget` and cache decoded containers (`Cache`): `fetchCompressedB_eq` (an exact
  cache and enough budget return what `fetchCompressed` returns), `fetchCompressedB_hit`,
  `_le`, `_cost`, `_depth` (section "Budgeted decoding and the object-stream cache").
-/

namespace SafePdf.Core.Xref.ObjStm

open SafePdf
open SafePdf.Core.Xref (XrefEntry)

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
def fetchCompressedTrace (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel num : Nat) : Trace :=
  match lookup num with
  | some (.compressed c idx) =>
    if c = num then ⟨0, 0, .error (.cycle 0 s!"object {num} is its own object stream")⟩
    else
      match lookup c with
      | some (.inUse off g) =>
        if g = 0 then
          match Length.parseIndirectResolved lookup limits bytes fuel off pre with
          | .error e => ⟨1, 0, .error e⟩
          | .ok (io, _) =>
            if io.num = c ∧ io.gen = 0 then
              match io.body with
              | .obj _ =>
                ⟨1, 0, .error (.malformed off "object stream container is not a stream")⟩
              | .stream st0 =>
                match pre.f c st0 with
                | .error e => ⟨1, 0, .error e⟩
                | .ok st =>
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
def fetchCompressed (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel num : Nat) : Except Error PdfObject :=
  (fetchCompressedTrace pre lookup limits bytes fuel num).result

/-! ## Theorems -/

/-- **Rank lemma / non-recursion** (Plan.md §5.2): a successful fetch went through exactly one
container `c ≠ num` whose entry is `inUse off 0`; a container is never itself compressed, so
the container chain has length one and no recursion is needed. -/
theorem fetchCompressed_no_recursion {pre : Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed pre lookup limits bytes fuel num = .ok o) :
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
theorem fetchCompressed_rank {pre : Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed pre lookup limits bytes fuel num = .ok o) :
    ∃ c idx, lookup num = some (.compressed c idx) ∧
      entryRank (lookup c) < entryRank (lookup num) := by
  obtain ⟨c, idx, off, h1, _, h2⟩ := fetchCompressed_no_recursion h
  exact ⟨c, idx, h1, by simp [entryRank, h1, h2]⟩

/-- **Self-container**: an object claiming to live in an object stream with its own number
is an error. -/
theorem fetchCompressed_self (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num idx : Nat) (h : lookup num = some (.compressed num idx)) :
    ∃ e, fetchCompressed pre lookup limits bytes fuel num = .error e := by
  simp [fetchCompressed, fetchCompressedTrace, h]

/-- **Self-container is a cycle** (task 2.13): the error of `fetchCompressed_self` is
`Error.cycle`. -/
theorem fetchCompressed_self_cycle (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num idx : Nat) (h : lookup num = some (.compressed num idx)) :
    fetchCompressed pre lookup limits bytes fuel num =
      .error (.cycle 0 s!"object {num} is its own object stream") := by
  simp [fetchCompressed, fetchCompressedTrace, h]

/-- **Two object streams containing each other are a cycle** (task 2.13): `num` lies in
`c ≠ num` and `c` lies in `num`. -/
theorem fetchCompressed_mutual_cycle (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num c idx idx' : Nat)
    (h : lookup num = some (.compressed c idx)) (hc : lookup c = some (.compressed num idx'))
    (hne : c ≠ num) :
    fetchCompressed pre lookup limits bytes fuel num =
      .error (.cycle 0 s!"object streams {num} and {c} contain each other") := by
  simp [fetchCompressed, fetchCompressedTrace, h, hc, hne]

/-- **Nested container**: a container that is itself in an object stream is an error. -/
theorem fetchCompressed_nested (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num c idx c' idx' : Nat)
    (h : lookup num = some (.compressed c idx)) (hc : lookup c = some (.compressed c' idx')) :
    ∃ e, fetchCompressed pre lookup limits bytes fuel num = .error e := by
  by_cases hcn : c = num
  · subst hcn; exact fetchCompressed_self pre lookup limits bytes fuel c idx h
  · simp [fetchCompressed, fetchCompressedTrace, h, hc, hcn]

/-- **Work bound**: at most one container parse and one object-stream decode. -/
theorem fetchCompressed_work (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num : Nat) :
    (fetchCompressedTrace pre lookup limits bytes fuel num).parses ≤ 1 ∧
    (fetchCompressedTrace pre lookup limits bytes fuel num).decodes ≤ 1 := by
  unfold fetchCompressedTrace
  repeat' split
  all_goals simp

/-- **Depth bound** for fetched objects. -/
theorem fetchCompressed_depth {pre : Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed pre lookup limits bytes fuel num = .ok o) :
    o.depth ≤ limits.maxObjectDepth := by
  unfold fetchCompressed fetchCompressedTrace at h
  repeat' split at h
  all_goals first | cases h | exact getObject_depth h

/-! ## Budgeted decoding and the object-stream cache (task 3.13)

`decodeObjStmB` is `decodeObjStm` with its decode charged against the document budget
(`Filter.decodeBytesB`). `fetchCompressedB` is `fetchCompressedTrace` with a budget and a
`Cache` of decoded containers: a container is decoded (and charged) once; later fetches of its
members reuse the decoded `ObjStm` and cost nothing. Only successful decodes are cached; a
failed decode is charged again on every attempt (rule B2), which drains the budget, so the
work stays bounded.

* `decodeObjStmB_le`, `decodeObjStmB_cost`, `decodeObjStmB_eq`: never increases the budget;
  costs at most `(maxFilters + 1) · (maxDecodedStreamBytes + data size)`; with at least that
  much left, returns what `decodeObjStm` returns.
* `fetchCompressedB_le`, `fetchCompressedB_cost`: never increases the budget; one fetch costs
  at most `(maxFilters + 1) · (maxDecodedStreamBytes + bytes.size)` (one container decode at
  most; none on a cache hit, `fetchCompressedB_hit`).
* `fetchCompressedB_eq`: **the cache returns what `fetchCompressed` would**: if every cached
  container is the exact decode of the container its number names (`CacheExact`) and the
  budget covers one decode, `fetchCompressedB` returns exactly `fetchCompressed`'s result and
  the cache stays exact.
* `fetchCompressedB_depth`: depth bound.
-/

open SafePdf.Core.Filter (Budget)

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

/-- Decoded object streams of one document, by container object number (newest first). -/
abbrev Cache := List (Nat × ObjStm)

/-- The cached decode of container `c`, if any (the newest entry). -/
def Cache.find? : Cache → Nat → Option ObjStm
  | [], _ => none
  | (k, os) :: rest, c => if k = c then some os else Cache.find? rest c

/-- Member `num` at index `idx` of the decoded object stream `os` (container `c` at `off`):
the header index check, then the object (rule O6, after the decode). -/
def selectMember (os : ObjStm) (limits : Limits) (off c num idx : Nat) :
    Except Error PdfObject :=
  if findObject os num = some idx then getObject os limits idx
  else .error (.malformed off s!"object {num} is not at index {idx} of object stream {c}")

/-- **Budgeted, cached fetch** (task 3.13): `fetchCompressedTrace` (rule O6) with the
container decode charged against `budget` (`decodeObjStmB`) and done at most once per
container: a container found in `cache` is not parsed nor decoded again. Returns the
result, the budget and the cache (the new decode added). -/
def fetchCompressedB (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel num : Nat) (budget : Budget) (cache : Cache) :
    (Except Error PdfObject) × Budget × Cache :=
  match lookup num with
  | some (.compressed c idx) =>
    if c = num then (.error (.cycle 0 s!"object {num} is its own object stream"), budget, cache)
    else
      match lookup c with
      | some (.inUse off g) =>
        if g = 0 then
          match cache.find? c with
          | some os => (selectMember os limits off c num idx, budget, cache)
          | none =>
            match Length.parseIndirectResolved lookup limits bytes fuel off pre with
            | .error e => (.error e, budget, cache)
            | .ok (io, _) =>
              if io.num = c ∧ io.gen = 0 then
                match io.body with
                | .obj _ =>
                  (.error (.malformed off "object stream container is not a stream"), budget,
                    cache)
                | .stream st0 =>
                  match pre.f c st0 with
                  | .error e => (.error e, budget, cache)
                  | .ok st =>
                    match decodeObjStmB limits budget st with
                    | (.error e, b1) => (.error e, b1, cache)
                    | (.ok os, b1) => (selectMember os limits off c num idx, b1, (c, os) :: cache)
              else (.error (.malformed off
                "object header does not match the cross-reference entry"), budget, cache)
        else (.error (.malformed off s!"object stream {c} has a non-zero generation"), budget,
          cache)
      | some (.compressed c' _) =>
        (.error (if c' = num then
          .cycle 0 s!"object streams {num} and {c} contain each other"
          else .malformed 0 s!"object stream {c} is itself in an object stream"), budget, cache)
      | some (.free _ _) => (.error (.malformed 0 s!"object stream {c} is free"), budget, cache)
      | none => (.error (.malformed 0 s!"object stream {c} is not in the xref"), budget, cache)
  | _ => (.error (.malformed 0 s!"object {num} is not in an object stream"), budget, cache)

/-- `fetchCompressedB` never increases the budget. -/
theorem fetchCompressedB_le (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num : Nat) (budget : Budget) (cache : Cache) :
    (fetchCompressedB pre lookup limits bytes fuel num budget cache).2.1.remaining ≤
      budget.remaining := by
  unfold fetchCompressedB
  repeat' split
  all_goals first
    | exact Nat.le_refl _
    | (rename_i hd; have := decodeObjStmB_le limits budget ‹_›; rw [hd] at this; exact this)
    | skip

/-- **Cost of one fetch**: at most one container decode,
`(maxFilters + 1) · (maxDecodedStreamBytes + bytes.size)`. -/
theorem fetchCompressedB_cost (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num : Nat) (budget : Budget) (cache : Cache) :
    budget.remaining ≤ (fetchCompressedB pre lookup limits bytes fuel num budget cache).2.1.remaining +
      (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + bytes.size) := by
  have hK : ∀ st : Stream, st.data.size ≤ bytes.size →
      (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + st.data.size) ≤
        (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + bytes.size) :=
    fun st hs => Nat.mul_le_mul_left _ (by omega)
  unfold fetchCompressedB
  rcases hn : lookup num with _ | (⟨_, _⟩ | ⟨_, _⟩ | ⟨c, idx⟩)
  all_goals simp only
  all_goals try exact Nat.le_add_right _ _
  by_cases hcn : c = num
  · simp only [hcn, ↓reduceIte]; exact Nat.le_add_right _ _
  · simp only [hcn, ↓reduceIte]
    rcases hcl : lookup c with _ | (⟨_, _⟩ | ⟨off, g⟩ | ⟨_, _⟩)
    all_goals simp only
    all_goals try exact Nat.le_add_right _ _
    by_cases hg : g = 0
    · simp only [hg, ↓reduceIte]
      rcases hf : cache.find? c with _ | os
      · simp only
        rcases hp : Length.parseIndirectResolved lookup limits bytes fuel off pre with e | ⟨io, r⟩
        · exact Nat.le_add_right _ _
        · simp only
          split
          · rcases hb : io.body with o | st0
            · exact Nat.le_add_right _ _
            · simp only
              have hd := Length.parseIndirectResolved_data hp hb
              rcases hpre : pre.f c st0 with e | st
              · exact Nat.le_add_right _ _
              simp only
              have hle : st.data.size ≤ bytes.size := by
                have := pre.le c st0 st hpre; omega
              have hc := decodeObjStmB_cost limits budget st
              have hk := hK st hle
              rcases hds : decodeObjStmB limits budget st with ⟨r1, b1⟩
              rw [hds] at hc
              rcases r1 with e | os <;> (simp only at hc ⊢; omega)
          · exact Nat.le_add_right _ _
      · exact Nat.le_add_right _ _
    · simp only [hg, ↓reduceIte]; exact Nat.le_add_right _ _

/-- **A cache hit costs nothing**: when the container of `num` is cached, the member is
selected from the cached decode and the budget and the cache are unchanged. -/
theorem fetchCompressedB_hit {pre : Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num c idx off : Nat} {budget : Budget} {cache : Cache}
    {os : ObjStm} (hn : lookup num = some (.compressed c idx)) (hne : c ≠ num)
    (hc : lookup c = some (.inUse off 0)) (hf : cache.find? c = some os) :
    fetchCompressedB pre lookup limits bytes fuel num budget cache =
      (selectMember os limits off c num idx, budget, cache) := by
  simp [fetchCompressedB, hn, hne, hc, hf]

/-- **Exact cache**: every cached container `c` is the decode (`decodeObjStm`, unbudgeted) of
the stream object that the cross-reference entry of `c` points at, read as
`fetchCompressedTrace` reads it. -/
def CacheExact (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel : Nat) (cache : Cache) : Prop :=
  ∀ c os, cache.find? c = some os → ∃ off io r st0 st, lookup c = some (.inUse off 0) ∧
    Length.parseIndirectResolved lookup limits bytes fuel off pre = .ok (io, r) ∧
    io.num = c ∧ io.gen = 0 ∧ io.body = .stream st0 ∧ pre.f c st0 = .ok st ∧
    decodeObjStm limits st = .ok os

/-- The empty cache is exact. -/
theorem cacheExact_nil (pre : Pre) (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel : Nat) : CacheExact pre lookup limits bytes fuel [] := by
  intro c os h; simp [Cache.find?] at h

/-- **The cache returns what `fetchCompressed` would** (task 3.13): with an exact cache and at
least one decode's worth of budget, `fetchCompressedB` returns exactly `fetchCompressed`'s
result, and the cache stays exact. -/
theorem fetchCompressedB_eq {pre : Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {budget : Budget} {cache : Cache}
    (hc : CacheExact pre lookup limits bytes fuel cache)
    (h : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + bytes.size) ≤
      budget.remaining) :
    (fetchCompressedB pre lookup limits bytes fuel num budget cache).1 =
      fetchCompressed pre lookup limits bytes fuel num ∧
    CacheExact pre lookup limits bytes fuel (fetchCompressedB pre lookup limits bytes fuel num budget cache).2.2 := by
  unfold fetchCompressedB fetchCompressed fetchCompressedTrace
  rcases hn : lookup num with _ | (⟨_, _⟩ | ⟨_, _⟩ | ⟨c, idx⟩)
  all_goals simp only
  all_goals try exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩
  by_cases hcn : c = num
  · simp only [hcn, ↓reduceIte]; exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩
  · simp only [hcn, ↓reduceIte]
    rcases hcl : lookup c with _ | (⟨_, _⟩ | ⟨off, g⟩ | ⟨_, _⟩)
    all_goals simp only
    all_goals try exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩
    by_cases hg : g = 0
    · subst hg
      simp only [↓reduceIte]
      rcases hf : cache.find? c with _ | os
      · simp only
        rcases hp : Length.parseIndirectResolved lookup limits bytes fuel off pre with e | ⟨io, r⟩
        · exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩
        · simp only
          by_cases hh : io.num = c ∧ io.gen = 0
          · simp only [hh, and_self, ↓reduceIte]
            rcases hb : io.body with o | st0
            · exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩
            · simp only
              have hd := Length.parseIndirectResolved_data hp hb
              rcases hpre : pre.f c st0 with e | st
              · exact ⟨rfl, hc⟩
              simp only
              have hle : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + st.data.size) ≤
                  budget.remaining :=
                Nat.le_trans (Nat.mul_le_mul_left _ (by have := pre.le c st0 st hpre; omega)) h
              have he := decodeObjStmB_eq (budget := budget) hle
              rcases hds : decodeObjStmB limits budget st with ⟨r1, b1⟩
              rw [hds] at he
              simp only at he
              rw [← he]
              rcases r1 with e | os
              · exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩
              · refine ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), ?_⟩
                intro c' os' hf'
                simp only [Cache.find?] at hf'
                by_cases hk : c = c'
                · subst hk
                  simp only [↓reduceIte, Option.some.injEq] at hf'
                  subst hf'
                  exact ⟨off, io, r, st0, st, hcl, hp, hh.1, hh.2, hb, hpre, he.symm⟩
                · simp only [hk, ↓reduceIte] at hf'
                  exact hc c' os' hf'
          · simp only [hh, ↓reduceIte]; exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩
      · simp only
        obtain ⟨off', io, r, st0, st, hl', hp, hnum, hgen, hb, hpre, hd⟩ := hc c os hf
        rw [hcl] at hl'
        simp only [Option.some.injEq, XrefEntry.inUse.injEq] at hl'
        obtain ⟨rfl, -⟩ := hl'
        simp only [hp, hnum, hgen, and_self, ↓reduceIte, hb, hpre, hd]
        exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩
    · simp only [hg, ↓reduceIte]; exact ⟨by first | rfl | trivial | (simp only [selectMember]; split <;> rfl), hc⟩

/-- **Depth bound** for objects fetched by `fetchCompressedB`. -/
theorem fetchCompressedB_depth {pre : Pre} {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {budget : Budget} {cache : Cache} {o : PdfObject}
    (h : (fetchCompressedB pre lookup limits bytes fuel num budget cache).1 = .ok o) :
    o.depth ≤ limits.maxObjectDepth := by
  have hs : ∀ os off c idx, selectMember os limits off c num idx = .ok o →
      o.depth ≤ limits.maxObjectDepth := by
    intro os off c idx hm
    unfold selectMember at hm
    split at hm
    · exact getObject_depth hm
    · cases hm
  unfold fetchCompressedB at h
  repeat' split at h
  all_goals first | cases h | exact hs _ _ _ _ h

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}:{m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o w => s!"cycle@{o}:{w}"
  | .encryption w => s!"encryption:{w}"


/-- Test helper: `fetchCompressed` summarised. -/
private def fc (lookup : Nat → Option XrefEntry) (b : ByteArray) (num : Nat) :
    Sum String PdfObject :=
  match fetchCompressed Pre.id lookup Limits.default b 100 num with
  | .ok o => .inr o
  | .error e => .inl (errS e)

/-- Test helper: lookup from an explicit list of entries. -/
private def mkLookup (l : List (Nat × XrefEntry)) : Nat → Option XrefEntry :=
  fun n => l.lookup n

/-- `raw3` (see `ObjStmDecode`) compressed with Python's `zlib.compress`. -/
private def z3 : ByteArray := ⟨#[120, 156, 51, 52, 80, 48, 80, 48, 52, 4, 35, 35, 5, 67, 75, 5,
  27, 27, 5, 125, 71, 5, 67, 5, 59, 59, 174, 104, 67, 5, 35, 5, 227, 88, 46, 141, 140, 76, 77,
  46, 0, 153, 183, 7, 166]⟩


private def dictA : PdfObject := .dict [(Name.ofString "A", .int 1)]
private def arr123 : PdfObject := .array [.int 1, .int 2, .int 3]
private def strHi : PdfObject := .string "hi".toUTF8.toList


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
#guard (fetchCompressedTrace Pre.id lookup20 Limits.default file20 100 12).parses == 1
#guard (fetchCompressedTrace Pre.id lookup20 Limits.default file20 100 12).decodes == 1
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
#guard (fetchCompressedTrace Pre.id selfContainerLookup Limits.default selfContainerPdf 6 5).parses == 0
-- pointing object 5 at the xref stream instead: a container that is not /Type /ObjStm
#guard fc (mkLookup [(4, .inUse 223 0), (5, .compressed 4 0)]) selfContainerPdf 5 ==
  .inl "malformed@0:object stream: /Type is not /ObjStm"

/-! ### Budgeted, cached fetches (task 3.13) -/

/-- Test helper: fetch `nums` in order from a budget of `n` bytes and an empty cache; the
results, the budget left and the cached containers. -/
private def fcb (lookup : Nat → Option XrefEntry) (b : ByteArray) (n : Nat) (nums : List Nat) :
    List (Sum String PdfObject) × Nat × List Nat :=
  let (rs, bud, cache) := nums.foldl (init := (([] : List (Sum String PdfObject)),
      (⟨n⟩ : Filter.Budget), ([] : Cache)))
    fun (rs, bud, cache) num =>
      let (r, bud', cache') := fetchCompressedB Pre.id lookup Limits.default b 100 num bud cache
      let r' : Sum String PdfObject := match r with
        | .ok o => .inr o
        | .error e => .inl (errS e)
      (rs ++ [r'], bud', cache')
  (rs, bud.remaining, cache.map Prod.fst)

-- one decode of container 20 (41 bytes charged), then three cache hits; only it is cached
#guard fcb lookup20 file20 1000 [10, 11, 12, 13] ==
  ([.inr dictA, .inr arr123, .inr strHi,
    .inl "malformed@0:object 13 is not at index 1 of object stream 20"], 959, [20])
-- not enough budget: the total-budget error, charged its cap; nothing cached
#guard fcb lookup20 file20 10 [10, 11] ==
  ([.inl "limit:SafePdf.LimitKind.decodedTotalBytes",
    .inl "limit:SafePdf.LimitKind.decodedTotalBytes"], 0, [])
-- structural errors are found before any decode and cost nothing
#guard fcb lookup20 file20 1000 [30, 40, 99] ==
  ([.inl "malformed@0:object stream 31 is itself in an object stream",
    .inl "malformed@0:object header does not match the cross-reference entry",
    .inl "malformed@0:object 99 is not in an object stream"], 1000, [])

end Tests

end SafePdf.Core.Xref.ObjStm