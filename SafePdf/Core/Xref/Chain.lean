import SafePdf.Core.Xref
import SafePdf.Core.Xref.Stream
import SafePdf.Core.Filter.Structural

/-!
# The `/Prev` chain of incremental updates

Plan.md §5.2 (first bullet), §4 S2/S3/S6, §6 Phase 2; ISO 32000-2 §7.5.5 (trailer `/Prev`)
and §7.5.6 (incremental updates); Bogk & Schöpl 2014 (cyclic `/Prev` chains hang readers).

Task 2.2, extended by 2.4a. A file updated incrementally has one cross-reference section per
revision; the trailer of each points with `/Prev` at the byte offset of the previous section.
`loadChain` starts at the `startxref` offset (`Core.Xref.findStartxref`), parses the section
there (`parseSection`: a classic table, `Core.Xref.parseXrefTable`, if the bytes are `xref`,
otherwise an xref stream, `Core.Xref.Stream.parseXrefStream`) and follows `/Prev` until a
trailer has none, newest revision first. `mergeChain` folds the revisions into one section in
which the newest entry wins per object number (S6 preview; the full unambiguity theorem is
task 2.5).

## Hybrid files (ISO 32000-2 §7.5.8.4)

A classic table whose trailer has `/XRefStm` is followed by the xref stream at that offset
*within the same step*: the revisions list gets the table, then the stream, then whatever
the table's `/Prev` leads to. Since `mergeChain` lets the earlier revision win, an object is
looked up first in the table, then in its `/XRefStm` stream, then in the older sections.
This is the search order of §7.5.8.4 ("the entries in the table first, then the
cross-reference stream, then `/Prev`"): the table wins over its own stream (as in pdf.js and
MuPDF), and the stream supplies the objects the table omits (typically those in object
streams). The stream's own `/Prev` and `/XRefStm`, and `/XRefStm` in an xref stream's
dictionary, are ignored. An `/XRefStm` offset counts as visited exactly like a `/Prev`
offset: it must be inside the input, not visited before (else `Error.cycle s "xref /XRefStm cycle"`) and
within the revision budget.

## Termination by the visited set (Plan.md §5.2)

The loop `walk` carries the list `visited` of offsets already parsed, together with the
proofs that it is duplicate-free and that every element is `< bytes.size`. Each round runs
`step`, which checks `off < bytes.size` (else `Error.malformed`, `/Prev` offsets are not
range-checked by 2.1) and `off ∉ visited` (else `Error.cycle off "xref /Prev cycle"`):
**a revisited offset is an error, not a loop**; for a hybrid table it checks the `/XRefStm`
offset the same way against `off :: visited`. `step` returns its revisions in a `StepOk`
whose fields prove that the new offsets are fresh, distinct and inside the input, and that
there is at least one. The measure is `bytes.size - visited.length`, the number of unvisited
offsets; it strictly decreases because a duplicate-free list of naturals below `n` has length
`≤ n` (`length_le_of_nodup_of_lt`) and every round adds at least one offset. No `partial`,
no fuel.

Independently the number of sections parsed is bounded by `limits.maxRevisions` (default
4096, `SafePdf.Limits`), whose excess yields `Error.limitExceeded .revisions`; an `/XRefStm`
stream counts as a revision.

`walk` also returns the number of section parses (tables and streams) it made, so that
`Spec.XrefTerm` can state the work bound.

## Budgeted loading (task 3.13)

`loadChainB` is `loadChain` with each xref-stream decode charged against a `Filter.Budget`
(`parseXrefStreamB`; `loadChainB_le`, `loadChainB_cost`); with at least
`maxRevisions · decodeAllowance` left it returns exactly `loadChain`'s result
(`loadChainB_eq`), so the theorems of `Spec.XrefTerm`, `Spec.Unambiguous` and
`Spec.PrefixStable` about `loadChain` carry over. Section "Budgeted loading" below.

## Not done here

* Object numbers of classic tables are not checked against `/Size` (task 2.5); xref streams
  check theirs (`Core.Xref.Stream`, XS4).
* Repair when a `/Prev` or `/XRefStm` offset is off by a few bytes (task 2.6).
-/

namespace SafePdf.Core.Xref.Chain

open SafePdf SafePdf.Core.Xref

/-! ## The counting lemma behind the measure -/

/-- A duplicate-free list of naturals all below `n` has at most `n` elements (it is a
subset of `List.range n`). -/
theorem length_le_of_nodup_of_lt {l : List Nat} {n : Nat} (hnd : l.Nodup)
    (hlt : ∀ x ∈ l, x < n) : l.length ≤ n := by
  have hsub : l ⊆ List.range n := fun x hx => List.mem_range.2 (hlt x hx)
  have := hnd.length_le_of_subset hsub
  simpa using this

/-- **The heart of the termination proof.** If `visited` is duplicate-free with all elements
below `n`, and `off < n` is fresh, then `visited.length < n`: some offset is still unvisited. -/
theorem length_lt_of_fresh {visited : List Nat} {n off : Nat} (hnd : visited.Nodup)
    (hlt : ∀ x ∈ visited, x < n) (hoff : off < n) (hfresh : off ∉ visited) :
    visited.length < n := by
  have h := length_le_of_nodup_of_lt (l := off :: visited) (n := n)
    (List.nodup_cons.2 ⟨hfresh, hnd⟩)
    (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hoff
      · exact hlt x hx)
  simp at h
  omega

/-! ## Loading the chain -/

/-- One revision of the file: its cross-reference section, its trailer, and the byte offset
of its `xref` keyword (classic table) or of its `n g obj` (xref stream). -/
abbrev Revision := XrefSection × Trailer × Nat

/-- The byte offset of a revision's section. -/
def Revision.offset (r : Revision) : Nat := r.2.2

/-- The cross-reference section at `o`: a classic table if the bytes at `o` are `xref`,
otherwise an xref stream (ISO 32000-2 §7.5.4, §7.5.8). -/
def parseSection (limits : Limits) (bytes : ByteArray) (o : Nat) :
    Except Error (XrefSection × Trailer) :=
  if matchAt bytes o kwXref then
    match parseXrefTable limits bytes o with
    | .ok (sec, tr, _) => .ok (sec, tr)
    | .error e => .error e
  else Stream.parseXrefStream limits bytes o

/-- The `/XRefStm` offset of a hybrid file (§7.5.8.4): only a classic table's trailer has
one; an xref stream's own `/XRefStm` key is ignored. -/
def hybridStm (bytes : ByteArray) (o : Nat) (tr : Trailer) : Option Nat :=
  if matchAt bytes o kwXref then tr.xrefStm? else none

/-- The successful result of one step of the walk from the visited list `visited`: the
revisions parsed (the section, then its `/XRefStm` stream if any), the `/Prev` to follow, and
the invariants the walk needs: the new offsets are fresh, distinct and inside the input. -/
structure StepOk (bytes : ByteArray) (visited : List Nat) where
  /-- The revisions of this step, newest first (1 or 2). -/
  revs : List Revision
  /-- The section's `/Prev`. -/
  prev? : Option Nat
  /-- The new offsets, followed by the old ones, are distinct. -/
  nodup : (revs.map Revision.offset ++ visited).Nodup
  /-- The new offsets lie inside the input. -/
  lt : ∀ x ∈ revs.map Revision.offset, x < bytes.size
  /-- At least one revision was parsed. -/
  ne : revs ≠ []

/-- One step of the walk at `off`: check `off` (inside the input, not visited, revision
budget), parse the section there, and for a hybrid file's classic table also the `/XRefStm`
stream (under the same checks, `off` counting as visited). Returns the step result and the
number of section parses made (0, 1 or 2). The stream's own `/Prev` is not followed: the
chain continues with the table's `/Prev`. -/
def step (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) :
    Except Error (StepOk bytes visited) × Nat :=
  if hoff : off < bytes.size then
    if hmem : off ∈ visited then (.error (.cycle off "xref /Prev cycle"), 0)
    else if limits.maxRevisions ≤ visited.length then (.error (.limitExceeded .revisions), 0)
    else
      match parseSection limits bytes off with
      | .error e => (.error e, 1)
      | .ok (sec, tr) =>
        match hybridStm bytes off tr with
        | none =>
          (.ok ⟨[(sec, tr, off)], tr.prev?,
            by simp only [List.map_cons, List.map_nil, Revision.offset, List.cons_append,
              List.nil_append, List.nodup_cons]; exact ⟨hmem, hnd⟩,
            by simp only [List.map_cons, List.map_nil, Revision.offset, List.mem_singleton]
               intro x hx; subst hx; exact hoff,
            by simp⟩, 1)
        | some s =>
          if hs : s < bytes.size then
            if hsm : s = off ∨ s ∈ visited then (.error (.cycle s "xref /XRefStm cycle"), 1)
            else if limits.maxRevisions ≤ visited.length + 1 then
              (.error (.limitExceeded .revisions), 1)
            else
              match Stream.parseXrefStream limits bytes s with
              | .error e => (.error e, 2)
              | .ok (sec2, tr2) =>
                (.ok ⟨[(sec, tr, off), (sec2, tr2, s)], tr.prev?, by
                    simp only [List.map_cons, List.map_nil, Revision.offset, List.cons_append,
                      List.nil_append, List.nodup_cons, List.mem_cons, not_or]
                    exact ⟨⟨fun h => hsm (Or.inl h.symm), hmem⟩,
                      ⟨fun h => hsm (Or.inr h), hnd⟩⟩, by
                    simp only [List.map_cons, List.map_nil, Revision.offset, List.mem_cons,
                      List.not_mem_nil, or_false]
                    intro x hx
                    rcases hx with rfl | rfl
                    · exact hoff
                    · exact hs, by simp⟩, 2)
          else (.error (.malformed s "xref /XRefStm offset beyond end of input"), 1)
  else (.error (.malformed off "xref /Prev offset beyond end of input"), 0)

/-- Follow the chain from `off`. `visited` holds the offsets parsed so far (newest first),
duplicate-free and inside the input. Each round runs one `step` (the section at `off` and,
for a hybrid file, its `/XRefStm` stream), then follows the section's `/Prev` with the new
offsets added to `visited`. Returns the revisions from `off` on, newest first (a hybrid
table is immediately followed by its `/XRefStm` stream), and the number of section parses
(tables and streams) made.

Errors: an offset `≥ bytes.size` (malformed), an offset already visited (`Error.cycle`,
`"xref /Prev cycle"` resp. `"xref /XRefStm cycle"`), more than `limits.maxRevisions`
revisions (`limitExceeded .revisions`), or a parse error. -/
def walk (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size) :
    Except Error (List Revision) × Nat :=
  match step limits bytes off visited hnd with
  | (.error e, k) => (.error e, k)
  | (.ok so, k) =>
    match so.prev? with
    | none => (.ok so.revs, k)
    | some p =>
      match walk limits bytes p (so.revs.map Revision.offset ++ visited) so.nodup
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact so.lt x hx
            · exact hlt x hx) with
      | (.error e, k') => (.error e, k' + k)
      | (.ok rest, k') => (.ok (so.revs ++ rest), k' + k)
termination_by bytes.size - visited.length
decreasing_by
  have h1 := length_le_of_nodup_of_lt so.nodup (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact so.lt x hx
    · exact hlt x hx)
  have h2 : 0 < so.revs.length := List.length_pos_iff.mpr so.ne
  simp only [List.length_append, List.length_map] at h1 ⊢
  omega

/-- `loadChain` with the number of section parses (tables and streams) made. -/
def loadChainCounted (limits : Limits) (bytes : ByteArray) :
    Except Error (List Revision) × Nat :=
  match findStartxref bytes with
  | .error e => (.error e, 0)
  | .ok off => walk limits bytes off [] List.nodup_nil (fun _ hx => absurd hx List.not_mem_nil)

/-- **Entry point.** All revisions of a classic-xref file, newest first: the section at the
`startxref` offset, then the one its `/Prev` points at, and so on (ISO 32000-2 §7.5.6).
A cyclic `/Prev` chain is an error (Bogk & Schöpl 2014). -/
def loadChain (limits : Limits) (bytes : ByteArray) : Except Error (List Revision) :=
  (loadChainCounted limits bytes).1

/-! ## Budgeted loading (task 3.13)

`loadChainB limits budget bytes` is `loadChain` with every cross-reference-stream decode
charged against the document budget (`Filter.Budget`, rules B1–B5 of `Core.Filter`): the
section parser `parseSectionB` runs `parseXrefStreamB`, which is `Stream.parseXrefStream`
(split into `xrefStreamPre`, the decode, and `xrefStreamPost`, `parseXrefStream_split`) with
the decode done by `Filter.decodeBytesB`. Classic tables decode nothing and are free. The
walk (`stepB`, `walkB`) is `step`/`walk` with the budget threaded through; it has the same
checks in the same order, so the same termination measure.

* `loadChainB_le`: the budget never grows.
* `parseXrefStreamB_cost`: one section parse costs at most `decodeAllowance limits bytes`
  `= (maxFilters + 1) · (maxDecodedStreamBytes + bytes.size)`.
* `loadChainB_eq`: **with at least `maxRevisions · decodeAllowance` left, `loadChainB`
  returns exactly what `loadChain` returns** (so every theorem about `loadChain` applies).
  With less, it may stop earlier with `Error.limitExceeded .decodedTotalBytes` (or a
  per-stream error under the lowered cap); that is the point of the budget.
-/

open SafePdf.Core.Filter (Budget)

/-- The most one structural decode of a stream of `bytes` can charge
(`Filter.decodeBytesB_cost`; the raw data of a stream lies within the input). -/
def decodeAllowance (limits : Limits) (bytes : ByteArray) : Nat :=
  (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + bytes.size)

/-- The stream data of an object parsed by `ObjParse.parseIndirect` lies within the input. -/
theorem parseIndirect_data_le {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {io : IndirectObject} {r : Nat} {st : Stream}
    (h : ObjParse.parseIndirect limits bytes pos = .ok (io, r)) (hs : io.body = .stream st) :
    st.data.size ≤ bytes.size := by
  unfold ObjParse.parseIndirect at h
  split at h
  · cases h
  · split at h
    · rename_i b r' hb
      cases h
      unfold ObjParse.parseIndirectBody at hb
      obtain ⟨_, _, hall⟩ := ObjParse.parseIndirectBodyWith_ok hb
      obtain ⟨s0, _, hle, _⟩ := hall st hs
      omega
    · cases h

/-- What `Stream.parseXrefStream` reads before decoding: the stream dictionary, the raw data,
the trailer, the widths, the subsections and the entry count. -/
abbrev XrefStreamHead :=
  Dict × ByteArray × Trailer × (Nat × Nat × Nat) × List (Nat × Nat) × Nat

/-- The part of `Stream.parseXrefStream` before the decode (XS1–XS4, the `/Index` and object
count checks), verbatim. -/
def xrefStreamPre (limits : Limits) (bytes : ByteArray) (off : Nat) :
    Except Error XrefStreamHead := do
  if !digitAt bytes off then
    throw (.malformed off "expected an xref keyword or an xref stream object")
  let (io, _) ← ObjParse.parseIndirect limits bytes off
  let st ← match io.body with
    | .stream st => pure st
    | .obj _ => throw (.malformed off "xref section is not a stream")
  let d := st.dict
  if d.get? Stream.nameType != some (.name Stream.nameXRef) then
    throw (.malformed off "xref stream without /Type /XRef")
  let tr ← Trailer.ofDict d off
  let (w1, w2, w3) ← Stream.widths d off
  let subs ← Stream.index d tr.size off
  if subs.any (fun sc => tr.size < sc.1 + sc.2) then
    throw (.malformed off "xref stream /Index subsection not below /Size")
  let total := (subs.map Prod.snd).sum
  if limits.maxObjects < total then throw (.limitExceeded .objects)
  pure (d, st.data, tr, (w1, w2, w3), subs, total)

/-- The part of `Stream.parseXrefStream` after the decode (XS6–XS8), verbatim. -/
def xrefStreamPost (bytes : ByteArray) (off : Nat) (h : XrefStreamHead) (data : ByteArray) :
    Except Error (XrefSection × Trailer) := do
  let (_, _, tr, (w1, w2, w3), subs, total) := h
  if data.size != total * (w1 + w2 + w3) then
    throw (.malformed off s!"xref stream data has {data.size} bytes, expected {total * (w1 + w2 + w3)}")
  let acc ← Stream.subsections bytes.size tr.size off data ⟨w1, w2, w3⟩ 0 subs []
  match mkSection acc with
  | none => throw (.malformed off "duplicate object number in cross-reference stream")
  | some sec => pure (sec, tr)

/-- **`parseXrefStream` split at its decode**: head, `Stream.decodeData`, tail. -/
theorem parseXrefStream_split (limits : Limits) (bytes : ByteArray) (off : Nat) :
    Stream.parseXrefStream limits bytes off =
      match xrefStreamPre limits bytes off with
      | .error e => .error e
      | .ok h =>
        match Stream.decodeData limits h.1 h.2.1 off with
        | .error e => .error e
        | .ok data => xrefStreamPost bytes off h data := by
  simp only [Stream.parseXrefStream, xrefStreamPre, xrefStreamPost, bind, Except.bind, pure,
    Except.pure, throw, throwThe, MonadExceptOf.throw]
  cases hd : digitAt bytes off
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hp : ObjParse.parseIndirect limits bytes off with
    | error e => simp
    | ok p =>
      obtain ⟨io, r⟩ := p
      simp only
      cases hb : io.body with
      | obj o => simp
      | stream st =>
        simp only
        cases ht : (st.dict.get? Stream.nameType != some (.name Stream.nameXRef))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases htr : Trailer.ofDict st.dict off with
          | error e => simp
          | ok tr =>
            simp only
            cases hw : Stream.widths st.dict off with
            | error e => simp
            | ok w =>
              obtain ⟨w1, w2, w3⟩ := w
              simp only
              cases hi : Stream.index st.dict tr.size off with
              | error e => simp
              | ok subs =>
                simp only
                cases ha : subs.any (fun sc => decide (tr.size < sc.1 + sc.2))
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  by_cases hm : limits.maxObjects < (subs.map Prod.snd).sum
                  · simp [hm]
                  · simp only [hm, ↓reduceIte]
                    cases Stream.decodeData limits st.dict st.data off <;> rfl
                · simp
        · simp

/-- The raw data in an xref-stream head lies within the input. -/
theorem xrefStreamPre_data_le {limits : Limits} {bytes : ByteArray} {off : Nat}
    {h : XrefStreamHead} (hp : xrefStreamPre limits bytes off = .ok h) :
    h.2.1.size ≤ bytes.size := by
  simp only [xrefStreamPre, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hp
  cases hd : digitAt bytes off
  · simp [hd] at hp
  · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
    cases hpi : ObjParse.parseIndirect limits bytes off with
    | error e => simp [hpi] at hp
    | ok p =>
      obtain ⟨io, r⟩ := p
      simp only [hpi] at hp
      cases hb : io.body with
      | obj o => simp [hb] at hp
      | stream st =>
        have hle := parseIndirect_data_le hpi hb
        simp only [hb] at hp
        repeat' split at hp
        all_goals first | (cases hp; done) | (cases hp; exact hle) | (simp at hp)

/-- `Stream.decodeData` with the budget (rule XS5 of `Core.Xref.Stream`): no `/Crypt` stage,
no image codec; the decode is `Filter.decodeBytesB`. -/
def decodeXrefDataB (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (at_ : Nat) : (Except Error ByteArray) × Budget :=
  match Filter.parseChain limits d with
  | .error e => (.error e, budget)
  | .ok stages =>
    if stages.any Filter.Stage.isCrypt then
      (.error (.malformed at_ "xref stream with a /Crypt filter (xref streams are not encrypted)"),
        budget)
    else Filter.decodeBytesB limits budget d raw (.malformed at_ "xref stream with an image filter")

/-- `decodeXrefDataB` never increases the budget. -/
theorem decodeXrefDataB_le (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (at_ : Nat) : (decodeXrefDataB limits budget d raw at_).2.remaining ≤ budget.remaining := by
  unfold decodeXrefDataB
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · exact Filter.decodeBytesB_le _ _ _ _ _ _

/-- Cost of `decodeXrefDataB`: at most `(maxFilters + 1) · (maxDecodedStreamBytes + raw.size)`. -/
theorem decodeXrefDataB_cost (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (at_ : Nat) : budget.remaining ≤ (decodeXrefDataB limits budget d raw at_).2.remaining +
      (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) := by
  unfold decodeXrefDataB
  split
  · exact Nat.le_add_right _ _
  · split
    · exact Nat.le_add_right _ _
    · exact Filter.decodeBytesB_cost _ _ _ _ _ _

/-- Budget large enough ⇒ `decodeXrefDataB` returns what `Stream.decodeData` returns. -/
theorem decodeXrefDataB_eq {limits : Limits} {budget : Budget} {d : Dict} {raw : ByteArray}
    {at_ : Nat}
    (h : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + raw.size) ≤ budget.remaining) :
    (decodeXrefDataB limits budget d raw at_).1 = Stream.decodeData limits d raw at_ := by
  unfold decodeXrefDataB Stream.decodeData
  cases hp : Filter.parseChain limits d with
  | error e => rfl
  | ok stages =>
    simp only
    split
    · rfl
    · exact Filter.decodeBytesB_eq h

/-- **Budgeted xref stream** (task 3.13): `Stream.parseXrefStream` with its decode charged
(`decodeXrefDataB`). Returns the budget also on failure. -/
def parseXrefStreamB (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat) :
    (Except Error (XrefSection × Trailer)) × Budget :=
  match xrefStreamPre limits bytes off with
  | .error e => (.error e, budget)
  | .ok h =>
    let p := decodeXrefDataB limits budget h.1 h.2.1 off
    (match p.1 with
     | .error e => .error e
     | .ok data => xrefStreamPost bytes off h data, p.2)

/-- `parseXrefStreamB` never increases the budget. -/
theorem parseXrefStreamB_le (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat) :
    (parseXrefStreamB limits budget bytes off).2.remaining ≤ budget.remaining := by
  unfold parseXrefStreamB
  split
  · exact Nat.le_refl _
  · exact decodeXrefDataB_le _ _ _ _ _

/-- **Cost of one xref stream**: at most `decodeAllowance limits bytes`. -/
theorem parseXrefStreamB_cost (limits : Limits) (budget : Budget) (bytes : ByteArray)
    (off : Nat) : budget.remaining ≤ (parseXrefStreamB limits budget bytes off).2.remaining +
      decodeAllowance limits bytes := by
  unfold parseXrefStreamB
  split
  · exact Nat.le_add_right _ _
  · rename_i h hp
    have h1 := decodeXrefDataB_cost limits budget h.1 h.2.1 off
    have h2 := xrefStreamPre_data_le hp
    have h3 : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + h.2.1.size) ≤
        decodeAllowance limits bytes :=
      Nat.mul_le_mul_left _ (by omega)
    simp only
    omega

/-- **Budget large enough ⇒ same xref stream**: with at least `decodeAllowance limits bytes`
left, `parseXrefStreamB` returns what `Stream.parseXrefStream` returns. -/
theorem parseXrefStreamB_eq {limits : Limits} {budget : Budget} {bytes : ByteArray} {off : Nat}
    (h : decodeAllowance limits bytes ≤ budget.remaining) :
    (parseXrefStreamB limits budget bytes off).1 = Stream.parseXrefStream limits bytes off := by
  rw [parseXrefStream_split]
  unfold parseXrefStreamB
  split
  · rfl
  · rename_i hd hp
    have h2 := xrefStreamPre_data_le hp
    have h3 : (limits.maxFilters + 1) * (limits.maxDecodedStreamBytes + hd.2.1.size) ≤
        budget.remaining :=
      Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) h
    simp only
    rw [decodeXrefDataB_eq h3]

/-- `parseSection` with the budget: a classic table is free, an xref stream is
`parseXrefStreamB`. -/
def parseSectionB (limits : Limits) (budget : Budget) (bytes : ByteArray) (o : Nat) :
    (Except Error (XrefSection × Trailer)) × Budget :=
  if matchAt bytes o kwXref then
    (match parseXrefTable limits bytes o with
     | .ok (sec, tr, _) => .ok (sec, tr)
     | .error e => .error e, budget)
  else parseXrefStreamB limits budget bytes o

/-- `parseSectionB` never increases the budget. -/
theorem parseSectionB_le (limits : Limits) (budget : Budget) (bytes : ByteArray) (o : Nat) :
    (parseSectionB limits budget bytes o).2.remaining ≤ budget.remaining := by
  unfold parseSectionB
  split
  · exact Nat.le_refl _
  · exact parseXrefStreamB_le _ _ _ _

/-- Cost of `parseSectionB`: at most `decodeAllowance limits bytes`. -/
theorem parseSectionB_cost (limits : Limits) (budget : Budget) (bytes : ByteArray) (o : Nat) :
    budget.remaining ≤ (parseSectionB limits budget bytes o).2.remaining +
      decodeAllowance limits bytes := by
  unfold parseSectionB
  split
  · exact Nat.le_add_right _ _
  · exact parseXrefStreamB_cost _ _ _ _

/-- Budget large enough ⇒ `parseSectionB` returns what `parseSection` returns. -/
theorem parseSectionB_eq {limits : Limits} {budget : Budget} {bytes : ByteArray} {o : Nat}
    (h : decodeAllowance limits bytes ≤ budget.remaining) :
    (parseSectionB limits budget bytes o).1 = parseSection limits bytes o := by
  unfold parseSectionB parseSection
  split
  · rfl
  · exact parseXrefStreamB_eq h

/-- `step` with the budget threaded through (same checks, same order; the section parses
are `parseSectionB` and `parseXrefStreamB`). -/
def stepB (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat)
    (visited : List Nat) (hnd : visited.Nodup) :
    (Except Error (StepOk bytes visited) × Nat) × Budget :=
  if hoff : off < bytes.size then
    if hmem : off ∈ visited then ((.error (.cycle off "xref /Prev cycle"), 0), budget)
    else if limits.maxRevisions ≤ visited.length then
      ((.error (.limitExceeded .revisions), 0), budget)
    else
      match parseSectionB limits budget bytes off with
      | (.error e, b1) => ((.error e, 1), b1)
      | (.ok (sec, tr), b1) =>
        match hybridStm bytes off tr with
        | none =>
          ((.ok ⟨[(sec, tr, off)], tr.prev?,
            by simp only [List.map_cons, List.map_nil, Revision.offset, List.cons_append,
              List.nil_append, List.nodup_cons]; exact ⟨hmem, hnd⟩,
            by simp only [List.map_cons, List.map_nil, Revision.offset, List.mem_singleton]
               intro x hx; subst hx; exact hoff,
            by simp⟩, 1), b1)
        | some s =>
          if hs : s < bytes.size then
            if hsm : s = off ∨ s ∈ visited then ((.error (.cycle s "xref /XRefStm cycle"), 1), b1)
            else if limits.maxRevisions ≤ visited.length + 1 then
              ((.error (.limitExceeded .revisions), 1), b1)
            else
              match parseXrefStreamB limits b1 bytes s with
              | (.error e, b2) => ((.error e, 2), b2)
              | (.ok (sec2, tr2), b2) =>
                ((.ok ⟨[(sec, tr, off), (sec2, tr2, s)], tr.prev?, by
                    simp only [List.map_cons, List.map_nil, Revision.offset, List.cons_append,
                      List.nil_append, List.nodup_cons, List.mem_cons, not_or]
                    exact ⟨⟨fun h => hsm (Or.inl h.symm), hmem⟩,
                      ⟨fun h => hsm (Or.inr h), hnd⟩⟩, by
                    simp only [List.map_cons, List.map_nil, Revision.offset, List.mem_cons,
                      List.not_mem_nil, or_false]
                    intro x hx
                    rcases hx with rfl | rfl
                    · exact hoff
                    · exact hs, by simp⟩, 2), b2)
          else ((.error (.malformed s "xref /XRefStm offset beyond end of input"), 1), b1)
  else ((.error (.malformed off "xref /Prev offset beyond end of input"), 0), budget)

/-- `stepB` never increases the budget. -/
theorem stepB_le (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat)
    (visited : List Nat) (hnd : visited.Nodup) :
    (stepB limits budget bytes off visited hnd).2.remaining ≤ budget.remaining := by
  unfold stepB
  have h1 := parseSectionB_le limits budget bytes off
  split
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · rcases hps : parseSectionB limits budget bytes off with ⟨r1, b1⟩
        rw [hps] at h1
        simp only at h1
        rcases r1 with e | ⟨sec, tr⟩
        · exact h1
        · simp only
          rcases hh : hybridStm bytes off tr with _ | s
          · exact h1
          · simp only
            split
            · split
              · exact h1
              · split
                · exact h1
                · have h2 := parseXrefStreamB_le limits b1 bytes s
                  rcases hps2 : parseXrefStreamB limits b1 bytes s with ⟨r2, b2⟩
                  rw [hps2] at h2
                  simp only at h2
                  rcases r2 with e | ⟨sec2, tr2⟩
                  · exact Nat.le_trans h2 h1
                  · exact Nat.le_trans h2 h1
            · exact h1
  · exact Nat.le_refl _

/-- Arithmetic of the walk's budget invariant: after a charge of at most `K` from at least
`a · K` (`a ≥ 1`), at least `(a - 1) · K` is left. -/
theorem budget_step {a K r r' : Nat} (h : a * K ≤ r) (ha : 1 ≤ a) (hc : r ≤ r' + K) :
    (a - 1) * K ≤ r' := by
  have : a * K = (a - 1) * K + K := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
  omega

/-- **Budget large enough ⇒ same step**, and the walk's budget invariant is kept: with at
least `(maxRevisions - visited.length) · decodeAllowance` left, `stepB` returns what `step`
returns, and after a successful step at least
`(maxRevisions - (visited.length + revs.length)) · decodeAllowance` is left. -/
theorem stepB_eq (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat)
    (visited : List Nat) (hnd : visited.Nodup)
    (h : (limits.maxRevisions - visited.length) * decodeAllowance limits bytes ≤ budget.remaining) :
    (stepB limits budget bytes off visited hnd).1 = step limits bytes off visited hnd ∧
    ∀ so k, (stepB limits budget bytes off visited hnd).1 = (.ok so, k) →
      (limits.maxRevisions - (visited.length + so.revs.length)) * decodeAllowance limits bytes ≤
        (stepB limits budget bytes off visited hnd).2.remaining := by
  have hK0 : ∀ a, 1 ≤ a → a * decodeAllowance limits bytes ≤ budget.remaining →
      decodeAllowance limits bytes ≤ budget.remaining := fun a ha h' => by
    have : 1 * decodeAllowance limits bytes ≤ a * decodeAllowance limits bytes :=
      Nat.mul_le_mul_right _ ha
    omega
  unfold stepB step
  by_cases hoff : off < bytes.size
  · simp only [hoff, dite_true]
    by_cases hmem : off ∈ visited
    · simp [hmem]
    · simp only [hmem, dite_false]
      by_cases hrev : limits.maxRevisions ≤ visited.length
      · simp [hrev]
      · simp only [hrev, ↓reduceIte]
        have hK1 := hK0 _ (by omega) h
        have he1 := parseSectionB_eq (o := off) hK1
        have hc1 := parseSectionB_cost limits budget bytes off
        rcases hps : parseSectionB limits budget bytes off with ⟨r1, b1⟩
        rw [hps] at he1 hc1
        simp only at he1 hc1
        subst he1
        have hb1 := budget_step h (by omega) hc1
        cases hsec : parseSection limits bytes off with
        | error e => simp
        | ok p =>
          obtain ⟨sec, tr⟩ := p
          simp only
          cases hh : hybridStm bytes off tr with
          | none =>
            refine ⟨rfl, ?_⟩
            intro so k hso
            simp only [Prod.mk.injEq, Except.ok.injEq] at hso
            obtain ⟨rfl, rfl⟩ := hso
            simp only [List.length_cons, List.length_nil]
            have : limits.maxRevisions - (visited.length + (0 + 1)) =
                limits.maxRevisions - visited.length - 1 := by omega
            rw [this]; exact hb1
          | some s =>
            simp only
            by_cases hs : s < bytes.size
            · simp only [hs, dite_true]
              by_cases hsm : s = off ∨ s ∈ visited
              · simp [hsm]
              · simp only [hsm, dite_false]
                by_cases hrev2 : limits.maxRevisions ≤ visited.length + 1
                · simp [hrev2]
                · simp only [hrev2, ↓reduceIte]
                  have hK2 : decodeAllowance limits bytes ≤ b1.remaining := by
                    have : 1 * decodeAllowance limits bytes ≤
                        (limits.maxRevisions - visited.length - 1) *
                          decodeAllowance limits bytes :=
                      Nat.mul_le_mul_right _ (by omega)
                    omega
                  have he2 := parseXrefStreamB_eq (off := s) hK2
                  have hc2 := parseXrefStreamB_cost limits b1 bytes s
                  rcases hps2 : parseXrefStreamB limits b1 bytes s with ⟨r2, b2⟩
                  rw [hps2] at he2 hc2
                  simp only at he2 hc2
                  subst he2
                  have hb2 := budget_step hb1 (by omega) hc2
                  cases hst : Stream.parseXrefStream limits bytes s with
                  | error e => simp
                  | ok q =>
                    obtain ⟨sec2, tr2⟩ := q
                    refine ⟨rfl, ?_⟩
                    intro so k hso
                    simp only [Prod.mk.injEq, Except.ok.injEq] at hso
                    obtain ⟨rfl, rfl⟩ := hso
                    simp only [List.length_cons, List.length_nil]
                    have : limits.maxRevisions - (visited.length + (0 + 1 + 1)) =
                        limits.maxRevisions - visited.length - 1 - 1 := by omega
                    rw [this]; exact hb2
            · simp [hs]
  · simp [hoff]

/-- `walk` with the budget threaded through (`stepB`; same recursion, same measure). -/
def walkB (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat)
    (visited : List Nat) (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size) :
    (Except Error (List Revision) × Nat) × Budget :=
  match stepB limits budget bytes off visited hnd with
  | ((.error e, k), b1) => ((.error e, k), b1)
  | ((.ok so, k), b1) =>
    match so.prev? with
    | none => ((.ok so.revs, k), b1)
    | some p =>
      match walkB limits b1 bytes p (so.revs.map Revision.offset ++ visited) so.nodup
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact so.lt x hx
            · exact hlt x hx) with
      | ((.error e, k'), b2) => ((.error e, k' + k), b2)
      | ((.ok rest, k'), b2) => ((.ok (so.revs ++ rest), k' + k), b2)
termination_by bytes.size - visited.length
decreasing_by
  have h1 := length_le_of_nodup_of_lt so.nodup (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact so.lt x hx
    · exact hlt x hx)
  have h2 : 0 < so.revs.length := List.length_pos_iff.mpr so.ne
  simp only [List.length_append, List.length_map] at h1 ⊢
  omega

/-- `walkB` never increases the budget. -/
theorem walkB_le (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat)
    (visited : List Nat) (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size) :
    (walkB limits budget bytes off visited hnd hlt).2.remaining ≤ budget.remaining := by
  rw [walkB]
  have h1 := stepB_le limits budget bytes off visited hnd
  rcases hs : stepB limits budget bytes off visited hnd with ⟨⟨r1, k⟩, b1⟩
  rw [hs] at h1
  simp only at h1
  rcases r1 with e | so
  · exact h1
  · simp only
    rcases hp : so.prev? with _ | p
    · exact h1
    · simp only
      have h2 := walkB_le limits b1 bytes p (so.revs.map Revision.offset ++ visited) so.nodup
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact so.lt x hx
          · exact hlt x hx)
      rcases hw : walkB limits b1 bytes p (so.revs.map Revision.offset ++ visited) so.nodup
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact so.lt x hx
          · exact hlt x hx) with ⟨⟨r2, k'⟩, b2⟩
      rw [hw] at h2
      simp only at h2
      rcases r2 with e | rest
      · exact Nat.le_trans h2 h1
      · exact Nat.le_trans h2 h1
termination_by bytes.size - visited.length
decreasing_by
  have h1 := length_le_of_nodup_of_lt so.nodup (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact so.lt x hx
    · exact hlt x hx)
  have h2 : 0 < so.revs.length := List.length_pos_iff.mpr so.ne
  simp only [List.length_append, List.length_map] at h1 ⊢
  omega

/-- **Budget large enough ⇒ same walk**: with at least
`(maxRevisions - visited.length) · decodeAllowance` left, `walkB` returns what `walk`
returns. -/
theorem walkB_eq (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat)
    (visited : List Nat) (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size)
    (h : (limits.maxRevisions - visited.length) * decodeAllowance limits bytes ≤ budget.remaining) :
    (walkB limits budget bytes off visited hnd hlt).1 = walk limits bytes off visited hnd hlt := by
  rw [walkB, walk]
  obtain ⟨he, hinv⟩ := stepB_eq limits budget bytes off visited hnd h
  rcases hs : stepB limits budget bytes off visited hnd with ⟨⟨r1, k⟩, b1⟩
  rw [hs] at he hinv
  simp only at he hinv
  rw [← he]
  rcases r1 with e | so
  · rfl
  · simp only
    have hb := hinv so k rfl
    rcases hp : so.prev? with _ | p
    · rfl
    · simp only
      have ih := walkB_eq limits b1 bytes p (so.revs.map Revision.offset ++ visited) so.nodup
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact so.lt x hx
          · exact hlt x hx)
        (by simp only [List.length_append, List.length_map]; rw [Nat.add_comm]; exact hb)
      rw [← ih]
      rcases walkB limits b1 bytes p (so.revs.map Revision.offset ++ visited) so.nodup
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact so.lt x hx
          · exact hlt x hx) with ⟨⟨r2, k'⟩, b2⟩
      rcases r2 with e | rest <;> rfl
termination_by bytes.size - visited.length
decreasing_by
  have h1 := length_le_of_nodup_of_lt so.nodup (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact so.lt x hx
    · exact hlt x hx)
  have h2 : 0 < so.revs.length := List.length_pos_iff.mpr so.ne
  simp only [List.length_append, List.length_map] at h1 ⊢
  omega

/-- **Entry point** (task 3.13). `loadChain` with every xref-stream decode charged against
`budget`; returns the charged budget, also on failure. -/
def loadChainB (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    (Except Error (List Revision)) × Budget :=
  match findStartxref bytes with
  | .error e => (.error e, budget)
  | .ok off =>
    let p := walkB limits budget bytes off [] List.nodup_nil
      (fun _ hx => absurd hx List.not_mem_nil)
    (p.1.1, p.2)

/-- **Budget monotone**: `loadChainB` never increases the budget. -/
theorem loadChainB_le (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    (loadChainB limits budget bytes).2.remaining ≤ budget.remaining := by
  unfold loadChainB
  split
  · exact Nat.le_refl _
  · exact walkB_le _ _ _ _ _ _ _

/-- **Budget large enough ⇒ same chain** (task 3.13): with at least
`maxRevisions · decodeAllowance limits bytes` left, `loadChainB` returns exactly what
`loadChain` returns, so every theorem about `loadChain` (`Spec.XrefTerm`,
`Spec.Unambiguous`, `Spec.PrefixStable`) applies to its result. -/
theorem loadChainB_eq {limits : Limits} {budget : Budget} {bytes : ByteArray}
    (h : limits.maxRevisions * decodeAllowance limits bytes ≤ budget.remaining) :
    (loadChainB limits budget bytes).1 = loadChain limits bytes := by
  unfold loadChainB loadChain loadChainCounted
  cases hs : findStartxref bytes with
  | error e => rfl
  | ok off =>
    simp only
    rw [walkB_eq _ _ _ _ _ _ _ (by simpa using h)]

/-- **Cost of one step**: at most `decodeAllowance` per section parsed; a failed step costs at
most `(maxRevisions - visited.length) · decodeAllowance`, a successful one at most
`revs.length · decodeAllowance`, with `visited.length + revs.length ≤ maxRevisions`. -/
theorem stepB_cost (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat)
    (visited : List Nat) (hnd : visited.Nodup) :
    budget.remaining ≤ (stepB limits budget bytes off visited hnd).2.remaining +
      (limits.maxRevisions - visited.length) * decodeAllowance limits bytes ∧
    ∀ so k, (stepB limits budget bytes off visited hnd).1 = (.ok so, k) →
      budget.remaining ≤ (stepB limits budget bytes off visited hnd).2.remaining +
        so.revs.length * decodeAllowance limits bytes ∧
      visited.length + so.revs.length ≤ limits.maxRevisions := by
  have hmulle : ∀ a b K : Nat, a ≤ b → a * K ≤ b * K := fun a b K h => Nat.mul_le_mul_right K h
  unfold stepB
  by_cases hoff : off < bytes.size
  · simp only [hoff, dite_true]
    by_cases hmem : off ∈ visited
    · simp [hmem]
    · simp only [hmem, dite_false]
      by_cases hrev : limits.maxRevisions ≤ visited.length
      · simp [hrev]
      · simp only [hrev, ↓reduceIte]
        have hc1 := parseSectionB_cost limits budget bytes off
        have hA := hmulle 1 (limits.maxRevisions - visited.length) (decodeAllowance limits bytes)
          (by omega)
        rcases hps : parseSectionB limits budget bytes off with ⟨r1, b1⟩
        rw [hps] at hc1
        simp only at hc1
        rcases r1 with e | ⟨sec, tr⟩
        · simp only
          refine ⟨by omega, ?_⟩
          intro so k hso; cases hso
        · simp only
          rcases hh : hybridStm bytes off tr with _ | s
          · simp only
            refine ⟨by omega, ?_⟩
            intro so k hso
            simp only [Prod.mk.injEq, Except.ok.injEq] at hso
            obtain ⟨rfl, rfl⟩ := hso
            simp only [List.length_cons, List.length_nil]
            omega
          · simp only
            by_cases hs : s < bytes.size
            · simp only [hs, dite_true]
              by_cases hsm : s = off ∨ s ∈ visited
              · simp only [hsm, dite_true]
                refine ⟨by omega, ?_⟩
                intro so k hso; cases hso
              · simp only [hsm, dite_false]
                by_cases hrev2 : limits.maxRevisions ≤ visited.length + 1
                · simp only [hrev2, ↓reduceIte]
                  refine ⟨by omega, ?_⟩
                  intro so k hso; cases hso
                · simp only [hrev2, ↓reduceIte]
                  have hB := hmulle 2 (limits.maxRevisions - visited.length)
                    (decodeAllowance limits bytes) (by omega)
                  have hc2 := parseXrefStreamB_cost limits b1 bytes s
                  rcases hps2 : parseXrefStreamB limits b1 bytes s with ⟨r2, b2⟩
                  rw [hps2] at hc2
                  simp only at hc2
                  rcases r2 with e | ⟨sec2, tr2⟩
                  · simp only
                    refine ⟨by omega, ?_⟩
                    intro so k hso; cases hso
                  · simp only
                    refine ⟨by omega, ?_⟩
                    intro so k hso
                    simp only [Prod.mk.injEq, Except.ok.injEq] at hso
                    obtain ⟨rfl, rfl⟩ := hso
                    simp only [List.length_cons, List.length_nil]
                    omega
            · simp only [hs, dite_false]
              refine ⟨by omega, ?_⟩
              intro so k hso; cases hso
  · simp [hoff]

/-- **Cost of the walk**: at most `(maxRevisions - visited.length) · decodeAllowance`. -/
theorem walkB_cost (limits : Limits) (budget : Budget) (bytes : ByteArray) (off : Nat)
    (visited : List Nat) (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size) :
    budget.remaining ≤ (walkB limits budget bytes off visited hnd hlt).2.remaining +
      (limits.maxRevisions - visited.length) * decodeAllowance limits bytes := by
  rw [walkB]
  obtain ⟨hc, hok⟩ := stepB_cost limits budget bytes off visited hnd
  rcases hs : stepB limits budget bytes off visited hnd with ⟨⟨r1, k⟩, b1⟩
  rw [hs] at hc hok
  simp only at hc hok
  rcases r1 with e | so
  · exact hc
  · simp only
    obtain ⟨hc1, hlen⟩ := hok so k rfl
    have hsplit : so.revs.length * decodeAllowance limits bytes +
        (limits.maxRevisions - (so.revs.length + visited.length)) * decodeAllowance limits bytes =
        (limits.maxRevisions - visited.length) * decodeAllowance limits bytes := by
      rw [← Nat.add_mul]; congr 1; omega
    have hle1 : so.revs.length * decodeAllowance limits bytes ≤
        (limits.maxRevisions - visited.length) * decodeAllowance limits bytes :=
      Nat.mul_le_mul_right _ (by omega)
    rcases hp : so.prev? with _ | p
    · simp only; omega
    · simp only
      have ih := walkB_cost limits b1 bytes p (so.revs.map Revision.offset ++ visited) so.nodup
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact so.lt x hx
          · exact hlt x hx)
      simp only [List.length_append, List.length_map] at ih
      rcases hw : walkB limits b1 bytes p (so.revs.map Revision.offset ++ visited) so.nodup
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact so.lt x hx
          · exact hlt x hx) with ⟨⟨r2, k'⟩, b2⟩
      rw [hw] at ih
      simp only at ih
      rcases r2 with e | rest <;> (simp only; omega)
termination_by bytes.size - visited.length
decreasing_by
  have h1 := length_le_of_nodup_of_lt so.nodup (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact so.lt x hx
    · exact hlt x hx)
  have h2 : 0 < so.revs.length := List.length_pos_iff.mpr so.ne
  simp only [List.length_append, List.length_map] at h1 ⊢
  omega

/-- **Cost of loading the chain**: at most `maxRevisions · decodeAllowance limits bytes`. -/
theorem loadChainB_cost (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    budget.remaining ≤ (loadChainB limits budget bytes).2.remaining +
      limits.maxRevisions * decodeAllowance limits bytes := by
  unfold loadChainB
  split
  · exact Nat.le_add_right _ _
  · rename_i off _
    have := walkB_cost limits budget bytes off [] List.nodup_nil
      (fun _ hx => absurd hx List.not_mem_nil)
    simpa using this

/-! ## Merging revisions: newest wins (S6 preview) -/

/-- The entry for object number `n` in an entry list (the first one). -/
def lookupEntry (n : Nat) : List (Nat × XrefEntry) → Option XrefEntry
  | [] => none
  | (k, e) :: rest => if k = n then some e else lookupEntry n rest

/-- Linear merge of two entry lists ascending by object number; on equal object numbers the
entry of the first (newer) list is kept and the other dropped. -/
def mergeTwo (xs ys : List (Nat × XrefEntry)) : List (Nat × XrefEntry) :=
  match xs, ys with
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x.1 < y.1 then x :: mergeTwo xs (y :: ys)
    else if y.1 < x.1 then y :: mergeTwo (x :: xs) ys
    else x :: mergeTwo xs ys
termination_by xs.length + ys.length

/-- Every element of a merge comes from one of the inputs. -/
theorem mem_mergeTwo {xs ys : List (Nat × XrefEntry)} {z : Nat × XrefEntry}
    (h : z ∈ mergeTwo xs ys) : z ∈ xs ∨ z ∈ ys := by
  fun_induction mergeTwo xs ys with
  | case1 ys => exact Or.inr h
  | case2 x xs => exact Or.inl h
  | case3 x xs y ys hlt ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases ih h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
  | case4 x xs y ys hlt hgt ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr List.mem_cons_self
    · rcases ih h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
  | case5 x xs y ys hlt hgt ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl List.mem_cons_self
    · rcases ih h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The merge of two strictly ascending lists is strictly ascending. -/
theorem mergeTwo_sorted {xs ys : List (Nat × XrefEntry)}
    (hx : xs.Pairwise (fun a b => a.1 < b.1)) (hy : ys.Pairwise (fun a b => a.1 < b.1)) :
    (mergeTwo xs ys).Pairwise (fun a b => a.1 < b.1) := by
  fun_induction mergeTwo xs ys with
  | case1 ys => exact hy
  | case2 x xs => exact hx
  | case3 x xs y ys hlt ih =>
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih hx'.2 hy⟩
    rcases mem_mergeTwo hz with hz | hz
    · exact hx'.1 z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hlt
      · exact Nat.lt_trans hlt (hy'.1 z hz)
  | case4 x xs y ys hlt hgt ih =>
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih hx hy'.2⟩
    rcases mem_mergeTwo hz with hz | hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hgt
      · exact Nat.lt_trans hgt (hx'.1 z hz)
    · exact hy'.1 z hz
  | case5 x xs y ys hlt hgt ih =>
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    have heq : x.1 = y.1 := by omega
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih hx'.2 hy'.2⟩
    rcases mem_mergeTwo hz with hz | hz
    · exact hx'.1 z hz
    · rw [heq]; exact hy'.1 z hz

/-- The merged entries of a chain, newest revision first in the input. -/
def mergeEntries : List Revision → List (Nat × XrefEntry)
  | [] => []
  | r :: rest => mergeTwo r.1.entries (mergeEntries rest)

/-- The merged entries are strictly ascending by object number. -/
theorem mergeEntries_sorted (revs : List Revision) :
    (mergeEntries revs).Pairwise (fun a b => a.1 < b.1) := by
  induction revs with
  | nil => exact List.Pairwise.nil
  | cons r rest ih => exact mergeTwo_sorted r.1.sorted ih

/-- **Merge.** One section for the whole chain (newest first): per object number, the entry
of the newest revision that has one (ISO 32000-2 §7.5.6). The result carries the
`XrefSection` invariant, hence has one entry per object number (S6). -/
def mergeChain (revs : List Revision) : XrefSection :=
  ⟨mergeEntries revs, mergeEntries_sorted revs⟩

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o w => s!"cycle@{o}: {w}"
  | .encryption w => s!"encryption: {w}"

/-- Test helper: `loadChain` summarised as the revision offsets, with the call count. -/
private def lc (b : ByteArray) : Sum String (List Nat) × Nat :=
  match loadChainCounted Limits.default b with
  | (.ok revs, k) => (.inr (revs.map Revision.offset), k)
  | (.error e, k) => (.inl (errS e), k)

/-- Test helper: `lc` under explicit limits. -/
private def lcl (limits : Limits) (b : ByteArray) : Sum String (List Nat) × Nat :=
  match loadChainCounted limits b with
  | (.ok revs, k) => (.inr (revs.map Revision.offset), k)
  | (.error e, k) => (.inl (errS e), k)

/-- Test helper: look up object `n` in the merged chain of `b`. -/
private def lk (b : ByteArray) (n : Nat) : Option XrefEntry :=
  match loadChain Limits.default b with
  | .ok revs => lookupEntry n (mergeChain revs).entries
  | .error _ => none

/-- Test helper: 32-bit FNV-1a hash, to pin the embedded files to the ones on disk. -/
private def fnv (b : ByteArray) : Nat :=
  (b.data.foldl (fun h x => ((h ^^^ x.toNat) * 16777619) % 4294967296) 2166136261 : Nat)

/-- Bytes 0–403 shared by `minimal-valid.pdf`, `xref-prev-self.pdf` and
`xref-prev-cycle.pdf` in `Tests/adversarial/` (header and objects 1–5). -/
private def advPrefix : ByteArray :=
  "%PDF-1.7\n%".toUTF8 ++ ByteArray.mk #[0xe2, 0xe3, 0xcf, 0xd3] ++ (
    "\n" ++
    "1 0 obj\n" ++
    "<< /Type /Catalog /Pages 2 0 R >>\n" ++
    "endobj\n" ++
    "2 0 obj\n" ++
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>\n" ++
    "endobj\n" ++
    "3 0 obj\n" ++
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R /Re" ++
    "sources << /Font << /F1 5 0 R >> >> >>\n" ++
    "endobj\n" ++
    "4 0 obj\n" ++
    "<<  /Length 36 >>\n" ++
    "stream\n" ++
    "BT /F1 24 Tf 72 700 Td (Hello) Tj ET\n" ++
    "endstream\n" ++
    "endobj\n" ++
    "5 0 obj\n" ++
    "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>\n" ++
    "endobj\n").toUTF8

/-- The six-entry table of objects 0–5 at offset 404 (shared by the three files). -/
private def advTable : String :=
  "xref\n" ++
  "0 6\n" ++
  "0000000000 65535 f \n" ++
  "0000000015 00000 n \n" ++
  "0000000064 00000 n \n" ++
  "0000000121 00000 n \n" ++
  "0000000247 00000 n \n" ++
  "0000000334 00000 n \n" ++
  "trailer\n"

/-- `Tests/adversarial/minimal-valid.pdf` (587 bytes). -/
private def minimalValid : ByteArray :=
  advPrefix ++ (advTable ++
    "<< /Size 6 /Root 1 0 R >>\n" ++
    "startxref\n" ++
    "404\n" ++
    "%%EOF\n").toUTF8

/-- `Tests/adversarial/xref-prev-self.pdf` (604 bytes): `/Prev` points at its own table. -/
private def prevSelf : ByteArray :=
  advPrefix ++ (advTable ++
    "<< /Size 6 /Root 1 0 R /Prev 0000000404 >>\n" ++
    "startxref\n" ++
    "404\n" ++
    "%%EOF\n").toUTF8

/-- `Tests/adversarial/xref-prev-cycle.pdf` (852 bytes): tables at 652 and 404 point at each
other. -/
private def prevCycle : ByteArray :=
  advPrefix ++ (advTable ++
    "<< /Size 6 /Root 1 0 R /Prev 0000000652 >>\n" ++
    "5 0 obj\n" ++
    "<< /Type /Font /Subtype /Type1 /BaseFont /Courier >>\n" ++
    "endobj\n" ++
    "xref\n" ++
    "0 6\n" ++
    "0000000000 65535 f \n" ++
    "0000000015 00000 n \n" ++
    "0000000064 00000 n \n" ++
    "0000000121 00000 n \n" ++
    "0000000247 00000 n \n" ++
    "0000000584 00000 n \n" ++
    "trailer\n" ++
    "<< /Size 6 /Root 1 0 R /Prev 0000000404 >>\n" ++
    "startxref\n" ++
    "652\n" ++
    "%%EOF\n").toUTF8

/-- A hand-built incremental update of `minimal-valid.pdf`: object 3 is rewritten at 587
and a one-entry table at 658 points back with `/Prev 404` (775 bytes). -/
private def twoRevisions : ByteArray :=
  minimalValid ++ (
    "3 0 obj\n" ++
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 595 842] >>\n" ++
    "endobj\n" ++
    "xref\n" ++
    "0 1\n" ++
    "0000000000 65535 f \n" ++
    "3 1\n" ++
    "0000000587 00000 n \n" ++
    "trailer\n" ++
    "<< /Size 6 /Root 1 0 R /Prev 404 >>\n" ++
    "startxref\n" ++
    "658\n" ++
    "%%EOF\n").toUTF8

-- the embedded files are the ones on disk (size and FNV-1a computed from the files)
#guard minimalValid.size == 587 && fnv minimalValid == 1180125090
#guard prevSelf.size == 604 && fnv prevSelf == 3475448084
#guard prevCycle.size == 852 && fnv prevCycle == 1023480011
-- minimal-valid: one revision, one parse
#guard lc minimalValid == (.inr [404], 1)
-- Bogk-style cycles are rejected as cycles, after 1 resp. 2 parses
#guard lc prevSelf == (.inl "cycle@404: xref /Prev cycle", 1)
#guard lc prevCycle == (.inl "cycle@652: xref /Prev cycle", 2)
-- an incremental update: two revisions, the newer one overrides object 3
#guard twoRevisions.size == 775
#guard lc twoRevisions == (.inr [658, 404], 2)
#guard lk twoRevisions 3 == some (.inUse 587 0)
-- the revision cap is `limits.maxRevisions`: excess is `limitExceeded .revisions`
#guard lcl { maxRevisions := 2 } twoRevisions == (.inr [658, 404], 2)
#guard lcl { maxRevisions := 1 } twoRevisions == (.inl "limit:SafePdf.LimitKind.revisions", 1)
#guard lcl { maxRevisions := 0 } twoRevisions == (.inl "limit:SafePdf.LimitKind.revisions", 0)
#guard lk twoRevisions 4 == some (.inUse 247 0)
#guard lk twoRevisions 0 == some (.free 0 65535)
#guard lk twoRevisions 6 == none
#guard (match loadChain Limits.default twoRevisions with
  | .ok revs => (mergeChain revs).entries.map Prod.fst == [0, 1, 2, 3, 4, 5]
  | .error _ => false)
-- /Prev beyond the end of input; /Prev at a non-table offset
#guard lc (minimalValid ++ ("xref\n0 1\n0000000000 65535 f \ntrailer\n" ++
    "<< /Size 6 /Prev 9999 >>\nstartxref\n587\n%%EOF\n").toUTF8) ==
  (.inl "malformed@9999: xref /Prev offset beyond end of input", 1)
#guard lc (minimalValid ++ ("xref\n0 1\n0000000000 65535 f \ntrailer\n" ++
    "<< /Size 6 /Prev 10 >>\nstartxref\n587\n%%EOF\n").toUTF8) ==
  (.inl "malformed@10: expected an xref keyword or an xref stream object", 2)
/-! ### Xref streams (task 2.4a) -/

/-- `Tests/adversarial/objstm-self-container.pdf` (378 bytes): an uncompressed xref stream
(`/W [1 4 2]`) whose entry for object 5 says it lies in object stream 5. -/
private def objstmSelf : ByteArray :=
  "%PDF-1.7\n%".toUTF8 ++
  ByteArray.mk #[226, 227, 207, 211] ++
  ("\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n2 0 obj\n" ++
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n3 0 obj\n" ++
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Rotate 5 0 R /Resources << >> >>\n" ++
    "endobj\n4 0 obj\n<< /Type /XRef /Size 6 /W [1 4 2] /Root 1 0 R /Length 42 >>\nstream\n").toUTF8 ++
  ByteArray.mk #[0, 0, 0, 0, 0, 255, 255, 1, 0, 0, 0, 15, 0, 0, 1, 0, 0, 0] ++
  "@".toUTF8 ++
  ByteArray.mk #[0, 0, 1, 0, 0, 0] ++
  "y".toUTF8 ++
  ByteArray.mk #[0, 0, 1, 0, 0, 0, 223, 0, 0, 2, 0, 0, 0, 5, 0, 0] ++
  "\nendstream\nendobj\nstartxref\n223\n%%EOF\n".toUTF8

/-- `Tests/adversarial/length-mutual.pdf` (550 bytes): an uncompressed xref stream
(`/W [1 4 2]`) at 381; object 6 lies in object stream 5. -/
private def lengthMutual : ByteArray :=
  "%PDF-1.7\n%".toUTF8 ++
  ByteArray.mk #[226, 227, 207, 211] ++
  ("\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n2 0 obj\n" ++
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n3 0 obj\n" ++
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R /Resources << >> >>\n" ++
    "endobj\n4 0 obj\n<<  /Length 6 0 R >>\nstream\n0 0 m 10 10 l S\nendstream\nendobj\n" ++
    "5 0 obj\n<< /Type /ObjStm /N 1 /First 4 /Length 4 0 R >>\nstream\n6 0 15\nendstream\n" ++
    "endobj\n7 0 obj\n<< /Type /XRef /Size 8 /W [1 4 2] /Root 1 0 R /Length 56 >>\nstream\n").toUTF8 ++
  ByteArray.mk #[0, 0, 0, 0, 0, 255, 255, 1, 0, 0, 0, 15, 0, 0, 1, 0, 0, 0] ++
  "@".toUTF8 ++
  ByteArray.mk #[0, 0, 1, 0, 0, 0] ++
  "y".toUTF8 ++
  ByteArray.mk #[0, 0, 1, 0, 0, 0, 225, 0, 0, 1, 0, 0, 1] ++
  "&".toUTF8 ++
  ByteArray.mk #[0, 0, 2, 0, 0, 0, 5, 0, 0, 1, 0, 0, 1] ++
  "}".toUTF8 ++
  ByteArray.mk #[0, 0] ++
  "\nendstream\nendobj\nstartxref\n381\n%%EOF\n".toUTF8

#guard objstmSelf.size == 378 && fnv objstmSelf == 770663905
#guard lengthMutual.size == 550 && fnv lengthMutual == 3220438046
-- the self-containing object stream entry is a structural error of the xref stream
#guard lc objstmSelf == (.inl "cycle@223: xref stream: object 5 lies in its own object stream", 1)
-- length-mutual: the xref loads (the /Length cycle is found later, when resolving)
#guard lc lengthMutual == (.inr [381], 1)
#guard lk lengthMutual 6 == some (.compressed 5 0)
#guard lk lengthMutual 4 == some (.inUse 225 0)
#guard (match loadChain Limits.default lengthMutual with
  | .ok revs => (mergeChain revs).entries.map Prod.fst == [0, 1, 2, 3, 4, 5, 6, 7]
  | .error _ => false)

/-- An xref stream object `n 0 obj` with dictionary extras and raw rows. -/
private def xstm (n : Nat) (extra : String) (rows : List UInt8) : ByteArray :=
  (s!"{n} 0 obj\n<< /Type /XRef {extra} /Length {rows.length} >>\nstream\n").toUTF8 ++
    ByteArray.mk rows.toArray ++ "\nendstream\nendobj\n".toUTF8

/-- A file of header, `body` and a `startxref` pointing at `sx`. -/
private def withStartxref (body : ByteArray) (sx : Nat) : ByteArray :=
  "%PDF-1.7\n".toUTF8 ++ body ++ s!"startxref\n{sx}\n%%EOF\n".toUTF8

/-- Flate + PNG-Up (`/Predictor 12 /Columns 5`) rows for objects 0–3 of `/W [1 3 1]`
(generated with Python's `zlib`, task 2.4a): free; at 15; at 64; in object stream 9. -/
private def flatePng : List UInt8 :=
  [120, 156, 99, 98, 0, 130, 255, 76, 140, 12, 12, 252, 140, 76, 64, 166, 33, 3, 136, 125,
   146, 1, 0, 23, 140, 2, 20]

/-- A one-revision file whose xref stream at 9 is Flate-compressed with a PNG predictor. -/
private def flateFile : ByteArray :=
  withStartxref (xstm 9 ("/Size 10 /Index [0 4] /W [1 3 1] /Root 1 0 R /Filter /FlateDecode " ++
    "/DecodeParms << /Predictor 12 /Columns 5 >>") flatePng) 9

#guard lc flateFile == (.inr [9], 1)
#guard lk flateFile 2 == some (.inUse 64 0)
#guard lk flateFile 3 == some (.compressed 9 0)

/-- An xref stream at 9 whose `/Prev` is its own offset. -/
private def streamPrevSelf : ByteArray :=
  withStartxref (xstm 1 "/Size 2 /Prev 9 /W [1 1 0]" [0, 0, 1, 0]) 9

#guard lc streamPrevSelf == (.inl "cycle@9: xref /Prev cycle", 1)

/-- Two stream revisions: the older at 9, the newer (object 1 moved) with `/Prev 9`. -/
private def twoStreams : ByteArray :=
  let s1 := xstm 1 "/Size 2 /W [1 1 0]" [0, 0, 1, 0]
  withStartxref (s1 ++ xstm 2 "/Size 3 /Index [1 2] /Prev 9 /W [1 1 0]" [1, 40, 1, 9])
    (9 + s1.size)

#guard lc twoStreams == (.inr [93, 9], 2)
#guard lk twoStreams 1 == some (.inUse 40 0)
#guard lk twoStreams 0 == some (.free 0 0)
-- a /W width of 9 and a decoded-length mismatch are errors in the chain as well
#guard lc (withStartxref (xstm 1 "/Size 1 /W [1 9 0]" [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) 9) ==
  (.inl "unsupported:xref stream /W field width above 8", 1)
#guard lc (withStartxref (xstm 1 "/Size 2 /W [1 1 0]" [1, 0, 1]) 9) ==
  (.inl "malformed@9: xref stream data has 3 bytes, expected 4", 1)

/-! ### Hybrid files (§7.5.8.4) -/

/-- The `/XRefStm` stream of the hybrid test file (object 6 at 587): object 3 at 15
(overridden by the table) and object 7 in object stream 4. -/
private def hybStm : ByteArray :=
  xstm 6 "/Size 8 /Index [3 1 7 1] /W [1 2 1]" [1, 0, 15, 0, 2, 0, 4, 0]

/-- An incremental update of `minimal-valid.pdf` in hybrid form: the table at `t` lists
object 3 at 121 and points with `/XRefStm` at `hybStm` (at `stm`) and `/Prev` at 404. -/
private def hybridAt (stm : Nat) : ByteArray :=
  let t := minimalValid.size + hybStm.size
  minimalValid ++ hybStm ++ (s!"xref\n0 1\n0000000000 65535 f \n3 1\n0000000121 00000 n \n" ++
    s!"trailer\n<< /Size 8 /Root 1 0 R /Prev 404 /XRefStm {stm} >>\nstartxref\n{t}\n%%EOF\n").toUTF8

/-- The hybrid file proper. -/
private def hybrid : ByteArray := hybridAt minimalValid.size

#guard hybStm.size == 105
-- table, then its /XRefStm stream, then /Prev: three parses
#guard lc hybrid == (.inr [692, 587, 404], 3)
-- the table wins over its /XRefStm stream; the stream supplies what the table lacks
#guard lk hybrid 3 == some (.inUse 121 0)
#guard lk hybrid 7 == some (.compressed 4 0)
#guard lk hybrid 5 == some (.inUse 334 0)
-- /XRefStm pointing at the table itself, at the /Prev table, beyond the end of input
#guard lc (hybridAt 692) == (.inl "cycle@692: xref /XRefStm cycle", 1)
#guard lc (hybridAt 404) ==
  (.inl "malformed@404: expected an xref keyword or an xref stream object", 2)
#guard lc (hybridAt 99999) == (.inl "malformed@99999: xref /XRefStm offset beyond end of input", 1)
-- the revision cap counts the /XRefStm stream
#guard lcl { maxRevisions := 2 } hybrid == (.inl "limit:SafePdf.LimitKind.revisions", 2)
#guard lcl { maxRevisions := 1 } hybrid == (.inl "limit:SafePdf.LimitKind.revisions", 1)
-- no startxref: no parse at all
#guard lc "%PDF-1.7\n".toUTF8 == (.inl "malformed@9: startxref not found", 0)

/-! ### Budgeted loading (task 3.13) -/

/-- Test helper: `loadChainB` from a budget of `n` bytes, with the budget left. -/
private def lcb (n : Nat) (b : ByteArray) : Sum String (List Nat) × Nat :=
  match loadChainB Limits.default ⟨n⟩ b with
  | (.ok revs, bud) => (.inr (revs.map Revision.offset), bud.remaining)
  | (.error e, bud) => (.inl (errS e), bud.remaining)

-- Flate + PNG predictor: 20 decoded bytes charged; with a budget of 10 the decode fails with
-- the total-budget error and is charged its cap (rule B2)
#guard lcb 1000 flateFile == (.inr [9], 980)
#guard lcb 10 flateFile == (.inl "limit:SafePdf.LimitKind.decodedTotalBytes", 0)
-- unfiltered xref streams are charged their data (rule B3); classic tables are free
#guard lcb 1000 twoStreams == (.inr [93, 9], 992)
#guard lcb 1000 minimalValid == (.inr [404], 1000)
#guard lcb 0 minimalValid == (.inr [404], 0)
#guard lcb 1000 hybrid == (.inr [692, 587, 404], 992)
#guard lcb 0 hybrid == (.inl "limit:SafePdf.LimitKind.decodedTotalBytes", 0)
-- a cycle is still a cycle under the budget
#guard lcb 1000 prevCycle == (.inl "cycle@652: xref /Prev cycle", 1000)
#guard lcb 1000 streamPrevSelf == (.inl "cycle@9: xref /Prev cycle", 996)
-- with the full default budget: the revisions loadChain finds
#guard (match (loadChainB Limits.default (Filter.Budget.init Limits.default) hybrid).1 with
  | .ok revs => revs.map Revision.offset == [692, 587, 404]
  | .error _ => false)

end Tests

end SafePdf.Core.Xref.Chain
