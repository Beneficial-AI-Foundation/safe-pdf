import SafePdf.Core.Xref

/-!
# The `/Prev` chain of incremental updates

Plan.md §5.2 (first bullet), §4 S2/S3/S6, §6 Phase 2; ISO 32000-2 §7.5.5 (trailer `/Prev`)
and §7.5.6 (incremental updates); Bogk & Schöpl 2014 (cyclic `/Prev` chains hang readers).

Task 2.2. A file updated incrementally has one cross-reference section per revision; the
trailer of each points with `/Prev` at the byte offset of the previous section. `loadChain`
starts at the `startxref` offset (`Core.Xref.findStartxref`), parses the classic table there
(`Core.Xref.parseXrefTable`) and follows `/Prev` until a trailer has none, newest revision
first. `mergeChain` folds the revisions into one section in which the newest entry wins per
object number (S6 preview; the full unambiguity theorem is task 2.5).

## Termination by the visited set (Plan.md §5.2)

The loop `walk` carries the list `visited` of offsets already parsed, together with the
proofs that it is duplicate-free and that every element is `< bytes.size`. Before following
an offset `off` it checks `off < bytes.size` (else `Error.malformed`, `/Prev` offsets are not
range-checked by 2.1) and `off ∉ visited` (else `Error.malformed off "xref /Prev cycle"`):
**a revisited offset is an error, not a loop**. The measure is `bytes.size - visited.length`,
the number of unvisited offsets; it strictly decreases because a duplicate-free list of
naturals below `n` with one more fresh element below `n` has length `< n`
(`length_lt_of_fresh`, from `length_le_of_nodup_of_lt`). No `partial`, no fuel.

Independently the chain length is bounded by `limits.maxRevisions` (default 4096,
`SafePdf.Limits`), whose excess yields `Error.limitExceeded .revisions`.

`walk` also returns the number of `parseXrefTable` calls it made (the count is incremented
exactly where `parseXrefTable` is invoked), so that `Spec.XrefTerm` can state the work bound.

## Not done here

* `/XRefStm` (hybrid files, §7.5.8.4) is not followed: xref streams are task 2.4; 2.5 will
  merge the hybrid stream between a section and its `/Prev`.
* Object numbers are not checked against `/Size` (task 2.5).
* `/Prev` pointing at an xref *stream* is an error here (`expected xref keyword`); 2.4/2.6.
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
of its `xref` keyword. -/
abbrev Revision := XrefSection × Trailer × Nat

/-- The byte offset of a revision's section. -/
def Revision.offset (r : Revision) : Nat := r.2.2

/-- Follow the `/Prev` chain from `off`. `visited` holds the offsets parsed so far (newest
first), duplicate-free and inside the input. Returns the revisions from `off` on, newest
first, and the number of `parseXrefTable` calls made.

Errors: `off ≥ bytes.size` (malformed), `off ∈ visited` (malformed, `"xref /Prev cycle"`),
more than `limits.maxRevisions` revisions (`limitExceeded .revisions`), or a parse error. -/
def walk (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size) :
    Except Error (List Revision) × Nat :=
  if hoff : off < bytes.size then
    if hmem : off ∈ visited then (.error (.malformed off "xref /Prev cycle"), 0)
    else if limits.maxRevisions ≤ visited.length then (.error (.limitExceeded .revisions), 0)
    else
      match parseXrefTable limits bytes off with
      | .error e => (.error e, 1)
      | .ok (sec, tr, _) =>
        match tr.prev? with
        | none => (.ok [(sec, tr, off)], 1)
        | some p =>
          match walk limits bytes p (off :: visited) (List.nodup_cons.2 ⟨hmem, hnd⟩)
              (fun x hx => by
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hoff
                · exact hlt x hx) with
          | (.error e, k) => (.error e, k + 1)
          | (.ok revs, k) => (.ok ((sec, tr, off) :: revs), k + 1)
  else (.error (.malformed off "xref /Prev offset beyond end of input"), 0)
termination_by bytes.size - visited.length
decreasing_by
  have := length_lt_of_fresh hnd hlt hoff hmem
  simp only [List.length_cons]
  omega

/-- `loadChain` with the number of `parseXrefTable` calls made. -/
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
#guard lc prevSelf == (.inl "malformed@404: xref /Prev cycle", 1)
#guard lc prevCycle == (.inl "malformed@652: xref /Prev cycle", 2)
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
  (.inl "malformed@10: expected xref keyword", 2)
-- no startxref: no parse at all
#guard lc "%PDF-1.7\n".toUTF8 == (.inl "malformed@9: startxref not found", 0)

end Tests

end SafePdf.Core.Xref.Chain
