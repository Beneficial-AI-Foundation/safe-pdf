import SafePdf.Core.Xref
import SafePdf.Core.Xref.Stream

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

end Tests

end SafePdf.Core.Xref.Chain
