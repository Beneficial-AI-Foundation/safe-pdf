import SafePdf.Spec.RepairAgreeExt

/-!
# Exact C4 for compressed entries (task 12.7f)

Plan.md §5 (claim C4), §5.4 (the repair path), §6 Phase 12 "Proof gaps"; `docs/safety.md` §5,
gap 1. Follows `Spec.RepairAgreeExt` (12.7c/12.7e), whose `c4_comp` is one-sided: since
repair rule R6 (12.7e) gives object-stream members compressed entries, the repaired section
can hold exactly the strict compressed entries, and then C4 is exact.

## Lookups equal up to free entries

`RepairAgreeFree.LookupRel` forbade compressed entries; here only `strip` equality is kept
(`∀ n, strip (l1 n) = strip (l2 n)`: equal entries, or both free or absent). With the **same
fuel**, every reader of the lookup gives identical results, the (parse count, result) pair
included, with no fuel bound at all (free and absent give the same errors since 12.7d):
`resolve_strip` (strong induction: the object-stream hop's second call gets `fuel - used`),
`lengthOf_strip`, `parseIndirectResolved_strip`/`parseFun_strip`, `fetchCompressed_strip`,
`getObject_strip` (equal bytes, decryption state and `objectCount`). `strip_of` builds the
relation from equal in-use and compressed entries.

## The hypotheses

* `trailerOkCompEq` (H5c + **H7f**): the repaired trailer is unencrypted with the strict
  `/Root`; every repaired compressed entry is the strict one (H7c) and every strict
  compressed entry is the repaired one (H7f: R6 found exactly the strict object-stream
  members). `HypCompStrip` = H1, H2c, H3, H4 of `HypComp`, H5c + H7f, H6 (unencrypted).
* **H8** (`fuelEq`, until task 12.7g): the repaired section has as many entries as the
  strict one, i.e. the strict section has no free entry besides 0. **Dropped by task 12.7g**:
  `HypCompEq` is now `HypCompStrip` (the name is kept); `fuelEq` stays as a diagnostic.
  All decidable; checkers `checkCompEq`, `checkCompStrip` (now the same condition).

## Results

* `c4_comp_eq` / `c4_comp_eq_check` (**exact, no H8**): under `HypCompEq` (= `HypCompStrip`)
  the repair path succeeds, with the same bytes, in-use entries, compressed entries and
  `/Root`, and **equal** `getObject` for every `num gen`. `#guard`: `objStmBytes` and
  `freeEntryBytes` (a free entry 4, sections of 7 and 6 entries) pass `checkCompEq`.
* Fuel independence (task 12.7g): `resolve_fuel` (any two fuels above `cnt S V` give the
  identical pair, compressed entries included), `lengthOf_fuel`, `parseFun_fuel`,
  `fetchCompressed_fuel`, `getObject_strip_cnt` (strip-equal lookups, both fuels above the
  number of in-use objects ⇒ equal `getObject`).
* `c4_comp_strip` / `c4_comp_strip_check` (12.7f's weaker statement, still proved): the repair
  path fails with `fuelOut` or succeeds with `getObject` equal wherever it does not run out of
  fuel (`resolve_mono_ne` … `getObject_strip_le`). Subsumed by `c4_comp_eq`.

## The former obstacle (fixed by task 12.7g)

Until 12.7g, in `Length.resolveLengthAux` the object-stream hop resolved the container's
`/Length` recursively and then the member's value with visiting only `ref.1 :: V` and fuel
`fuel - used`, so the second call could re-walk objects the first had parsed: the work was
not bounded by the number of objects and two fuels above it could differ (one path running
out). Core now resolves the container's `/Length` in one hop (`Length.lengthHop`, ISO 32000-2
§7.5.7) and adds the container and its `/Length` object to the member's visiting list
(`Length.hopVis`); no in-use object is parsed twice, so `cnt S V` bounds the parses
(`hop_cnt`) and the fuel is not observed above it.

## Open

* **Encrypted files with compressed entries**: not covered. R6 does not run on an encrypted
  repaired trailer (containers are encrypted; the decryption state exists only after repair),
  so H7f fails whenever the strict section has a compressed entry, and `HypCompStrip` also
  requires H6 (unencrypted). What holds: `RepairAgreeExt.c4_enc` (exact) needs no compressed
  entries; `c4_comp` (one-sided) needs H6 too, so for encrypted files with compressed entries
  **no** C4 statement is proved. Exact C4 there needs R6 after `withCrypt`
  (`Core.Open.repairOpen`, decrypting containers with `OpenDoc.pre`) and `encryptDict`'s case
  for a compressed `/Encrypt` reference (task 12.7h).
* A catalog in an object stream still fails repair (R4 takes `/Root` only from classic
  objects), as noted in `RepairAgreeExt`.
-/

namespace SafePdf.Spec.RepairAgreeComp

open SafePdf
open SafePdf.Core.Open
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)
open SafePdf.Core.Xref.Length
open SafePdf.Spec.RepairAgree
open SafePdf.Spec.RepairAgreeFree
open SafePdf.Spec.RepairAgreeExt
open SafePdf.Repair (scanSection toEntries)

/-! ## Lookups equal up to free entries (compressed entries allowed) -/

/-- Lookups equal once `free` is forgotten: at each number they are equal, or both are free
or absent. -/
theorem strip_cases {l1 l2 : Nat → Option XrefEntry} (hs : ∀ n, strip (l1 n) = strip (l2 n))
    (n : Nat) :
    l1 n = l2 n ∨ ((l1 n = none ∨ ∃ a g, l1 n = some (.free a g)) ∧
      (l2 n = none ∨ ∃ a g, l2 n = some (.free a g))) := by
  have h := hs n
  rcases h1 : l1 n with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩) <;>
    rcases h2 : l2 n with _ | (⟨a', g'⟩ | ⟨off', g'⟩ | ⟨c', i'⟩) <;>
    simp_all [strip]

/-- `errOffset` only reads in-use entries. -/
theorem errOffset_strip {l1 l2 : Nat → Option XrefEntry} (hs : ∀ n, strip (l1 n) = strip (l2 n))
    (n : Nat) : errOffset l1 n = errOffset l2 n := by
  unfold errOffset
  rcases strip_cases hs n with h | ⟨h1, h2⟩
  · rw [h]
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]

/-- The one-hop resolver of an object stream's own `/Length` reads the lookup only up to
free entries. -/
theorem lengthHop_strip {l1 l2 : Nat → Option XrefEntry} (hs : ∀ n, strip (l1 n) = strip (l2 n))
    (limits : Limits) (bytes : ByteArray) :
    lengthHop l1 limits bytes = lengthHop l2 limits bytes := by
  funext f V r
  unfold lengthHop
  rw [errOffset_strip hs]
  rcases strip_cases hs r.1 with he | ⟨h1, h2⟩
  · rw [he]
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]

/-- **`/Length` resolution reads the lookup only up to free entries**: with the **same fuel**,
lookups equal up to `free` versus absent (compressed entries allowed) give the identical
(parse count, result) pair. -/
theorem resolve_strip {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hs : ∀ n, strip (l1 n) = strip (l2 n)) (limits : Limits) (bytes : ByteArray) :
    ∀ f V ref, resolveLengthAux pre l1 limits bytes f V ref =
      resolveLengthAux pre l2 limits bytes f V ref := by
  intro f
  induction f using Nat.strongRecOn with
  | _ f ih =>
  intro V ref
  cases f with
  | zero =>
    rw [resolveLengthAux.eq_def, resolveLengthAux.eq_def]
    simp only [errOffset_strip hs]
  | succ k =>
  have hk : ∀ m, m ≤ k → resolveLengthAux pre l1 limits bytes m =
      resolveLengthAux pre l2 limits bytes m :=
    fun m hm => funext fun V => funext fun r => ih m (by omega) V r
  rw [resolveLengthAux, resolveLengthAux]
  by_cases hv : ref.1 ∈ V
  · simp only [hv, ↓reduceIte, errOffset_strip hs]
  simp only [hv, ↓reduceIte]
  rcases strip_cases hs ref.1 with he | ⟨h1, h2⟩
  · rw [he, hk k (Nat.le_refl k), lengthHop_strip hs]
    rcases hl : l2 ref.1 with _ | (⟨a, g⟩ | ⟨off, g'⟩ | ⟨c, idx⟩)
    · rfl
    · rfl
    · rfl
    · simp only [errOffset_strip hs]
      split
      · rfl
      · rcases strip_cases hs c with hc | ⟨h1, h2⟩
        · rw [hc]
          rcases l2 c with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
          · rfl
          · rfl
          · simp only
            split
            · split
              · rfl
              · rename_i d p _
                rw [hk _ (Nat.sub_le k _)]
            · rfl
          · rfl
        · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]

/-- `resolveLengthAux` as a function is the same for lookups equal up to free entries. -/
theorem resolveFun_strip {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hs : ∀ n, strip (l1 n) = strip (l2 n)) (limits : Limits) (bytes : ByteArray) :
    resolveLengthAux pre l1 limits bytes = resolveLengthAux pre l2 limits bytes :=
  funext fun f => funext fun V => funext fun r => resolve_strip hs limits bytes f V r

/-- `lengthOf` is the same for lookups equal up to free entries (same fuel). -/
theorem lengthOf_strip {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hs : ∀ n, strip (l1 n) = strip (l2 n)) (limits : Limits) (bytes : ByteArray) :
    lengthOf pre l1 limits bytes = lengthOf pre l2 limits bytes := by
  funext f self d at_
  unfold lengthOf lengthDict resolveLength
  rw [resolveFun_strip hs]

/-- The object parse is the same for lookups equal up to free entries (same fuel). -/
theorem parseIndirectResolved_strip {l1 l2 : Nat → Option XrefEntry}
    (hs : ∀ n, strip (l1 n) = strip (l2 n)) (limits : Limits) (bytes : ByteArray)
    (f pos : Nat) (pre : Core.Xref.ObjStm.Pre) :
    parseIndirectResolved l1 limits bytes f pos pre =
      parseIndirectResolved l2 limits bytes f pos pre := by
  unfold parseIndirectResolved
  rw [lengthOf_strip hs]

/-- `parseIndirectResolved` as a function is the same for lookups equal up to free
entries. -/
theorem parseFun_strip {l1 l2 : Nat → Option XrefEntry}
    (hs : ∀ n, strip (l1 n) = strip (l2 n)) :
    @parseIndirectResolved l1 = @parseIndirectResolved l2 :=
  funext fun limits => funext fun bytes => funext fun f => funext fun pos => funext fun pre =>
    parseIndirectResolved_strip hs limits bytes f pos pre

/-- `ObjStm.fetchCompressedTrace` is the same for lookups equal up to free entries (same
fuel), provided the fetched number has the same entry. -/
theorem fetchCompressed_strip {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hs : ∀ n, strip (l1 n) = strip (l2 n)) (limits : Limits) (bytes : ByteArray)
    (f num : Nat) (hn : l1 num = l2 num) :
    Core.Xref.ObjStm.fetchCompressedTrace pre l1 limits bytes f num =
      Core.Xref.ObjStm.fetchCompressedTrace pre l2 limits bytes f num := by
  unfold Core.Xref.ObjStm.fetchCompressedTrace
  rw [hn, parseFun_strip hs]
  rcases l2 num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, idx⟩)
  · rfl
  · rfl
  · rfl
  simp only
  split
  · rfl
  rcases strip_cases hs c with hc | ⟨h1, h2⟩
  · rw [hc]
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]

/-- **`getObject` is equal** on two documents over the same bytes, with the same decryption
state and the **same fuel** (`objectCount`), whose lookups are equal up to free entries
(compressed entries included). -/
theorem getObject_strip {d d' : OpenDoc} (hb : d.bytes = d'.bytes) (hc : d.crypt = d'.crypt)
    (hs : ∀ n, strip (d.lookup n) = strip (d'.lookup n)) (hf : d.objectCount = d'.objectCount)
    (limits : Limits) (num gen : Nat) :
    d.getObject limits num gen = d'.getObject limits num gen := by
  have hpre : d.pre = d'.pre := by unfold OpenDoc.pre; rw [hc]
  have hdec : d.decrypt = d'.decrypt := by
    funext a b c; unfold OpenDoc.decrypt; rw [hc]
  unfold OpenDoc.getObject OpenDoc.getObjectTrace
  rcases strip_cases hs num with he | ⟨h1, h2⟩
  · rw [he, hb, hpre, hdec, hf, fetchCompressed_strip hs limits _ _ num he, parseFun_strip hs]
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]

/-- Lookups with the same in-use and the same compressed entries are equal up to free
entries. -/
theorem strip_of {l1 l2 : Nat → Option XrefEntry}
    (hU : ∀ n off g, l1 n = some (.inUse off g) ↔ l2 n = some (.inUse off g))
    (hC : ∀ n c i, l1 n = some (.compressed c i) ↔ l2 n = some (.compressed c i)) (n : Nat) :
    strip (l1 n) = strip (l2 n) := by
  rcases h1 : l1 n with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩) <;>
    rcases h2 : l2 n with _ | (⟨a', g'⟩ | ⟨off', g'⟩ | ⟨c', i'⟩) <;>
    first
    | rfl
    | (have := (hU n off g).mp h1; rw [h2] at this; cases this <;> rfl)
    | (have := (hU n off' g').mpr h2; rw [h1] at this; cases this <;> rfl)
    | (have := (hC n c i).mp h1; rw [h2] at this; cases this <;> rfl)
    | (have := (hC n c' i').mpr h2; rw [h1] at this; cases this <;> rfl)

/-! ## The hypothesis -/

/-- Conditions H5c and **H7f** (task 12.7f): the repair path's trailer exists, has the strict
`/Root` and no `/Encrypt`; every compressed entry of the repaired section is the strict entry
of its number (H7c, as in `trailerOkComp`); and every compressed entry of the strict section
is the repaired entry of its number (H7f: repair rule R6 found exactly the strict compressed
entries). -/
def trailerOkCompEq (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Bool :=
  match Repair.repair limits bytes with
  | .ok (sec, tr) =>
    !tr.encrypted && tr.root? == d.trailer.root? &&
      sec.entries.all (fun x => !isComp x.2 || d.lookup x.1 == some x.2) &&
      d.xref.entries.all (fun x =>
        !isComp x.2 || (OpenDoc.mk' bytes sec tr 0 true).lookup x.1 == some x.2)
  | .error _ => false

/-- Condition **H8** (equal fuel): the repaired section has as many entries as the strict
one, so both paths resolve `/Length` with the same fuel (`OpenDoc.objectCount`). Under H1–H4
and H7f it says that the strict section has no other free entry besides object 0. No longer
part of `HypCompEq` (task 12.7g); kept as a diagnostic. -/
def fuelEq (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Bool :=
  match Repair.repair limits bytes with
  | .ok (sec, _) => sec.entries.length == d.xref.entries.length
  | .error _ => false

/-- **The hypothesis of exact C4 with compressed entries, without the fuel condition**:
`HypComp` with H5c strengthened to H5c + H7f (`trailerOkCompEq`). -/
def HypCompStrip (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  (0, XrefEntry.free 0 65535) ∈ d.xref.entries ∧
  (∀ x ∈ d.xref.entries, EntryOkComp (hits limits bytes) x) ∧
  (∀ x ∈ hits limits bytes, ∃ e ∈ d.xref.entries, e.1 = x.1 ∧ isInUse e.2 = true) ∧
  (newestHits (hits limits bytes)).length ≤ limits.maxObjects ∧
  trailerOkCompEq limits bytes d = true ∧
  d.crypt.isNone = true

/-- `HypCompStrip` is decidable. -/
instance instDecidableHypCompStrip (limits : Limits) (bytes : ByteArray) (d : OpenDoc) :
    Decidable (HypCompStrip limits bytes d) := by
  unfold HypCompStrip; infer_instance

/-- **The hypothesis of exact C4 with compressed entries**: `HypCompStrip`. Until task 12.7g
it also required H8 (`fuelEq`); since `/Length` resolution no longer depends on the fuel above
the number of in-use objects (`resolve_fuel`), H8 is dropped and the name is kept. -/
def HypCompEq (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  HypCompStrip limits bytes d

/-- `HypCompEq` is decidable. -/
instance instDecidableHypCompEq (limits : Limits) (bytes : ByteArray) (d : OpenDoc) :
    Decidable (HypCompEq limits bytes d) := by
  unfold HypCompEq; infer_instance

/-- **The checker**: the strict path succeeds and its document satisfies `HypCompEq`. -/
def checkCompEq (limits : Limits) (bytes : ByteArray) : Bool :=
  match strictOpen limits bytes with
  | .ok d => decide (HypCompEq limits bytes d)
  | .error _ => false

/-- **The checker without H8**: the strict path succeeds and satisfies `HypCompStrip`. -/
def checkCompStrip (limits : Limits) (bytes : ByteArray) : Bool :=
  match strictOpen limits bytes with
  | .ok d => decide (HypCompStrip limits bytes d)
  | .error _ => false

/-- `HypCompStrip` implies `HypComp` (12.7e's one-sided hypothesis). -/
theorem HypCompStrip.toComp {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : HypCompStrip limits bytes d) : HypComp limits bytes d := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6⟩
  unfold trailerOkCompEq at h5
  unfold trailerOkComp
  split at h5
  · rename_i sec tr hrep
    rw [hrep]
    simp only [Bool.and_eq_true] at h5 ⊢
    exact h5.1
  · cases h5

/-- **The repaired section, under `HypCompStrip`.** If the repair path's section is `sec` with
trailer `tr`, then the document `OpenDoc.mk' bytes sec tr 0 true` has, at every number, the
strict in-use entries and the strict compressed entries (so its lookup equals the strict one
up to free entries), its trailer is unencrypted with the strict `/Root`, and its section is at
most as long as the strict one. -/
theorem compStrip_sec {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hh : HypCompStrip limits bytes d) {sec : XrefSection} {tr : Trailer}
    (hrep : Repair.repair limits bytes = .ok (sec, tr)) :
    tr.encrypted = false ∧ tr.root? = d.trailer.root? ∧
      (∀ n off g, d.lookup n = some (.inUse off g) ↔
        (OpenDoc.mk' bytes sec tr 0 true).lookup n = some (.inUse off g)) ∧
      (∀ n c i, d.lookup n = some (.compressed c i) ↔
        (OpenDoc.mk' bytes sec tr 0 true).lookup n = some (.compressed c i)) ∧
      sec.entries.length ≤ d.xref.entries.length := by
  obtain ⟨hz, hent, hcov, hcap, htr, -⟩ := hh
  have hin : ∀ n off g, (n, XrefEntry.inUse off g) ∈ d.xref.entries ↔
      (n, XrefEntry.inUse off g) ∈ (scanSection limits bytes).entries :=
    inUse_mem_iff_of (fun n off g hx => hent _ hx) hcov hcap
  obtain ⟨hsup, hsub⟩ := Repair.repair_entries hrep
  unfold trailerOkCompEq at htr
  rw [hrep] at htr
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at htr
  obtain ⟨⟨⟨henc, hroot⟩, hcomp⟩, hcomp2⟩ := htr
  let d' := OpenDoc.mk' bytes sec tr 0 true
  have hnd1 := d.xref.keys_nodup
  have hnd2 := sec.keys_nodup
  have hl1 : ∀ m e, d.lookup m = some e ↔ (m, e) ∈ d.xref.entries := fun m e => by
    rw [WritePrefix.lookup_eq d, Unambiguous.lookupEntry_eq_some_iff hnd1]
  have hl2 : ∀ m e, d'.lookup m = some e ↔ (m, e) ∈ sec.entries :=
    fun m e => by
      rw [WritePrefix.lookup_eq d']; exact Unambiguous.lookupEntry_eq_some_iff hnd2
  have hinS : ∀ n off g, (n, XrefEntry.inUse off g) ∈ sec.entries ↔
      (n, XrefEntry.inUse off g) ∈ (scanSection limits bytes).entries := by
    intro n off g
    constructor
    · intro h
      rcases hsub _ h with h | ⟨c, i, hc⟩
      · exact h
      · cases hc
    · exact hsup _
  have hcd : ∀ n c i, (n, XrefEntry.compressed c i) ∈ sec.entries →
      d.lookup n = some (.compressed c i) := by
    intro n c i h
    have := List.all_eq_true.mp hcomp _ h
    simpa [isComp] using this
  have hcd2 : ∀ n c i, (n, XrefEntry.compressed c i) ∈ d.xref.entries →
      d'.lookup n = some (.compressed c i) := by
    intro n c i h
    have := List.all_eq_true.mp hcomp2 _ h
    simpa [isComp] using this
  refine ⟨henc, hroot, fun n off g => ?_, fun n c i => ?_, ?_⟩
  · rw [hl1, hl2, hin, hinS]
  · exact ⟨fun h => hcd2 n c i ((hl1 _ _).mp h), fun h => hcd n c i ((hl2 _ _).mp h)⟩
  · have hnd : sec.entries.Nodup := by
      unfold List.Nodup at hnd2 ⊢
      rw [List.pairwise_map] at hnd2
      exact hnd2.imp (fun h e => h (congrArg Prod.fst e))
    refine hnd.length_le_of_subset (fun x hx => ?_)
    obtain ⟨n, e⟩ := x
    cases e with
    | free a g =>
      rcases hsub _ hx with hx | ⟨c, i, hc⟩
      · simp only [scanSection, toEntries, List.mem_cons, List.mem_map] at hx
        rcases hx with h0 | ⟨y, -, hy⟩
        · cases h0; exact hz
        · cases hy
      · cases hc
    | compressed c i => exact (hl1 _ _).mp (hcd n c i hx)
    | inUse off g => exact (hin n off g).mpr ((hinS n off g).mp hx)

/-! ## Fuel independence (task 12.7g)

Since task 12.7g an object stream's own `/Length` is resolved in one hop (`Length.lengthHop`)
and the member's value is resolved with the container and its `/Length` object added to the
visiting list (`Length.hopVis`), so no resolution parses an in-use object twice. Hence the
parses of a resolution with visiting list `V` number at most `cnt S V` (`S` holding every
in-use number), the fuel is never exhausted above that, and the result is the same for every
fuel above `cnt S V`, compressed entries included (`resolve_fuel`). Lifted to `lengthOf`,
`parseIndirectResolved`, `fetchCompressedTrace` and `getObject` (`getObject_strip_cnt`): two
documents whose lookups are equal up to free entries give equal `getObject` whenever both
fuels exceed the number of in-use objects, whatever their free entries. -/

/-- An object of `S` that is not visited makes `cnt` positive. -/
theorem cnt_pos {S V : List Nat} {x : Nat} (hx : x ∈ S) (hv : x ∉ V) : 0 < cnt S V := by
  have := cnt_cons_lt hx hv
  omega

/-- The visiting list of the member's value (rule L6) has at least one more in-use object
than the hop's own visiting list, two when the container's `/Length` is a reference, and the
hop's parse count is exactly the extra one. -/
theorem hop_cnt {l : Nat → Option XrefEntry} {limits : Limits} {bytes : ByteArray}
    {S : List Nat} (hS : ∀ n off g, l n = some (.inUse off g) → n ∈ S) {f : Nat}
    {V : List Nat} {c n : Nat} {d : Dict} {p x : Nat} (hcS : c ∈ S) (hc : c ∉ n :: V)
    (hx : (containerLength (lengthHop l limits bytes f) (c :: n :: V) d p).2 = .ok x) :
    cnt S (hopVis d (c :: n :: V)) +
      (containerLength (lengthHop l limits bytes f) (c :: n :: V) d p).1 + 1 ≤ cnt S V := by
  have h1 := cnt_cons_lt hcS hc
  have h2 := cnt_cons_le S V n
  unfold containerLength at hx ⊢
  unfold hopVis
  rcases hm : Dict.lookup d Core.ObjParse.nameLength with _ | o
  · simp only; omega
  · cases o with
    | ref m h =>
      rw [hm] at hx
      simp only at hx ⊢
      obtain ⟨h', -⟩ := lengthHop_snd_ok hx
      obtain ⟨off, l', hv, -, hl, -, -, -⟩ := lengthHop_ok h'
      rw [h']
      have := cnt_cons_lt (hS _ _ _ hl) hv
      simp only at this ⊢
      omega
    | _ => simp only; omega

/-- **Fuel independence of `/Length` resolution** (any lookup, compressed entries included):
with every in-use number in `S`, resolution with any two fuels above `cnt S V` gives the
identical (parse count, result) pair. -/
theorem resolve_fuel {pre : Core.Xref.ObjStm.Pre} {l : Nat → Option XrefEntry}
    (limits : Limits) (bytes : ByteArray) (S : List Nat)
    (hS : ∀ n off g, l n = some (.inUse off g) → n ∈ S) :
    ∀ f1 f2 V ref, cnt S V < f1 → cnt S V < f2 →
      resolveLengthAux pre l limits bytes f1 V ref =
        resolveLengthAux pre l limits bytes f2 V ref := by
  intro f1
  induction f1 using Nat.strongRecOn with
  | _ f1 ih =>
  intro f2 V ref h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, f1 = k + 1 := ⟨f1 - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, f2 = j + 1 := ⟨f2 - 1, by omega⟩
  rw [resolveLengthAux, resolveLengthAux]
  by_cases hv : ref.1 ∈ V
  · simp only [hv, ↓reduceIte]
  simp only [hv, ↓reduceIte]
  rcases hl : l ref.1 with _ | (⟨a, g⟩ | ⟨off, g'⟩ | ⟨c, idx⟩)
  · rfl
  · rfl
  · have hlt := cnt_cons_lt (hS _ _ _ hl) hv
    simp only
    split
    · rcases parseLengthObj limits bytes off ref.1 ref.2 with e | o
      · rfl
      · cases o
        all_goals try rfl
        rename_i m hh
        simp only
        rw [ih k (by omega) j _ _ (by omega) (by omega)]
    · rfl
  · simp only
    by_cases hcy : c = ref.1 ∨ c ∈ V
    · simp only [hcy, ↓reduceIte]
    simp only [hcy, ↓reduceIte]
    rcases hlc : l c with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
    · rfl
    · rfl
    · simp only
      split
      · rcases hph : parseContainerHead limits bytes off c with e | ⟨d, p⟩
        · rfl
        · simp only
          have hcS := hS _ _ _ hlc
          have hcV : c ∉ ref.1 :: V := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => hcy (Or.inl h), fun h => hcy (Or.inr h)⟩
          have hpos := cnt_pos hcS (fun h => hcy (Or.inr h))
          rw [lengthHop_fuel l limits bytes (f := j) (f' := k) (by omega) (by omega)]
          have hcnt : ∀ x, (containerLength (lengthHop l limits bytes k) (c :: ref.1 :: V) d p).2 =
              .ok x → _ := fun x hx => hop_cnt (limits := limits) (bytes := bytes) (f := k)
                (d := d) (p := p) (x := x) hS hcS hcV hx
          generalize containerLength (lengthHop l limits bytes k) (c :: ref.1 :: V) d p = X
            at hcnt ⊢
          rcases hX : X.2 with e | x
          · simp [containerMember]
          · have hc := hcnt x hX
            rcases containerMember pre limits bytes off c ref.1 idx d p (.ok x) with e | o
            · rfl
            · cases o
              all_goals try rfl
              rename_i m hh
              simp only
              rw [ih (k - X.1) (by omega) (j - X.1) _ _ (by omega) (by omega)]
      · rfl
    · rfl

/-- `lengthOf` is the same for any two fuels above the number of in-use objects. -/
theorem lengthOf_fuel {pre : Core.Xref.ObjStm.Pre} {l : Nat → Option XrefEntry}
    {limits : Limits} {bytes : ByteArray} {S : List Nat}
    (hS : ∀ n off g, l n = some (.inUse off g) → n ∈ S) {f1 f2 : Nat}
    (h1 : S.length < f1) (h2 : S.length < f2) :
    lengthOf pre l limits bytes f1 = lengthOf pre l limits bytes f2 := by
  funext self d at_
  unfold lengthOf lengthDict resolveLength
  have hc := Nat.le_trans (cnt_cons_le S [] self) (cnt_le S [])
  rcases Dict.lookup d Core.ObjParse.nameLength with _ | o
  · rfl
  · cases o
    all_goals try rfl
    rename_i m h
    simp only
    rw [resolve_fuel limits bytes S hS f1 f2 [self] (m, h) (by omega) (by omega)]

/-- The object parse is the same for any two fuels above the number of in-use objects. -/
theorem parseFun_fuel {l : Nat → Option XrefEntry} {limits : Limits} {bytes : ByteArray}
    {S : List Nat} (hS : ∀ n off g, l n = some (.inUse off g) → n ∈ S) {f1 f2 : Nat}
    (h1 : S.length < f1) (h2 : S.length < f2) :
    @parseIndirectResolved l limits bytes f1 = @parseIndirectResolved l limits bytes f2 := by
  funext pos pre
  unfold parseIndirectResolved
  rw [lengthOf_fuel (pre := pre) hS h1 h2]

/-- `ObjStm.fetchCompressedTrace` is the same for any two fuels above the number of in-use
objects (the fuel only reaches the container's parse). -/
theorem fetchCompressed_fuel {pre : Core.Xref.ObjStm.Pre} {l : Nat → Option XrefEntry}
    {limits : Limits} {bytes : ByteArray} {S : List Nat}
    (hS : ∀ n off g, l n = some (.inUse off g) → n ∈ S) {f1 f2 : Nat}
    (h1 : S.length < f1) (h2 : S.length < f2) (num : Nat) :
    Core.Xref.ObjStm.fetchCompressedTrace pre l limits bytes f1 num =
      Core.Xref.ObjStm.fetchCompressedTrace pre l limits bytes f2 num := by
  unfold Core.Xref.ObjStm.fetchCompressedTrace
  rw [parseFun_fuel hS h1 h2]

/-- **`getObject` is equal** on two documents over the same bytes and decryption state whose
lookups are equal up to free entries (compressed entries included), when each fuel
(`objectCount`) exceeds the length of a list holding that document's in-use numbers: the free
entries, which make the fuels differ, are not observed. -/
theorem getObject_strip_cnt {d d' : OpenDoc} (hb : d.bytes = d'.bytes) (hc : d.crypt = d'.crypt)
    (hs : ∀ n, strip (d.lookup n) = strip (d'.lookup n)) {S1 S2 : List Nat}
    (hS1 : ∀ n off g, d.lookup n = some (.inUse off g) → n ∈ S1)
    (hS2 : ∀ n off g, d'.lookup n = some (.inUse off g) → n ∈ S2)
    (h1 : S1.length < d.objectCount) (h2 : S2.length < d'.objectCount)
    (limits : Limits) (num gen : Nat) :
    d.getObject limits num gen = d'.getObject limits num gen := by
  have hS1' : ∀ n off g, d'.lookup n = some (.inUse off g) → n ∈ S1 := by
    intro n off g h
    rcases strip_cases hs n with he | ⟨_, h2'⟩
    · exact hS1 n off g (he.trans h)
    · rcases h2' with h2' | ⟨a, g', h2'⟩ <;> rw [h2'] at h <;> cases h
  have hpre : d.pre = d'.pre := by unfold OpenDoc.pre; rw [hc]
  have hdec : d.decrypt = d'.decrypt := by
    funext a b c; unfold OpenDoc.decrypt; rw [hc]
  have hP : @parseIndirectResolved d'.lookup limits d'.bytes d.objectCount =
      @parseIndirectResolved d'.lookup limits d'.bytes d'.objectCount :=
    (parseFun_fuel (f2 := max d.objectCount d'.objectCount) hS1' h1 (by omega)).trans
      (parseFun_fuel (f1 := d'.objectCount) (f2 := max d.objectCount d'.objectCount) hS2 h2
        (by omega)).symm
  have hF : ∀ num, Core.Xref.ObjStm.fetchCompressedTrace d'.pre d'.lookup limits d'.bytes
      d.objectCount num = Core.Xref.ObjStm.fetchCompressedTrace d'.pre d'.lookup limits
      d'.bytes d'.objectCount num := fun num => by
    unfold Core.Xref.ObjStm.fetchCompressedTrace
    rw [hP]
  unfold OpenDoc.getObject OpenDoc.getObjectTrace
  rcases strip_cases hs num with he | ⟨h1', h2'⟩
  · rw [he, hb, hpre, hdec, fetchCompressed_strip hs limits _ _ num he, parseFun_strip hs, hP,
      hF]
  · rcases h1' with h1' | ⟨a, g, h1'⟩ <;> rcases h2' with h2' | ⟨a', g', h2'⟩ <;> rw [h1', h2']

/-- The in-use numbers of an entry list. -/
def inUseNums : List (Nat × XrefEntry) → List Nat
  | [] => []
  | (n, .inUse _ _) :: es => n :: inUseNums es
  | _ :: es => inUseNums es

/-- Every in-use entry's number is in `inUseNums`. -/
theorem mem_inUseNums {es : List (Nat × XrefEntry)} {n off g : Nat}
    (h : (n, XrefEntry.inUse off g) ∈ es) : n ∈ inUseNums es := by
  induction es with
  | nil => cases h
  | cons e es ih =>
    obtain ⟨m, x⟩ := e
    rcases List.mem_cons.mp h with h' | h'
    · cases h'; simp [inUseNums]
    · have := ih h'
      cases x <;> simp [inUseNums, this]

/-- An entry list with a non-in-use entry has fewer in-use numbers than entries. -/
theorem inUseNums_lt {es : List (Nat × XrefEntry)} {n a g : Nat}
    (h : (n, XrefEntry.free a g) ∈ es) : (inUseNums es).length < es.length := by
  have hle : ∀ es : List (Nat × XrefEntry), (inUseNums es).length ≤ es.length := by
    intro es
    induction es with
    | nil => simp [inUseNums]
    | cons e es ih =>
      obtain ⟨m, x⟩ := e
      cases x <;> simp [inUseNums] <;> omega
  induction es with
  | nil => cases h
  | cons e es ih =>
    obtain ⟨m, x⟩ := e
    rcases List.mem_cons.mp h with h' | h'
    · cases h'; simp [inUseNums]; exact Nat.lt_succ_of_le (hle es)
    · have := ih h'
      cases x <;> simp [inUseNums] <;> omega

/-! ## Exact C4 with compressed entries -/

/-- **C4 with compressed entries, exact form (repair conservativity; task 12.7f).** If the
strict path opens `bytes` as `d` and `HypCompEq limits bytes d` holds (compressed entries
allowed; repair rule R6 finds exactly the strict compressed entries; equal fuel), the repair
path also succeeds; its document is flagged `repaired`, has the same bytes, the same in-use
entries, the **same compressed entries** and the same `/Root` as `d`, and for **every**
`num gen` its `getObject` is **equal** to `d`'s. -/
theorem c4_comp_eq {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : HypCompEq limits bytes d) :
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, d'.lookup n = some (.inUse off g) ↔ d.lookup n = some (.inUse off g)) ∧
      (∀ n c i, d'.lookup n = some (.compressed c i) ↔ d.lookup n = some (.compressed c i)) ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  have hpl := hh.2.2.2.2.2
  have htr := hh.2.2.2.2.1
  have hbytes := strictOpen_bytes hs
  obtain ⟨-, -, -, -, hval⟩ := strictOpen_ok hs
  unfold trailerOkCompEq at htr
  split at htr
  · rename_i sec tr hrep
    obtain ⟨henc, hroot, hU, hC, -⟩ := compStrip_sec hh hrep
    let d' := OpenDoc.mk' bytes sec tr 0 true
    have hc : d.crypt = d'.crypt := Option.isNone_iff_eq_none.mp hpl
    have hz : (0, XrefEntry.free 0 65535) ∈ sec.entries :=
      (Repair.repair_entries hrep).1 _ (by simp [Repair.scanSection])
    have hl2 : ∀ m e, d'.lookup m = some e ↔ (m, e) ∈ sec.entries := fun m e => by
      rw [WritePrefix.lookup_eq d']; exact Unambiguous.lookupEntry_eq_some_iff sec.keys_nodup
    have hl1 : ∀ m e, d.lookup m = some e ↔ (m, e) ∈ d.xref.entries := fun m e => by
      rw [WritePrefix.lookup_eq d, Unambiguous.lookupEntry_eq_some_iff d.xref.keys_nodup]
    have hS : ∀ n off g, d'.lookup n = some (.inUse off g) → n ∈ inUseNums sec.entries :=
      fun n off g h => mem_inUseNums ((hl2 _ _).mp h)
    have hS1 : ∀ n off g, d.lookup n = some (.inUse off g) → n ∈ inUseNums d.xref.entries :=
      fun n off g h => mem_inUseNums ((hl1 _ _).mp h)
    have h1 : (inUseNums sec.entries).length < d'.objectCount := by
      simp only [OpenDoc.objectCount, d', OpenDoc.mk', List.size_toArray]; exact inUseNums_lt hz
    have h2 : (inUseNums d.xref.entries).length < d.objectCount := by
      simp only [OpenDoc.objectCount, d.index_eq, List.size_toArray]
      exact inUseNums_lt hh.1
    have hg : ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen :=
      fun num gen => getObject_strip_cnt (by rw [hbytes]; rfl) hc.symm
        (fun n => (strip_of hU hC n).symm) hS hS1 h1 h2 limits num gen
    have hv : validate limits d' = .ok d' :=
      validate_congr hroot.symm (fun n g => (hg n g).symm) hval
    refine ⟨d', ?_, rfl, by rw [hbytes]; rfl, fun n off g => (hU n off g).symm,
      fun n c i => (hC n c i).symm, hroot, hg⟩
    unfold repairOpen
    rw [hrep]
    simp only
    rw [withCrypt_plain (d := d') henc]
    exact hv
  · cases htr

/-- **Exact C4 with compressed entries, from the checker.** -/
theorem c4_comp_eq_check {limits : Limits} {bytes : ByteArray}
    (hc : checkCompEq limits bytes = true) :
    ∃ d d', strictOpen limits bytes = .ok d ∧ repairOpen limits bytes = .ok d' ∧
      d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, d'.lookup n = some (.inUse off g) ↔ d.lookup n = some (.inUse off g)) ∧
      (∀ n c i, d'.lookup n = some (.compressed c i) ↔ d.lookup n = some (.compressed c i)) ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  unfold checkCompEq at hc
  split at hc
  · rename_i d hs
    obtain ⟨d', h⟩ := c4_comp_eq hs (of_decide_eq_true hc)
    exact ⟨d, d', hs, h⟩
  · cases hc

/-! ## Different fuels: equal unless the repair path runs out of fuel -/

/-- The error of `/Length` resolution running out of fuel. -/
def fuelOut : Error := .limitExceeded .objects

/-- **Fuel monotonicity of `/Length` resolution beyond successes** (any lookup, compressed
entries included): if resolution with fuel `f` does not end in `fuelOut`, any fuel `f' ≥ f`
gives the identical (parse count, result) pair. (Running out of fuel is the only way the fuel
is observed, and its error propagates unchanged.) -/
theorem resolve_mono_ne (pre : Core.Xref.ObjStm.Pre) (lookup : Nat → Option XrefEntry)
    (limits : Limits) (bytes : ByteArray) :
    ∀ f f' V ref, f ≤ f' → (resolveLengthAux pre lookup limits bytes f V ref).2 ≠ .error fuelOut →
      resolveLengthAux pre lookup limits bytes f' V ref =
        resolveLengthAux pre lookup limits bytes f V ref := by
  intro f
  induction f using Nat.strongRecOn with
  | _ f ih =>
  intro f' V ref hff hne
  by_cases hv : ref.1 ∈ V
  · rw [resolveLengthAux.eq_def, resolveLengthAux.eq_def]
    simp [hv]
  cases f with
  | zero =>
    rw [resolveLengthAux.eq_def] at hne
    simp [hv, fuelOut] at hne
  | succ k =>
  obtain ⟨k', rfl⟩ : ∃ k', f' = k' + 1 := ⟨f' - 1, by omega⟩
  rw [resolveLengthAux] at hne
  rw [resolveLengthAux, resolveLengthAux]
  simp only [hv, ↓reduceIte] at hne ⊢
  rcases hl : lookup ref.1 with _ | (⟨a, g⟩ | ⟨off, g'⟩ | ⟨c, idx⟩)
  · rfl
  · rfl
  · rw [hl] at hne
    by_cases hg : g' = ref.2
    · simp only [hg, ↓reduceIte] at hne ⊢
      rcases hp : parseLengthObj limits bytes off ref.1 ref.2 with e | o
      · rfl
      · rw [hp] at hne
        cases o
        all_goals try rfl
        simp only at hne ⊢
        rw [ih k (by omega) k' _ _ (by omega) hne]
    · simp only [hg, ↓reduceIte]
  · rw [hl] at hne
    by_cases hcy : c = ref.1 ∨ c ∈ V
    · simp only [hcy, ↓reduceIte]
    · simp only [hcy, ↓reduceIte] at hne ⊢
      rcases hc : lookup c with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
      · rfl
      · rfl
      · rw [hc] at hne
        by_cases hg : g = 0
        · simp only [hg, ↓reduceIte] at hne ⊢
          rcases hph : parseContainerHead limits bytes off c with e | ⟨d, p⟩
          · rfl
          · rw [hph] at hne
            simp only at hne ⊢
            have hr1 : (containerLength
                (lengthHop lookup limits bytes k)
                (c :: ref.1 :: V) d p).2 ≠ .error fuelOut := by
              intro h1
              rw [h1] at hne
              simp [containerMember] at hne
            have hcl : containerLength
                (lengthHop lookup limits bytes k') (c :: ref.1 :: V) d p =
                containerLength
                (lengthHop lookup limits bytes k)
                (c :: ref.1 :: V) d p := by
              unfold containerLength at hr1 ⊢
              split
              · rename_i m hh hm
                rw [hm] at hr1
                exact lengthHop_mono_ne (by omega) hr1
              · rfl
            rw [hcl]
            rcases hm : containerMember pre limits bytes off c ref.1 idx d p
                (containerLength (lengthHop lookup limits bytes k)
                  (c :: ref.1 :: V) d p).2 with e | o
            · rfl
            · rw [hm] at hne
              cases o
              all_goals try rfl
              simp only at hne ⊢
              rw [ih _ (by omega) _ _ _ (by omega) hne]
        · simp only [hg, ↓reduceIte]
      · rfl

/-- `lengthOf` with a larger fuel is unchanged unless it ran out of fuel. -/
theorem lengthOf_mono_ne {pre : Core.Xref.ObjStm.Pre} {lookup : Nat → Option XrefEntry}
    {limits : Limits} {bytes : ByteArray} {f f' self : Nat} {d : Dict} {at_ : Nat}
    (hff : f ≤ f') (hne : lengthOf pre lookup limits bytes f self d at_ ≠ .error fuelOut) :
    lengthOf pre lookup limits bytes f' self d at_ = lengthOf pre lookup limits bytes f self d at_ := by
  unfold lengthOf lengthDict resolveLength at hne ⊢
  rcases hd : Dict.lookup d Core.ObjParse.nameLength with _ | o
  · rfl
  · rw [hd] at hne
    cases o
    case ref m g =>
      simp only at hne ⊢
      have hr : (resolveLengthAux pre lookup limits bytes f [self] (m, g)).2 ≠ .error fuelOut := by
        intro h; rw [h] at hne; exact hne rfl
      rw [resolve_mono_ne pre lookup limits bytes f f' [self] (m, g) hff hr]
    all_goals rfl

/-- The object parse with a larger fuel is unchanged unless it ran out of fuel. -/
theorem parseIndirectResolved_mono_ne {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {f f' pos : Nat} {pre : Core.Xref.ObjStm.Pre} (hff : f ≤ f')
    (hne : parseIndirectResolved lookup limits bytes f pos pre ≠ .error fuelOut) :
    parseIndirectResolved lookup limits bytes f' pos pre =
      parseIndirectResolved lookup limits bytes f pos pre := by
  rw [parseIndirectResolved_eq_with] at hne ⊢
  rw [parseIndirectResolved_eq_with]
  rcases hc : callPoint limits bytes pos with _ | ⟨n, d, p⟩
  · exact parseIndirectWith_congr (fun n d p h' => by rw [hc] at h'; cases h')
  · rw [parseIndirectWith_const hc] at hne ⊢
    rw [parseIndirectWith_const (lenF := lengthOf pre lookup limits bytes f) hc]
    have hl : lengthOf pre lookup limits bytes f n d p ≠ .error fuelOut := by
      intro h; rw [h, parseIndirectWith_err hc] at hne; exact hne rfl
    rw [lengthOf_mono_ne hff hl]

/-- `ObjStm.fetchCompressedTrace` with a larger fuel is unchanged unless its result ran out of
fuel. -/
theorem fetchCompressed_mono_ne {pre : Core.Xref.ObjStm.Pre} {lookup : Nat → Option XrefEntry}
    {limits : Limits} {bytes : ByteArray} {f f' num : Nat} (hff : f ≤ f')
    (hne : (Core.Xref.ObjStm.fetchCompressedTrace pre lookup limits bytes f num).result ≠
      .error fuelOut) :
    Core.Xref.ObjStm.fetchCompressedTrace pre lookup limits bytes f' num =
      Core.Xref.ObjStm.fetchCompressedTrace pre lookup limits bytes f num := by
  unfold Core.Xref.ObjStm.fetchCompressedTrace at hne ⊢
  rcases hl : lookup num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, idx⟩)
  · rfl
  · rfl
  · rfl
  rw [hl] at hne
  simp only at hne ⊢
  split
  · rfl
  rename_i hcn
  simp only [hcn, ↓reduceIte] at hne
  rcases hc : lookup c with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
  · rfl
  · rfl
  · rw [hc] at hne
    simp only at hne ⊢
    split
    · rename_i hg
      simp only [hg, ↓reduceIte] at hne
      have hp : parseIndirectResolved lookup limits bytes f off pre ≠ .error fuelOut := by
        intro h; rw [h] at hne; exact hne rfl
      rw [parseIndirectResolved_mono_ne hff hp]
    · rfl
  · rfl

/-- **`getObject` with different fuels.** Two documents over the same bytes and decryption
state whose lookups are equal up to free entries, the second with at most the first's fuel:
wherever the second's `getObject` does not run out of fuel, the two are equal. -/
theorem getObject_strip_le {d d' : OpenDoc} (hb : d.bytes = d'.bytes) (hc : d.crypt = d'.crypt)
    (hs : ∀ n, strip (d.lookup n) = strip (d'.lookup n)) (hf : d'.objectCount ≤ d.objectCount)
    (limits : Limits) (num gen : Nat)
    (hne : d'.getObject limits num gen ≠ .error fuelOut) :
    d.getObject limits num gen = d'.getObject limits num gen := by
  have hpre : d.pre = d'.pre := by unfold OpenDoc.pre; rw [hc]
  have hdec : d.decrypt = d'.decrypt := by
    funext a b c; unfold OpenDoc.decrypt; rw [hc]
  unfold OpenDoc.getObject OpenDoc.getObjectTrace at hne ⊢
  rcases strip_cases hs num with he | ⟨h1, h2⟩
  · rw [he, hb, hpre, hdec, fetchCompressed_strip hs limits _ _ num he, parseFun_strip hs]
    rcases hl : d'.lookup num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, idx⟩)
    · rfl
    · rfl
    · rw [hl] at hne
      simp only at hne ⊢
      split
      · rename_i hg
        simp only [hg, ↓reduceIte] at hne
        have hp : parseIndirectResolved d'.lookup limits d'.bytes d'.objectCount off d'.pre ≠
            .error fuelOut := by
          intro h; rw [h] at hne; exact hne rfl
        rw [parseIndirectResolved_mono_ne hf hp]
      · rfl
    · rw [hl] at hne
      simp only at hne ⊢
      split
      · rename_i hg
        simp only [hg, ↓reduceIte] at hne
        have hp : (Core.Xref.ObjStm.fetchCompressedTrace d'.pre d'.lookup limits d'.bytes
            d'.objectCount num).result ≠ .error fuelOut := by
          intro h; rw [h] at hne; exact hne rfl
        rw [fetchCompressed_mono_ne hf hp]
      · rfl
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]

/-- **C4 with compressed entries without the fuel condition (task 12.7f).** If the strict
path opens `bytes` as `d` and `HypCompStrip limits bytes d` holds (no H8: the strict section
may have more free entries, hence more fuel), then the repair path fails with `fuelOut`, or
it succeeds with a document that is flagged `repaired`, has the same bytes, in-use entries,
compressed entries and `/Root` as `d`, and whose `getObject` is **equal** to `d`'s at every
`num gen` where it does not run out of fuel itself. (Since task 12.7g it never does:
`c4_comp_eq` holds under the same hypothesis.) -/
theorem c4_comp_strip {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : HypCompStrip limits bytes d) :
    repairOpen limits bytes = .error fuelOut ∨
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, d'.lookup n = some (.inUse off g) ↔ d.lookup n = some (.inUse off g)) ∧
      (∀ n c i, d'.lookup n = some (.compressed c i) ↔ d.lookup n = some (.compressed c i)) ∧
      d'.trailer.root? = d.trailer.root? ∧
      d'.objectCount ≤ d.objectCount ∧
      ∀ num gen, d'.getObject limits num gen ≠ .error fuelOut →
        d'.getObject limits num gen = d.getObject limits num gen := by
  have hpl := hh.2.2.2.2.2
  have htr := hh.2.2.2.2.1
  have hbytes := strictOpen_bytes hs
  obtain ⟨-, -, -, -, hval⟩ := strictOpen_ok hs
  unfold trailerOkCompEq at htr
  split at htr
  · rename_i sec tr hrep
    obtain ⟨henc, hroot, hU, hC, hlen⟩ := compStrip_sec hh hrep
    let d' := OpenDoc.mk' bytes sec tr 0 true
    have hc : d.crypt = d'.crypt := Option.isNone_iff_eq_none.mp hpl
    have hf : d'.objectCount ≤ d.objectCount := by
      simp only [OpenDoc.objectCount, d.index_eq, d', OpenDoc.mk', List.size_toArray]
      exact hlen
    have hg : ∀ num gen, d'.getObject limits num gen ≠ .error fuelOut →
        d'.getObject limits num gen = d.getObject limits num gen :=
      fun num gen hne => (getObject_strip_le (by rw [hbytes]; rfl) hc (strip_of hU hC) hf
        limits num gen hne).symm
    have hro : repairOpen limits bytes = validate limits d' := by
      unfold repairOpen
      rw [hrep]
      simp only
      rw [withCrypt_plain (d := d') henc]
    rw [hro]
    -- `validate` reads one object, the `/Root`
    rcases hr : d.trailer.root? with _ | ⟨n, g⟩
    · unfold validate at hval; rw [hr] at hval; cases hval
    · by_cases hne : d'.getObject limits n g = .error fuelOut
      · left
        unfold validate
        rw [show d'.trailer.root? = some (n, g) from hroot.trans hr]
        simp only [hne]
      · right
        have hv : validate limits d' = .ok d' := by
          unfold validate at hval ⊢
          rw [show d'.trailer.root? = some (n, g) from hroot.trans hr]
          rw [hr] at hval
          simp only at hval ⊢
          rw [hg n g hne]
          split at hval
          · cases hval
          · rfl
          all_goals cases hval
        exact ⟨d', hv, rfl, by rw [hbytes]; rfl, fun n off g => (hU n off g).symm,
          fun n c i => (hC n c i).symm, hroot.trans hr, hf, hg⟩
  · cases htr

/-- **C4 with compressed entries without the fuel condition, from the checker.** -/
theorem c4_comp_strip_check {limits : Limits} {bytes : ByteArray}
    (hc : checkCompStrip limits bytes = true) :
    ∃ d, strictOpen limits bytes = .ok d ∧ (repairOpen limits bytes = .error fuelOut ∨
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, d'.lookup n = some (.inUse off g) ↔ d.lookup n = some (.inUse off g)) ∧
      (∀ n c i, d'.lookup n = some (.compressed c i) ↔ d.lookup n = some (.compressed c i)) ∧
      d'.trailer.root? = d.trailer.root? ∧
      d'.objectCount ≤ d.objectCount ∧
      ∀ num gen, d'.getObject limits num gen ≠ .error fuelOut →
        d'.getObject limits num gen = d.getObject limits num gen) := by
  unfold checkCompStrip at hc
  split at hc
  · rename_i d hs
    exact ⟨d, hs, c4_comp_strip hs (of_decide_eq_true hc)⟩
  · cases hc

/-! ## Fixtures -/

-- `objStmBytes` (objects 2, 3 compressed in object stream 4): the strict and the repaired
-- sections both have six entries, R6 finds exactly the strict compressed entries, so
-- `HypCompEq` holds and `c4_comp_eq_check` applies.
#guard checkCompEq Limits.default objStmBytes = true
#guard checkCompStrip Limits.default objStmBytes = true
#guard (List.range 7).all (sameObj objStmBytes)
-- Files without compressed entries: `HypCompStrip` holds whenever `HypFree` does
-- (`freeEntryBytes` has a free entry for object 4, so H8 fails there); a file that fails H5
-- fails here too.
#guard checkCompEq Limits.default repairFixedBytes = true
#guard checkCompStrip Limits.default freeEntryBytes = true
-- Task 12.7g: H8 is dropped, so `freeEntryBytes` (sections of 7 and 6 entries) passes the
-- exact checker; `fuelEq` still tells the two sections apart.
#guard checkCompEq Limits.default freeEntryBytes = true
#guard (List.range 7).all (sameObj freeEntryBytes)
#guard checkCompEq Limits.default repairDiffBytes = false
-- Encrypted files are excluded (H6, and R6 does not run on encrypted trailers).
#guard checkCompStrip Limits.default encBytes = false

end SafePdf.Spec.RepairAgreeComp
