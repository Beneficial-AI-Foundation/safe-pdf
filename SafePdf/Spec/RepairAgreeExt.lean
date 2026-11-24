import SafePdf.Spec.RepairAgreeFree

/-!
# C4 for encrypted files and for compressed entries (tasks 12.7c, 12.7e)

Plan.md §5 (claim C4), §5.4 (the repair path), §6 Phase 12 "Proof gaps" (task 12.7c);
`docs/safety.md` §5, gap 1. Extends `Spec.RepairAgree` (12.7) and `Spec.RepairAgreeFree`
(12.7a/12.7d), whose H2 forbade compressed entries and whose H5/H6 forbade encryption.

## (b) Encrypted files: exact C4

`Crypt.setup` reads only the encryption dictionary, its reference and the first `/ID` string
of the trailer (`Crypt.id0Of`); `OpenDoc.encryptDict` reads the trailer's `/Encrypt` value
and, when it is a reference, the lookup (compressed or not) and `getObject` of the document
without decryption state. So equal `/Encrypt` and `/ID` on both trailers plus 12.7a's section
agreement give the **same decryption state** (rule E3), and then the same decrypted objects.

* `getObject_eq_crypt`: `RepairAgreeFree.getObject_eq` for any equal decryption states (the
  object-stream pre-pass and `decrypt` depend only on `crypt`).
* `SecOk` (H1–H4 of `HypFree`), `inUse_mem_iff_of`, `getObject_sec`: any two documents over
  the strict and the repaired section with equal states have equal `getObject`.
* `encryptDict_congr`, `withCrypt_congr`: equal flag, `/Encrypt`, first `/ID`, no compressed
  entries and equal undecrypted `getObject` ⇒ `withCrypt` yields the same state.
* `HypEnc` = `SecOk` ∧ H5e (`trailerOkEnc`: the repaired trailer has the strict `/Root`,
  `encrypted` flag, `/Encrypt` value and first `/ID` string); decidable, checker `checkEnc`.
  H6 is dropped. Rule R4' copies `/Encrypt` and `/ID` only when the chosen dictionary lacks
  `/Encrypt`; H5e holds whenever the newest `trailer` dictionary with `/Root` is the strict
  trailer, the usual case.
* `c4_enc` / `c4_enc_check`: the repair path succeeds; same bytes, in-use entries, `/Root`,
  **same `crypt`**, and **equal** `getObject` (decrypted) for every `num gen`.
* Fixtures: `encBytes`, an RC4-40 file (`/V 1 /R 2`, indirect `/Encrypt`) written by an
  independent stdlib-Python generator, passes `checkEnc` (and fails `checkFree`, by H6);
  `/Lang` and the content stream decrypt to their plaintexts and all objects agree.
  `encStaleBytes` (a stale `trailer` dictionary with another `/ID`, in a comment) shows H5e
  is needed: the strict path opens and decrypts it, the repair path fails with
  `Error.encryption`.

## (a) Compressed entries: a one-sided result (tasks 12.7c, 12.7e)

Before task 12.7e, `Repair` (rules R1–R5) recorded only classic `N G obj` headers and never
parsed object streams, so every object that lives only in an object stream was `null` (rule
G4) after repair, and C4 was false for compressed entries (`objStmBytes`: strictly
dictionaries, after repair `null`). Task 12.7e added **repair rule R6**
(`Repair.withObjStm`): classic `/Type /ObjStm` containers are decoded and their members get
compressed entries (newest container wins, a classic hit always wins, no self-member, not
for encrypted trailers). On `objStmBytes` the repair path now has the strict entries
`2 → compressed 4 0`, `3 → compressed 4 1`, and every object agrees.

What is proved (`HypComp`: `HypFree` with compressed entries allowed and H5 replaced by H5c,
`trailerOkComp`: every compressed entry of the repaired section is the strict entry of its
number; decidable, checker `checkComp`; `HypFree.toComp` via `trailerOk_toComp`):

* `resolve_sub`, `lengthOf_sub`, `parseIndirectResolved_sub`, `getObject_sub`: a successful
  resolution under a lookup without compressed entries transfers to any lookup that extends
  its in-use entries, with any larger fuel (12.7c, unchanged).
* `resolve_sub2`, `lengthOf_sub2`, `parseIndirectResolved_sub2`, `fetchCompressed_sub2`,
  `getObject_sub2` (12.7e): the same when the smaller lookup **has** compressed entries, all
  of which the larger one has too; `resolve_sub2` gives the identical (count, result) pair,
  which the object-stream hop needs (the second hop's fuel is `fuel - used`).
* `c4_comp` / `c4_comp_check`: when both paths open the file, the repaired document has the
  same bytes, in-use entries and `/Root`; for every object number **not compressed** strictly,
  every success of the repair path's `getObject` is the strict one; every **compressed**
  object is `null` after repair **or** has the same compressed entry, and then every success
  of the repair path is the strict one. **Changed in 12.7e:** the last conjunct used to read
  "every compressed object is `null` after repair", which R6 makes false by design; and H5
  (`trailerOk`, which now includes H7: no compressed entry after repair) became H5c.
* `#guard`s on `objStmBytes`: `checkComp` holds, `checkFree` and `check` fail, objects 2 and
  3 are `("dict", "dict")`, objects 0–6 agree.

The exact theorems (`RepairAgree.c4`, `RepairAgreeFree.c4_free`, `c4_enc`, `c4_bytes`, …)
gained H7 through `trailerOk` / `trailerOkEnc`: the repaired section has no compressed entry
(`Repair.repair_scan` then makes it the scanned section, as before). H7 is necessary for
them: a strictly valid file with an orphan object stream (members free or absent strictly)
gets the members back after repair, where strict returns `null`.

## Open: notes for 12.7f (exact C4 for compressed entries)

* Hypothesis shape: H1, H3, H4, H6 as in `HypComp`; H2c (in-use strict entries are newest
  scan hits; compressed strict entries allowed); **H7f: the repaired section equals the
  strict section up to free entries**, i.e. for every `n`, `strip` of the strict and the
  repaired lookup agree (compressed entries included). Decidable from `Repair.repair`'s
  output (compare the two entry lists with free entries dropped). A byte-level replacement
  for H7f would say: every strict container is a classic newest hit of generation 0 whose
  decoded header lists exactly the strict compressed entries pointing into it, no number is
  both classic and compressed, and R6's newest-container rule picks the strict container
  (this needs a characterization of `Repair.r6Raw`, including its `lastEnd` skip and the
  failure/decode budgets, which is much more work than H7f).
* Proof route: generalize `LookupRel` (RepairAgreeFree) to allow **equal** compressed
  entries on both sides (drop `nc1`/`nc2`, require `strip` equality only), then redo
  `resolve_agree`/`resolve_eq` with the object-stream branch (as `resolve_sub2` does: the
  pair (count, result) must be equal, not only the result, because of `fuel - used`); the
  fuel argument `cnt S V` must also count containers visited through the hop (the hop adds
  `c :: ref.1` to the visiting list). `getObject_eq_crypt`'s compressed branch then follows
  from equal `fetchCompressedTrace` (same lookup on the container, same fuel bound).
* `objectCount` differs when free entries differ, as in 12.7a: compressed entries count on
  both sides, so `S` (in-use numbers) still bounds the fuel needed.
* Encrypted files **with** compressed entries (`HypEnc` requires `SecOk`, i.e. none): R6 does
  not run for an encrypted repaired trailer, so the repaired section never has compressed
  entries there; exact C4 for them needs R6 to run after `withCrypt` (decrypting containers
  with the repaired state, `OpenDoc.pre`), a Core change in `Core.Open.repairOpen`, plus
  `encryptDict`'s special case for a compressed `/Encrypt` reference.
* Catalog in an object stream: R4 synthesizes `/Root` only from **classic** catalog objects,
  so a file with no `trailer` keyword (xref-stream files) whose catalog is compressed still
  fails repair; a follow-up could take `/Root` from the newest `/Type /XRef` dictionary (as
  R4' does for `/Encrypt`) or search R6 members for `/Type /Catalog`.
-/

namespace SafePdf.Spec.RepairAgreeExt

open SafePdf
open SafePdf.Core.Open
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)
open SafePdf.Core.Xref.Length
open SafePdf.Spec.RepairAgree
open SafePdf.Spec.RepairAgreeFree
open SafePdf.Repair (scanSection toEntries)

/-! ## `getObject` with equal decryption states -/

/-- **`getObject` is equal** on two documents over the same bytes with the **same decryption
state** (any, not only `none`) whose lookups are related by `LookupRel`, when both fuels
(`objectCount`) exceed the number of in-use objects. Generalizes
`RepairAgreeFree.getObject_eq` (which needs `crypt = none` on both sides). -/
theorem getObject_eq_crypt {d d' : OpenDoc} (hb : d.bytes = d'.bytes) (hc : d.crypt = d'.crypt)
    (h : LookupRel d.lookup d'.lookup) (S : List Nat)
    (hS : ∀ n off g, d.lookup n = some (.inUse off g) → n ∈ S)
    (hf : S.length < d.objectCount) (hf' : S.length < d'.objectCount) (limits : Limits)
    (num gen : Nat) : d.getObject limits num gen = d'.getObject limits num gen := by
  have hpre : d.pre = d'.pre := by unfold OpenDoc.pre; rw [hc]
  have hdec : d.decrypt = d'.decrypt := by
    funext a b c; unfold OpenDoc.decrypt; rw [hc]
  unfold OpenDoc.getObject OpenDoc.getObjectTrace
  rcases h.cases num with ⟨off, g, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    simp only
    by_cases hg : g = gen
    · simp only [hg, ↓reduceIte]
      rw [parseIndirectResolved_eq_with, parseIndirectResolved_eq_with, ← hb, ← hpre, hdec]
      rw [parseIndirectWith_congr (lenF := lengthOf d.pre d.lookup limits d.bytes d.objectCount)
        (lenG := lengthOf d.pre d'.lookup limits d.bytes d'.objectCount)
        (fun n dd p _ => lengthOf_eq h limits d.bytes S hS _ _ n
          (Nat.lt_of_le_of_lt (cnt_le S [n]) hf) (Nat.lt_of_le_of_lt (cnt_le S [n]) hf') dd p)]
    · simp only [hg, ↓reduceIte]
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]

/-! ## The section part of the hypothesis (H1–H4 of `HypFree`) -/

/-- H1–H4 of `HypFree` (the cross-reference part): `0 → free 0 65535`; every strict entry is
free or in use at the newest scan hit of its number (no compressed entry); every scan hit has
an in-use strict entry; the scan's distinct numbers fit in `limits.maxObjects`. -/
def SecOk (limits : Limits) (bytes : ByteArray) (sec : XrefSection) : Prop :=
  (0, XrefEntry.free 0 65535) ∈ sec.entries ∧
  (∀ x ∈ sec.entries, EntryOkFree (hits limits bytes) x) ∧
  (∀ x ∈ hits limits bytes, ∃ e ∈ sec.entries, e.1 = x.1 ∧ isInUse e.2 = true) ∧
  (newestHits (hits limits bytes)).length ≤ limits.maxObjects

/-- `SecOk` is decidable. -/
instance instDecidableSecOk (limits : Limits) (bytes : ByteArray) (sec : XrefSection) :
    Decidable (SecOk limits bytes sec) := by
  unfold SecOk; infer_instance

/-- The in-use entries of a section `sec` are those of the repaired section when every in-use
entry of `sec` is the newest scan hit of its number (H2's in-use part), every hit has an in-use
entry (H3) and the scan is below the cap (H4). -/
theorem inUse_mem_iff_of {limits : Limits} {bytes : ByteArray} {sec : XrefSection}
    (hent : ∀ n off g, (n, XrefEntry.inUse off g) ∈ sec.entries →
      1 ≤ n ∧ newestHit (hits limits bytes) n = some (n, g, off))
    (hcov : ∀ x ∈ hits limits bytes, ∃ e ∈ sec.entries, e.1 = x.1 ∧ isInUse e.2 = true)
    (hcap : (newestHits (hits limits bytes)).length ≤ limits.maxObjects) (n off g : Nat) :
    (n, XrefEntry.inUse off g) ∈ sec.entries ↔
      (n, XrefEntry.inUse off g) ∈ (scanSection limits bytes).entries := by
  simp only [scanSection, toEntries, scanObjects_eq limits bytes hcap, List.mem_cons,
    List.mem_map]
  constructor
  · intro hx
    obtain ⟨h1, hn⟩ := hent _ _ _ hx
    exact Or.inr ⟨(n, g, off), (newestHits_mem_iff _ _).mpr ⟨h1, hn⟩, rfl⟩
  · rintro (h0 | ⟨⟨yn, yg, yoff⟩, hy, hyx⟩)
    · simp at h0
    · simp only [Prod.mk.injEq, XrefEntry.inUse.injEq] at hyx
      obtain ⟨rfl, rfl, rfl⟩ := hyx
      obtain ⟨h1, hy⟩ := (newestHits_mem_iff _ _).mp hy
      obtain ⟨e, he, hk, hu⟩ := hcov _ (List.mem_of_find?_eq_some hy)
      obtain ⟨n', e⟩ := e
      cases e with
      | free _ _ => simp [isInUse] at hu
      | compressed _ _ => simp [isInUse] at hu
      | inUse off' g' =>
        have hok := hent _ _ _ he
        simp only at hk
        subst hk
        obtain ⟨-, hn⟩ := hok
        rw [hy] at hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨-, rfl, rfl⟩ := hn
        exact he

/-- Under `SecOk`, the strict and the repaired sections have the same in-use entries. -/
theorem SecOk.inUse_mem_iff {limits : Limits} {bytes : ByteArray} {sec : XrefSection}
    (h : SecOk limits bytes sec) (n off g : Nat) :
    (n, XrefEntry.inUse off g) ∈ sec.entries ↔
      (n, XrefEntry.inUse off g) ∈ (scanSection limits bytes).entries :=
  inUse_mem_iff_of (fun _ _ _ hx => h.2.1 _ hx) h.2.2.1 h.2.2.2 n off g

/-- Under `SecOk`, the strict section has no compressed entry. -/
theorem SecOk.no_compressed {limits : Limits} {bytes : ByteArray} {sec : XrefSection}
    (h : SecOk limits bytes sec) (n c i : Nat) : (n, XrefEntry.compressed c i) ∉ sec.entries :=
  fun hm => h.2.1 _ hm

/-- **`getObject` agreement for any two documents over the strict and the repaired
section.** Under `SecOk` for the section of `d₁`, if `d₂` holds the repaired section, both
hold `bytes` and they have the same decryption state, `getObject` is equal everywhere. -/
theorem getObject_sec {limits : Limits} {bytes : ByteArray} {d₁ d₂ : OpenDoc}
    (hsec : SecOk limits bytes d₁.xref) (hb1 : d₁.bytes = bytes) (hb2 : d₂.bytes = bytes)
    (he2 : d₂.xref = scanSection limits bytes) (hc : d₁.crypt = d₂.crypt) (num gen : Nat) :
    d₁.getObject limits num gen = d₂.getObject limits num gen := by
  have hin := hsec.inUse_mem_iff
  have hnd1 := d₁.xref.keys_nodup
  have hnd2 := d₂.xref.keys_nodup
  have hl1 : ∀ m, d₁.lookup m = Core.Xref.Chain.lookupEntry m d₁.xref.entries :=
    WritePrefix.lookup_eq d₁
  have hl2 : ∀ m, d₂.lookup m = Core.Xref.Chain.lookupEntry m d₂.xref.entries :=
    WritePrefix.lookup_eq d₂
  have hrel : LookupRel d₁.lookup d₂.lookup := lookupRel_of
    (fun n off g => by
      rw [hl1, hl2, Unambiguous.lookupEntry_eq_some_iff hnd1,
        Unambiguous.lookupEntry_eq_some_iff hnd2, he2]
      exact hin n off g)
    (fun n c i h => by
      rw [hl1, Unambiguous.lookupEntry_eq_some_iff hnd1] at h
      exact hsec.no_compressed _ _ _ h)
    (fun n c i h => by
      rw [hl2, Unambiguous.lookupEntry_eq_some_iff hnd2, he2] at h
      exact scanSection_no_compressed _ _ _ _ _ h)
  let S := (d₁.xref.entries.filter (fun x => isInUse x.2)).map (·.1)
  let S' := ((scanSection limits bytes).entries.filter (fun x => isInUse x.2)).map (·.1)
  have hS : ∀ n off g, d₁.lookup n = some (.inUse off g) → n ∈ S := by
    intro n off g h
    rw [hl1, Unambiguous.lookupEntry_eq_some_iff hnd1] at h
    exact List.mem_map.mpr ⟨(n, .inUse off g), List.mem_filter.mpr ⟨h, rfl⟩, rfl⟩
  have hf : S.length < d₁.objectCount := by
    simp only [S, List.length_map, OpenDoc.objectCount, d₁.index_eq, List.size_toArray]
    exact List.length_filter_lt_length_iff_exists.mpr ⟨_, hsec.1, by simp [isInUse]⟩
  have hSS : S ⊆ S' := by
    intro n hn
    obtain ⟨⟨n', e⟩, he, rfl⟩ := List.mem_map.mp hn
    obtain ⟨he, hu⟩ := List.mem_filter.mp he
    cases e with
    | free _ _ => simp [isInUse] at hu
    | compressed _ _ => simp [isInUse] at hu
    | inUse off g =>
      exact List.mem_map.mpr ⟨(n', .inUse off g),
        List.mem_filter.mpr ⟨(hin n' off g).mp he, rfl⟩, rfl⟩
  have hSnd : S.Nodup :=
    (List.Sublist.map (·.1) (List.filter_sublist (l := d₁.xref.entries))).nodup hnd1
  have hf' : S.length < d₂.objectCount := by
    have h1 := hSnd.length_le_of_subset hSS
    have h2 : S'.length < (scanSection limits bytes).entries.length := by
      simp only [S', List.length_map]
      exact List.length_filter_lt_length_iff_exists.mpr
        ⟨(0, .free 0 65535), by simp [scanSection], by simp [isInUse]⟩
    simp only [OpenDoc.objectCount, d₂.index_eq, List.size_toArray, he2]
    omega
  exact getObject_eq_crypt (by rw [hb1, hb2]) hc hrel S hS hf hf' limits num gen

/-! ## Encryption: the same decryption state on both paths -/

/-- A `match` on a lookup without compressed entries takes its catch-all branch. -/
theorem match_no_compressed {α : Type} {l : Nat → Option XrefEntry}
    (hnc : ∀ n c i, l n ≠ some (.compressed c i)) (n : Nat) (x : Nat → Nat → α) (y : α) :
    (match l n with
      | some (.compressed c i) => x c i
      | _ => y) = y := by
  rcases h : l n with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩)
  · rfl
  · rfl
  · rfl
  · exact absurd h (hnc n c i)

/-- **The encryption dictionary is the same** on two documents whose trailers have the same
`/Encrypt` value, whose lookups have no compressed entry, and whose `getObject` agree
everywhere (rule E1: `encryptDict` reads only these). -/
theorem encryptDict_congr {limits : Limits} {e e' : OpenDoc}
    (hE : Dict.get? e.trailer.dict Core.Xref.nameEncrypt =
      Dict.get? e'.trailer.dict Core.Xref.nameEncrypt)
    (hnc : ∀ n c i, e.lookup n ≠ some (.compressed c i))
    (hnc' : ∀ n c i, e'.lookup n ≠ some (.compressed c i))
    (hg : ∀ num gen, e.getObject limits num gen = e'.getObject limits num gen) :
    e.encryptDict limits = e'.encryptDict limits := by
  unfold OpenDoc.encryptDict
  rw [hE]
  rcases Dict.get? e'.trailer.dict Core.Xref.nameEncrypt with _ | o
  · rfl
  · cases o
    case ref n g =>
      simp only
      have k1 := hnc n
      have k2 := hnc' n
      rw [hg n g]
      rcases h1 : e.lookup n with _ | (⟨a, g1⟩ | ⟨off, g1⟩ | ⟨c, i⟩) <;>
        rcases h2 : e'.lookup n with _ | (⟨a', g2⟩ | ⟨off', g2⟩ | ⟨c', i'⟩) <;>
        simp_all
    all_goals rfl

/-- **Same decryption state (rules E1, E3).** If `e.withCrypt` succeeds with `d`, and `e'` has
the same `encrypted` flag, the same `/Encrypt` value, the same first `/ID` string, no
compressed entries (neither has), the same `getObject` and the same initial state, then
`e'.withCrypt` succeeds with `e'` given `d`'s decryption state. -/
theorem withCrypt_congr {limits : Limits} {e e' d : OpenDoc}
    (hen : e.trailer.encrypted = e'.trailer.encrypted)
    (hE : Dict.get? e.trailer.dict Core.Xref.nameEncrypt =
      Dict.get? e'.trailer.dict Core.Xref.nameEncrypt)
    (hid : Core.Crypt.id0Of e.trailer.dict = Core.Crypt.id0Of e'.trailer.dict)
    (hnc : ∀ n c i, e.lookup n ≠ some (.compressed c i))
    (hnc' : ∀ n c i, e'.lookup n ≠ some (.compressed c i))
    (hg : ∀ num gen, e.getObject limits num gen = e'.getObject limits num gen)
    (hc0 : e.crypt = e'.crypt)
    (h : e.withCrypt limits = .ok d) : e'.withCrypt limits = .ok { e' with crypt := d.crypt } := by
  have hed := encryptDict_congr hE hnc hnc' hg
  unfold OpenDoc.withCrypt at h ⊢
  rw [← hen]
  split at h
  · rw [← hed]
    split at h
    · cases h
    · rename_i enc ref _
      have hs : Core.Crypt.setup enc e.trailer.dict ref =
          Core.Crypt.setup enc e'.trailer.dict ref := by
        unfold Core.Crypt.setup; rw [hid]
      split at h
      · cases h
      · rename_i st hst
        cases h
        simp only [← hs, hst, ‹e.trailer.encrypted = true›, ↓reduceIte]
  · rename_i hne
    cases h
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hc0]

/-- A document whose section has no compressed entry has a lookup without compressed
entries. -/
theorem lookup_no_compressed {d : OpenDoc}
    (h : ∀ n c i, (n, XrefEntry.compressed c i) ∉ d.xref.entries) (n c i : Nat) :
    d.lookup n ≠ some (.compressed c i) := by
  rw [WritePrefix.lookup_eq d, ne_eq, Unambiguous.lookupEntry_eq_some_iff d.xref.keys_nodup]
  exact h n c i

/-- Byte arrays with equal contents are equal. -/
theorem byteArray_eq_of_data {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a; cases b; simp only at h; rw [h]

/-! ## The hypothesis for encrypted files -/

/-- Condition H5e (replaces H5 and H6): the repair path's trailer exists and has the strict
`/Root`, the same `encrypted` flag, the same `/Encrypt` value and the same first `/ID` string
as the strict trailer; and H7 (task 12.7e): the repaired section has no compressed entry
(always true when the repaired trailer is encrypted: rule R6 then does not run). Rule R4'
makes the trailer part hold whenever the newest `trailer` dictionary with
`/Root` is the strict trailer (the usual single-revision classic file). -/
def trailerOkEnc (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Bool :=
  match Repair.repair limits bytes with
  | .ok (sec, tr) =>
    decide (tr.root? = d.trailer.root?) && decide (tr.encrypted = d.trailer.encrypted) &&
      decide (Dict.get? tr.dict Core.Xref.nameEncrypt =
        Dict.get? d.trailer.dict Core.Xref.nameEncrypt) &&
      decide ((Core.Crypt.id0Of tr.dict).data = (Core.Crypt.id0Of d.trailer.dict).data) &&
      noComp sec.entries
  | .error _ => false

/-- **The C4 hypothesis for encrypted files**: H1–H4 with free entries (`SecOk`, as in
`HypFree`) and H5e (`trailerOkEnc`); no condition on the decryption state (H6 dropped). -/
def HypEnc (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  SecOk limits bytes d.xref ∧ trailerOkEnc limits bytes d = true

/-- `HypEnc` is decidable. -/
instance instDecidableHypEnc (limits : Limits) (bytes : ByteArray) (d : OpenDoc) :
    Decidable (HypEnc limits bytes d) := by
  unfold HypEnc; infer_instance

/-- **The checker**: the strict path succeeds and its document satisfies `HypEnc`. -/
def checkEnc (limits : Limits) (bytes : ByteArray) : Bool :=
  match strictOpen limits bytes with
  | .ok d => decide (HypEnc limits bytes d)
  | .error _ => false

/-- The strictly opened document is a chain document with a decryption state: it has the
form `{e with crypt := c}` for `e = OpenDoc.mk' bytes … false` (no state), and
`e.withCrypt limits = .ok d`. -/
theorem strictOpen_pre {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) :
    ∃ sec tr k, (OpenDoc.mk' bytes sec tr k false).withCrypt limits = .ok d := by
  obtain ⟨revs, -, -, ho, -⟩ := strictOpen_ok hs
  unfold ofChain at ho
  split at ho
  · cases ho
  · exact ⟨_, _, _, ho⟩

/-- **C4 for encrypted files (repair conservativity, exact).** If the strict path opens `bytes`
as `d` (encrypted or not) and `HypEnc limits bytes d` holds, the repair path also succeeds; its
document is flagged `repaired`, has the same bytes, the same in-use entries, the same `/Root`
and the **same decryption state** as `d` (same handler and file key, rule E3), and its
`getObject` (decrypted, rule G5) is **equal** to `d`'s for every `num gen`. -/
theorem c4_enc {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : HypEnc limits bytes d) :
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧ d'.crypt = d.crypt ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  obtain ⟨hsec, htr⟩ := hh
  have hbytes := strictOpen_bytes hs
  obtain ⟨-, -, -, -, hval⟩ := strictOpen_ok hs
  obtain ⟨sec0, tr0, k, hwc⟩ := strictOpen_pre hs
  obtain ⟨c, hd⟩ := withCrypt_ok hwc
  let e := OpenDoc.mk' bytes sec0 tr0 k false
  have hex : e.xref = d.xref := by rw [hd]
  have het : e.trailer = d.trailer := by rw [hd]
  unfold trailerOkEnc at htr
  split at htr
  · rename_i sec tr hrep
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htr
    obtain ⟨⟨⟨⟨hroot, henc⟩, hE⟩, hid⟩, hnc⟩ := htr
    have hsec' := Repair.repair_scan hrep (noComp_spec hnc)
    subst hsec'
    let e' := OpenDoc.mk' bytes (scanSection limits bytes) tr 0 true
    have hsecE : SecOk limits bytes e.xref := by rw [hex]; exact hsec
    have hg0 : ∀ num gen, e.getObject limits num gen = e'.getObject limits num gen :=
      getObject_sec hsecE rfl rfl rfl rfl
    have hwc' : e'.withCrypt limits = .ok { e' with crypt := d.crypt } :=
      withCrypt_congr (e := e) (e' := e') (by rw [het]; exact henc.symm)
        (by rw [het]; exact hE.symm) (by rw [het]; exact (byteArray_eq_of_data hid).symm)
        (lookup_no_compressed hsecE.no_compressed)
        (lookup_no_compressed (scanSection_no_compressed limits bytes)) hg0 rfl hwc
    let d' : OpenDoc := { e' with crypt := d.crypt }
    have hg : ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen :=
      fun num gen => (getObject_sec (d₂ := d') hsec hbytes rfl rfl rfl num gen).symm
    have hv : validate limits d' = .ok d' :=
      validate_congr hroot.symm (fun n g => (hg n g).symm) hval
    refine ⟨d', ?_, rfl, by rw [hbytes]; rfl, fun n off g => (hsec.inUse_mem_iff n off g).symm,
      hroot, rfl, hg⟩
    unfold repairOpen
    rw [hrep]
    simp only
    rw [hwc']
    exact hv
  · cases htr

/-- **C4 for encrypted files, from the checker.** -/
theorem c4_enc_check {limits : Limits} {bytes : ByteArray} (hc : checkEnc limits bytes = true) :
    ∃ d d', strictOpen limits bytes = .ok d ∧ repairOpen limits bytes = .ok d' ∧
      d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧ d'.crypt = d.crypt ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  unfold checkEnc at hc
  split at hc
  · rename_i d hs
    obtain ⟨d', h⟩ := c4_enc hs (of_decide_eq_true hc)
    exact ⟨d, d', hs, h⟩
  · cases hc

/-! ## Compressed entries: one-sided agreement -/

/-- **Resolution transfers along a lookup extension.** If `l2` has no compressed entry and
every in-use entry of `l2` is one of `l1`, a `/Length` resolution that **succeeds** with `l2`
gives the same value with `l1` and the same fuel. (A failing one may succeed with `l1`: an
object missing from `l2` may be in use or compressed in `l1`.) -/
theorem resolve_sub {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hsub : ∀ n off g, l2 n = some (.inUse off g) → l1 n = some (.inUse off g))
    (hnc : ∀ n c i, l2 n ≠ some (.compressed c i)) (limits : Limits) (bytes : ByteArray) :
    ∀ f V ref v, (resolveLengthAux pre l2 limits bytes f V ref).2 = .ok v →
      (resolveLengthAux pre l1 limits bytes f V ref).2 = .ok v := by
  intro f
  induction f with
  | zero =>
    intro V ref v h
    rw [resolveLengthAux.eq_def] at h
    split at h <;> simp at h
  | succ k ih =>
    intro V ref v h
    rw [resolveLengthAux] at h ⊢
    by_cases hv : ref.1 ∈ V
    · simp [hv] at h
    simp only [hv, ↓reduceIte] at h ⊢
    rcases hl : l2 ref.1 with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩)
    · rw [hl] at h; simp at h
    · rw [hl] at h; simp at h
    · rw [hl] at h
      rw [hsub _ _ _ hl]
      simp only at h ⊢
      split at h
      · rename_i hg
        simp only [hg, ↓reduceIte]
        rcases hp : parseLengthObj limits bytes off ref.1 ref.2 with e | o
        · rw [hp] at h; simp at h
        · rw [hp] at h
          cases o
          all_goals try exact h
          exact ih _ _ _ h
      · simp at h
    · exact absurd hl (hnc _ _ _)

/-- `lengthOf` transfers along a lookup extension when it succeeds. -/
theorem lengthOf_sub {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hsub : ∀ n off g, l2 n = some (.inUse off g) → l1 n = some (.inUse off g))
    (hnc : ∀ n c i, l2 n ≠ some (.compressed c i)) (limits : Limits) (bytes : ByteArray)
    (f self : Nat) (d : Dict) (at_ x : Nat)
    (h : lengthOf pre l2 limits bytes f self d at_ = .ok x) :
    lengthOf pre l1 limits bytes f self d at_ = .ok x := by
  unfold lengthOf lengthDict at h ⊢
  rcases hd : Dict.lookup d Core.ObjParse.nameLength with _ | o
  · rw [hd] at h; exact h
  · rw [hd] at h
    cases o
    case ref m g =>
      simp only at h ⊢
      unfold resolveLength at h ⊢
      rcases hr : (resolveLengthAux pre l2 limits bytes f [self] (m, g)).2 with e | len
      · rw [hr] at h; cases h
      · rw [resolve_sub hsub hnc limits bytes f [self] (m, g) len hr]
        rw [hr] at h; exact h
    all_goals exact h

/-- **The object parse transfers along a lookup extension and a larger fuel** when it
succeeds. -/
theorem parseIndirectResolved_sub {l1 l2 : Nat → Option XrefEntry}
    (hsub : ∀ n off g, l2 n = some (.inUse off g) → l1 n = some (.inUse off g))
    (hnc : ∀ n c i, l2 n ≠ some (.compressed c i)) {limits : Limits} {bytes : ByteArray}
    {f f' pos : Nat} {pre : Core.Xref.ObjStm.Pre} {r : IndirectObject × Nat} (hff : f ≤ f')
    (h : parseIndirectResolved l2 limits bytes f pos pre = .ok r) :
    parseIndirectResolved l1 limits bytes f' pos pre = .ok r := by
  apply parseIndirectResolved_mono hff
  rw [parseIndirectResolved_eq_with] at h ⊢
  rcases hc : callPoint limits bytes pos with _ | ⟨n, d, p⟩
  · rw [parseIndirectWith_congr (lenG := lengthOf pre l2 limits bytes f)
      (fun n d p h' => by rw [hc] at h'; cases h')]
    exact h
  · rw [parseIndirectWith_const hc] at h ⊢
    rcases hle : lengthOf pre l2 limits bytes f n d p with e | x
    · rw [hle, parseIndirectWith_err hc] at h; cases h
    · rw [lengthOf_sub hsub hnc limits bytes f n d p x hle]
      rw [hle] at h; exact h

/-- **One-sided `getObject` agreement.** Two documents over the same bytes and the same
decryption state, where the second's lookup has no compressed entry, its in-use entries are
entries of the first, and its fuel is at most the first's: for an object number **in use in
the second**, every success of the second is a success of the first with the same body. -/
theorem getObject_sub {d d' : OpenDoc} (hb : d.bytes = d'.bytes) (hc : d.crypt = d'.crypt)
    (hsub : ∀ n off g, d'.lookup n = some (.inUse off g) → d.lookup n = some (.inUse off g))
    (hnc : ∀ n c i, d'.lookup n ≠ some (.compressed c i))
    (hf : d'.objectCount ≤ d.objectCount) (limits : Limits) (num gen off g : Nat)
    (hin : d'.lookup num = some (.inUse off g)) (v : IndirectBody)
    (h : d'.getObject limits num gen = .ok v) : d.getObject limits num gen = .ok v := by
  have hpre : d.pre = d'.pre := by unfold OpenDoc.pre; rw [hc]
  have hdec : d.decrypt = d'.decrypt := by
    funext a b c; unfold OpenDoc.decrypt; rw [hc]
  unfold OpenDoc.getObject OpenDoc.getObjectTrace at h ⊢
  rw [hin] at h
  rw [hsub _ _ _ hin]
  simp only at h ⊢
  by_cases hg : g = gen
  · simp only [hg, ↓reduceIte] at h ⊢
    rcases hp : parseIndirectResolved d'.lookup limits d'.bytes d'.objectCount off d'.pre with
      e | ⟨io, r⟩
    · rw [hp] at h; cases h
    · rw [hp] at h
      rw [hb, hpre, parseIndirectResolved_sub hsub hnc hf hp, hdec]
      exact h
  · simp only [hg, ↓reduceIte] at h ⊢
    exact h

/-- An object number whose entry is neither in use nor compressed resolves to `null`
(rule G4). -/
theorem getObject_null_of {d : OpenDoc} {limits : Limits} {num gen : Nat}
    (hni : ∀ off g, d.lookup num ≠ some (.inUse off g))
    (hnc : ∀ c i, d.lookup num ≠ some (.compressed c i)) :
    d.getObject limits num gen = .ok nullBody := by
  unfold OpenDoc.getObject OpenDoc.getObjectTrace
  rcases h : d.lookup num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩)
  · rfl
  · rfl
  · exact absurd h (hni off g)
  · exact absurd h (hnc c i)

/-! ## Compressed entries on both sides: one-sided transfer (task 12.7e) -/

/-- **Resolution transfers along a lookup extension with compressed entries.** If every
in-use and every compressed entry of `l2` is an entry of `l1`, a `/Length` resolution that
succeeds with `l2` is **identical** (parse count and result) with `l1` and the same fuel. -/
theorem resolve_sub2 {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hU : ∀ n off g, l2 n = some (.inUse off g) → l1 n = some (.inUse off g))
    (hC : ∀ n c i, l2 n = some (.compressed c i) → l1 n = some (.compressed c i))
    (limits : Limits) (bytes : ByteArray) :
    ∀ f V ref v, (resolveLengthAux pre l2 limits bytes f V ref).2 = .ok v →
      resolveLengthAux pre l1 limits bytes f V ref =
        resolveLengthAux pre l2 limits bytes f V ref := by
  intro f
  induction f using Nat.strongRecOn with
  | _ f ih =>
  intro V ref v hok
  by_cases hv : ref.1 ∈ V
  · rw [resolveLengthAux.eq_def] at hok
    simp [hv] at hok
  cases f with
  | zero =>
    rw [resolveLengthAux.eq_def] at hok
    simp [hv] at hok
  | succ k =>
  rw [resolveLengthAux] at hok
  rw [resolveLengthAux, resolveLengthAux]
  simp only [hv, ↓reduceIte] at hok ⊢
  rcases hl : l2 ref.1 with _ | (⟨a, g⟩ | ⟨off, g'⟩ | ⟨c, idx⟩)
  · rw [hl] at hok; simp at hok
  · rw [hl] at hok; simp at hok
  · rw [hl] at hok
    rw [hU _ _ _ hl]
    by_cases hg : g' = ref.2
    · simp only [hg, ↓reduceIte] at hok ⊢
      rcases hp : parseLengthObj limits bytes off ref.1 ref.2 with e | o
      · rfl
      · rw [hp] at hok
        cases o
        all_goals try rfl
        simp only at hok ⊢
        rw [ih k (by omega) _ _ v hok]
    · simp only [hg, ↓reduceIte]
  · rw [hl] at hok
    rw [hC _ _ _ hl]
    by_cases hcy : c = ref.1 ∨ c ∈ V
    · simp only [hcy, ↓reduceIte] at hok; simp at hok
    · simp only [hcy, ↓reduceIte] at hok ⊢
      rcases hc : l2 c with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
      · rw [hc] at hok; simp at hok
      · rw [hc] at hok; simp at hok
      · rw [hc] at hok
        rw [hU _ _ _ hc]
        by_cases hg : g = 0
        · simp only [hg, ↓reduceIte] at hok ⊢
          rcases hph : parseContainerHead limits bytes off c with e | ⟨d, p⟩
          · rfl
          · rw [hph] at hok
            simp only at hok ⊢
            have hr1 : ∃ x, (containerLength
                (lengthHop l2 limits bytes k)
                (c :: ref.1 :: V) d p).2 = .ok x := by
              rcases h1 : (containerLength
                  (lengthHop l2 limits bytes k)
                  (c :: ref.1 :: V) d p).2 with e | x
              · rw [h1] at hok; simp [containerMember] at hok
              · exact ⟨x, rfl⟩
            have hcl : containerLength
                (lengthHop l1 limits bytes k) (c :: ref.1 :: V) d p =
                containerLength
                (lengthHop l2 limits bytes k)
                (c :: ref.1 :: V) d p := by
              obtain ⟨x, hx⟩ := hr1
              unfold containerLength at hx ⊢
              split
              · rename_i m hh hm
                rw [hm] at hx
                exact lengthHop_sub hx (hU _)
              · rfl
            rw [hcl]
            rcases hm : containerMember pre limits bytes off c ref.1 idx d p
                (containerLength (lengthHop l2 limits bytes k)
                  (c :: ref.1 :: V) d p).2 with e | o
            · rfl
            · rw [hm] at hok
              cases o
              all_goals try rfl
              simp only at hok ⊢
              rw [ih _ (by omega) _ _ v hok]
        · simp only [hg, ↓reduceIte]
      · rw [hc] at hok; simp at hok

/-- `lengthOf` transfers along a lookup extension with compressed entries when it
succeeds. -/
theorem lengthOf_sub2 {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hU : ∀ n off g, l2 n = some (.inUse off g) → l1 n = some (.inUse off g))
    (hC : ∀ n c i, l2 n = some (.compressed c i) → l1 n = some (.compressed c i))
    (limits : Limits) (bytes : ByteArray)
    (f self : Nat) (d : Dict) (at_ x : Nat)
    (h : lengthOf pre l2 limits bytes f self d at_ = .ok x) :
    lengthOf pre l1 limits bytes f self d at_ = .ok x := by
  unfold lengthOf lengthDict at h ⊢
  rcases hd : Dict.lookup d Core.ObjParse.nameLength with _ | o
  · rw [hd] at h; exact h
  · rw [hd] at h
    cases o
    case ref m g =>
      simp only at h ⊢
      unfold resolveLength at h ⊢
      rcases hr : (resolveLengthAux pre l2 limits bytes f [self] (m, g)).2 with e | len
      · rw [hr] at h; cases h
      · rw [resolve_sub2 hU hC limits bytes f [self] (m, g) len hr, hr]
        rw [hr] at h; exact h
    all_goals exact h

/-- **The object parse transfers along a lookup extension with compressed entries and a
larger fuel** when it succeeds. -/
theorem parseIndirectResolved_sub2 {l1 l2 : Nat → Option XrefEntry}
    (hU : ∀ n off g, l2 n = some (.inUse off g) → l1 n = some (.inUse off g))
    (hC : ∀ n c i, l2 n = some (.compressed c i) → l1 n = some (.compressed c i))
    {limits : Limits} {bytes : ByteArray}
    {f f' pos : Nat} {pre : Core.Xref.ObjStm.Pre} {r : IndirectObject × Nat} (hff : f ≤ f')
    (h : parseIndirectResolved l2 limits bytes f pos pre = .ok r) :
    parseIndirectResolved l1 limits bytes f' pos pre = .ok r := by
  apply parseIndirectResolved_mono hff
  rw [parseIndirectResolved_eq_with] at h ⊢
  rcases hc : callPoint limits bytes pos with _ | ⟨n, d, p⟩
  · rw [parseIndirectWith_congr (lenG := lengthOf pre l2 limits bytes f)
      (fun n d p h' => by rw [hc] at h'; cases h')]
    exact h
  · rw [parseIndirectWith_const hc] at h ⊢
    rcases hle : lengthOf pre l2 limits bytes f n d p with e | x
    · rw [hle, parseIndirectWith_err hc] at h; cases h
    · rw [lengthOf_sub2 hU hC limits bytes f n d p x hle]
      rw [hle] at h; exact h

/-- **`ObjStm.fetchCompressed` transfers along a lookup extension with compressed entries and
a larger fuel** when it succeeds. -/
theorem fetchCompressed_sub2 {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (hU : ∀ n off g, l2 n = some (.inUse off g) → l1 n = some (.inUse off g))
    (hC : ∀ n c i, l2 n = some (.compressed c i) → l1 n = some (.compressed c i))
    {limits : Limits} {bytes : ByteArray} {f f' num : Nat} {o : PdfObject} (hff : f ≤ f')
    (h : (Core.Xref.ObjStm.fetchCompressedTrace pre l2 limits bytes f num).result = .ok o) :
    (Core.Xref.ObjStm.fetchCompressedTrace pre l1 limits bytes f' num).result = .ok o := by
  unfold Core.Xref.ObjStm.fetchCompressedTrace at h ⊢
  rcases hl : l2 num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, idx⟩)
  all_goals rw [hl] at h
  · simp at h
  · simp at h
  · simp at h
  rw [hC _ _ _ hl]
  by_cases hcn : c = num
  · simp only [hcn, ↓reduceIte] at h; simp at h
  simp only [hcn, ↓reduceIte] at h ⊢
  rcases hc : l2 c with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
  all_goals rw [hc] at h
  · simp at h
  · simp at h
  · rw [hU _ _ _ hc]
    by_cases hg : g = 0
    · simp only [hg, ↓reduceIte] at h ⊢
      rcases hp : parseIndirectResolved l2 limits bytes f off pre with e | r
      · rw [hp] at h; simp at h
      · rw [parseIndirectResolved_sub2 hU hC hff hp]
        rw [hp] at h; exact h
    · simp only [hg, ↓reduceIte] at h; simp at h
  · simp at h

/-- **One-sided `getObject` agreement with compressed entries.** Two documents over the same
bytes and decryption state, where every in-use and compressed entry of the second's lookup
is one of the first's, and the second's fuel is at most the first's: for an object number
**in use or compressed in the second**, every success of the second is a success of the
first with the same body. -/
theorem getObject_sub2 {d d' : OpenDoc} (hb : d.bytes = d'.bytes) (hc : d.crypt = d'.crypt)
    (hU : ∀ n off g, d'.lookup n = some (.inUse off g) → d.lookup n = some (.inUse off g))
    (hC : ∀ n c i, d'.lookup n = some (.compressed c i) → d.lookup n = some (.compressed c i))
    (hf : d'.objectCount ≤ d.objectCount) (limits : Limits) (num gen : Nat)
    (hin : (∃ off g, d'.lookup num = some (.inUse off g)) ∨
      ∃ c i, d'.lookup num = some (.compressed c i)) (v : IndirectBody)
    (h : d'.getObject limits num gen = .ok v) : d.getObject limits num gen = .ok v := by
  have hpre : d.pre = d'.pre := by unfold OpenDoc.pre; rw [hc]
  have hdec : d.decrypt = d'.decrypt := by
    funext a b c; unfold OpenDoc.decrypt; rw [hc]
  unfold OpenDoc.getObject OpenDoc.getObjectTrace at h ⊢
  rcases hin with ⟨off, g, hin⟩ | ⟨c, i, hin⟩
  · rw [hin] at h
    rw [hU _ _ _ hin]
    simp only at h ⊢
    by_cases hg : g = gen
    · simp only [hg, ↓reduceIte] at h ⊢
      rcases hp : parseIndirectResolved d'.lookup limits d'.bytes d'.objectCount off d'.pre with
        e | ⟨io, r⟩
      · rw [hp] at h; cases h
      · rw [hp] at h
        rw [hb, hpre, parseIndirectResolved_sub2 hU hC hf hp, hdec]
        exact h
    · simp only [hg, ↓reduceIte] at h ⊢
      exact h
  · rw [hin] at h
    rw [hC _ _ _ hin]
    simp only at h ⊢
    by_cases hg : gen = 0
    · simp only [hg, ↓reduceIte] at h ⊢
      rcases hp : (Core.Xref.ObjStm.fetchCompressedTrace d'.pre d'.lookup limits d'.bytes
          d'.objectCount num).result with e | o
      · rw [hp] at h; cases h
      · rw [hp] at h
        rw [hb, hpre, fetchCompressed_sub2 hU hC hf hp]
        exact h
    · simp only [hg, ↓reduceIte] at h ⊢
      exact h

/-- Condition H2c on one strict entry: free and **compressed** entries are allowed for every
object number; an in-use entry points at the newest scan hit of its number. (By H3 a
compressed number then has no scan hit at all.) -/
def EntryOkComp (raw : List (Nat × Nat × Nat)) : Nat × XrefEntry → Prop
  | (_, .free _ _) => True
  | (_, .compressed _ _) => True
  | (n, .inUse off g) => 1 ≤ n ∧ newestHit raw n = some (n, g, off)

/-- `EntryOkComp` is decidable. -/
instance (raw : List (Nat × Nat × Nat)) : DecidablePred (EntryOkComp raw) := fun x =>
  match x with
  | (_, .free _ _) => inferInstanceAs (Decidable True)
  | (_, .compressed _ _) => inferInstanceAs (Decidable True)
  | (n, .inUse off g) =>
    inferInstanceAs (Decidable (1 ≤ n ∧ newestHit raw n = some (n, g, off)))

/-- Condition H5c (task 12.7e; replaces H5 in `HypComp`): the repair path's trailer exists,
has the strict `/Root` and no `/Encrypt`; and H7c: every compressed entry of the repaired
section (repair rule R6) is the strict entry of its number. -/
def trailerOkComp (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Bool :=
  match Repair.repair limits bytes with
  | .ok (sec, tr) =>
    !tr.encrypted && tr.root? == d.trailer.root? &&
      sec.entries.all (fun x => !isComp x.2 || d.lookup x.1 == some x.2)
  | .error _ => false

/-- H5 (with H7: no compressed entry after repair) implies H5c. -/
theorem trailerOk_toComp {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : trailerOk limits bytes d = true) : trailerOkComp limits bytes d = true := by
  unfold trailerOk at h
  unfold trailerOkComp
  rcases hrep : Repair.repair limits bytes with e | ⟨sec, tr⟩
  · rw [hrep] at h; cases h
  · rw [hrep] at h
    simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, List.all_eq_true.mpr (fun x hx => ?_)⟩
    have := List.all_eq_true.mp h2 x hx
    simp only [Bool.not_eq_true'] at this
    simp [this]

/-- **The hypothesis with compressed entries**: `HypFree` with H2 relaxed to `EntryOkComp`
(compressed entries allowed) and H5 replaced by H5c (`trailerOkComp`: repair rule R6 may add
compressed entries, but only ones the strict section has); H1, H3, H4, H6 unchanged
(unencrypted). -/
def HypComp (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  (0, XrefEntry.free 0 65535) ∈ d.xref.entries ∧
  (∀ x ∈ d.xref.entries, EntryOkComp (hits limits bytes) x) ∧
  (∀ x ∈ hits limits bytes, ∃ e ∈ d.xref.entries, e.1 = x.1 ∧ isInUse e.2 = true) ∧
  (newestHits (hits limits bytes)).length ≤ limits.maxObjects ∧
  trailerOkComp limits bytes d = true ∧
  d.crypt.isNone = true

/-- `HypComp` is decidable. -/
instance instDecidableHypComp (limits : Limits) (bytes : ByteArray) (d : OpenDoc) :
    Decidable (HypComp limits bytes d) := by
  unfold HypComp; infer_instance

/-- **The checker**: the strict path succeeds and its document satisfies `HypComp`. -/
def checkComp (limits : Limits) (bytes : ByteArray) : Bool :=
  match strictOpen limits bytes with
  | .ok d => decide (HypComp limits bytes d)
  | .error _ => false

/-- `HypFree` is `HypComp` without compressed entries. -/
theorem HypFree.toComp {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : HypFree limits bytes d) : HypComp limits bytes d := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, fun x hx => ?_, h3, h4, trailerOk_toComp h5, h6⟩
  have := h2 x hx
  obtain ⟨n, e⟩ := x
  cases e with
  | free a g => trivial
  | compressed _ _ => exact this.elim
  | inUse off g => exact this

/-- **C4 with compressed entries (one-sided).** If the strict path opens `bytes` as `d` with
`HypComp`, and the repair path opens it as `d'`, then `d'` is flagged `repaired`, has the same
bytes, the same in-use entries and the same `/Root`, and:

* for every object number that is **not compressed** in `d`, every success of `d'.getObject`
  is a success of `d.getObject` with the same body (repair never returns a different object;
  it may fail where strict succeeds);
* every **compressed** object of `d` is `null` in `d'` (repair rule R6 did not find it), or
  it has the **same** compressed entry in `d'` and every success of `d'.getObject` is a
  success of `d.getObject` with the same body.

Before task 12.7e (no rule R6) the second point read "every compressed object of `d` is
`null` in `d'`"; R6 makes that false by design (`objStmBytes`, below), so it is replaced by
the disjunction, and H5 by H5c. Exact agreement is task 12.7f. -/
theorem c4_comp {limits : Limits} {bytes : ByteArray} {d d' : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : HypComp limits bytes d)
    (hr : repairOpen limits bytes = .ok d') :
    d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧
      (∀ num gen v, (∀ c i, d.lookup num ≠ some (.compressed c i)) →
        d'.getObject limits num gen = .ok v → d.getObject limits num gen = .ok v) ∧
      (∀ num gen c i, d.lookup num = some (.compressed c i) →
        d'.getObject limits num gen = .ok nullBody ∨
        (d'.lookup num = some (.compressed c i) ∧
          ∀ v, d'.getObject limits num gen = .ok v → d.getObject limits num gen = .ok v)) := by
  obtain ⟨hz, hent, hcov, hcap, htr, hpl⟩ := hh
  have hin : ∀ n off g, (n, XrefEntry.inUse off g) ∈ d.xref.entries ↔
      (n, XrefEntry.inUse off g) ∈ (scanSection limits bytes).entries :=
    inUse_mem_iff_of (fun n off g hx => hent _ hx) hcov hcap
  have hbytes := strictOpen_bytes hs
  obtain ⟨sec, tr, hrep, hwc, -⟩ := repairOpen_ok hr
  obtain ⟨hsup, hsub⟩ := Repair.repair_entries hrep
  unfold trailerOkComp at htr
  rw [hrep] at htr
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at htr
  obtain ⟨⟨henc, hroot⟩, hcomp⟩ := htr
  rw [withCrypt_plain (d := OpenDoc.mk' bytes sec tr 0 true) henc] at hwc
  cases hwc
  have hc : d.crypt = none := Option.isNone_iff_eq_none.mp hpl
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
  have hU : ∀ n off g, d'.lookup n = some (.inUse off g) → d.lookup n = some (.inUse off g) :=
    fun n off g h => (hl1 _ _).mpr ((hin n off g).mpr ((hinS n off g).mp ((hl2 _ _).mp h)))
  have hC : ∀ n c i, d'.lookup n = some (.compressed c i) →
      d.lookup n = some (.compressed c i) :=
    fun n c i h => hcd n c i ((hl2 _ _).mp h)
  have hf : d'.objectCount ≤ d.objectCount := by
    simp only [OpenDoc.objectCount, d.index_eq, d', OpenDoc.mk', List.size_toArray]
    have hnd : sec.entries.Nodup := by
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
  refine ⟨rfl, by rw [hbytes]; rfl, fun n off g => (hinS n off g).trans (hin n off g).symm,
    hroot, ?_, ?_⟩
  · intro num gen v hncs h
    rcases h2 : d'.lookup num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩)
    · have hn : d'.getObject limits num gen = .ok nullBody :=
        getObject_null_of (by simp [h2]) (by simp [h2])
      rw [hn] at h; cases h
      refine getObject_null_of (fun off g h1 => ?_) hncs
      have := (hl2 _ _).mpr ((hinS num off g).mpr ((hin num off g).mp ((hl1 _ _).mp h1)))
      rw [h2] at this; cases this
    · have hn : d'.getObject limits num gen = .ok nullBody :=
        getObject_null_of (by simp [h2]) (by simp [h2])
      rw [hn] at h; cases h
      refine getObject_null_of (fun off g h1 => ?_) hncs
      have := (hl2 _ _).mpr ((hinS num off g).mpr ((hin num off g).mp ((hl1 _ _).mp h1)))
      rw [h2] at this; cases this
    · exact getObject_sub2 (d' := d') (by rw [hbytes]; rfl) hc hU hC hf limits num gen
        (Or.inl ⟨off, g, h2⟩) v h
    · exact absurd (hC _ _ _ h2) (hncs c i)
  · intro num gen c i h1
    rcases h2 : d'.lookup num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
    · exact Or.inl (getObject_null_of (d := d') (by simp [h2]) (by simp [h2]))
    · exact Or.inl (getObject_null_of (d := d') (by simp [h2]) (by simp [h2]))
    · have := hU _ _ _ h2
      rw [h1] at this; cases this
    · have h3 := hC _ _ _ h2
      rw [h1] at h3
      cases h3
      exact Or.inr ⟨rfl, fun v h => getObject_sub2 (d' := d') (by rw [hbytes]; rfl) hc hU hC hf
        limits num gen (Or.inr ⟨c, i, h2⟩) v h⟩

/-- **C4 with compressed entries, from the checker.** -/
theorem c4_comp_check {limits : Limits} {bytes : ByteArray} (hc : checkComp limits bytes = true)
    {d' : OpenDoc} (hr : repairOpen limits bytes = .ok d') :
    ∃ d, strictOpen limits bytes = .ok d ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧
      (∀ num gen v, (∀ c i, d.lookup num ≠ some (.compressed c i)) →
        d'.getObject limits num gen = .ok v → d.getObject limits num gen = .ok v) ∧
      (∀ num gen c i, d.lookup num = some (.compressed c i) →
        d'.getObject limits num gen = .ok nullBody ∨
        (d'.lookup num = some (.compressed c i) ∧
          ∀ v, d'.getObject limits num gen = .ok v → d.getObject limits num gen = .ok v)) := by
  unfold checkComp at hc
  split at hc
  · rename_i d hs
    exact ⟨d, hs, c4_comp hs (of_decide_eq_true hc) hr⟩
  · cases hc

/-! ## Fixtures -/

/-- A strictly openable **RC4-40 encrypted** file (776 bytes, SHA-256 `ce52a560…e647`; `/V 1
/R 2`, empty user password, `/P -4`, `/ID` = bytes `10…1F`), written by a stdlib Python script
independent of `Core.Crypt`: an indirect `/Encrypt 5 0 R`, a catalog with the encrypted string
`/Lang (en-US)`, and an encrypted content stream (object 4, plaintext
`BT /F1 24 Tf 72 700 Td (Hello) Tj ET`, direct `/Length 36`). Classic table, one revision. -/
def encBytes : ByteArray := ⟨#[
  37, 80, 68, 70, 45, 49, 46, 52, 10, 49, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121,
  112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103, 32, 47, 80, 97, 103, 101, 115, 32, 50, 32,
  48, 32, 82, 32, 47, 76, 97, 110, 103, 32, 60, 68, 50, 57, 53, 49, 65, 51, 55, 51, 54, 62, 32,
  62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 50, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47,
  84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 115, 32, 47, 75, 105, 100, 115, 32, 91, 51, 32,
  48, 32, 82, 93, 32, 47, 67, 111, 117, 110, 116, 32, 49, 32, 62, 62, 10, 101, 110, 100, 111,
  98, 106, 10, 51, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80,
  97, 103, 101, 32, 47, 80, 97, 114, 101, 110, 116, 32, 50, 32, 48, 32, 82, 32, 47, 77, 101,
  100, 105, 97, 66, 111, 120, 32, 91, 48, 32, 48, 32, 54, 49, 50, 32, 55, 57, 50, 93, 32, 47,
  67, 111, 110, 116, 101, 110, 116, 115, 32, 52, 32, 48, 32, 82, 32, 62, 62, 10, 101, 110, 100,
  111, 98, 106, 10, 52, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 76, 101, 110, 103, 116,
  104, 32, 51, 54, 32, 62, 62, 10, 115, 116, 114, 101, 97, 109, 10, 118, 154, 113, 214, 157, 70,
  85, 16, 102, 72, 130, 43, 238, 134, 185, 167, 82, 224, 245, 161, 121, 47, 150, 6, 198, 118,
  182, 222, 21, 67, 142, 94, 221, 14, 50, 12, 10, 101, 110, 100, 115, 116, 114, 101, 97, 109,
  10, 101, 110, 100, 111, 98, 106, 10, 53, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 70,
  105, 108, 116, 101, 114, 32, 47, 83, 116, 97, 110, 100, 97, 114, 100, 32, 47, 86, 32, 49, 32,
  47, 82, 32, 50, 32, 47, 79, 32, 60, 50, 48, 53, 53, 67, 55, 53, 54, 67, 55, 50, 69, 49, 65,
  68, 55, 48, 50, 54, 48, 56, 69, 56, 49, 57, 54, 65, 67, 65, 68, 52, 52, 55, 65, 68, 51, 50,
  68, 49, 55, 67, 70, 70, 53, 56, 51, 50, 51, 53, 70, 54, 68, 68, 49, 53, 70, 69, 68, 55, 68,
  65, 66, 54, 55, 62, 32, 47, 85, 32, 60, 67, 51, 53, 52, 56, 48, 51, 52, 54, 67, 48, 69, 51,
  53, 55, 54, 52, 65, 51, 65, 67, 54, 56, 67, 53, 56, 49, 67, 48, 54, 55, 57, 57, 68, 69, 51,
  68, 48, 53, 68, 68, 57, 65, 57, 65, 53, 53, 52, 67, 65, 70, 54, 55, 53, 51, 54, 68, 69, 69,
  55, 54, 67, 67, 53, 62, 32, 47, 80, 32, 45, 52, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106,
  10, 120, 114, 101, 102, 10, 48, 32, 54, 10, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 32, 54,
  53, 53, 51, 53, 32, 102, 32, 10, 48, 48, 48, 48, 48, 48, 48, 48, 48, 57, 32, 48, 48, 48, 48,
  48, 32, 110, 32, 10, 48, 48, 48, 48, 48, 48, 48, 48, 55, 55, 32, 48, 48, 48, 48, 48, 32, 110,
  32, 10, 48, 48, 48, 48, 48, 48, 48, 49, 51, 52, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48,
  48, 48, 48, 48, 48, 48, 50, 50, 49, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48,
  48, 48, 48, 51, 48, 55, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 116, 114, 97, 105, 108, 101,
  114, 10, 60, 60, 32, 47, 83, 105, 122, 101, 32, 54, 32, 47, 82, 111, 111, 116, 32, 49, 32, 48,
  32, 82, 32, 47, 69, 110, 99, 114, 121, 112, 116, 32, 53, 32, 48, 32, 82, 32, 47, 73, 68, 32,
  91, 60, 49, 48, 49, 49, 49, 50, 49, 51, 49, 52, 49, 53, 49, 54, 49, 55, 49, 56, 49, 57, 49,
  65, 49, 66, 49, 67, 49, 68, 49, 69, 49, 70, 62, 32, 60, 49, 48, 49, 49, 49, 50, 49, 51, 49,
  52, 49, 53, 49, 54, 49, 55, 49, 56, 49, 57, 49, 65, 49, 66, 49, 67, 49, 68, 49, 69, 49, 70,
  62, 93, 32, 62, 62, 10, 115, 116, 97, 114, 116, 120, 114, 101, 102, 10, 53, 48, 50, 10, 37,
  37, 69, 79, 70, 10
]⟩

/-- `encBytes` with a stale trailer dictionary inserted between the trailer and `startxref`
(in a comment line, so the strict path, which follows `startxref`, ignores it; the offsets do
not move): same `/Root` and `/Encrypt`, but
`/ID` = sixteen zero bytes. The repair path takes the newest `trailer` dictionary with
`/Root` (rule R4), so it derives its key from another `/ID`: the `/U` check fails and the
repair path fails with `Error.encryption` while the strict path opens the file. H5e fails,
and so does the conclusion of `c4_enc`. -/
def encStaleBytes : ByteArray :=
  encBytes.extract 0 756 ++ ("%trailer\n<< /Size 6 /Root 1 0 R /Encrypt 5 0 R /ID " ++
    "[<00000000000000000000000000000000> <00000000000000000000000000000000>] >>\n").toUTF8 ++
    encBytes.extract 756 encBytes.size

-- The insertion point is the `startxref` keyword.
#guard (encBytes.extract 756 765).toList = "startxref".toUTF8.toList

/-- A strictly openable file with an **object stream** (386 bytes, SHA-256 `c7c139b7…f7ed`):
the catalog (object 1) is a classic object; the page tree node (object 2) and the page
(object 3) are compressed in object stream 4; object 5 is the cross-reference stream
(`/W [1 2 2]`, no filter, no `trailer` keyword). Strictly, objects 2 and 3 are
dictionaries; the repair scan finds only objects 1, 4 and 5 (it synthesizes the trailer from
the catalog), so objects 2 and 3 are `null` after repair. -/
def objStmBytes : ByteArray := ⟨#[
  37, 80, 68, 70, 45, 49, 46, 53, 10, 49, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121,
  112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103, 32, 47, 80, 97, 103, 101, 115, 32, 50, 32,
  48, 32, 82, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 52, 32, 48, 32, 111, 98, 106, 10,
  60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 79, 98, 106, 83, 116, 109, 32, 47, 78, 32, 50, 32,
  47, 70, 105, 114, 115, 116, 32, 57, 32, 47, 76, 101, 110, 103, 116, 104, 32, 49, 48, 54, 32,
  62, 62, 10, 115, 116, 114, 101, 97, 109, 10, 50, 32, 48, 32, 51, 32, 52, 50, 10, 60, 60, 32,
  47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 115, 32, 47, 75, 105, 100, 115, 32, 91, 51,
  32, 48, 32, 82, 93, 32, 47, 67, 111, 117, 110, 116, 32, 49, 32, 62, 62, 10, 60, 60, 32, 47,
  84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 32, 47, 80, 97, 114, 101, 110, 116, 32, 50, 32,
  48, 32, 82, 32, 47, 77, 101, 100, 105, 97, 66, 111, 120, 32, 91, 48, 32, 48, 32, 54, 49, 50,
  32, 55, 57, 50, 93, 32, 62, 62, 10, 101, 110, 100, 115, 116, 114, 101, 97, 109, 10, 101, 110,
  100, 111, 98, 106, 10, 53, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101,
  32, 47, 88, 82, 101, 102, 32, 47, 83, 105, 122, 101, 32, 54, 32, 47, 87, 32, 91, 49, 32, 50,
  32, 50, 93, 32, 47, 82, 111, 111, 116, 32, 49, 32, 48, 32, 82, 32, 47, 76, 101, 110, 103, 116,
  104, 32, 51, 48, 32, 62, 62, 10, 115, 116, 114, 101, 97, 109, 10, 0, 0, 0, 255, 255, 1, 0, 9,
  0, 0, 2, 0, 4, 0, 0, 2, 0, 4, 0, 1, 1, 0, 58, 0, 0, 1, 0, 243, 0, 0, 10, 101, 110, 100, 115,
  116, 114, 101, 97, 109, 10, 101, 110, 100, 111, 98, 106, 10, 115, 116, 97, 114, 116, 120, 114,
  101, 102, 10, 50, 52, 51, 10, 37, 37, 69, 79, 70, 10
]⟩

/-- Test helper: `getObject num 0` is the same on the strict and the repair path (both open). -/
def sameObj (bytes : ByteArray) (num : Nat) : Bool :=
  match strictOpen Limits.default bytes, repairOpen Limits.default bytes with
  | .ok d, .ok d' =>
    match d.getObject Limits.default num 0, d'.getObject Limits.default num 0 with
    | .ok a, .ok b => decide (a = b)
    | _, _ => false
  | _, _ => false

/-- Test helper: the catalog's `/Lang` string (object 1) on the strict and the repair path. -/
def langs (bytes : ByteArray) : Option (List UInt8 × List UInt8) :=
  let lang : Except Error IndirectBody → List UInt8 := fun r =>
    match r with
    | .ok (.obj (.dict d)) =>
      match Dict.get? d (Name.ofString "Lang") with
      | some (.string s) => s
      | _ => []
    | _ => []
  match strictOpen Limits.default bytes, repairOpen Limits.default bytes with
  | .ok d, .ok d' => some (lang (d.getObject Limits.default 1 0),
      lang (d'.getObject Limits.default 1 0))
  | _, _ => none

/-- Test helper: the stream data of object 4 on the strict path. -/
def data4 (bytes : ByteArray) : List UInt8 :=
  match strictOpen Limits.default bytes with
  | .ok d =>
    match d.getObject Limits.default 4 0 with
    | .ok (.stream s) => s.data.toList
    | _ => []
  | .error _ => []

/-- Test helper: whether both paths open with a decryption state. -/
def bothCrypt (bytes : ByteArray) : Bool :=
  match strictOpen Limits.default bytes, repairOpen Limits.default bytes with
  | .ok d, .ok d' => d.crypt.isSome && d'.crypt.isSome
  | _, _ => false

-- (b) Encryption. The RC4 file opens strictly and after repair, both with a decryption state.
#guard bothCrypt encBytes
-- 12.7a's checker rejects it (H6), the new checker accepts it: `c4_enc_check` applies.
#guard checkFree Limits.default encBytes = false
#guard checkEnc Limits.default encBytes = true
-- Decryption is effective and equal on both paths: `/Lang` decrypts to `en-US`, the content
-- stream to its plaintext; every object is equal.
#guard langs encBytes = some ("en-US".toUTF8.toList, "en-US".toUTF8.toList)
#guard data4 encBytes = "BT /F1 24 Tf 72 700 Td (Hello) Tj ET".toUTF8.toList
#guard (List.range 7).all (sameObj encBytes)
-- Necessity of H5e: with a stale trailer (different `/ID`) the strict path opens the file and
-- decrypts it, the checker rejects it, and the repair path fails (wrong key: `/U` mismatch).
#guard (match strictOpen Limits.default encStaleBytes with
  | .ok d => d.crypt.isSome && (match d.getObject Limits.default 1 0 with
    | .ok (.obj (.dict x)) =>
      Dict.get? x (Name.ofString "Lang") == some (.string "en-US".toUTF8.toList)
    | _ => false)
  | .error _ => false)
#guard checkEnc Limits.default encStaleBytes = false
#guard (match repairOpen Limits.default encStaleBytes with
  | .ok _ => false
  | .error e => e.isEncryption)
-- `checkEnc` also covers the unencrypted fixtures of 12.7 and 12.7a.
#guard checkEnc Limits.default repairFixedBytes = true
#guard checkEnc Limits.default freeEntryBytes = true
#guard checkEnc Limits.default repairDiffBytes = false

-- (a) Compressed entries. The file opens on both paths; `HypComp` holds (so `c4_comp_check`
-- applies), `HypFree` does not.
#guard (match strictOpen Limits.default objStmBytes with
  | .ok d => d.lookup 2 == some (.compressed 4 0) && d.lookup 3 == some (.compressed 4 1)
  | .error _ => false)
#guard checkComp Limits.default objStmBytes = true
#guard checkFree Limits.default objStmBytes = false
-- Before task 12.7e the compressed objects were lost by repair (`("dict", "null")`). Repair
-- rule R6 reads object stream 4 and gives objects 2 and 3 the strict compressed entries, so
-- both paths now return the same dictionaries, and every object agrees (`c4_comp`'s second
-- disjunct; exact C4 for compressed entries is task 12.7f).
#guard (match repairOpen Limits.default objStmBytes with
  | .ok d => d.lookup 2 == some (.compressed 4 0) && d.lookup 3 == some (.compressed 4 1)
  | .error _ => false)
#guard both objStmBytes 2 = some ("dict", "dict")
#guard both objStmBytes 3 = some ("dict", "dict")
#guard (List.range 7).all (sameObj objStmBytes)
-- R6 adds compressed entries, so H7 (in `trailerOk`) fails: the exact theorems do not apply.
#guard check Limits.default objStmBytes = false
-- `checkComp` extends `checkFree` (`HypFree.toComp`).
#guard checkComp Limits.default freeEntryBytes = true
#guard checkComp Limits.default repairDiffBytes = false

end SafePdf.Spec.RepairAgreeExt
