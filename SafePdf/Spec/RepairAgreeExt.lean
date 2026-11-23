import SafePdf.Spec.RepairAgreeFree

/-!
# C4 for encrypted files and for compressed entries (task 12.7c)

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

## (a) Compressed entries: an obstacle in `Repair`, and a one-sided result

**C4 is false for compressed entries with the current repair algorithm.** `Repair` (rules
R1–R5) records only classic `N G obj` headers; it never parses object streams, so its section
has no compressed entry and every object that lives only in an object stream is absent, hence
`null` (rule G4), after repair. `objStmBytes` is a strictly valid file whose page tree node and
page live in an object stream: strictly they are dictionaries, after repair `null`. Exact
agreement therefore needs a change to `Repair` (scan `/Type /ObjStm` containers and add
compressed entries), which is outside this Spec task (proposed split below).

What does hold (`HypComp`: `HypFree` with compressed entries allowed; decidable, checker
`checkComp`; `HypFree.toComp`):

* `resolve_sub`, `lengthOf_sub`, `parseIndirectResolved_sub`, `getObject_sub`: a successful
  resolution under a lookup without compressed entries transfers to any lookup that extends
  its in-use entries, with any larger fuel.
* `c4_comp` / `c4_comp_check`: when both paths open the file, the repaired document has the
  same bytes, in-use entries and `/Root`; for every object number **not compressed** strictly,
  every success of the repair path's `getObject` is the strict one (repair never returns a
  different object; it may fail where strict succeeds, through a `/Length` chain that passes
  through a compressed object); every **compressed** object is `null` after repair.
* `#guard`s on `objStmBytes`: `checkComp` holds, `checkFree` fails, objects 2 and 3 are
  `("dict", "null")`, objects 1, 4, 5 agree.

## Open (proposed split)

* **12.7e (Core):** repair rule R6 — parse every scanned `/Type /ObjStm` container (newest
  hit, generation 0) and add a compressed entry `n → compressed c i` for every member `n`
  listed in its index that has no classic hit (newest container wins), within the existing
  failure budget.
* **12.7f (Spec):** exact C4 for compressed entries after 12.7e, under a hypothesis like:
  every container is an in-use newest hit, its index lists exactly the strict compressed
  entries pointing into it, no number is both classic and compressed. The pieces here
  (`getObject_eq_crypt` with a `LookupRel` that admits equal compressed entries) are the
  starting point.
* Encrypted files **with** compressed entries (`HypEnc` requires `SecOk`, i.e. none): needs
  12.7f, since `encryptDict` treats compressed references specially.
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
as the strict trailer. Rule R4' makes this hold whenever the newest `trailer` dictionary with
`/Root` is the strict trailer (the usual single-revision classic file). -/
def trailerOkEnc (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Bool :=
  match Repair.repair limits bytes with
  | .ok (_, tr) =>
    decide (tr.root? = d.trailer.root?) && decide (tr.encrypted = d.trailer.encrypted) &&
      decide (Dict.get? tr.dict Core.Xref.nameEncrypt =
        Dict.get? d.trailer.dict Core.Xref.nameEncrypt) &&
      decide ((Core.Crypt.id0Of tr.dict).data = (Core.Crypt.id0Of d.trailer.dict).data)
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
    obtain ⟨⟨⟨hroot, henc⟩, hE⟩, hid⟩ := htr
    have hsec' := (Repair.repair_ok hrep).1
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

/-- **The hypothesis with compressed entries**: `HypFree` with H2 relaxed to `EntryOkComp`
(compressed entries allowed; H1, H3–H6 unchanged: unencrypted). -/
def HypComp (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  (0, XrefEntry.free 0 65535) ∈ d.xref.entries ∧
  (∀ x ∈ d.xref.entries, EntryOkComp (hits limits bytes) x) ∧
  (∀ x ∈ hits limits bytes, ∃ e ∈ d.xref.entries, e.1 = x.1 ∧ isInUse e.2 = true) ∧
  (newestHits (hits limits bytes)).length ≤ limits.maxObjects ∧
  trailerOk limits bytes d = true ∧
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
  refine ⟨h1, fun x hx => ?_, h3, h4, h5, h6⟩
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
  it may fail where strict succeeds, when a `/Length` chain passes through a compressed
  object);
* every **compressed** object of `d` is `null` in `d'`: the repair scan does not read object
  streams (`Repair` rules R1–R5), so exact agreement fails whenever such an object is not
  `null` strictly (`objStmBytes`, below). -/
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
        d'.getObject limits num gen = .ok nullBody) := by
  obtain ⟨hz, hent, hcov, hcap, htr, hpl⟩ := hh
  have hin : ∀ n off g, (n, XrefEntry.inUse off g) ∈ d.xref.entries ↔
      (n, XrefEntry.inUse off g) ∈ (scanSection limits bytes).entries :=
    inUse_mem_iff_of (fun n off g hx => hent _ hx) hcov hcap
  have hbytes := strictOpen_bytes hs
  obtain ⟨sec, tr, hrep, hwc, -⟩ := repairOpen_ok hr
  have hsec := (Repair.repair_ok hrep).1
  subst hsec
  unfold trailerOk at htr
  rw [hrep] at htr
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at htr
  obtain ⟨henc, hroot⟩ := htr
  rw [withCrypt_plain (d := OpenDoc.mk' bytes (scanSection limits bytes) tr 0 true) henc] at hwc
  cases hwc
  have hc : d.crypt = none := Option.isNone_iff_eq_none.mp hpl
  let d' := OpenDoc.mk' bytes (scanSection limits bytes) tr 0 true
  have hnd1 := d.xref.keys_nodup
  have hnd2 := (scanSection limits bytes).keys_nodup
  have hl1 : ∀ m e, d.lookup m = some e ↔ (m, e) ∈ d.xref.entries := fun m e => by
    rw [WritePrefix.lookup_eq d, Unambiguous.lookupEntry_eq_some_iff hnd1]
  have hl2 : ∀ m e, d'.lookup m = some e ↔ (m, e) ∈ (scanSection limits bytes).entries :=
    fun m e => by
      rw [WritePrefix.lookup_eq d']; exact Unambiguous.lookupEntry_eq_some_iff hnd2
  have hsub : ∀ n off g, d'.lookup n = some (.inUse off g) → d.lookup n = some (.inUse off g) :=
    fun n off g h => (hl1 _ _).mpr ((hin n off g).mpr ((hl2 _ _).mp h))
  have hnc : ∀ n c i, d'.lookup n ≠ some (.compressed c i) := fun n c i h =>
    scanSection_no_compressed limits bytes n c i ((hl2 _ _).mp h)
  have hf : d'.objectCount ≤ d.objectCount := by
    simp only [OpenDoc.objectCount, d.index_eq, d', OpenDoc.mk', List.size_toArray]
    have hnd : (scanSection limits bytes).entries.Nodup := by
      unfold List.Nodup at hnd2 ⊢
      rw [List.pairwise_map] at hnd2
      exact hnd2.imp (fun h e => h (congrArg Prod.fst e))
    refine hnd.length_le_of_subset (fun x hx => ?_)
    obtain ⟨n, e⟩ := x
    cases e with
    | free a g =>
      simp only [scanSection, toEntries, List.mem_cons, List.mem_map] at hx
      rcases hx with h0 | ⟨y, -, hy⟩
      · cases h0; exact hz
      · cases hy
    | compressed c i => exact absurd hx (scanSection_no_compressed limits bytes n c i)
    | inUse off g => exact (hin n off g).mpr hx
  refine ⟨rfl, by rw [hbytes]; rfl, fun n off g => (hin n off g).symm, hroot, ?_, ?_⟩
  · intro num gen v hncs h
    rcases h2 : d'.lookup num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩)
    · have hn : d'.getObject limits num gen = .ok nullBody :=
        getObject_null_of (by simp [h2]) (by simp [h2])
      rw [hn] at h; cases h
      refine getObject_null_of (fun off g h1 => ?_) hncs
      have := hl2 _ _ |>.mpr ((hin num off g).mp ((hl1 _ _).mp h1))
      rw [h2] at this; cases this
    · have hn : d'.getObject limits num gen = .ok nullBody :=
        getObject_null_of (by simp [h2]) (by simp [h2])
      rw [hn] at h; cases h
      refine getObject_null_of (fun off g h1 => ?_) hncs
      have := hl2 _ _ |>.mpr ((hin num off g).mp ((hl1 _ _).mp h1))
      rw [h2] at this; cases this
    · exact getObject_sub (d' := d') (by rw [hbytes]; rfl) hc hsub hnc hf limits num gen off g
        h2 v h
    · exact absurd h2 (hnc _ _ _)
  · intro num gen c i h1
    refine getObject_null_of (fun off g h2 => ?_) (hnc num)
    have := hl1 _ _ |>.mpr ((hin num off g).mpr ((hl2 _ _).mp h2))
    rw [h1] at this; cases this

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
        d'.getObject limits num gen = .ok nullBody) := by
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
-- The compressed objects are lost by repair: exact agreement fails (the obstacle).
#guard both objStmBytes 2 = some ("dict", "null")
#guard both objStmBytes 3 = some ("dict", "null")
#guard sameObj objStmBytes 1 && sameObj objStmBytes 4 && sameObj objStmBytes 5
-- `checkComp` extends `checkFree` (`HypFree.toComp`).
#guard checkComp Limits.default freeEntryBytes = true
#guard checkComp Limits.default repairDiffBytes = false

end SafePdf.Spec.RepairAgreeExt
