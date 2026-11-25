import SafePdf.Core.Open
import SafePdf.Repair

/-!
# C4 (repair conservativity) with explicit hypotheses

Plan.md §5 (claim C4, "on files accepted by the strict parser, repair path ≡ strict path"),
§5.4 (the repair path), §6 Phase 12 "Proof gaps" (task 12.7); `docs/safety.md` §5, gap 1.

C4 does **not** hold as sketched: `Tests/golden/xref/repair-diff.pdf` is strictly openable,
yet its xref entry for object 3 points 5 bytes past the real header (offset 120 instead of
115) and object 2 is marked free while the file defines it. The repair scan finds both
objects at their headers, so the two paths disagree on objects 2 and 3. This module states C4
with the hypotheses that make it true and proves it.

## The hypothesis (`Hyp`)

Let `hits` be the raw header hits of the repair scan (`Repair.scanRaw`, newest first): every
`N G obj` header at a boundary that is not inside an object the scan already parsed and jumped
over (rules R1, R2). For a strictly opened document `d` (`Core.Open.strictOpen`):

* H1 `zero`: the strict section has `0 → free 0 65535`;
* H2 `entries`: every other strict entry is in use (no free entry for `n ≥ 1`, no compressed
  entry), and points at the **newest** scan hit of its object number, with the same
  generation (`newestHit hits n = some (n, g, off)`);
* H3 `covered`: every object number the scan finds has an in-use strict entry;
* H4 `cap`: the scan's distinct object numbers fit in `limits.maxObjects`;
* H5 `trailer`: the repaired trailer has the strict `/Root` and no `/Encrypt`; with H7
  (task 12.7e, checked in the same `trailerOk`): the repaired section has **no compressed
  entry**, i.e. repair rule R6 (object-stream members) added nothing, so the repaired
  section is the scanned one (`Repair.repair_scan`). H7 is new: without it, a strictly valid
  file with an object stream whose members are free or absent in the strict xref (an orphan
  container) would get those members back after repair, and `getObject` would differ;
  `RepairAgreeExt.c4_comp` covers files where R6 does add entries;
* H6 `plain`: the strict document has no decryption state.

`Hyp` is decidable (`instDecidableHyp`); `check limits bytes` runs the strict path and decides
it.

## Theorems

* `newestHits_mem_iff` (newest wins, R3): a hit survives the scan's sort-and-dedup iff it is
  the first (newest) hit of its object number (stability of `List.mergeSort`).
* `entries_eq`: under H1–H4 the strict merged section **equals** the repaired section.
* `c4`: under `Hyp`, the repair path succeeds and yields the strict document up to
  `repaired := true`, `revisions := 0` and the trailer dictionary: same bytes, same section,
  same `/Root`, and `getObject` agrees on **every** `(num, gen)`.
* `c4_check`: the same from `check limits bytes = true`.
* Necessity on the fixture (`#guard`s at the end): `repair-diff.pdf` opens strictly, violates
  H2 (object 3: entry offset 120, newest hit 115) and H3 (object 2 found, strict entry free),
  and the conclusion fails (`getObject 2 0` is `null` strictly but a dictionary after repair;
  `getObject 3 0` is an error strictly but a dictionary after repair). The same file with the
  two xref lines corrected (`repairFixedBytes`) satisfies `check`.

## Open (not covered here)

* A byte-level hypothesis independent of the scan's jump-over behaviour (`hits` mentions
  `scanRaw`; a header hidden inside a parsed object is not a hit). Characterizing `hits` by
  the bytes alone needs a theorem about `scanLoop`'s jumps.
* Free entries other than object 0 (common after deletions): strict returns `null` for them
  and so does repair (absent), but the sections differ in length, and `getObject` uses the
  section length as the `/Length`-resolution fuel; a fuel-monotonicity lemma for
  `Length.parseIndirectResolved` / `ObjStm.fetchCompressed` would lift H2's "no free entry".
* Compressed entries (objects in object streams; the scan sees only classic headers) and
  encrypted files (H6, H5's no-`/Encrypt`).
-/

namespace SafePdf.Spec.RepairAgree

open SafePdf
open SafePdf.Core.Open
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)
open SafePdf.Repair (scanRaw keepAsc keyLe scanObjects scanSection toEntries)

/-! ## Newest hit per object number (rule R3) -/

/-- The raw header hits `(num, gen, offset)` of the repair scan, newest first (R1, R2). -/
def hits (limits : Limits) (bytes : ByteArray) : List (Nat × Nat × Nat) :=
  (scanRaw limits bytes).1

/-- The newest hit of object number `n` in a newest-first hit list. -/
def newestHit (raw : List (Nat × Nat × Nat)) (n : Nat) : Option (Nat × Nat × Nat) :=
  raw.find? (fun y => y.1 == n)

/-- The hits the repair scan keeps before its `maxObjects` cap (R3). -/
def newestHits (raw : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  keepAsc (raw.mergeSort keyLe) 1

/-- On a list sorted by object number, `keepAsc s b` keeps exactly the first hit of each
object number `≥ b`. -/
theorem keepAsc_mem_iff (s : List (Nat × Nat × Nat))
    (hs : s.Pairwise (fun a c => keyLe a c = true)) (b : Nat) (x : Nat × Nat × Nat) :
    x ∈ keepAsc s b ↔ b ≤ x.1 ∧ s.find? (fun y => y.1 == x.1) = some x := by
  induction s generalizing b with
  | nil => simp [keepAsc]
  | cons y ys ih =>
    have hys := hs.of_cons
    have hle : ∀ z ∈ ys, y.1 ≤ z.1 := by
      intro z hz
      have := List.rel_of_pairwise_cons hs hz
      simpa [keyLe] using this
    unfold keepAsc
    by_cases hb : b ≤ y.1
    · simp only [hb, ↓reduceIte, List.mem_cons, ih hys, List.find?_cons]
      by_cases hxy : y.1 = x.1
      · simp only [hxy, beq_self_eq_true, Option.some.injEq]
        constructor
        · rintro (rfl | ⟨h, -⟩)
          · exact ⟨Nat.le_trans hb (Nat.le_of_eq hxy), rfl⟩
          · omega
        · rintro ⟨-, rfl⟩; exact Or.inl rfl
      · have hne : (y.1 == x.1) = false := by simpa using hxy
        simp only [hne]
        constructor
        · rintro (rfl | ⟨h, hf⟩)
          · exact absurd rfl hxy
          · exact ⟨by omega, hf⟩
        · rintro ⟨-, hf⟩
          have hm := hle _ (List.mem_of_find?_eq_some hf)
          exact Or.inr ⟨by omega, hf⟩
    · simp only [hb, ↓reduceIte, ih hys, List.find?_cons]
      constructor
      · rintro ⟨h, hf⟩
        have hne : (y.1 == x.1) = false := by simp; omega
        simp only [hne]; exact ⟨h, hf⟩
      · rintro ⟨h, hf⟩
        have hne : (y.1 == x.1) = false := by simp; omega
        simp only [hne] at hf; exact ⟨h, hf⟩

/-- `keyLe` is transitive. -/
theorem keyLe_trans (a b c : Nat × Nat × Nat) (h1 : keyLe a b = true) (h2 : keyLe b c = true) :
    keyLe a c = true := by
  simp [keyLe] at *; omega

/-- `keyLe` is total. -/
theorem keyLe_total (a b : Nat × Nat × Nat) : (keyLe a b || keyLe b a) = true := by
  simp [keyLe]; omega

/-- **Stability.** Sorting by object number keeps the order of hits with equal numbers, so the
first hit of `n` is the same before and after the sort. -/
theorem find?_mergeSort (raw : List (Nat × Nat × Nat)) (n : Nat) :
    (raw.mergeSort keyLe).find? (fun y => y.1 == n) = raw.find? (fun y => y.1 == n) := by
  rw [← List.head?_filter, ← List.head?_filter]
  congr 1
  let p : Nat × Nat × Nat → Bool := fun y => y.1 == n
  have hc : (raw.filter p).Pairwise (fun a c => keyLe a c = true) := by
    refine List.pairwise_of_forall_mem_list ?_
    intro a ha c hc
    have := (List.mem_filter.mp ha).2
    have := (List.mem_filter.mp hc).2
    simp_all [p, keyLe]
  have hsub : (raw.filter p).Sublist (raw.mergeSort keyLe) :=
    List.sublist_mergeSort keyLe_trans keyLe_total hc (List.filter_sublist)
  have hsub' : (raw.filter p).Sublist ((raw.mergeSort keyLe).filter p) := by
    have := hsub.filter p
    rwa [List.filter_filter, show (fun a => p a && p a) = p by funext a; simp] at this
  have hlen : (raw.filter p).length = ((raw.mergeSort keyLe).filter p).length :=
    (((List.mergeSort_perm raw keyLe).filter p).length_eq).symm
  exact (hsub'.eq_of_length hlen).symm

/-- **Newest wins (R3).** A hit is kept by the repair scan (before the cap) iff its object
number is at least 1 and it is the newest hit of that number. -/
theorem newestHits_mem_iff (raw : List (Nat × Nat × Nat)) (x : Nat × Nat × Nat) :
    x ∈ newestHits raw ↔ 1 ≤ x.1 ∧ newestHit raw x.1 = some x := by
  unfold newestHits newestHit
  rw [keepAsc_mem_iff _ (List.pairwise_mergeSort keyLe_trans keyLe_total raw), find?_mergeSort]

/-- Below the cap, `scanObjects` is `newestHits` of the raw hits. -/
theorem scanObjects_eq (limits : Limits) (bytes : ByteArray)
    (hcap : (newestHits (hits limits bytes)).length ≤ limits.maxObjects) :
    scanObjects limits bytes = newestHits (hits limits bytes) := by
  unfold scanObjects
  exact List.take_of_length_le hcap

/-! ## The hypothesis -/

/-- Condition H2 on one strict entry: object 0 may be `free 0 65535`; every other entry is in
use and points at the newest scan hit of its number with the same generation. -/
def EntryOk (raw : List (Nat × Nat × Nat)) : Nat × XrefEntry → Prop
  | (n, .free a g) => n = 0 ∧ a = 0 ∧ g = 65535
  | (_, .compressed _ _) => False
  | (n, .inUse off g) => 1 ≤ n ∧ newestHit raw n = some (n, g, off)

/-- `EntryOk` is decidable. -/
instance (raw : List (Nat × Nat × Nat)) : DecidablePred (EntryOk raw) := fun x =>
  match x with
  | (n, .free a g) => inferInstanceAs (Decidable (n = 0 ∧ a = 0 ∧ g = 65535))
  | (_, .compressed _ _) => inferInstanceAs (Decidable False)
  | (n, .inUse off g) => inferInstanceAs (Decidable (1 ≤ n ∧ newestHit raw n = some (n, g, off)))

/-- Whether an entry is in use. -/
def isInUse : XrefEntry → Bool
  | .inUse _ _ => true
  | _ => false

/-- Whether an entry is compressed. -/
def isComp : XrefEntry → Bool
  | .compressed _ _ => true
  | _ => false

/-- Whether a list of entries has no compressed entry. -/
def noComp (es : List (Nat × XrefEntry)) : Bool := es.all (fun x => !isComp x.2)

/-- `noComp` is sound. -/
theorem noComp_spec {es : List (Nat × XrefEntry)} (h : noComp es = true) (n c i : Nat) :
    (n, XrefEntry.compressed c i) ∉ es := by
  intro hm
  have := List.all_eq_true.mp h _ hm
  simp [isComp] at this

/-- Condition H5: the repair path's trailer exists, has the strict `/Root`, and no
`/Encrypt`; and H7 (task 12.7e): the repaired section has no compressed entry, i.e. repair
rule R6 (object-stream members) added nothing (`Repair.repair_scan`). -/
def trailerOk (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Bool :=
  match Repair.repair limits bytes with
  | .ok (sec, tr) => !tr.encrypted && tr.root? == d.trailer.root? && noComp sec.entries
  | .error _ => false

/-- **The C4 hypothesis** for the strictly opened document `d` of `bytes` (H1–H6, see the
module doc). -/
def Hyp (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  (0, XrefEntry.free 0 65535) ∈ d.xref.entries ∧
  (∀ x ∈ d.xref.entries, EntryOk (hits limits bytes) x) ∧
  (∀ x ∈ hits limits bytes, ∃ e ∈ d.xref.entries, e.1 = x.1 ∧ isInUse e.2 = true) ∧
  (newestHits (hits limits bytes)).length ≤ limits.maxObjects ∧
  trailerOk limits bytes d = true ∧
  d.crypt.isNone = true

/-- `Hyp` is decidable. -/
instance instDecidableHyp (limits : Limits) (bytes : ByteArray) (d : OpenDoc) :
    Decidable (Hyp limits bytes d) := by
  unfold Hyp; infer_instance

/-- **The checker**: the strict path succeeds and its document satisfies `Hyp`. -/
def check (limits : Limits) (bytes : ByteArray) : Bool :=
  match strictOpen limits bytes with
  | .ok d => decide (Hyp limits bytes d)
  | .error _ => false

/-! ## Equal sections -/

/-- Two lists strictly sorted by key with the same members are equal. -/
theorem eq_of_sorted_mem_iff {α : Type} :
    ∀ (l₁ l₂ : List (Nat × α)), l₁.Pairwise (fun a b => a.1 < b.1) →
      l₂.Pairwise (fun a b => a.1 < b.1) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: _, [], _, _, h => absurd ((h a).mp (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: as, b :: bs, h₁, h₂, h => by
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp (List.mem_cons_self ..)) with e | ha
      · exact e
      · rcases List.mem_cons.mp ((h b).mpr (List.mem_cons_self ..)) with e | hb
        · exact e.symm
        · have := List.rel_of_pairwise_cons h₂ ha
          have := List.rel_of_pairwise_cons h₁ hb
          omega
    subst hab
    congr 1
    refine eq_of_sorted_mem_iff as bs h₁.of_cons h₂.of_cons (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hx'
      · have := List.rel_of_pairwise_cons h₁ hx; omega
      · exact hx'
    · rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hx'
      · have := List.rel_of_pairwise_cons h₂ hx; omega
      · exact hx'

/-- **Equal sections.** Under H1–H4 the strict section of `d` is the repaired section. -/
theorem entries_eq {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : Hyp limits bytes d) : d.xref.entries = (scanSection limits bytes).entries := by
  obtain ⟨hz, hent, hcov, hcap, -, -⟩ := h
  apply eq_of_sorted_mem_iff _ _ d.xref.sorted (scanSection limits bytes).sorted
  intro x
  simp only [scanSection, toEntries, scanObjects_eq limits bytes hcap, List.mem_cons,
    List.mem_map]
  constructor
  · intro hx
    have he := hent x hx
    obtain ⟨n, e⟩ := x
    cases e with
    | free a g =>
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inl rfl
    | compressed _ _ => exact he.elim
    | inUse off g =>
      obtain ⟨h1, hn⟩ := he
      exact Or.inr ⟨(n, g, off), (newestHits_mem_iff _ _).mpr ⟨h1, hn⟩, rfl⟩
  · rintro (rfl | ⟨⟨yn, yg, yoff⟩, hy, rfl⟩)
    · exact hz
    · obtain ⟨h1, hy⟩ := (newestHits_mem_iff _ _).mp hy
      obtain ⟨e, he, hk, hu⟩ := hcov _ (List.mem_of_find?_eq_some hy)
      obtain ⟨n, e⟩ := e
      cases e with
      | free _ _ => simp [isInUse] at hu
      | compressed _ _ => simp [isInUse] at hu
      | inUse off g =>
        have hok := hent _ he
        simp only at hk
        subst hk
        obtain ⟨-, hn⟩ := hok
        rw [hy] at hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨-, rfl, rfl⟩ := hn
        exact he

/-! ## Equal observations -/

/-- `getObject` depends only on the bytes, the section and the decryption state. -/
theorem getObject_congr {d₁ d₂ : OpenDoc} (hb : d₁.bytes = d₂.bytes)
    (he : d₁.xref.entries = d₂.xref.entries) (hc : d₁.crypt = d₂.crypt) (limits : Limits)
    (num gen : Nat) : d₁.getObject limits num gen = d₂.getObject limits num gen := by
  have hi : d₁.index = d₂.index := by rw [d₁.index_eq, d₂.index_eq, he]
  unfold OpenDoc.getObject OpenDoc.getObjectTrace OpenDoc.lookup OpenDoc.objectCount
    OpenDoc.pre OpenDoc.decrypt
  rw [hb, hi, hc]

/-- `validate` succeeds on a document with the same `/Root` and the same `getObject`. -/
theorem validate_congr {limits : Limits} {d₁ d₂ : OpenDoc}
    (hr : d₁.trailer.root? = d₂.trailer.root?)
    (hg : ∀ num gen, d₁.getObject limits num gen = d₂.getObject limits num gen)
    (h : validate limits d₁ = .ok d₁) : validate limits d₂ = .ok d₂ := by
  unfold validate at h ⊢
  rw [← hr]
  split at h
  · cases h
  · rename_i n g _
    split at h
    · cases h
    · rename_i heq
      rw [← hg n g, heq]
    all_goals cases h

/-- The strictly opened document holds the input bytes. -/
theorem strictOpen_bytes {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : strictOpen limits bytes = .ok d) : d.bytes = bytes := by
  obtain ⟨revs, -, -, ho, -⟩ := strictOpen_ok h
  unfold ofChain at ho
  split at ho
  · cases ho
  · obtain ⟨c, rfl⟩ := withCrypt_ok ho
    rfl

/-- **C4 (repair conservativity), with explicit hypotheses.** If the strict path opens `bytes`
as `d` and `Hyp limits bytes d` holds, the repair path also succeeds, and its document has the
same bytes, the same cross-reference section and the same `/Root` as `d`, is flagged
`repaired`, and returns the same result as `d` for **every** `getObject num gen`. -/
theorem c4 {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : Hyp limits bytes d) :
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      d'.xref.entries = d.xref.entries ∧ d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  have hent := entries_eq hh
  obtain ⟨-, -, -, -, htr, hpl⟩ := hh
  have hbytes := strictOpen_bytes hs
  obtain ⟨-, -, -, -, hval⟩ := strictOpen_ok hs
  unfold trailerOk at htr
  split at htr
  · rename_i sec tr hrep
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at htr
    obtain ⟨⟨henc, hroot⟩, hnc⟩ := htr
    have hsec := Repair.repair_scan hrep (noComp_spec hnc)
    subst hsec
    let d' := OpenDoc.mk' bytes (scanSection limits bytes) tr 0 true
    have hg : ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen :=
      getObject_congr (by rw [hbytes]; rfl) hent.symm
        (by simpa [d', OpenDoc.mk'] using (Option.isNone_iff_eq_none.mp hpl).symm) limits
    have hv : validate limits d' = .ok d' :=
      validate_congr hroot.symm (fun n g => (hg n g).symm) hval
    refine ⟨d', ?_, rfl, by rw [hbytes]; rfl, hent.symm, hroot, hg⟩
    unfold repairOpen
    rw [hrep]
    simp only
    rw [withCrypt_plain (d := d') henc]
    exact hv
  · cases htr

/-- **C4 from the checker.** `check limits bytes = true` gives the strict document and the
conclusion of `c4`. -/
theorem c4_check {limits : Limits} {bytes : ByteArray} (hc : check limits bytes = true) :
    ∃ d d', strictOpen limits bytes = .ok d ∧ repairOpen limits bytes = .ok d' ∧
      d'.repaired = true ∧ d'.bytes = d.bytes ∧ d'.xref.entries = d.xref.entries ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  unfold check at hc
  split at hc
  · rename_i d hs
    obtain ⟨d', h⟩ := c4 hs (of_decide_eq_true hc)
    exact ⟨d, d', hs, h⟩
  · cases hc

/-! ## Necessity: the `repair-diff.pdf` fixture -/

/-- `Tests/golden/xref/repair-diff.pdf` (329 bytes, SHA-256 `e941d405…c5d7`), embedded as a
byte literal: object 2 is marked free (`0000000000 00001 f`) though the file defines it at 58,
and object 3's entry is 120, five bytes past its header at 115. -/
def repairDiffBytes : ByteArray := ⟨#[
37, 80, 68, 70, 45, 49, 46, 55, 10, 49, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121,
  112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103, 32, 47, 80, 97, 103, 101, 115, 32, 50, 32,
  48, 32, 82, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 50, 32, 48, 32, 111, 98, 106, 10,
  60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 115, 32, 47, 75, 105, 100, 115,
  32, 91, 51, 32, 48, 32, 82, 93, 32, 47, 67, 111, 117, 110, 116, 32, 49, 32, 62, 62, 10, 101,
  110, 100, 111, 98, 106, 10, 51, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112,
  101, 32, 47, 80, 97, 103, 101, 32, 47, 80, 97, 114, 101, 110, 116, 32, 50, 32, 48, 32, 82, 32,
  47, 77, 101, 100, 105, 97, 66, 111, 120, 32, 91, 48, 32, 48, 32, 54, 49, 50, 32, 55, 57, 50,
  93, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 120, 114, 101, 102, 10, 48, 32, 52, 10,
  48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 32, 54, 53, 53, 51, 53, 32, 102, 32, 10, 48, 48, 48,
  48, 48, 48, 48, 48, 48, 57, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48, 48, 48,
  48, 48, 48, 48, 32, 48, 48, 48, 48, 49, 32, 102, 32, 10, 48, 48, 48, 48, 48, 48, 48, 49, 50,
  48, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 116, 114, 97, 105, 108, 101, 114, 10, 60, 60, 32,
  47, 83, 105, 122, 101, 32, 52, 32, 47, 82, 111, 111, 116, 32, 49, 32, 48, 32, 82, 32, 62, 62,
  10, 115, 116, 97, 114, 116, 120, 114, 101, 102, 10, 49, 56, 54, 10, 37, 37, 69, 79, 70, 10]⟩

/-- The same file with the two xref lines corrected (`0000000058 00000 n`,
`0000000115 00000 n`; same length, so `startxref` is unchanged): a file satisfying `Hyp`. -/
def repairFixedBytes : ByteArray := ⟨#[
  37, 80, 68, 70, 45, 49, 46, 55, 10, 49, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121,
  112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103, 32, 47, 80, 97, 103, 101, 115, 32, 50, 32,
  48, 32, 82, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 50, 32, 48, 32, 111, 98, 106, 10,
  60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 115, 32, 47, 75, 105, 100, 115,
  32, 91, 51, 32, 48, 32, 82, 93, 32, 47, 67, 111, 117, 110, 116, 32, 49, 32, 62, 62, 10, 101,
  110, 100, 111, 98, 106, 10, 51, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112,
  101, 32, 47, 80, 97, 103, 101, 32, 47, 80, 97, 114, 101, 110, 116, 32, 50, 32, 48, 32, 82, 32,
  47, 77, 101, 100, 105, 97, 66, 111, 120, 32, 91, 48, 32, 48, 32, 54, 49, 50, 32, 55, 57, 50,
  93, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 120, 114, 101, 102, 10, 48, 32, 52, 10,
  48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 32, 54, 53, 53, 51, 53, 32, 102, 32, 10, 48, 48, 48,
  48, 48, 48, 48, 48, 48, 57, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48, 48, 48,
  48, 48, 53, 56, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48, 48, 48, 48, 49, 49,
  53, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 116, 114, 97, 105, 108, 101, 114, 10, 60, 60, 32,
  47, 83, 105, 122, 101, 32, 52, 32, 47, 82, 111, 111, 116, 32, 49, 32, 48, 32, 82, 32, 62, 62,
  10, 115, 116, 97, 114, 116, 120, 114, 101, 102, 10, 49, 56, 54, 10, 37, 37, 69, 79, 70, 10]⟩

/-- Test helper: a `getObject` result as a comparable string. -/
def showGet : Except Error IndirectBody → String
  | .ok (.obj .null) => "null"
  | .ok (.obj (.dict _)) => "dict"
  | .ok _ => "other"
  | .error _ => "error"

/-- Test helper: `getObject num 0` on the strict and on the repair path. -/
def both (bytes : ByteArray) (num : Nat) : Option (String × String) :=
  match strictOpen Limits.default bytes, repairOpen Limits.default bytes with
  | .ok d, .ok d' => some (showGet (d.getObject Limits.default num 0),
      showGet (d'.getObject Limits.default num 0))
  | _, _ => none

-- The fixture opens strictly, and the checker rejects it.
#guard (match strictOpen Limits.default repairDiffBytes with | .ok _ => true | .error _ => false)
#guard check Limits.default repairDiffBytes = false
-- H2 fails for object 3 (strict entry at 120, newest scan hit at 115) …
#guard newestHit (hits Limits.default repairDiffBytes) 3 = some (3, 0, 115)
#guard (match strictOpen Limits.default repairDiffBytes with
  | .ok d => d.lookup 3 == some (.inUse 120 0) && d.lookup 2 == some (.free 0 1)
  | .error _ => false)
-- … and H3 fails for object 2 (found by the scan, free in the strict section).
#guard newestHit (hits Limits.default repairDiffBytes) 2 = some (2, 0, 58)
-- The conclusion of `c4` fails: both paths succeed and disagree on objects 2 and 3.
#guard both repairDiffBytes 2 = some ("null", "dict")
#guard both repairDiffBytes 3 = some ("error", "dict")
#guard both repairDiffBytes 1 = some ("dict", "dict")

-- The corrected file satisfies the hypothesis, so `c4_check` applies (non-vacuity).
#guard check Limits.default repairFixedBytes = true
#guard both repairFixedBytes 2 = some ("dict", "dict")
#guard both repairFixedBytes 3 = some ("dict", "dict")

end SafePdf.Spec.RepairAgree
