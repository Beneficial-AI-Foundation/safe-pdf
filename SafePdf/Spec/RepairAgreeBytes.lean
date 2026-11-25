import SafePdf.Spec.RepairAgreeFree

/-!
# C4 with a byte-level hypothesis (task 12.7b)

Plan.md §5 (claim C4), §5.4 (the repair path, rules R1/R2), §6 Phase 12 "Proof gaps" (task
12.7b); `docs/safety.md` §5, gap 1. Removes the "Open" item of `Spec.RepairAgree` (task 12.7)
that its H2/H3 speak about the repair scan's hits (`Repair.scanRaw`) rather than the bytes.

## Header occurrences in the bytes

`Header bytes p n g`: at offset `p < bytes.size`, at a token boundary (`Repair.boundaryAt`:
start of input, or after a whitespace or delimiter byte), the bytes read
`n SP+ g SP+ obj` followed by a whitespace byte, a delimiter or the end of input, with
`1 ≤ n`, `g ≤ 65535` (`Repair.headerAt`). `headers bytes` lists every occurrence, newest
first (`Repair.headerLoop`, a parse-free byte scan); `mem_headers` characterizes it.

## The scan against the occurrences

* `hits_sublist_headers` (unconditional): the scan's hits are a sublist of the occurrences
  (every hit is a header occurrence, in the same order).
* `hits_eq_headers`: under `NoNested` the hits **are** the occurrences. `NoNested` says: for
  every occurrence at `p` whose parse attempt (`Repair.attempt`, the scan's own parse, against
  the byte-level `headerTable`) ends at `r`, no occurrence lies strictly between `p` and `r`
  ("no `obj` header inside an object's byte range"). It mentions the parser but not the scan's
  state (jump targets, failure budget): it is a property of the bytes alone, and it is
  decidable (quadratic in the number of occurrences).

Why `NoNested` is the right side condition: the scan jumps from `p` to `max r (p + 1)` after a
successful attempt, so occurrences inside `(p, r)` are skipped. When the failure budget
(`limits.maxRepairFailures`) runs out, the scan stops parsing and records every occurrence,
which only adds hits; `NoNested` covers both regimes.

## C4 over bytes

* `HypBytes` / `checkBytes`: `NoNested` plus 12.7's H1–H6 with `hits` replaced by `headers`;
  `c4_bytes`, `c4_bytes_check` derive 12.7's conclusion (exact `getObject` agreement) from
  `c4`.
* `HypFreeBytes` / `checkFreeBytes`: the same over 12.7a's `HypFree` (free entries `n ≥ 1`);
  `c4_free_bytes`, `c4_free_bytes_check` derive `c4_free`'s conclusion (`Agree`).
* `#guard`s: on `repairDiffBytes`, `repairFixedBytes` and `freeEntryBytes` the hits equal the
  occurrences and `NoNested` holds; the byte checkers agree with 12.7/12.7a's checkers on them.
  `nestedBytes` (a stream whose data contains `2 0 obj`) shows that `NoNested` is needed: the
  occurrence inside the stream is not a hit, and `NoNested` fails.

## Open

* An exact characterization of the hits without a side condition (an occurrence is a hit iff
  it lies inside no earlier *hit's* successful-attempt range, while the failure budget lasts)
  is not stated; `NoNested` is a sufficient condition, not a necessary one (a nested occurrence
  inside a stream whose header comes after the budget runs out is still a hit).
* Compressed entries and encrypted files (as in `Spec.RepairAgree`).
-/

namespace SafePdf.Spec.RepairAgreeBytes

open SafePdf
open SafePdf.Core.Open
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)
open SafePdf.Spec.RepairAgree
open SafePdf.Spec.RepairAgreeFree
open SafePdf.Repair (boundaryAt headerAt headerLoop headerTable attempt scanLoop scanRaw)

/-! ## Header occurrences -/

/-- **A header occurrence**: at offset `p` (inside the input, at a token boundary) the bytes
read `n g obj` (R1: `1 ≤ n`, `g ≤ 65535`, properly terminated). A property of the bytes. -/
def Header (bytes : ByteArray) (p n g : Nat) : Prop :=
  p < bytes.size ∧ boundaryAt bytes p = true ∧ headerAt bytes p = some (n, g)

/-- Every header occurrence `(num, gen, offset)`, newest (highest offset) first. -/
def headers (bytes : ByteArray) : List (Nat × Nat × Nat) :=
  headerLoop bytes 0 []

/-- `headerLoop` at an occurrence records it and moves on. -/
theorem headerLoop_hit {bytes : ByteArray} {p num gen : Nat} (acc : List (Nat × Nat × Nat))
    (h : Header bytes p num gen) :
    headerLoop bytes p acc = headerLoop bytes (p + 1) ((num, gen, p) :: acc) := by
  obtain ⟨hp, hb, hh⟩ := h
  rw [headerLoop.eq_def bytes p acc]
  simp only [hp, ↓reduceDIte, hb, ↓reduceIte, hh]

/-- `headerLoop` at a position with no occurrence moves on. -/
theorem headerLoop_miss {bytes : ByteArray} {p : Nat} (acc : List (Nat × Nat × Nat))
    (h : ∀ n g, ¬ Header bytes p n g) :
    headerLoop bytes p acc = headerLoop bytes (p + 1) acc := by
  rw [headerLoop.eq_def bytes p acc]
  by_cases hp : p < bytes.size
  · simp only [hp, ↓reduceDIte]
    by_cases hb : boundaryAt bytes p = true
    · simp only [hb, ↓reduceIte]
      rcases hh : headerAt bytes p with _ | ⟨n, g⟩
      · rfl
      · exact absurd ⟨hp, hb, hh⟩ (h n g)
    · simp only [hb]; rfl
  · simp only [hp, ↓reduceDIte]
    rw [headerLoop.eq_def bytes (p + 1) acc]
    simp only [show ¬ p + 1 < bytes.size by omega, ↓reduceDIte]

/-- `headerLoop` past the input returns its accumulator. -/
theorem headerLoop_end {bytes : ByteArray} {p : Nat} (acc : List (Nat × Nat × Nat))
    (h : bytes.size ≤ p) : headerLoop bytes p acc = acc := by
  rw [headerLoop.eq_def bytes p acc]
  simp only [show ¬ p < bytes.size by omega, ↓reduceDIte]

/-- Whether position `p` holds an occurrence is decided by `headerAt` and the boundary test. -/
theorem header_or_not (bytes : ByteArray) (p : Nat) :
    (∃ n g, Header bytes p n g) ∨ (∀ n g, ¬ Header bytes p n g) := by
  by_cases h : ∃ n g, Header bytes p n g
  · exact Or.inl h
  · exact Or.inr fun n g hh => h ⟨n, g, hh⟩

/-- Membership in `headerLoop`: the accumulator, or an occurrence at or after `p`. -/
theorem mem_headerLoop (bytes : ByteArray) (p : Nat) (acc : List (Nat × Nat × Nat))
    (x : Nat × Nat × Nat) :
    x ∈ headerLoop bytes p acc ↔ x ∈ acc ∨ (p ≤ x.2.2 ∧ Header bytes x.2.2 x.1 x.2.1) := by
  fun_induction headerLoop bytes p acc
  case case1 p acc hp hb num gen hh ih =>
    rw [ih]
    obtain ⟨xn, xg, xq⟩ := x
    simp only [List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ((⟨rfl, rfl, rfl⟩ | hx) | ⟨hle, hx⟩)
      · exact Or.inr ⟨Nat.le_refl _, hp, hb, hh⟩
      · exact Or.inl hx
      · exact Or.inr ⟨by omega, hx⟩
    · rintro (hx | ⟨hle, hx⟩)
      · exact Or.inl (Or.inr hx)
      · by_cases he : xq = p
        · subst he
          obtain ⟨-, -, hx⟩ := hx
          rw [hh] at hx
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)
        · exact Or.inr ⟨by omega, hx⟩
  case case2 p acc hp hb hh ih =>
    rw [ih]
    constructor
    · rintro (hx | ⟨hle, hx⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨by omega, hx⟩
    · rintro (hx | ⟨hle, hx⟩)
      · exact Or.inl hx
      · by_cases he : x.2.2 = p
        · rw [he] at hx; obtain ⟨-, -, hx⟩ := hx; rw [hh] at hx; cases hx
        · exact Or.inr ⟨by omega, hx⟩
  case case3 p acc hp hb ih =>
    rw [ih]
    constructor
    · rintro (hx | ⟨hle, hx⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨by omega, hx⟩
    · rintro (hx | ⟨hle, hx⟩)
      · exact Or.inl hx
      · by_cases he : x.2.2 = p
        · rw [he] at hx; obtain ⟨-, hx, -⟩ := hx; exact absurd hx hb
        · exact Or.inr ⟨by omega, hx⟩
  case case4 p acc hp =>
    constructor
    · exact Or.inl
    · rintro (hx | ⟨hle, hx, -⟩)
      · exact hx
      · omega

/-- **The occurrences.** `headers bytes` lists exactly the header occurrences of `bytes`. -/
theorem mem_headers (bytes : ByteArray) (x : Nat × Nat × Nat) :
    x ∈ headers bytes ↔ Header bytes x.2.2 x.1 x.2.1 := by
  unfold headers
  rw [mem_headerLoop]
  simp

/-- `headerLoop` only prepends to its accumulator. -/
theorem headerLoop_append (bytes : ByteArray) (p : Nat) (acc ext : List (Nat × Nat × Nat)) :
    headerLoop bytes p (acc ++ ext) = headerLoop bytes p acc ++ ext := by
  fun_induction headerLoop bytes p acc
  case case1 p acc hp hb num gen hh ih =>
    rw [headerLoop_hit _ ⟨hp, hb, hh⟩, ← ih]; rfl
  case case2 p acc hp hb hh ih =>
    rw [headerLoop_miss _ (fun n g h => by rw [h.2.2] at hh; cases hh), ih]
  case case3 p acc hp hb ih =>
    rw [headerLoop_miss _ (fun n g h => hb h.2.1), ih]
  case case4 p acc hp =>
    rw [headerLoop_end _ (by omega)]

/-- One step of `headerLoop` only adds occurrences. -/
theorem headerLoop_succ_sublist (bytes : ByteArray) (p : Nat) (acc : List (Nat × Nat × Nat)) :
    (headerLoop bytes (p + 1) acc).Sublist (headerLoop bytes p acc) := by
  rcases header_or_not bytes p with ⟨n, g, h⟩ | h
  · rw [headerLoop_hit acc h, ← List.nil_append acc, headerLoop_append,
      ← List.nil_append ((n, g, p) :: _), headerLoop_append]
    exact List.Sublist.append_left (List.sublist_cons_self _ _) _
  · rw [headerLoop_miss acc h]; exact List.Sublist.refl _

/-- Starting `headerLoop` later only drops occurrences. -/
theorem headerLoop_mono (bytes : ByteArray) (acc : List (Nat × Nat × Nat)) :
    ∀ (k p : Nat), (headerLoop bytes (p + k) acc).Sublist (headerLoop bytes p acc)
  | 0, _ => List.Sublist.refl _
  | k + 1, p => by
    have := headerLoop_mono bytes acc k (p + 1)
    rw [show p + 1 + k = p + (k + 1) by omega] at this
    exact this.trans (headerLoop_succ_sublist bytes p acc)

/-- `headerLoop` skips a stretch of positions holding no occurrence. -/
theorem headerLoop_skip (bytes : ByteArray) (acc : List (Nat × Nat × Nat)) :
    ∀ (k a : Nat), (∀ q, a ≤ q → q < a + k → ∀ n g, ¬ Header bytes q n g) →
      headerLoop bytes a acc = headerLoop bytes (a + k) acc
  | 0, _, _ => rfl
  | k + 1, a, h => by
    rw [headerLoop_miss acc (h a (Nat.le_refl _) (by omega)),
      headerLoop_skip bytes acc k (a + 1) (fun q h1 h2 => h q (by omega) (by omega)),
      show a + 1 + k = a + (k + 1) by omega]

/-! ## The scan against the occurrences -/

/-- The scan's lazy header table, as `Repair.scanRaw` builds it. -/
def tblOf (bytes : ByteArray) : Thunk (Array (Nat × Nat × Nat)) :=
  Thunk.mk fun _ => headerTable bytes

/-- `hits` is the scan loop with `tblOf`. -/
theorem hits_eq_scanLoop (limits : Limits) (bytes : ByteArray) :
    hits limits bytes = (scanLoop limits bytes (tblOf bytes) 0 [] 0 0).1 := rfl

/-- The scan loop's hits are a sublist of `headerLoop` from the same position. -/
theorem scanLoop_sublist (limits : Limits) (bytes : ByteArray)
    (tbl : Thunk (Array (Nat × Nat × Nat))) (p : Nat) (acc : List (Nat × Nat × Nat))
    (n fails : Nat) : (scanLoop limits bytes tbl p acc n fails).1.Sublist (headerLoop bytes p acc) := by
  fun_induction scanLoop limits bytes tbl p acc n fails
  case case1 p acc n fails hp hb num gen hh _ r _ ih =>
    rw [headerLoop_hit acc ⟨hp, hb, hh⟩]
    have hm := headerLoop_mono bytes ((num, gen, p) :: acc) (max r (p + 1) - (p + 1)) (p + 1)
    rw [show p + 1 + (max r (p + 1) - (p + 1)) = max r (p + 1) by omega] at hm
    exact ih.trans hm
  case case2 p acc n fails hp hb num gen hh _ _ ih =>
    rw [headerLoop_hit acc ⟨hp, hb, hh⟩]; exact ih
  case case3 p acc n fails hp hb num gen hh _ ih =>
    rw [headerLoop_hit acc ⟨hp, hb, hh⟩]; exact ih
  case case4 p acc n fails hp hb hh ih =>
    rw [headerLoop_miss acc (fun n g h => by rw [h.2.2] at hh; cases hh)]; exact ih
  case case5 p acc n fails hp hb ih =>
    rw [headerLoop_miss acc (fun n g h => hb h.2.1)]; exact ih
  case case6 p acc n fails hp =>
    rw [headerLoop_end acc (by omega)]; exact List.Sublist.refl _

/-- **Hits are occurrences (unconditional).** The repair scan's hits are a sublist of the
header occurrences of the bytes: every hit is an occurrence, in the same order. -/
theorem hits_sublist_headers (limits : Limits) (bytes : ByteArray) :
    (hits limits bytes).Sublist (headers bytes) :=
  scanLoop_sublist limits bytes (tblOf bytes) 0 [] 0 0

/-- Every hit is a header occurrence. -/
theorem hit_header {limits : Limits} {bytes : ByteArray} {x : Nat × Nat × Nat}
    (hx : x ∈ hits limits bytes) : Header bytes x.2.2 x.1 x.2.1 :=
  (mem_headers bytes x).mp ((hits_sublist_headers limits bytes).subset hx)

/-- Under a no-nesting condition stated for a table `tbl`, the scan loop's hits are exactly
`headerLoop`'s occurrences. -/
theorem scanLoop_eq_headerLoop (limits : Limits) (bytes : ByteArray)
    (tbl : Thunk (Array (Nat × Nat × Nat)))
    (hno : ∀ q n g r, Header bytes q n g → attempt limits bytes tbl q = some r →
      ∀ q', q < q' → q' < r → ∀ n' g', ¬ Header bytes q' n' g')
    (p : Nat) (acc : List (Nat × Nat × Nat)) (n fails : Nat) :
    (scanLoop limits bytes tbl p acc n fails).1 = headerLoop bytes p acc := by
  fun_induction scanLoop limits bytes tbl p acc n fails
  case case1 p acc n fails hp hb num gen hh _ r hr ih =>
    rw [ih, headerLoop_hit acc ⟨hp, hb, hh⟩,
      headerLoop_skip bytes _ (max r (p + 1) - (p + 1)) (p + 1)
        (fun q h1 h2 => hno p num gen r ⟨hp, hb, hh⟩ hr q (by omega) (by omega)),
      show p + 1 + (max r (p + 1) - (p + 1)) = max r (p + 1) by omega]
  case case2 p acc n fails hp hb num gen hh _ _ ih =>
    rw [headerLoop_hit acc ⟨hp, hb, hh⟩]; exact ih
  case case3 p acc n fails hp hb num gen hh _ ih =>
    rw [headerLoop_hit acc ⟨hp, hb, hh⟩]; exact ih
  case case4 p acc n fails hp hb hh ih =>
    rw [headerLoop_miss acc (fun n g h => by rw [h.2.2] at hh; cases hh)]; exact ih
  case case5 p acc n fails hp hb ih =>
    rw [headerLoop_miss acc (fun n g h => hb h.2.1)]; exact ih
  case case6 p acc n fails hp =>
    rw [headerLoop_end acc (by omega)]

/-! ## No header inside a parsed object -/

/-- After the attempt at `p` (result `res`), no occurrence of `hs` lies strictly inside the
parsed object `(p, r)`. -/
def JumpFree (hs : List (Nat × Nat × Nat)) (p : Nat) : Option Nat → Prop
  | some r => ∀ y ∈ hs, ¬ (p < y.2.2 ∧ y.2.2 < r)
  | none => True

/-- `JumpFree` is decidable. -/
instance (hs : List (Nat × Nat × Nat)) (p : Nat) : DecidablePred (JumpFree hs p) := fun res =>
  match res with
  | some r => inferInstanceAs (Decidable (∀ y ∈ hs, ¬ (p < y.2.2 ∧ y.2.2 < r)))
  | none => inferInstanceAs (Decidable True)

/-- **No header inside an object (bytes only).** For every header occurrence whose parse
attempt (`Repair.attempt`, against the byte-level `headerTable`) succeeds with end `r`, no
occurrence lies strictly between it and `r`. -/
def NoNested (limits : Limits) (bytes : ByteArray) : Prop :=
  ∀ x ∈ headers bytes, JumpFree (headers bytes) x.2.2 (attempt limits bytes (tblOf bytes) x.2.2)

/-- `NoNested` is decidable. -/
instance instDecidableNoNested (limits : Limits) (bytes : ByteArray) :
    Decidable (NoNested limits bytes) := by
  unfold NoNested; infer_instance

/-- `NoNested` in positional form. -/
theorem NoNested.pos {limits : Limits} {bytes : ByteArray} (h : NoNested limits bytes) :
    ∀ q n g r, Header bytes q n g → attempt limits bytes (tblOf bytes) q = some r →
      ∀ q', q < q' → q' < r → ∀ n' g', ¬ Header bytes q' n' g' := by
  intro q n g r hq hr q' h1 h2 n' g' hq'
  have hj := h (n, g, q) ((mem_headers bytes _).mpr hq)
  simp only [hr, JumpFree] at hj
  exact hj (n', g', q') ((mem_headers bytes _).mpr hq') ⟨h1, h2⟩

/-- **Hits are the occurrences.** Under `NoNested`, the repair scan's hits are exactly the
header occurrences of the bytes. -/
theorem hits_eq_headers {limits : Limits} {bytes : ByteArray} (h : NoNested limits bytes) :
    hits limits bytes = headers bytes :=
  scanLoop_eq_headerLoop limits bytes (tblOf bytes) h.pos 0 [] 0 0

/-! ## C4 over bytes -/

/-- **The byte-level C4 hypothesis**: `NoNested`, and 12.7's H1–H6 (`Spec.RepairAgree.Hyp`)
with the scan's hits replaced by the header occurrences of the bytes. -/
def HypBytes (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  NoNested limits bytes ∧
  (0, XrefEntry.free 0 65535) ∈ d.xref.entries ∧
  (∀ x ∈ d.xref.entries, EntryOk (headers bytes) x) ∧
  (∀ x ∈ headers bytes, ∃ e ∈ d.xref.entries, e.1 = x.1 ∧ isInUse e.2 = true) ∧
  (newestHits (headers bytes)).length ≤ limits.maxObjects ∧
  trailerOk limits bytes d = true ∧
  d.crypt.isNone = true

/-- `HypBytes` is decidable. -/
instance instDecidableHypBytes (limits : Limits) (bytes : ByteArray) (d : OpenDoc) :
    Decidable (HypBytes limits bytes d) := by
  unfold HypBytes; infer_instance

/-- **The checker**: the strict path succeeds and its document satisfies `HypBytes`. -/
def checkBytes (limits : Limits) (bytes : ByteArray) : Bool :=
  match strictOpen limits bytes with
  | .ok d => decide (HypBytes limits bytes d)
  | .error _ => false

/-- `HypBytes` implies 12.7's `Hyp`. -/
theorem HypBytes.toHyp {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : HypBytes limits bytes d) : Hyp limits bytes d := by
  obtain ⟨hn, h⟩ := h
  unfold Hyp
  rw [hits_eq_headers hn]
  exact h

/-- **C4 over bytes.** If the strict path opens `bytes` as `d` and `HypBytes` holds, the
repair path succeeds with the same bytes, section and `/Root`, flagged `repaired`, and the
same `getObject` on every `(num, gen)` (12.7's `c4`). -/
theorem c4_bytes {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : HypBytes limits bytes d) :
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      d'.xref.entries = d.xref.entries ∧ d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen :=
  c4 hs hh.toHyp

/-- **C4 over bytes, from the checker.** -/
theorem c4_bytes_check {limits : Limits} {bytes : ByteArray} (hc : checkBytes limits bytes = true) :
    ∃ d d', strictOpen limits bytes = .ok d ∧ repairOpen limits bytes = .ok d' ∧
      d'.repaired = true ∧ d'.bytes = d.bytes ∧ d'.xref.entries = d.xref.entries ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  unfold checkBytes at hc
  split at hc
  · rename_i d hs
    obtain ⟨d', h⟩ := c4_bytes hs (of_decide_eq_true hc)
    exact ⟨d, d', hs, h⟩
  · cases hc

/-- **The byte-level C4 hypothesis with free entries**: `NoNested`, and 12.7a's `HypFree`
with the scan's hits replaced by the header occurrences. -/
def HypFreeBytes (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  NoNested limits bytes ∧
  (0, XrefEntry.free 0 65535) ∈ d.xref.entries ∧
  (∀ x ∈ d.xref.entries, EntryOkFree (headers bytes) x) ∧
  (∀ x ∈ headers bytes, ∃ e ∈ d.xref.entries, e.1 = x.1 ∧ isInUse e.2 = true) ∧
  (newestHits (headers bytes)).length ≤ limits.maxObjects ∧
  trailerOk limits bytes d = true ∧
  d.crypt.isNone = true

/-- `HypFreeBytes` is decidable. -/
instance instDecidableHypFreeBytes (limits : Limits) (bytes : ByteArray) (d : OpenDoc) :
    Decidable (HypFreeBytes limits bytes d) := by
  unfold HypFreeBytes; infer_instance

/-- **The checker**: the strict path succeeds and its document satisfies `HypFreeBytes`. -/
def checkFreeBytes (limits : Limits) (bytes : ByteArray) : Bool :=
  match strictOpen limits bytes with
  | .ok d => decide (HypFreeBytes limits bytes d)
  | .error _ => false

/-- `HypFreeBytes` implies 12.7a's `HypFree`. -/
theorem HypFreeBytes.toHypFree {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : HypFreeBytes limits bytes d) : HypFree limits bytes d := by
  obtain ⟨hn, h⟩ := h
  unfold HypFree
  rw [hits_eq_headers hn]
  exact h

/-- `HypBytes` is stronger than `HypFreeBytes`. -/
theorem HypBytes.toFree {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : HypBytes limits bytes d) : HypFreeBytes limits bytes d := by
  obtain ⟨hn, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hn, h1, fun x hx => ?_, h3, h4, h5, h6⟩
  have := h2 x hx
  obtain ⟨n, e⟩ := x
  cases e with
  | free a g => trivial
  | compressed _ _ => exact this.elim
  | inUse off g => exact this

/-- **C4 with free entries, over bytes.** Under `HypFreeBytes` the repair path succeeds with
the same bytes, in-use entries and `/Root`, and `getObject` agrees (`Agree`) on every
`(num, gen)` (12.7a's `c4_free`). -/
theorem c4_free_bytes {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : HypFreeBytes limits bytes d) :
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, Agree (d'.getObject limits num gen) (d.getObject limits num gen) :=
  c4_free hs hh.toHypFree

/-- **C4 with free entries over bytes, from the checker.** -/
theorem c4_free_bytes_check {limits : Limits} {bytes : ByteArray}
    (hc : checkFreeBytes limits bytes = true) :
    ∃ d d', strictOpen limits bytes = .ok d ∧ repairOpen limits bytes = .ok d' ∧
      d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, Agree (d'.getObject limits num gen) (d.getObject limits num gen) := by
  unfold checkFreeBytes at hc
  split at hc
  · rename_i d hs
    obtain ⟨d', h⟩ := c4_free_bytes hs (of_decide_eq_true hc)
    exact ⟨d, d', hs, h⟩
  · cases hc

/-! ## Fixtures -/

/-- A one-object file whose stream data (8 bytes) is `2 0 obj\n`: a header occurrence inside
an object that parses, so the scan jumps over it. -/
def nestedBytes : ByteArray :=
  "%PDF-1.7\n1 0 obj\n<< /Length 8 >>\nstream\n2 0 obj\nendstream\nendobj\n".toUTF8

-- 12.7's and 12.7a's fixtures: no nesting, so the hits are the occurrences.
#guard decide (NoNested Limits.default repairDiffBytes)
#guard decide (NoNested Limits.default repairFixedBytes)
#guard decide (NoNested Limits.default freeEntryBytes)
#guard hits Limits.default repairDiffBytes = headers repairDiffBytes
#guard hits Limits.default repairFixedBytes = headers repairFixedBytes
#guard hits Limits.default freeEntryBytes = headers freeEntryBytes
#guard headers repairFixedBytes = [(3, 0, 115), (2, 0, 58), (1, 0, 9)]

-- The byte-level checkers agree with 12.7's and 12.7a's on the fixtures (non-vacuity).
#guard checkBytes Limits.default repairDiffBytes = false
#guard checkFreeBytes Limits.default repairDiffBytes = false
#guard checkBytes Limits.default repairFixedBytes = true
#guard checkFreeBytes Limits.default repairFixedBytes = true
#guard checkBytes Limits.default freeEntryBytes = false
#guard checkFreeBytes Limits.default freeEntryBytes = true

-- `NoNested` is needed: the occurrence inside the stream data is not a hit.
#guard headers nestedBytes = [(2, 0, 40), (1, 0, 9)]
#guard hits Limits.default nestedBytes = [(1, 0, 9)]
#guard decide (NoNested Limits.default nestedBytes) = false

end SafePdf.Spec.RepairAgreeBytes
