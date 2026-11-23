import SafePdf.Spec.XrefTerm

/-!
# Unambiguous object resolution across incremental updates (S6)

Plan.md §4 S6 ("each (file, object id) resolves to at most one object, even across
incremental updates; parse is deterministic … version-stable"), §6 Phase 2 ("one winner per
object id across revisions, newest-revision-wins, deterministic"); ISO 32000-2 §7.5.6
(incremental updates) and §7.5.8.4 (hybrid-reference files).

Task 2.5. `resolveEntry limits bytes n` is the cross-reference entry of object `n`: the
lookup of `n` in `Core.Xref.Chain.mergeChain` of `Core.Xref.Chain.loadChain`. It is a total
function, hence deterministic; the theorems say *which* entry it returns.

* **Newest revision wins** (`resolveEntry_eq_some_iff`, `resolveEntry_eq_none_iff`): the
  result is `e` iff the chain loads, some revision `i` lists `n ↦ e`, and no newer revision
  `j < i` lists `n` at all.
* **One winner per object id** (`mergeChain_keys_nodup`, `mergeChain_mem_unique`,
  `lookupEntry_mergeChain_iff`): the merged section has at most one entry per object number,
  and lookup returns exactly that entry.
* **Hybrid precedence** (`resolveEntry_hybrid_table`, `resolveEntry_hybrid_stream`): in a
  chain `[table, its /XRefStm stream, older …]` the table's entry wins over the stream's, and
  the stream supplies what the table lacks (§7.5.8.4).
* **Revision monotonicity** (`loadChain_update`, `resolveEntry_update`): appending an
  incremental update whose (non-hybrid) section parses and whose `/Prev` is the old
  `startxref` offset yields the old chain with the new section in front, provided the old
  sections parse identically in the new bytes (`SameAt`); then object `n` resolves to the
  update's entry if it has one, else to the old resolution. `resolveEntry_of_cons` is the
  underlying statement about chains.
* **Object numbers vs `/Size`.** `loadChain` checks xref-stream object numbers against their
  own `/Size` (task 2.4a, XS4) but not classic-table numbers (2.1). `checkSize` is the
  separate check that every merged object number is below the newest trailer's `/Size`
  (§7.5.5: `/Size` of an update covers the whole file); `checkSize_ok` and
  `resolveEntry_lt_size` state what it guarantees. It is composed into the open path by 2.11.

## Not proved here

`SameAt` (the old section offsets parse the same way in the extended file) is a hypothesis of
`loadChain_update`. Discharging it needs a prefix-stability lemma for `parseSection`
(`parseXrefTable`, `ObjParse.parseObject`, `Stream.parseXrefStream`), all of which read
`bytes.size` for their range checks; that lemma is not proved.
-/

namespace SafePdf.Spec.Unambiguous

open SafePdf SafePdf.Core.Xref SafePdf.Core.Xref.Chain SafePdf.Spec.XrefTerm

/-! ## The resolution function -/

/-- **Resolution.** The cross-reference entry of object number `n`: the entry of the newest
revision of the `/Prev` chain that lists `n` (`none` if no revision does), or the error of
loading the chain. -/
def resolveEntry (limits : Limits) (bytes : ByteArray) (n : Nat) :
    Except Error (Option XrefEntry) :=
  match loadChain limits bytes with
  | .ok revs => .ok (lookupEntry n (mergeChain revs).entries)
  | .error e => .error e

/-- `resolveEntry` on a chain that loads. -/
theorem resolveEntry_of_ok {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) (n : Nat) :
    resolveEntry limits bytes n = .ok (revs.findSome? (fun r => lookupEntry n r.1.entries)) := by
  unfold resolveEntry
  rw [h]
  exact congrArg Except.ok (mergeChain_lookup n revs)

/-- `resolveEntry` fails exactly when the chain fails to load, with the same error. -/
theorem resolveEntry_eq_error_iff {limits : Limits} {bytes : ByteArray} {n : Nat}
    {e : Error} : resolveEntry limits bytes n = .error e ↔ loadChain limits bytes = .error e := by
  unfold resolveEntry
  cases loadChain limits bytes <;> simp

/-! ## Lookup in a list with distinct keys -/

/-- Lookup finds nothing iff the key is absent. -/
theorem lookupEntry_eq_none_iff {n : Nat} {l : List (Nat × XrefEntry)} :
    lookupEntry n l = none ↔ n ∉ l.map Prod.fst := by
  induction l with
  | nil => simp [lookupEntry]
  | cons x rest ih =>
    obtain ⟨k, e⟩ := x
    by_cases hk : k = n
    · subst hk
      rw [lookupEntry_cons_self]
      simp
    · rw [lookupEntry_cons_ne hk, ih]
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h => ⟨fun h' => hk h'.symm, h⟩, fun h => h.2⟩

/-- In a list with distinct keys, lookup returns `e` iff `(n, e)` is in the list. -/
theorem lookupEntry_eq_some_iff {n : Nat} {e : XrefEntry} {l : List (Nat × XrefEntry)}
    (hnd : (l.map Prod.fst).Nodup) : lookupEntry n l = some e ↔ (n, e) ∈ l := by
  induction l with
  | nil => simp [lookupEntry]
  | cons x rest ih =>
    obtain ⟨k, e'⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hk : k = n
    · subst hk
      rw [lookupEntry_cons_self]
      constructor
      · intro h
        cases h
        exact List.mem_cons_self
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h; rfl
        · exact absurd (List.mem_map_of_mem (f := Prod.fst) h) hnd.1
    · rw [lookupEntry_cons_ne hk, ih hnd.2]
      constructor
      · exact List.mem_cons_of_mem _
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h; exact absurd rfl hk
        · exact h

/-! ## One winner per object id -/

/-- **S6, one entry per object number.** The merged section has distinct object numbers. -/
theorem mergeChain_keys_nodup (revs : List Revision) :
    ((mergeChain revs).entries.map Prod.fst).Nodup :=
  (mergeChain revs).keys_nodup

/-- **S6, uniqueness.** Any two entries for object `n` in the merged section are equal. -/
theorem mergeChain_mem_unique {revs : List Revision} {n : Nat} {e₁ e₂ : XrefEntry}
    (h₁ : (n, e₁) ∈ (mergeChain revs).entries) (h₂ : (n, e₂) ∈ (mergeChain revs).entries) :
    e₁ = e₂ := by
  have hnd := mergeChain_keys_nodup revs
  have a := (lookupEntry_eq_some_iff hnd).mpr h₁
  have b := (lookupEntry_eq_some_iff hnd).mpr h₂
  rw [a] at b
  exact Option.some.inj b

/-- **S6, lookup returns the unique entry.** Lookup in the merged section returns `e` iff
`(n, e)` is (the only entry for `n`) in it. -/
theorem lookupEntry_mergeChain_iff {revs : List Revision} {n : Nat} {e : XrefEntry} :
    lookupEntry n (mergeChain revs).entries = some e ↔ (n, e) ∈ (mergeChain revs).entries :=
  lookupEntry_eq_some_iff (mergeChain_keys_nodup revs)

/-- Within one revision, too, an object number has at most one entry. -/
theorem section_mem_unique {sec : XrefSection} {n : Nat} {e₁ e₂ : XrefEntry}
    (h₁ : (n, e₁) ∈ sec.entries) (h₂ : (n, e₂) ∈ sec.entries) : e₁ = e₂ := by
  have a := (lookupEntry_eq_some_iff sec.keys_nodup).mpr h₁
  have b := (lookupEntry_eq_some_iff sec.keys_nodup).mpr h₂
  rw [a] at b
  exact Option.some.inj b

/-! ## Newest revision wins -/

/-- `findSome?` by index: the result is `b` iff some position `i` yields `b` and every
earlier position yields nothing. -/
theorem findSome?_eq_some_iff_index {α β : Type} {f : α → Option β} {l : List α} {b : β} :
    l.findSome? f = some b ↔
      ∃ i, ∃ h : i < l.length, f l[i] = some b ∧
        ∀ j, ∀ hj : j < i, f (l[j]'(Nat.lt_trans hj h)) = none := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.findSome?_cons]
    cases hfa : f a with
    | some b' =>
      simp only [Option.some.injEq]
      constructor
      · intro hb
        subst hb
        exact ⟨0, by simp, by simpa using hfa, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      · rintro ⟨i, hi, hfi, hj⟩
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero] at hfi
          rw [hfa] at hfi
          exact Option.some.inj hfi
        | succ i =>
          have := hj 0 (Nat.succ_pos i)
          simp only [List.getElem_cons_zero] at this
          rw [hfa] at this
          cases this
    | none =>
      simp only
      rw [ih]
      constructor
      · rintro ⟨i, hi, hfi, hj⟩
        refine ⟨i + 1, by simp; omega, by simpa using hfi, fun j hji => ?_⟩
        cases j with
        | zero => simpa using hfa
        | succ j => simpa using hj j (by omega)
      · rintro ⟨i, hi, hfi, hj⟩
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero] at hfi
          rw [hfa] at hfi
          cases hfi
        | succ i =>
          refine ⟨i, by simp at hi; omega, by simpa using hfi, fun j hji => ?_⟩
          simpa using hj (j + 1) (by omega)

/-- **S6, newest revision wins.** Object `n` resolves to `e` iff the chain loads (revisions
newest first), some revision `i` lists `n ↦ e`, and no newer revision `j < i` lists `n`. -/
theorem resolveEntry_eq_some_iff {limits : Limits} {bytes : ByteArray} {n : Nat}
    {e : XrefEntry} :
    resolveEntry limits bytes n = .ok (some e) ↔
      ∃ revs, loadChain limits bytes = .ok revs ∧
        ∃ i, ∃ h : i < revs.length, (n, e) ∈ revs[i].1.entries ∧
          ∀ j, ∀ hj : j < i, n ∉ (revs[j]'(Nat.lt_trans hj h)).1.entries.map Prod.fst := by
  constructor
  · intro hr
    cases hl : loadChain limits bytes with
    | error err =>
      rw [resolveEntry_eq_error_iff.mpr hl] at hr
      cases hr
    | ok revs =>
      rw [resolveEntry_of_ok hl] at hr
      simp only [Except.ok.injEq] at hr
      obtain ⟨i, hi, hfi, hj⟩ := findSome?_eq_some_iff_index.mp hr
      exact ⟨revs, rfl, i, hi, (lookupEntry_eq_some_iff revs[i].1.keys_nodup).mp hfi,
        fun j hji => lookupEntry_eq_none_iff.mp (hj j hji)⟩
  · rintro ⟨revs, hl, i, hi, hmem, hj⟩
    rw [resolveEntry_of_ok hl]
    congr 1
    exact findSome?_eq_some_iff_index.mpr ⟨i, hi,
      (lookupEntry_eq_some_iff revs[i].1.keys_nodup).mpr hmem,
      fun j hji => lookupEntry_eq_none_iff.mpr (hj j hji)⟩

/-- Object `n` resolves to no entry iff the chain loads and no revision lists `n`. -/
theorem resolveEntry_eq_none_iff {limits : Limits} {bytes : ByteArray} {n : Nat} :
    resolveEntry limits bytes n = .ok none ↔
      ∃ revs, loadChain limits bytes = .ok revs ∧
        ∀ r ∈ revs, n ∉ r.1.entries.map Prod.fst := by
  constructor
  · intro hr
    cases hl : loadChain limits bytes with
    | error err =>
      rw [resolveEntry_eq_error_iff.mpr hl] at hr
      cases hr
    | ok revs =>
      rw [resolveEntry_of_ok hl] at hr
      simp only [Except.ok.injEq, List.findSome?_eq_none_iff] at hr
      exact ⟨revs, rfl, fun r hr' => lookupEntry_eq_none_iff.mp (hr r hr')⟩
  · rintro ⟨revs, hl, h⟩
    rw [resolveEntry_of_ok hl]
    simp only [Except.ok.injEq, List.findSome?_eq_none_iff]
    exact fun r hr => lookupEntry_eq_none_iff.mpr (h r hr)

/-- **Determinism of the winner.** If object `n` resolves to `e` and some revision lists
`n ↦ e'` with no newer revision listing `n`, then `e = e'`: the winner is unique. -/
theorem resolveEntry_winner_unique {limits : Limits} {bytes : ByteArray} {n : Nat}
    {e e' : XrefEntry} {revs : List Revision} (hr : resolveEntry limits bytes n = .ok (some e))
    (hl : loadChain limits bytes = .ok revs) (i : Nat) (hi : i < revs.length)
    (hmem : (n, e') ∈ revs[i].1.entries)
    (hj : ∀ j, ∀ hj : j < i, n ∉ (revs[j]'(Nat.lt_trans hj hi)).1.entries.map Prod.fst) :
    e = e' := by
  have h' := resolveEntry_eq_some_iff.mpr ⟨revs, hl, i, hi, hmem, hj⟩
  rw [hr] at h'
  simp only [Except.ok.injEq, Option.some.injEq] at h'
  exact h'

/-! ## Hybrid precedence (§7.5.8.4) -/

/-- **Hybrid precedence.** In a chain `[table, stream, older …]` (a hybrid table followed by
its `/XRefStm` stream, as `loadChain` produces it), the table's entry for `n` wins. -/
theorem resolveEntry_hybrid_table {limits : Limits} {bytes : ByteArray}
    {t s : Revision} {older : List Revision} {n : Nat} {e : XrefEntry}
    (hl : loadChain limits bytes = .ok (t :: s :: older)) (ht : (n, e) ∈ t.1.entries) :
    resolveEntry limits bytes n = .ok (some e) :=
  resolveEntry_eq_some_iff.mpr ⟨_, hl, 0, by simp, ht, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- **Hybrid fallback.** If the table does not list `n`, the `/XRefStm` stream's entry wins
over every older revision. -/
theorem resolveEntry_hybrid_stream {limits : Limits} {bytes : ByteArray}
    {t s : Revision} {older : List Revision} {n : Nat} {e : XrefEntry}
    (hl : loadChain limits bytes = .ok (t :: s :: older)) (ht : n ∉ t.1.entries.map Prod.fst)
    (hs : (n, e) ∈ s.1.entries) :
    resolveEntry limits bytes n = .ok (some e) := by
  refine resolveEntry_eq_some_iff.mpr ⟨_, hl, 1, by simp, by simpa using hs, fun j hj => ?_⟩
  have : j = 0 := by omega
  subst this
  simpa using ht

/-! ## Revision monotonicity -/

/-- **Resolution after an update, at the chain level.** If the new file's chain is the old
one with a revision `r'` in front, object `n` resolves to `r'`'s entry if it has one, else
to the old resolution. -/
theorem resolveEntry_of_cons {limits : Limits} {bytes bytes' : ByteArray} {r' : Revision}
    {revs : List Revision} (h' : loadChain limits bytes' = .ok (r' :: revs))
    (h : loadChain limits bytes = .ok revs) (n : Nat) :
    resolveEntry limits bytes' n =
      (resolveEntry limits bytes n).map (fun o => (lookupEntry n r'.1.entries).or o) := by
  rw [resolveEntry_of_ok h', resolveEntry_of_ok h, List.findSome?_cons]
  cases lookupEntry n r'.1.entries <;> rfl

/-- The section at `o` reads the same in `bytes'` as in `bytes`: the section parse, the
`xref` keyword test (table or stream) and the xref-stream parse all agree. -/
def SameAt (limits : Limits) (bytes bytes' : ByteArray) (o : Nat) : Prop :=
  parseSection limits bytes' o = parseSection limits bytes o ∧
    matchAt bytes' o kwXref = matchAt bytes o kwXref ∧
    Stream.parseXrefStream limits bytes' o = Stream.parseXrefStream limits bytes o

/-- The shape of a successful step: the section at `off` parses, and either it is not
hybrid and is the only revision, or its `/XRefStm` stream parses too and follows it. -/
theorem step_ok_shape {limits : Limits} {bytes : ByteArray} {off : Nat} {visited : List Nat}
    {hnd : visited.Nodup} {so : StepOk bytes visited} {k : Nat}
    (h : step limits bytes off visited hnd = (.ok so, k)) :
    ∃ sec tr, parseSection limits bytes off = .ok (sec, tr) ∧ so.prev? = tr.prev? ∧
      ((hybridStm bytes off tr = none ∧ so.revs = [(sec, tr, off)]) ∨
        (∃ s sec2 tr2, hybridStm bytes off tr = some s ∧
          Stream.parseXrefStream limits bytes s = .ok (sec2, tr2) ∧
          so.revs = [(sec, tr, off), (sec2, tr2, s)])) := by
  unfold step at h
  split at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i sec tr hp
          split at h
          · rename_i hh
            simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨sec, tr, hp, rfl, Or.inl ⟨hh, rfl⟩⟩
          · rename_i s hh
            split at h
            · split at h
              · simp at h
              · split at h
                · simp at h
                · split at h
                  · simp at h
                  · rename_i sec2 tr2 hp2
                    simp only [Prod.mk.injEq, Except.ok.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact ⟨sec, tr, hp, rfl, Or.inr ⟨s, sec2, tr2, hh, hp2, rfl⟩⟩
            · simp at h
  · simp at h

/-- A step succeeds on a non-hybrid section that parses at a fresh in-range offset within
the revision budget. -/
theorem step_of_plain {limits : Limits} {bytes : ByteArray} {off : Nat} {visited : List Nat}
    (hnd : visited.Nodup) {sec : XrefSection} {tr : Trailer} (hoff : off < bytes.size)
    (hmem : off ∉ visited) (hbud : visited.length < limits.maxRevisions)
    (hp : parseSection limits bytes off = .ok (sec, tr)) (hh : hybridStm bytes off tr = none) :
    ∃ so k, step limits bytes off visited hnd = (.ok so, k) ∧ so.revs = [(sec, tr, off)] ∧
      so.prev? = tr.prev? := by
  unfold step
  rw [dite_eq_left_of_eq_true (eq_true hoff), dite_eq_right_of_eq_false (eq_false hmem),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  split
  · rename_i e he
    rw [hp] at he
    cases he
  · rename_i sec' tr' he
    rw [hp] at he
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    split
    · exact ⟨_, _, rfl, rfl, rfl⟩
    · rename_i s hs
      rw [hh] at hs
      cases hs

/-- A step succeeds on a hybrid section when the section and its `/XRefStm` stream parse at
fresh, distinct, in-range offsets within the revision budget. -/
theorem step_of_hybrid {limits : Limits} {bytes : ByteArray} {off s : Nat}
    {visited : List Nat} (hnd : visited.Nodup) {sec sec2 : XrefSection} {tr tr2 : Trailer}
    (hoff : off < bytes.size) (hmem : off ∉ visited) (hs : s < bytes.size) (hso : s ≠ off)
    (hsm : s ∉ visited) (hbud : visited.length + 2 ≤ limits.maxRevisions)
    (hp : parseSection limits bytes off = .ok (sec, tr)) (hh : hybridStm bytes off tr = some s)
    (hp2 : Stream.parseXrefStream limits bytes s = .ok (sec2, tr2)) :
    ∃ so k, step limits bytes off visited hnd = (.ok so, k) ∧
      so.revs = [(sec, tr, off), (sec2, tr2, s)] ∧ so.prev? = tr.prev? := by
  unfold step
  rw [dite_eq_left_of_eq_true (eq_true hoff), dite_eq_right_of_eq_false (eq_false hmem),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  split
  · rename_i e he
    rw [hp] at he
    cases he
  · rename_i sec' tr' he
    rw [hp] at he
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    split
    · rename_i hs'
      rw [hh] at hs'
      cases hs'
    · rename_i s' hs'
      rw [hh] at hs'
      cases hs'
      rw [dite_eq_left_of_eq_true (eq_true hs), dite_eq_right_of_eq_false (eq_false (by
        rintro (h | h)
        · exact hso h
        · exact hsm h)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      split
      · rename_i e he
        rw [hp2] at he
        cases he
      · rename_i sec2' tr2' he
        rw [hp2] at he
        simp only [Except.ok.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨_, _, rfl, rfl, rfl⟩

/-- **Frame lemma for one step.** A successful step in `bytes` is reproduced in `bytes'`
(at least as long) from a visited list `visited'` that avoids its offsets and leaves room in
the revision budget, provided its sections read the same in `bytes'`. -/
theorem step_frame {limits : Limits} {bytes bytes' : ByteArray} (hsz : bytes.size ≤ bytes'.size)
    {off : Nat} {visited : List Nat} {hnd : visited.Nodup} {so : StepOk bytes visited} {k : Nat}
    (h : step limits bytes off visited hnd = (.ok so, k))
    {visited' : List Nat} (hnd' : visited'.Nodup)
    (hfresh : ∀ o ∈ so.revs.map Revision.offset, o ∉ visited')
    (hbud : so.revs.length + visited'.length ≤ limits.maxRevisions)
    (hsame : ∀ o ∈ so.revs.map Revision.offset, SameAt limits bytes bytes' o) :
    ∃ so' k', step limits bytes' off visited' hnd' = (.ok so', k') ∧ so'.revs = so.revs ∧
      so'.prev? = so.prev? := by
  obtain ⟨sec, tr, hp, hprev, hcase⟩ := step_ok_shape h
  have hlt := so.lt
  have hndo := (List.nodup_append.mp so.nodup).1
  rcases hcase with ⟨hh, hrevs⟩ | ⟨s, sec2, tr2, hh, hp2, hrevs⟩
  · rw [hrevs] at hfresh hbud hsame hlt
    simp only [List.map_cons, List.map_nil, Revision.offset, List.mem_singleton,
      forall_eq] at hfresh hsame hlt
    obtain ⟨hs1, hs2, -⟩ := hsame
    have hh' : hybridStm bytes' off tr = none := by
      unfold hybridStm at hh ⊢
      rw [hs2]; exact hh
    obtain ⟨so', k', hst, hr', hp'⟩ := step_of_plain hnd' (Nat.lt_of_lt_of_le hlt hsz) hfresh
      (by simp at hbud; omega) (hs1.trans hp) hh'
    exact ⟨so', k', hst, hr'.trans hrevs.symm, hp'.trans hprev.symm⟩
  · rw [hrevs] at hfresh hbud hsame hlt hndo
    simp only [List.map_cons, List.map_nil, Revision.offset, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq] at hfresh hsame hlt
    simp only [List.map_cons, List.map_nil, Revision.offset, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false] at hndo
    obtain ⟨⟨hs1, hs2, -⟩, ⟨-, -, hs3⟩⟩ := hsame
    have hh' : hybridStm bytes' off tr = some s := by
      unfold hybridStm at hh ⊢
      rw [hs2]; exact hh
    obtain ⟨so', k', hst, hr', hp'⟩ := step_of_hybrid hnd' (Nat.lt_of_lt_of_le hlt.1 hsz)
      hfresh.1 (Nat.lt_of_lt_of_le hlt.2 hsz) (fun he => hndo.1 he.symm) hfresh.2
      (by simp at hbud; omega) (hs1.trans hp) hh' (hs3.trans hp2)
    exact ⟨so', k', hst, hr'.trans hrevs.symm, hp'.trans hprev.symm⟩

/-- **Frame lemma for the walk.** A successful walk in `bytes` from `off` is reproduced in
`bytes'` (at least as long) from any visited list `visited'` that avoids its offsets and leaves
room in the revision budget, provided its sections read the same in `bytes'` (`SameAt`). -/
theorem walk_frame {limits : Limits} {bytes bytes' : ByteArray} (hsz : bytes.size ≤ bytes'.size)
    (off : Nat) (visited : List Nat) (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size)
    {revs : List Revision} (h : (walk limits bytes off visited hnd hlt).1 = .ok revs)
    (visited' : List Nat) (hnd' : visited'.Nodup) (hlt' : ∀ x ∈ visited', x < bytes'.size)
    (hfresh : ∀ o ∈ revs.map Revision.offset, o ∉ visited')
    (hbud : revs.length + visited'.length ≤ limits.maxRevisions)
    (hsame : ∀ o ∈ revs.map Revision.offset, SameAt limits bytes bytes' o) :
    (walk limits bytes' off visited' hnd' hlt').1 = .ok revs := by
  revert revs visited' hnd' hlt'
  fun_induction walk limits bytes off visited hnd hlt with
  | case1 => simp
  | case3 => simp
  | case2 off visited hnd hlt so k hs hp =>
    intro revs h visited' hnd' hlt' hfresh hbud hsame
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨so', k', hst, hr', hp'⟩ := step_frame hsz hs hnd' hfresh hbud hsame
    rw [walk, hst]
    simp only
    rw [hp', hp]
    simp only [hr']
  | case4 off visited hnd hlt so k hs p hp rest k' hw ih =>
    intro revs h visited' hnd' hlt' hfresh hbud hsame
    simp only [Except.ok.injEq] at h
    subst h
    have hwo := walk_ok limits bytes p _ so.nodup _ (by rw [hw])
    simp only [List.map_append, List.mem_append, List.length_append] at hfresh hbud hsame
    obtain ⟨so', k'', hst, hr', hp'⟩ := step_frame hsz hs hnd' (fun o ho => hfresh o (Or.inl ho))
      (by omega) (fun o ho => hsame o (Or.inl ho))
    rw [walk, hst]
    simp only
    rw [hp', hp]
    simp only
    have hih := ih (revs := rest) (by rw [hw]) (so'.revs.map Revision.offset ++ visited')
      so'.nodup (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact so'.lt x hx
        · exact hlt' x hx)
      (fun o ho hmem => by
        rw [hr'] at hmem
        rcases List.mem_append.mp hmem with hm | hm
        · exact (hwo.2.1 o ho).2 (List.mem_append_left _ hm)
        · exact hfresh o (Or.inr ho) hm)
      (by rw [hr']; simp only [List.length_append, List.length_map]; omega)
      (fun o ho => hsame o (Or.inr ho))
    split
    · rename_i e k3 he
      rw [he] at hih
      cases hih
    · rename_i rest' k3 he
      rw [he] at hih
      simp only [Except.ok.injEq] at hih
      rw [hih, hr']

/-- **Revision monotonicity** (ISO 32000-2 §7.5.6). Let `bytes` load as the chain `revs`
from its `startxref` offset `start`, and let `bytes'` be an incremental update of it: its
`startxref` offset `off'` lies at or after the end of `bytes`, the section there parses as
`(sec', tr')`, is not hybrid, and has `/Prev start`; the old sections read the same in
`bytes'` (`SameAt`), and the revision budget has room for one more. Then `bytes'` loads as
the old chain with the new section in front. -/
theorem loadChain_update {limits : Limits} {bytes bytes' : ByteArray} {start off' : Nat}
    {revs : List Revision} {sec' : XrefSection} {tr' : Trailer}
    (hold : loadChain limits bytes = .ok revs) (hstart : findStartxref bytes = .ok start)
    (hnew : findStartxref bytes' = .ok off') (hoff : bytes.size ≤ off')
    (hsec : parseSection limits bytes' off' = .ok (sec', tr'))
    (hnohyb : hybridStm bytes' off' tr' = none) (hprev : tr'.prev? = some start)
    (hbud : revs.length + 1 ≤ limits.maxRevisions)
    (hsame : ∀ o ∈ revs.map Revision.offset, SameAt limits bytes bytes' o) :
    loadChain limits bytes' = .ok ((sec', tr', off') :: revs) := by
  have hlt' : off' < bytes'.size := findStartxref_lt hnew
  have hsz : bytes.size ≤ bytes'.size := by omega
  have hold' := hold
  rw [loadChain_eq hstart] at hold'
  rw [loadChain_eq hnew]
  obtain ⟨so, k, hst, hr, hp⟩ := step_of_plain (visited := []) List.nodup_nil hlt'
    List.not_mem_nil (by simp; omega) hsec hnohyb
  rw [walk, hst]
  simp only
  rw [hp, hprev]
  simp only
  have hih := walk_frame hsz start [] _ _ hold' (so.revs.map Revision.offset ++ [])
    so.nodup (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact so.lt x hx
      · cases hx)
    (fun o ho hmem => by
      rw [hr] at hmem
      simp only [List.map_cons, List.map_nil, Revision.offset, List.append_nil,
        List.mem_singleton] at hmem
      have := loadChain_offsets_lt hold o ho
      omega)
    (by rw [hr]; simp; omega) hsame
  split
  · rename_i e k3 he
    rw [he] at hih
    cases hih
  · rename_i rest' k3 he
    rw [he] at hih
    simp only [Except.ok.injEq] at hih
    rw [hih, hr]
    rfl

/-- **Resolution after an incremental update.** Under the hypotheses of `loadChain_update`,
object `n` resolves in `bytes'` to the update's entry if its section lists `n`, and
otherwise exactly as in `bytes`. -/
theorem resolveEntry_update {limits : Limits} {bytes bytes' : ByteArray} {start off' : Nat}
    {revs : List Revision} {sec' : XrefSection} {tr' : Trailer}
    (hold : loadChain limits bytes = .ok revs) (hstart : findStartxref bytes = .ok start)
    (hnew : findStartxref bytes' = .ok off') (hoff : bytes.size ≤ off')
    (hsec : parseSection limits bytes' off' = .ok (sec', tr'))
    (hnohyb : hybridStm bytes' off' tr' = none) (hprev : tr'.prev? = some start)
    (hbud : revs.length + 1 ≤ limits.maxRevisions)
    (hsame : ∀ o ∈ revs.map Revision.offset, SameAt limits bytes bytes' o) (n : Nat) :
    resolveEntry limits bytes' n =
      (resolveEntry limits bytes n).map (fun o => (lookupEntry n sec'.entries).or o) :=
  resolveEntry_of_cons
    (loadChain_update hold hstart hnew hoff hsec hnohyb hprev hbud hsame) hold n

/-! ## Object numbers below the newest `/Size` -/

/-- **`/Size` check** (ISO 32000-2 §7.5.5). Every object number of the merged chain must be
below the `/Size` of the newest trailer (which, per §7.5.6, counts the objects of the whole
file). `loadChain` checks this for xref streams against their own `/Size` but not for classic
tables; this check covers both and is meant to be composed after `loadChain`. An empty chain
passes. -/
def checkSize : List Revision → Except Error Unit
  | [] => .ok ()
  | r :: rest =>
    if (mergeChain (r :: rest)).entries.all (fun x => decide (x.1 < r.2.1.size)) then .ok ()
    else .error (.malformed r.2.2 "cross-reference object number not below the trailer /Size")

/-- `checkSize` on a non-empty chain. -/
theorem checkSize_cons (r : Revision) (rest : List Revision) :
    checkSize (r :: rest) =
      if (mergeChain (r :: rest)).entries.all (fun x => decide (x.1 < r.2.1.size)) then .ok ()
      else .error (.malformed r.2.2 "cross-reference object number not below the trailer /Size") :=
  rfl

/-- What `checkSize` guarantees: every merged object number is below the newest `/Size`. -/
theorem checkSize_ok {r : Revision} {rest : List Revision} (h : checkSize (r :: rest) = .ok ()) :
    ∀ x ∈ (mergeChain (r :: rest)).entries, x.1 < r.2.1.size := by
  rw [checkSize_cons] at h
  split at h
  · rename_i hall
    intro x hx
    have := List.all_eq_true.mp hall x hx
    simpa using this
  · cases h

/-- `checkSize` fails exactly when some merged object number reaches the newest `/Size`. -/
theorem checkSize_ok_iff {r : Revision} {rest : List Revision} :
    checkSize (r :: rest) = .ok () ↔ ∀ x ∈ (mergeChain (r :: rest)).entries, x.1 < r.2.1.size := by
  refine ⟨checkSize_ok, fun h => ?_⟩
  have hall : (mergeChain (r :: rest)).entries.all (fun x => decide (x.1 < r.2.1.size)) = true :=
    List.all_eq_true.mpr (fun x hx => by simpa using h x hx)
  rw [checkSize_cons]
  simp only [hall, ↓reduceIte]

/-- **Resolved objects lie below `/Size`.** If the chain loads with newest revision `r` and
passes `checkSize`, every object number that resolves to an entry is below `r`'s `/Size`. -/
theorem resolveEntry_lt_size {limits : Limits} {bytes : ByteArray} {r : Revision}
    {rest : List Revision} (hl : loadChain limits bytes = .ok (r :: rest))
    (hc : checkSize (r :: rest) = .ok ()) {n : Nat} {e : XrefEntry}
    (hr : resolveEntry limits bytes n = .ok (some e)) : n < r.2.1.size := by
  unfold resolveEntry at hr
  rw [hl] at hr
  simp only [Except.ok.injEq] at hr
  exact checkSize_ok hc (n, e) (lookupEntry_mergeChain_iff.mp hr)

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"

/-- Test helper: `resolveEntry` under the default limits, errors summarised. -/
private def rs (b : ByteArray) (n : Nat) : Sum String (Option XrefEntry) :=
  match resolveEntry Limits.default b n with
  | .ok o => .inr o
  | .error e => .inl (errS e)

/-- Test helper: the revision offsets of `loadChain` under the default limits. -/
private def offs (b : ByteArray) : Option (List Nat) :=
  match loadChain Limits.default b with
  | .ok revs => some (revs.map Revision.offset)
  | .error _ => none

/-- Test helper: `checkSize` of the chain, errors summarised. -/
private def cs (b : ByteArray) : Sum String Unit :=
  match loadChain Limits.default b with
  | .ok revs => match checkSize revs with
    | .ok () => .inr ()
    | .error e => .inl (errS e)
  | .error e => .inl (errS e)

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

/-- An xref stream object `n 0 obj` with dictionary extras and raw rows. -/
private def xstm (n : Nat) (extra : String) (rows : List UInt8) : ByteArray :=
  (s!"{n} 0 obj\n<< /Type /XRef {extra} /Length {rows.length} >>\nstream\n").toUTF8 ++
    ByteArray.mk rows.toArray ++ "\nendstream\nendobj\n".toUTF8

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

/-- An update of `minimal-valid.pdf` whose table lists object 6 while its trailer says
`/Size 6`: loads, but fails `checkSize`. -/
private def overSize : ByteArray :=
  minimalValid ++ ("xref\n6 1\n0000000015 00000 n \ntrailer\n" ++
    "<< /Size 6 /Root 1 0 R /Prev 404 >>\nstartxref\n587\n%%EOF\n").toUTF8

-- the embedded files are the ones of `Core.Xref.Chain`'s tests
#guard minimalValid.size == 587 && twoRevisions.size == 775 && hybStm.size == 105
-- one revision: object 3 at 121
#guard rs minimalValid 3 == .inr (some (.inUse 121 0))
-- two revisions: the newer one overrides object 3, the older one supplies the others
#guard rs twoRevisions 3 == .inr (some (.inUse 587 0))
#guard rs twoRevisions 4 == .inr (some (.inUse 247 0))
#guard rs twoRevisions 0 == .inr (some (.free 0 65535))
#guard rs twoRevisions 6 == .inr none
-- revision monotonicity: the update's chain is the old chain with the new section in front
#guard offs twoRevisions == some [658, 404] && offs minimalValid == some [404]
#guard (List.range 8).all (fun n =>
  rs twoRevisions n == (if n = 3 then .inr (some (.inUse 587 0)) else rs minimalValid n))
-- hybrid: the table wins over its /XRefStm stream, which supplies what the table lacks
#guard offs hybrid == some [692, 587, 404]
#guard rs hybrid 3 == .inr (some (.inUse 121 0))
#guard rs hybrid 7 == .inr (some (.compressed 4 0))
#guard rs hybrid 5 == .inr (some (.inUse 334 0))
#guard rs hybrid 8 == .inr none
-- a broken chain: resolution fails with the chain's error
#guard rs (hybridAt 692) 3 == .inl "malformed@692: xref /XRefStm cycle"
-- /Size: satisfied by the regular files, violated by an object 6 under /Size 6
#guard cs minimalValid == .inr () && cs twoRevisions == .inr () && cs hybrid == .inr ()
#guard offs overSize == some [587, 404]
#guard rs overSize 6 == .inr (some (.inUse 15 0))
#guard cs overSize == .inl "malformed@587: cross-reference object number not below the trailer /Size"

end Tests

end SafePdf.Spec.Unambiguous
