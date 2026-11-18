import SafePdf.Core.Xref.Chain

/-!
# Termination and cycle rejection of `/Prev` chain resolution

Plan.md §5.2 (first bullet), §4 S2/S3/S6, §6 Phase 2 (exit M2); ISO 32000-2 §7.5.5–7.5.6;
Bogk & Schöpl 2014.

Theorems about `Core.Xref.Chain` (task 2.2):

* **S2 totality.** `loadChain` is a total function, accepted by Lean with the measure
  `bytes.size - visited.length` (unvisited offsets, bounded by the file length); no `partial`,
  no fuel. `loadChain_terminates` records this.
* **Structure of a success.** The revision offsets are pairwise distinct
  (`loadChain_offsets_nodup`) and inside the input (`loadChain_offsets_lt`); there are at most
  `bytes.size` and at most `maxRevisions` of them (`loadChain_length_le`); and the `/Prev`
  path from the `startxref` offset ends in a table without `/Prev` (`loadChain_ok_reach`).
* **Cycle rejection.** `PrevStep limits bytes o o'` says "the table at `o` parses and its
  trailer's `/Prev` is `o'`". If a `PrevStep` path from the `startxref` offset reaches an
  offset that lies on a `PrevStep` cycle, `loadChain` returns an error
  (`loadChain_cycle_rejected`). This covers cycles of every length, including the 1-cycle
  (`/Prev` = own offset) and the 2-cycle of `Tests/adversarial/xref-prev-{self,cycle}.pdf`,
  whose concrete `"xref /Prev cycle"` errors are checked by `#guard` in `Core.Xref.Chain`.
* **S3 work bound.** `loadChainCounted` returns the number of `parseXrefTable` calls next to
  the result; it is at most `bytes.size` and at most `maxRevisions`
  (`loadChainCounted_calls_le`), and equals the number of revisions on success.
* **S6 preview.** `mergeChain` keeps, per object number, the entry of the newest revision
  that has one (`mergeChain_lookup`).
-/

namespace SafePdf.Spec.XrefTerm

open SafePdf SafePdf.Core.Xref SafePdf.Core.Xref.Chain

/-! ## The `/Prev` relation -/

/-- One `/Prev` step: the classic table at `o` parses and its trailer's `/Prev` is `o'`. -/
def PrevStep (limits : Limits) (bytes : ByteArray) (o o' : Nat) : Prop :=
  ∃ sec tr r, parseXrefTable limits bytes o = .ok (sec, tr, r) ∧ tr.prev? = some o'

/-- The table at `o` parses and its trailer has no `/Prev`: the oldest revision. -/
def Terminal (limits : Limits) (bytes : ByteArray) (o : Nat) : Prop :=
  ∃ sec tr r, parseXrefTable limits bytes o = .ok (sec, tr, r) ∧ tr.prev? = none

/-- Reflexive-transitive closure of `PrevStep`: a `/Prev` path from `o` to `t`. -/
inductive PrevReach (limits : Limits) (bytes : ByteArray) : Nat → Nat → Prop
  /-- The empty path. -/
  | refl (o : Nat) : PrevReach limits bytes o o
  /-- One step, then a path. -/
  | step {o o' t : Nat} : PrevStep limits bytes o o' → PrevReach limits bytes o' t →
      PrevReach limits bytes o t

/-- `PrevStep` is deterministic: a table has at most one `/Prev`. -/
theorem PrevStep.det {limits : Limits} {bytes : ByteArray} {o a b : Nat}
    (ha : PrevStep limits bytes o a) (hb : PrevStep limits bytes o b) : a = b := by
  obtain ⟨s1, t1, r1, h1, p1⟩ := ha
  obtain ⟨s2, t2, r2, h2, p2⟩ := hb
  rw [h1] at h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨-, rfl, -⟩ := h2
  rw [p1] at p2
  exact Option.some.inj p2

/-- A terminal table has no `/Prev` step. -/
theorem Terminal.not_step {limits : Limits} {bytes : ByteArray} {o o' : Nat}
    (ht : Terminal limits bytes o) (hs : PrevStep limits bytes o o') : False := by
  obtain ⟨s1, t1, r1, h1, p1⟩ := ht
  obtain ⟨s2, t2, r2, h2, p2⟩ := hs
  rw [h1] at h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨-, rfl, -⟩ := h2
  rw [p1] at p2
  cases p2

/-- Append one step at the end of a path. -/
theorem PrevReach.tail {limits : Limits} {bytes : ByteArray} {o t t' : Nat}
    (h : PrevReach limits bytes o t) (hs : PrevStep limits bytes t t') :
    PrevReach limits bytes o t' := by
  induction h with
  | refl o => exact .step hs (.refl t')
  | step h1 _ ih => exact .step h1 (ih hs)

/-- No terminal table is reachable from an offset `o` on a `/Prev` cycle
(`o → o1 →* o`): by determinism the path from `o` never leaves the cycle. -/
theorem not_terminal_of_cycle {limits : Limits} {bytes : ByteArray} {o t : Nat}
    (hr : PrevReach limits bytes o t) (ht : Terminal limits bytes t) :
    ∀ {o1 : Nat}, PrevStep limits bytes o o1 → PrevReach limits bytes o1 o → False := by
  induction hr with
  | refl o => exact fun hs _ => ht.not_step hs
  | @step o x t hox _ ih =>
    intro o1 hs hback
    have hx : x = o1 := hox.det hs
    subst hx
    -- `x →* o → x`, so `x` is on a cycle too; rotate it to start at `x`.
    cases hback with
    | refl => exact ih ht hox (.refl _)
    | step hxy hyo => exact ih ht hxy (hyo.tail hox)

/-! ## The loop -/

/-- Work bound of the loop: the number of `parseXrefTable` calls is at most the number of
unvisited offsets, and at most the remaining revision budget. -/
theorem walk_calls_le (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size) :
    (walk limits bytes off visited hnd hlt).2 ≤ bytes.size - visited.length ∧
      (walk limits bytes off visited hnd hlt).2 ≤ maxRevisions - visited.length := by
  fun_induction walk limits bytes off visited hnd hlt with
  | case1 => simp
  | case2 => simp
  | case3 off visited hnd hlt hoff hmem hmax e hp =>
    have := length_lt_of_fresh hnd hlt hoff hmem
    simp; omega
  | case4 off visited hnd hlt hoff hmem hmax sec tr r hp hprev =>
    have := length_lt_of_fresh hnd hlt hoff hmem
    simp; omega
  | case5 off visited hnd hlt hoff hmem hmax sec tr r hp p hprev e k hw ih =>
    have := length_lt_of_fresh hnd hlt hoff hmem
    rw [hw] at ih
    simp at ih ⊢; omega
  | case6 off visited hnd hlt hoff hmem hmax sec tr r hp p hprev revs k hw ih =>
    have := length_lt_of_fresh hnd hlt hoff hmem
    rw [hw] at ih
    simp at ih ⊢; omega
  | case7 => simp

/-- What a successful run of the loop from `off` guarantees: the revision offsets are
distinct, inside the input and not previously visited; the revision budget is respected;
there is one parse per revision; and the `/Prev` path from `off` ends in a terminal table. -/
theorem walk_ok (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) (hlt : ∀ x ∈ visited, x < bytes.size) {revs : List Revision}
    (h : (walk limits bytes off visited hnd hlt).1 = .ok revs) :
    (revs.map Revision.offset).Nodup ∧
      (∀ o ∈ revs.map Revision.offset, o < bytes.size ∧ o ∉ visited) ∧
      revs.length + visited.length ≤ maxRevisions ∧
      (walk limits bytes off visited hnd hlt).2 = revs.length ∧
      ∃ t, PrevReach limits bytes off t ∧ Terminal limits bytes t := by
  revert revs
  fun_induction walk limits bytes off visited hnd hlt with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 off visited hnd hlt hoff hmem hmax sec tr r hp hprev =>
    intro revs h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨by simp, ?_, by simp; omega, rfl, off, .refl off, sec, tr, r, hp, hprev⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton, Revision.offset]
    intro o ho
    subst ho
    exact ⟨hoff, hmem⟩
  | case5 off visited hnd hlt hoff hmem hmax sec tr r hp p hprev e k hw ih => simp
  | case6 off visited hnd hlt hoff hmem hmax sec tr r hp p hprev revs' k hw ih =>
    intro revs h
    simp only [Except.ok.injEq] at h
    subst h
    rw [hw] at ih
    obtain ⟨hnd', hmem', hlen, hk, t, hreach, hterm⟩ := ih rfl
    refine ⟨?_, ?_, ?_, ?_, t, .step ⟨sec, tr, r, hp, hprev⟩ hreach, hterm⟩
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hin => ?_, hnd'⟩
      exact (hmem' _ hin).2 List.mem_cons_self
    · simp only [List.map_cons, List.mem_cons]
      intro o ho
      rcases ho with rfl | ho
      · exact ⟨hoff, hmem⟩
      · have := hmem' o ho
        exact ⟨this.1, fun hv => this.2 (List.mem_cons_of_mem _ hv)⟩
    · simp at hlen ⊢; omega
    · simp only at hk
      simp [hk]
  | case7 => simp

/-! ## Headline theorems -/

/-- **S2 (totality).** `loadChain` returns on every input. The content of this theorem is
that the definition is accepted without `partial` or fuel: Lean checked the measure
`bytes.size - visited.length` (Plan.md §5.2). -/
theorem loadChain_terminates : ∀ (limits : Limits) (bytes : ByteArray),
    ∃ r, loadChain limits bytes = r :=
  fun _ _ => ⟨_, rfl⟩

/-- `loadChain` from a known `startxref` offset. -/
theorem loadChain_eq {limits : Limits} {bytes : ByteArray} {start : Nat}
    (hs : findStartxref bytes = .ok start) :
    loadChain limits bytes =
      (walk limits bytes start [] List.nodup_nil (fun _ hx => absurd hx List.not_mem_nil)).1 := by
  unfold loadChain loadChainCounted
  rw [hs]

/-- What a successful `loadChain` guarantees (all parts below in one statement). -/
theorem loadChain_ok {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) :
    ∃ start, findStartxref bytes = .ok start ∧
      (revs.map Revision.offset).Nodup ∧
      (∀ o ∈ revs.map Revision.offset, o < bytes.size) ∧
      revs.length ≤ maxRevisions ∧
      (loadChainCounted limits bytes).2 = revs.length ∧
      ∃ t, PrevReach limits bytes start t ∧ Terminal limits bytes t := by
  unfold loadChain loadChainCounted at h
  split at h
  · simp at h
  · rename_i start hs
    have := walk_ok limits bytes start [] List.nodup_nil
      (fun _ hx => absurd hx List.not_mem_nil) h
    obtain ⟨h1, h2, h3, h4, h5⟩ := this
    refine ⟨start, hs, h1, fun o ho => (h2 o ho).1, by simpa using h3, ?_, h5⟩
    unfold loadChainCounted
    rw [hs]
    exact h4

/-- **(b)** On success the revision offsets are pairwise distinct. -/
theorem loadChain_offsets_nodup {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) : (revs.map Revision.offset).Nodup := by
  obtain ⟨_, _, h1, _⟩ := loadChain_ok h
  exact h1

/-- On success every revision offset lies inside the input. -/
theorem loadChain_offsets_lt {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) :
    ∀ o ∈ revs.map Revision.offset, o < bytes.size := by
  obtain ⟨_, _, _, h2, _⟩ := loadChain_ok h
  exact h2

/-- **(c)** On success there are at most `bytes.size` revisions (distinct offsets inside the
input) and at most `maxRevisions`. -/
theorem loadChain_length_le {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) :
    revs.length ≤ bytes.size ∧ revs.length ≤ maxRevisions := by
  obtain ⟨_, _, h1, h2, h3, _⟩ := loadChain_ok h
  have := length_le_of_nodup_of_lt h1 h2
  simp only [List.length_map] at this
  exact ⟨this, h3⟩

/-- On success the `/Prev` path from the `startxref` offset ends in a table without `/Prev`. -/
theorem loadChain_ok_reach {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) :
    ∃ start, findStartxref bytes = .ok start ∧
      ∃ t, PrevReach limits bytes start t ∧ Terminal limits bytes t := by
  obtain ⟨start, hs, _, _, _, _, h5⟩ := loadChain_ok h
  exact ⟨start, hs, h5⟩

/-- **(d) Cycle rejection** (Bogk & Schöpl 2014). If the `/Prev` path from the `startxref`
offset reaches an offset `o` that lies on a `/Prev` cycle (`o → o1 →* o`, every table on it
parsing), then `loadChain` fails. Cycles of every length are covered, the 1-cycle
(`o1 = o`) included. -/
theorem loadChain_cycle_rejected {limits : Limits} {bytes : ByteArray} {start o o1 : Nat}
    (hs : findStartxref bytes = .ok start) (hr : PrevReach limits bytes start o)
    (hstep : PrevStep limits bytes o o1) (hback : PrevReach limits bytes o1 o) :
    ∃ e, loadChain limits bytes = .error e := by
  cases hl : loadChain limits bytes with
  | error e => exact ⟨e, rfl⟩
  | ok revs =>
    obtain ⟨start', hs', ht⟩ := loadChain_ok_reach hl
    rw [hs] at hs'
    cases hs'
    obtain ⟨t, hrt, hterm⟩ := ht
    -- `start →* o` and `start →* t`: by determinism one path extends the other.
    exact (reach_cycle_terminal hr hrt hterm hstep hback).elim
where
  /-- If `start →* o` with `o` on a cycle and `start →* t` with `t` terminal: contradiction. -/
  reach_cycle_terminal {start o t o1 : Nat} (hr : PrevReach limits bytes start o)
      (hrt : PrevReach limits bytes start t) (hterm : Terminal limits bytes t)
      (hstep : PrevStep limits bytes o o1) (hback : PrevReach limits bytes o1 o) : False := by
    induction hr generalizing t with
    | refl => exact not_terminal_of_cycle hrt hterm hstep hback
    | @step a b _ hab _ ih =>
      cases hrt with
      | refl => exact hterm.not_step hab
      | step hab' hbt =>
        have := hab.det hab'
        subst this
        exact ih hbt hterm hstep hback

/-- **(e) Work bound** (S3). `loadChain` makes at most `bytes.size` calls of
`parseXrefTable`, and at most `maxRevisions`; the count is returned by `loadChainCounted`,
whose first component is `loadChain`. -/
theorem loadChainCounted_calls_le (limits : Limits) (bytes : ByteArray) :
    (loadChainCounted limits bytes).2 ≤ bytes.size ∧
      (loadChainCounted limits bytes).2 ≤ maxRevisions := by
  unfold loadChainCounted
  split
  · simp
  · rename_i start _
    have := walk_calls_le limits bytes start [] List.nodup_nil
      (fun _ hx => absurd hx List.not_mem_nil)
    simpa using this

/-- `loadChainCounted` computes `loadChain`. -/
theorem loadChainCounted_fst (limits : Limits) (bytes : ByteArray) :
    (loadChainCounted limits bytes).1 = loadChain limits bytes := rfl

/-! ## Merge: newest revision wins -/

/-- Lookup hits the head when its key matches. -/
theorem lookupEntry_cons_self {n : Nat} {e : XrefEntry} {r : List (Nat × XrefEntry)} :
    lookupEntry n ((n, e) :: r) = some e := by
  simp [lookupEntry]

/-- Lookup skips a head with another key. -/
theorem lookupEntry_cons_ne {n k : Nat} {e : XrefEntry} {r : List (Nat × XrefEntry)}
    (hk : k ≠ n) : lookupEntry n ((k, e) :: r) = lookupEntry n r := by
  simp [lookupEntry, hk]

/-- Below the first key of a strictly ascending list, lookup finds nothing. -/
theorem lookupEntry_lt {n : Nat} {x : Nat × XrefEntry} {xs : List (Nat × XrefEntry)}
    (hs : (x :: xs).Pairwise (fun a b => a.1 < b.1)) (hn : n < x.1) :
    lookupEntry n (x :: xs) = none := by
  induction xs generalizing x with
  | nil =>
    obtain ⟨k, e⟩ := x
    simp only [lookupEntry]
    simp at hn
    simp [show k ≠ n by omega]
  | cons y ys ih =>
    obtain ⟨k, e⟩ := x
    simp only [lookupEntry]
    simp at hn
    have hy := List.rel_of_pairwise_cons hs List.mem_cons_self
    have hs' := (List.pairwise_cons.mp hs).2
    simp only [show k ≠ n by omega, ↓reduceIte]
    exact ih hs' (by simp at hy; omega)

/-- Lookup in a merge: the first (newer) list wins, else the second. -/
theorem lookupEntry_mergeTwo (n : Nat) {xs ys : List (Nat × XrefEntry)}
    (hx : xs.Pairwise (fun a b => a.1 < b.1)) (hy : ys.Pairwise (fun a b => a.1 < b.1)) :
    lookupEntry n (mergeTwo xs ys) = (lookupEntry n xs).or (lookupEntry n ys) := by
  fun_induction mergeTwo xs ys with
  | case1 ys => simp [lookupEntry]
  | case2 x xs => simp [lookupEntry]
  | case3 x xs y ys hlt ih =>
    obtain ⟨k, e⟩ := x
    simp only [lookupEntry]
    by_cases hk : k = n
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      exact ih (List.pairwise_cons.mp hx).2 hy
  | case4 x xs y ys hlt hgt ih =>
    obtain ⟨k, e⟩ := y
    by_cases hk : k = n
    · subst hk
      rw [lookupEntry_lt (n := k) hx (by simpa using hgt), lookupEntry_cons_self,
        lookupEntry_cons_self]
      rfl
    · rw [lookupEntry_cons_ne hk, lookupEntry_cons_ne (r := ys) hk]
      exact ih hx (List.pairwise_cons.mp hy).2
  | case5 x xs y ys hlt hgt ih =>
    obtain ⟨k, e⟩ := x
    obtain ⟨k', e'⟩ := y
    simp at hlt hgt
    have hkk : k = k' := by omega
    subst hkk
    simp only [lookupEntry]
    by_cases hk : k = n
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      exact ih (List.pairwise_cons.mp hx).2 (List.pairwise_cons.mp hy).2

/-- **S6 preview.** In the merged chain (revisions newest first), object `n` maps to the
entry of the first, i.e. newest, revision that has one. -/
theorem mergeChain_lookup (n : Nat) (revs : List Revision) :
    lookupEntry n (mergeChain revs).entries =
      revs.findSome? (fun r => lookupEntry n r.1.entries) := by
  induction revs with
  | nil => rfl
  | cons r rest ih =>
    show lookupEntry n (mergeTwo r.1.entries (mergeEntries rest)) = _
    rw [lookupEntry_mergeTwo n r.1.sorted (mergeEntries_sorted rest)]
    have ih' : lookupEntry n (mergeEntries rest) = _ := ih
    rw [ih', List.findSome?_cons]
    cases lookupEntry n r.1.entries <;> rfl

end SafePdf.Spec.XrefTerm
