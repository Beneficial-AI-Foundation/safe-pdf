import SafePdf.Core.Xref.Chain
import SafePdf.Core.Open

/-!
# Termination and cycle rejection of `/Prev` chain resolution

Plan.md §5.2 (first bullet), §4 S2/S3/S6, §6 Phase 2 (exit M2); ISO 32000-2 §7.5.5–7.5.6;
Bogk & Schöpl 2014.

Theorems about `Core.Xref.Chain` (task 2.2; generalized by 2.4a from classic tables to
*sections*: a classic table or an xref stream, `Chain.parseSection`, with hybrid files'
`/XRefStm` streams parsed in the same step and counted as visited offsets):

* **S2 totality.** `loadChain` is a total function, accepted by Lean with the measure
  `bytes.size - visited.length` (unvisited offsets, bounded by the file length); no `partial`,
  no fuel. `loadChain_terminates` records this.
* **Structure of a success.** The revision offsets are pairwise distinct
  (`loadChain_offsets_nodup`) and inside the input (`loadChain_offsets_lt`); there are at most
  `bytes.size` and at most `limits.maxRevisions` of them (`loadChain_length_le`); and the `/Prev`
  path from the `startxref` offset ends in a section without `/Prev` (`loadChain_ok_reach`).
* **Cycle rejection.** `PrevStep limits bytes o o'` says "the section at `o` (table or
  stream) parses and its trailer's `/Prev` is `o'`". It contains the 2.2 relation on classic
  tables (`PrevStep.of_table`) and the xref-stream steps (`PrevStep.of_stream`).
  If a `PrevStep` path from the `startxref` offset reaches an offset that lies on a `PrevStep` cycle, `loadChain` returns an error
  (`loadChain_cycle_rejected`). This covers cycles of every length, including the 1-cycle
  (`/Prev` = own offset) and the 2-cycle of `Tests/adversarial/xref-prev-{self,cycle}.pdf`,
  whose concrete `"xref /Prev cycle"` errors are checked by `#guard` in `Core.Xref.Chain`
  (as is an xref stream whose `/Prev` is its own offset). The error kind is not pinned there
  (a hybrid `/XRefStm` stream may fail to parse first, a long tail may hit the revision limit).
* **Cycle errors** (task 2.13, M2). A revisited offset is `Error.cycle` (`step_revisited`).
  If every section on the path from `startxref` is `Endless` (parses, has a `/Prev`, is not
  hybrid), `loadChain` fails with `Error.cycle` or, only when `limits.maxRevisions` is below
  the input size, `limitExceeded .revisions` (`loadChain_endless`); for inputs within the
  budget it is `Error.cycle` (`loadChain_endless_cycle`), and then `Core.Open.openFile`
  returns that error without trying repair (`openFile_endless`).
* **S3 work bound.** `loadChainCounted` returns the number of section parses (tables, xref
  streams and `/XRefStm` streams) next to the result; it is at most `bytes.size` and at most `limits.maxRevisions`
  (`loadChainCounted_calls_le`), and equals the number of revisions on success.
* **S6 preview.** `mergeChain` keeps, per object number, the entry of the newest revision
  that has one (`mergeChain_lookup`).
-/

namespace SafePdf.Spec.XrefTerm

open SafePdf SafePdf.Core.Xref SafePdf.Core.Xref.Chain

/-! ## The `/Prev` relation -/

/-- One `/Prev` step: the section at `o` (classic table or xref stream, `parseSection`)
parses and its trailer's `/Prev` is `o'`. -/
def PrevStep (limits : Limits) (bytes : ByteArray) (o o' : Nat) : Prop :=
  ∃ sec tr, parseSection limits bytes o = .ok (sec, tr) ∧ tr.prev? = some o'

/-- The section at `o` parses and its trailer has no `/Prev`: the oldest revision. -/
def Terminal (limits : Limits) (bytes : ByteArray) (o : Nat) : Prop :=
  ∃ sec tr, parseSection limits bytes o = .ok (sec, tr) ∧ tr.prev? = none

/-- A classic table that parses is a section: the 2.2 relation (tables only) is contained in
`PrevStep`, so every 2.2 cycle is still a `PrevStep` cycle. -/
theorem parseSection_of_table {limits : Limits} {bytes : ByteArray} {o : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : parseXrefTable limits bytes o = .ok (sec, tr, r)) :
    parseSection limits bytes o = .ok (sec, tr) := by
  have hm : matchAt bytes o kwXref = true := by
    unfold parseXrefTable at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact hc.1
    · simp at h
  unfold parseSection
  simp only [hm, ↓reduceIte, h]

/-- A 2.2 `/Prev` step (classic table) is a `PrevStep`. -/
theorem PrevStep.of_table {limits : Limits} {bytes : ByteArray} {o o' : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : parseXrefTable limits bytes o = .ok (sec, tr, r)) (hp : tr.prev? = some o') :
    PrevStep limits bytes o o' :=
  ⟨sec, tr, parseSection_of_table h, hp⟩

/-- An xref stream that parses at an offset not holding `xref` is a section. -/
theorem parseSection_of_stream {limits : Limits} {bytes : ByteArray} {o : Nat}
    {sec : XrefSection} {tr : Trailer} (hk : matchAt bytes o kwXref = false)
    (h : Stream.parseXrefStream limits bytes o = .ok (sec, tr)) :
    parseSection limits bytes o = .ok (sec, tr) := by
  unfold parseSection
  simp only [hk, Bool.false_eq_true, ↓reduceIte, h]

/-- An xref-stream `/Prev` step is a `PrevStep`. -/
theorem PrevStep.of_stream {limits : Limits} {bytes : ByteArray} {o o' : Nat}
    {sec : XrefSection} {tr : Trailer} (hk : matchAt bytes o kwXref = false)
    (h : Stream.parseXrefStream limits bytes o = .ok (sec, tr)) (hp : tr.prev? = some o') :
    PrevStep limits bytes o o' :=
  ⟨sec, tr, parseSection_of_stream hk h, hp⟩

/-- Reflexive-transitive closure of `PrevStep`: a `/Prev` path from `o` to `t`. -/
inductive PrevReach (limits : Limits) (bytes : ByteArray) : Nat → Nat → Prop
  /-- The empty path. -/
  | refl (o : Nat) : PrevReach limits bytes o o
  /-- One step, then a path. -/
  | step {o o' t : Nat} : PrevStep limits bytes o o' → PrevReach limits bytes o' t →
      PrevReach limits bytes o t

/-- `PrevStep` is deterministic: a section has at most one `/Prev`. -/
theorem PrevStep.det {limits : Limits} {bytes : ByteArray} {o a b : Nat}
    (ha : PrevStep limits bytes o a) (hb : PrevStep limits bytes o b) : a = b := by
  obtain ⟨s1, t1, h1, p1⟩ := ha
  obtain ⟨s2, t2, h2, p2⟩ := hb
  rw [h1] at h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨-, rfl⟩ := h2
  rw [p1] at p2
  exact Option.some.inj p2

/-- A terminal section has no `/Prev` step. -/
theorem Terminal.not_step {limits : Limits} {bytes : ByteArray} {o o' : Nat}
    (ht : Terminal limits bytes o) (hs : PrevStep limits bytes o o') : False := by
  obtain ⟨s1, t1, h1, p1⟩ := ht
  obtain ⟨s2, t2, h2, p2⟩ := hs
  rw [h1] at h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨-, rfl⟩ := h2
  rw [p1] at p2
  cases p2

/-- Append one step at the end of a path. -/
theorem PrevReach.tail {limits : Limits} {bytes : ByteArray} {o t t' : Nat}
    (h : PrevReach limits bytes o t) (hs : PrevStep limits bytes t t') :
    PrevReach limits bytes o t' := by
  induction h with
  | refl o => exact .step hs (.refl t')
  | step h1 _ ih => exact .step h1 (ih hs)

/-- No terminal section is reachable from an offset `o` on a `/Prev` cycle
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

/-! ## One step -/

/-- Work bound of one step: its section parses (0, 1 or 2) are at most the number of
unvisited offsets and at most the remaining revision budget. -/
theorem step_calls_le (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) (sn : Seen visited) (hlt : ∀ x ∈ visited, x < bytes.size) :
    (step limits bytes off visited hnd sn).2 ≤ bytes.size - visited.length ∧
      (step limits bytes off visited hnd sn).2 ≤ limits.maxRevisions - visited.length := by
  have hl := sn.len_eq
  unfold step
  split
  · rename_i hoff
    split
    · simp
    · rename_i hmem
      have h1 := length_lt_of_fresh hnd hlt hoff hmem
      split
      · simp
      · rename_i hmax
        split
        · simp; omega
        · split
          · simp; omega
          · split
            · rename_i s _ hs
              split
              · simp; omega
              · rename_i hsm
                split
                · simp; omega
                · rename_i hmax2
                  -- `s` and `off` are both fresh: two more offsets below `bytes.size`
                  have h2 := length_le_of_nodup_of_lt (l := s :: off :: visited)
                    (n := bytes.size)
                    (by
                      simp only [List.nodup_cons, List.mem_cons, not_or]
                      exact ⟨⟨fun h => hsm (Or.inl h), fun h => hsm (Or.inr h)⟩, hmem, hnd⟩)
                    (by
                      intro x hx
                      simp only [List.mem_cons] at hx
                      rcases hx with rfl | rfl | hx
                      · exact hs
                      · exact hoff
                      · exact hlt x hx)
                  simp only [List.length_cons] at h2
                  split
                  · simp; omega
                  · simp; omega
            · simp; omega
  · simp

/-- What a successful step guarantees: one parse per revision, the revision budget is
respected, and the section at `off` parses with the returned `/Prev`. -/
theorem step_ok {limits : Limits} {bytes : ByteArray} {off : Nat} {visited : List Nat}
    {hnd : visited.Nodup} {sn : Seen visited} {so : StepOk bytes visited} {k : Nat}
    (h : step limits bytes off visited hnd sn = (.ok so, k)) :
    k = so.revs.length ∧ so.revs.length + visited.length ≤ limits.maxRevisions ∧
      ∃ sec tr, parseSection limits bytes off = .ok (sec, tr) ∧ so.prev? = tr.prev? := by
  have hl := sn.len_eq
  unfold step at h
  split at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hmax
        split at h
        · simp at h
        · rename_i sec tr hp
          split at h
          · simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨rfl, by simp; omega, sec, tr, hp, rfl⟩
          · split at h
            · split at h
              · simp at h
              · split at h
                · simp at h
                · rename_i hmax2
                  split at h
                  · simp at h
                  · simp only [Prod.mk.injEq, Except.ok.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact ⟨rfl, by simp; omega, sec, tr, hp, rfl⟩
            · simp at h
  · simp at h

/-! ## The loop -/

/-- Work bound of the loop: the number of section parses is at most the number of unvisited
offsets, and at most the remaining revision budget. -/
theorem walk_calls_le (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) (sn : Seen visited) (hlt : ∀ x ∈ visited, x < bytes.size) :
    (walk limits bytes off visited hnd sn hlt).2 ≤ bytes.size - visited.length ∧
      (walk limits bytes off visited hnd sn hlt).2 ≤ limits.maxRevisions - visited.length := by
  fun_induction walk limits bytes off visited hnd sn hlt with
  | case1 off visited hnd sn hlt e k hs =>
    have := step_calls_le limits bytes off visited hnd sn hlt
    rw [hs] at this
    simpa using this
  | case2 off visited hnd sn hlt so k hs hp =>
    have := step_calls_le limits bytes off visited hnd sn hlt
    rw [hs] at this
    simpa using this
  | case3 off visited hnd sn hlt so k hs p hp e k' hw ih =>
    obtain ⟨hk, hlen, -⟩ := step_ok hs
    have hb := length_le_of_nodup_of_lt so.nodup (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact so.lt x hx
      · exact hlt x hx)
    rw [hw] at ih
    simp only [List.length_append, List.length_map] at ih hb
    simp only
    omega
  | case4 off visited hnd sn hlt so k hs p hp rest k' hw ih =>
    obtain ⟨hk, hlen, -⟩ := step_ok hs
    have hb := length_le_of_nodup_of_lt so.nodup (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact so.lt x hx
      · exact hlt x hx)
    rw [hw] at ih
    simp only [List.length_append, List.length_map] at ih hb
    simp only
    omega

/-- What a successful run of the loop from `off` guarantees: the revision offsets are
distinct, inside the input and not previously visited; the revision budget is respected;
there is one parse per revision; and the `/Prev` path from `off` ends in a terminal section. -/
theorem walk_ok (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) (sn : Seen visited) (hlt : ∀ x ∈ visited, x < bytes.size)
    {revs : List Revision}
    (h : (walk limits bytes off visited hnd sn hlt).1 = .ok revs) :
    (revs.map Revision.offset).Nodup ∧
      (∀ o ∈ revs.map Revision.offset, o < bytes.size ∧ o ∉ visited) ∧
      revs.length + visited.length ≤ limits.maxRevisions ∧
      (walk limits bytes off visited hnd sn hlt).2 = revs.length ∧
      ∃ t, PrevReach limits bytes off t ∧ Terminal limits bytes t := by
  revert revs
  fun_induction walk limits bytes off visited hnd sn hlt with
  | case1 => simp
  | case2 off visited hnd sn hlt so k hs hp =>
    intro revs h
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨hk, hlen, sec, tr, hsec, hprev⟩ := step_ok hs
    have hnd' := List.nodup_append.mp so.nodup
    refine ⟨hnd'.1, fun o ho => ⟨so.lt o ho, fun hv => hnd'.2.2 o ho o hv rfl⟩, hlen, hk,
      off, .refl off, sec, tr, hsec, ?_⟩
    rw [← hprev, hp]
  | case3 => simp
  | case4 off visited hnd sn hlt so k hs p hp rest k' hw ih =>
    intro revs h
    simp only [Except.ok.injEq] at h
    subst h
    rw [hw] at ih
    obtain ⟨hnd2, hmem2, hlen2, hk2, t, hreach, hterm⟩ := ih rfl
    obtain ⟨hk, hlen, sec, tr, hsec, hprev⟩ := step_ok hs
    have hnd' := List.nodup_append.mp so.nodup
    refine ⟨?_, ?_, ?_, ?_, t, .step ⟨sec, tr, hsec, by rw [← hprev, hp]⟩ hreach, hterm⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨hnd'.1, hnd2, fun a ha b hb hab => ?_⟩
      subst hab
      exact (hmem2 a hb).2 (List.mem_append_left _ ha)
    · intro o ho
      rw [List.map_append, List.mem_append] at ho
      rcases ho with ho | ho
      · exact ⟨so.lt o ho, fun hv => hnd'.2.2 o ho o hv rfl⟩
      · have := hmem2 o ho
        exact ⟨this.1, fun hv => this.2 (List.mem_append_right _ hv)⟩
    · simp only [List.length_append, List.length_map] at hlen2 ⊢
      omega
    · simp only [List.length_append] at hk2 ⊢
      omega

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
      (walk limits bytes start [] List.nodup_nil Seen.empty (fun _ hx => absurd hx List.not_mem_nil)).1 := by
  unfold loadChain loadChainCounted
  rw [hs]

/-- What a successful `loadChain` guarantees (all parts below in one statement). -/
theorem loadChain_ok {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) :
    ∃ start, findStartxref bytes = .ok start ∧
      (revs.map Revision.offset).Nodup ∧
      (∀ o ∈ revs.map Revision.offset, o < bytes.size) ∧
      revs.length ≤ limits.maxRevisions ∧
      (loadChainCounted limits bytes).2 = revs.length ∧
      ∃ t, PrevReach limits bytes start t ∧ Terminal limits bytes t := by
  unfold loadChain loadChainCounted at h
  split at h
  · simp at h
  · rename_i start hs
    have := walk_ok limits bytes start [] List.nodup_nil Seen.empty
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
input) and at most `limits.maxRevisions`. -/
theorem loadChain_length_le {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) :
    revs.length ≤ bytes.size ∧ revs.length ≤ limits.maxRevisions := by
  obtain ⟨_, _, h1, h2, h3, _⟩ := loadChain_ok h
  have := length_le_of_nodup_of_lt h1 h2
  simp only [List.length_map] at this
  exact ⟨this, h3⟩

/-- On success the `/Prev` path from the `startxref` offset ends in a section without `/Prev`. -/
theorem loadChain_ok_reach {limits : Limits} {bytes : ByteArray} {revs : List Revision}
    (h : loadChain limits bytes = .ok revs) :
    ∃ start, findStartxref bytes = .ok start ∧
      ∃ t, PrevReach limits bytes start t ∧ Terminal limits bytes t := by
  obtain ⟨start, hs, _, _, _, _, h5⟩ := loadChain_ok h
  exact ⟨start, hs, h5⟩

/-- **(d) Cycle rejection** (Bogk & Schöpl 2014). If the `/Prev` path from the `startxref`
offset reaches an offset `o` that lies on a `/Prev` cycle (`o → o1 →* o`, every section on it
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

/-! ## Cycle errors are `Error.cycle` (task 2.13) -/

/-- **A revisited offset is a cycle error.** One step at an offset inside the input that was
already visited fails with `Error.cycle off "xref /Prev cycle"` and parses nothing. -/
theorem step_revisited {limits : Limits} {bytes : ByteArray} {off : Nat} {visited : List Nat}
    (hnd : visited.Nodup) (sn : Seen visited) (hoff : off < bytes.size) (hmem : off ∈ visited) :
    step limits bytes off visited hnd sn = (.error (.cycle off "xref /Prev cycle"), 0) := by
  unfold step
  simp only [hoff, hmem, dite_true]

/-- The offset `x` lies on an endless `/Prev` path in a non-hybrid way: it is inside the
input, its section parses, has no `/XRefStm` stream (`hybridStm`) and has a `/Prev`. -/
def Endless (limits : Limits) (bytes : ByteArray) (x : Nat) : Prop :=
  x < bytes.size ∧ ∃ sec tr y, parseSection limits bytes x = .ok (sec, tr) ∧
    hybridStm bytes x tr = none ∧ tr.prev? = some y

/-- A failing step at an `Endless` offset fails with a cycle, or with the revision limit when
the limit is below the input size (the visited offsets are distinct and inside the input, so
a smaller input cannot exhaust the budget). -/
theorem step_error_endless {limits : Limits} {bytes : ByteArray} {off : Nat}
    {visited : List Nat} {hnd : visited.Nodup} {sn : Seen visited} (hlt : ∀ x ∈ visited, x < bytes.size)
    {e : Error} {k : Nat}
    (hend : Endless limits bytes off) (h : step limits bytes off visited hnd sn = (.error e, k)) :
    e.isCycle = true ∨
      (e = .limitExceeded .revisions ∧ limits.maxRevisions < bytes.size) := by
  obtain ⟨hoff, sec, tr, y, hp, hh, -⟩ := hend
  have hl := sn.len_eq
  unfold step at h
  simp only [hoff, dite_true] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h, -⟩ := h
    cases h
    exact Or.inl rfl
  · rename_i hmem
    split at h
    · rename_i hmax
      simp only [Prod.mk.injEq] at h
      obtain ⟨h, -⟩ := h
      cases h
      have := length_lt_of_fresh hnd hlt hoff hmem
      exact Or.inr ⟨rfl, by omega⟩
    · rw [hp] at h
      simp only [hh] at h
      cases h

/-- **Endless chains end in a cycle error.** If every offset reachable from `off` by `/Prev`
steps is `Endless` (no section terminates the chain, none is hybrid), `walk` fails with a
cycle error (`Error.cycle`) or, when the cycle is reached only after more than
`limits.maxRevisions` revisions, with `limitExceeded .revisions`. -/
theorem walk_endless (limits : Limits) (bytes : ByteArray) (off : Nat) (visited : List Nat)
    (hnd : visited.Nodup) (sn : Seen visited) (hlt : ∀ x ∈ visited, x < bytes.size)
    (hend : ∀ x, PrevReach limits bytes off x → Endless limits bytes x) :
    ∃ e, (walk limits bytes off visited hnd sn hlt).1 = .error e ∧
      (e.isCycle = true ∨
        (e = .limitExceeded .revisions ∧ limits.maxRevisions < bytes.size)) := by
  revert hend
  fun_induction walk limits bytes off visited hnd sn hlt with
  | case1 off visited hnd sn hlt e k hs =>
    intro hend
    exact ⟨e, rfl, step_error_endless hlt (hend off (.refl off)) hs⟩
  | case2 off visited hnd sn hlt so k hs hp =>
    intro hend
    obtain ⟨-, -, sec, tr, hsec, hprev⟩ := step_ok hs
    obtain ⟨-, sec', tr', y, hsec', -, hy⟩ := hend off (.refl off)
    rw [hsec] at hsec'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsec'
    obtain ⟨-, rfl⟩ := hsec'
    rw [hp, hy] at hprev
    cases hprev
  | case3 off visited hnd sn hlt so k hs p hp e k' hw ih =>
    intro _
    exact ⟨e, rfl, by
      obtain ⟨e', he', hc⟩ := ih (fun x hx => by
        obtain ⟨-, -, sec, tr, hsec, hprev⟩ := step_ok hs
        exact ‹∀ x, PrevReach limits bytes off x → Endless limits bytes x› x
          (.step ⟨sec, tr, hsec, by rw [← hprev, hp]⟩ hx))
      rw [hw] at he'
      cases he'
      exact hc⟩
  | case4 off visited hnd sn hlt so k hs p hp rest k' hw ih =>
    intro hend
    obtain ⟨e', he', -⟩ := ih (fun x hx => by
      obtain ⟨-, -, sec, tr, hsec, hprev⟩ := step_ok hs
      exact hend x (.step ⟨sec, tr, hsec, by rw [← hprev, hp]⟩ hx))
    rw [hw] at he'
    cases he'

/-- **(d′) Cycles are reported as cycles** (task 2.13). If every offset on the `/Prev` path
from the `startxref` offset is `Endless` — the Bogk & Schöpl situation: a `/Prev` path that
never reaches a section without `/Prev`, so it must revisit an offset — then `loadChain`
fails with `Error.cycle` or, for a path of more than `limits.maxRevisions` distinct sections
(possible only if `limits.maxRevisions < bytes.size`), with `limitExceeded .revisions`.
With `Core.Open.openFile_loadChain_cycle`, a cycle error here is what `openFile` returns. (Hybrid sections are excluded: an `/XRefStm` stream on the
path may fail to parse first, which is a parse error, not a cycle.) -/
theorem loadChain_endless {limits : Limits} {bytes : ByteArray} {start : Nat}
    (hs : findStartxref bytes = .ok start)
    (hend : ∀ x, PrevReach limits bytes start x → Endless limits bytes x) :
    ∃ e, loadChain limits bytes = .error e ∧
      (e.isCycle = true ∨
        (e = .limitExceeded .revisions ∧ limits.maxRevisions < bytes.size)) := by
  unfold loadChain loadChainCounted
  rw [hs]
  exact walk_endless limits bytes start [] List.nodup_nil Seen.empty
    (fun _ hx => absurd hx List.not_mem_nil) hend

/-- **Within the revision budget a cycle is `Error.cycle`.** If, moreover, the input has at
most `limits.maxRevisions` bytes (so every set of distinct offsets fits the budget; the
default budget is 4096), `loadChain`'s error is a cycle error. -/
theorem loadChain_endless_cycle {limits : Limits} {bytes : ByteArray} {start : Nat}
    (hs : findStartxref bytes = .ok start)
    (hend : ∀ x, PrevReach limits bytes start x → Endless limits bytes x)
    (hbudget : bytes.size ≤ limits.maxRevisions) :
    ∃ e, loadChain limits bytes = .error e ∧ e.isCycle = true := by
  obtain ⟨e, he, hc⟩ := loadChain_endless hs hend
  refine ⟨e, he, ?_⟩
  rcases hc with hc | ⟨-, hlt⟩
  · exact hc
  · omega

/-- **M2: endless `/Prev` chains are rejected by `openFile`** (task 2.13). Under the
hypotheses of `loadChain_endless_cycle`, `Core.Open.openFile` fails with a cycle error: the
repair path is not tried (`Core.Open.openFile_loadChain_cycle`). -/
theorem openFile_endless {limits : Limits} {bytes : ByteArray} {start : Nat}
    (hs : findStartxref bytes = .ok start)
    (hend : ∀ x, PrevReach limits bytes start x → Endless limits bytes x)
    (hbudget : bytes.size ≤ limits.maxRevisions) :
    ∃ e, Core.Open.openFile limits bytes = .error e ∧ e.isCycle = true := by
  obtain ⟨e, he, hc⟩ := loadChain_endless_cycle hs hend hbudget
  exact ⟨e, Core.Open.openFile_loadChain_cycle he hc, hc⟩

/-- **(e) Work bound** (S3). `loadChain` makes at most `bytes.size` section parses (classic
tables, xref streams and `/XRefStm` streams), and at most `limits.maxRevisions`; the
count is returned by `loadChainCounted`, whose first component is `loadChain`. -/
theorem loadChainCounted_calls_le (limits : Limits) (bytes : ByteArray) :
    (loadChainCounted limits bytes).2 ≤ bytes.size ∧
      (loadChainCounted limits bytes).2 ≤ limits.maxRevisions := by
  unfold loadChainCounted
  split
  · simp
  · rename_i start _
    have := walk_calls_le limits bytes start [] List.nodup_nil Seen.empty
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

/-- A pass of `mergePairs` keeps the first list that has an entry for `n`. -/
theorem findSome?_mergePairs (n : Nat) : ∀ l : List (List (Nat × XrefEntry)),
    (∀ x ∈ l, x.Pairwise (fun a b => a.1 < b.1)) →
    (mergePairs l).findSome? (lookupEntry n) = l.findSome? (lookupEntry n)
  | [], _ => by simp [mergePairs]
  | [a], _ => by simp [mergePairs]
  | a :: b :: rest, h => by
    simp only [mergePairs, List.findSome?_cons]
    rw [lookupEntry_mergeTwo n (h a (by simp)) (h b (by simp)),
      findSome?_mergePairs n rest (fun y hy => h y (by simp [hy]))]
    cases lookupEntry n a <;> cases lookupEntry n b <;> rfl

/-- Lookup in `mergeRounds`: the first list that has an entry for `n` wins. -/
theorem lookupEntry_mergeRounds (n : Nat) (l : List (List (Nat × XrefEntry)))
    (h : ∀ x ∈ l, x.Pairwise (fun a b => a.1 < b.1)) :
    lookupEntry n (mergeRounds l) = l.findSome? (lookupEntry n) := by
  fun_induction mergeRounds l with
  | case1 => rfl
  | case2 a => simp [List.findSome?_cons]; cases lookupEntry n a <;> rfl
  | case3 a b rest ih =>
    rw [ih (mergePairs_sorted _ h), findSome?_mergePairs n _ h]

/-- **S6 preview.** In the merged chain (revisions newest first), object `n` maps to the
entry of the first, i.e. newest, revision that has one. -/
theorem mergeChain_lookup (n : Nat) (revs : List Revision) :
    lookupEntry n (mergeChain revs).entries =
      revs.findSome? (fun r => lookupEntry n r.1.entries) := by
  show lookupEntry n (mergeRounds (revs.map fun r => r.1.entries)) = _
  rw [lookupEntry_mergeRounds n _ (fun x hx => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    exact r.1.sorted)]
  induction revs with
  | nil => rfl
  | cons r rest ih => simp only [List.map_cons, List.findSome?_cons, ih]

end SafePdf.Spec.XrefTerm
