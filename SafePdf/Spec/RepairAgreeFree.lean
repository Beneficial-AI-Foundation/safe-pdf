import SafePdf.Spec.RepairAgree
import SafePdf.Spec.WritePrefix

/-!
# C4 with free entries `n ≥ 1` (task 12.7a)

Plan.md §5 (claim C4), §5.2 (fuel = number of objects), §5.4 (the repair path), §6 Phase 12
"Proof gaps" (tasks 12.7a, 12.7d); `docs/safety.md` §5, gap 1. Extends `Spec.RepairAgree` (task 12.7),
whose H2 forbade free entries other than object 0.

## The obstacle

With a free entry `n ≥ 1` (a deleted object) the strict section has that entry and the
repaired section does not, so the two sections differ in length, and `getObject` passes the
section length (`OpenDoc.objectCount`) as the fuel of `/Length` resolution
(`Length.parseIndirectResolved`) and of object streams (`ObjStm.fetchCompressed`). Besides, the
strict lookup returns `free` where the repaired one returns nothing: `getObject` maps both to
`null` (rule G4), and until task 12.7d `/Length` resolution reported them with **different
messages** (`malformed 0 "/Length refers to free object n"` against `"… not in the xref"`;
`freeLengthBytes`), so 12.7a could only state `Agree`. Task 12.7d made Core report both with
one message (`Length.lengthMissingMsg`; likewise `ObjStm.containerMissingMsg` for object
stream containers), and `getObject` is now **equal** on both paths (`c4_free_eq`).

## Theorems

* Fuel monotonicity (any lookup, compressed entries included): `resolveLengthAux_mono`
  (success with fuel `f` ⇒ same parses and result with every `f' ≥ f`; strong induction, the
  object-stream case shares the fuel), `parseIndirectResolved_mono`, `fetchCompressed_mono`.
* Fuel stability and lookup agreement (no compressed entries): `resolve_agree` — for lookups
  related by `LookupRel` (same entries once `free` is forgotten) and fuels above `cnt S V`
  (in-use objects not being visited), resolution agrees; lifted by `lengthOf_agree`,
  `parseIndirectWith_agree` (only the call point matters, `parseIndirectWith_err`) and
  `getObject_agree`. Exact forms (task 12.7d): `resolve_eq`, `lengthOf_eq`, `getObject_eq`.
* `HypFree` (decidable, checker `checkFree`): `Hyp` with H2 relaxed to `EntryOkFree` (free
  entries allowed for every number; H1, H3–H6 unchanged; `Hyp.toFree`). A free `n ≥ 1` has no
  scan hit, by H3: "shadowed" hits do not exist, since the scan keeps the newest hit of every
  number.
* `c4_free_eq` / `c4_free_eq_check`: the repair path succeeds, same bytes, same in-use
  entries (`inUse_mem_iff`), same `/Root`, and **equal** `getObject` for every `num gen`.
  `c4_free` / `c4_free_check` keep 12.7a's statement (`Agree`: equal, or both `malformed 0`;
  `Agree.ok_iff`: the same successes), now derived from the exact form. The fixtures
  `freeEntryBytes` (passes `checkFree`, fails 12.7's `check`, sections of 7 and 6 entries,
  `getObject` equal) and `freeLengthBytes` (a `/Length` naming the free object: the same
  error on both paths) are checked by `#guard`.

## Open

* Compressed entries and encrypted files (as in `Spec.RepairAgree`).
-/

namespace SafePdf.Spec.RepairAgreeFree

open SafePdf
open SafePdf.Core.Open
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)
open SafePdf.Core.Xref.Length
open SafePdf.Spec.RepairAgree
open SafePdf.Repair (scanSection toEntries)

/-! ## Agreement up to the message of a `malformed 0` error -/

/-- Two results **agree**: they are equal, or both are `malformed 0` errors (whose messages
may differ: "free object" against "not in the xref"). -/
def Agree {α : Type} (a b : Except Error α) : Prop :=
  a = b ∨ ∃ m m', a = .error (.malformed 0 m) ∧ b = .error (.malformed 0 m')

/-- `Agree` is reflexive. -/
theorem Agree.refl {α : Type} (a : Except Error α) : Agree a a := Or.inl rfl

/-- `Agree` is symmetric. -/
theorem Agree.symm {α : Type} {a b : Except Error α} (h : Agree a b) : Agree b a := by
  rcases h with rfl | ⟨m, m', rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨m', m, rfl, rfl⟩

/-- Agreeing results have the same successes. -/
theorem Agree.ok_iff {α : Type} {a b : Except Error α} (h : Agree a b) (v : α) :
    a = .ok v ↔ b = .ok v := by
  rcases h with rfl | ⟨m, m', rfl, rfl⟩
  · exact Iff.rfl
  · simp

/-! ## Lookups that differ only between `free` and absent -/

/-- An entry with `free` forgotten (`free` and absent both resolve to nothing). -/
def strip : Option XrefEntry → Option XrefEntry
  | some (.free _ _) => none
  | e => e

/-- Two lookups that agree up to `free` versus absent, with no compressed entry. -/
structure LookupRel (l1 l2 : Nat → Option XrefEntry) : Prop where
  /-- Same entries once `free` is forgotten. -/
  strip_eq : ∀ n, strip (l1 n) = strip (l2 n)
  /-- No compressed entry in the first lookup. -/
  nc1 : ∀ n c i, l1 n ≠ some (.compressed c i)
  /-- No compressed entry in the second lookup. -/
  nc2 : ∀ n c i, l2 n ≠ some (.compressed c i)

/-- The cases of a related pair of lookups at one object number: the same in-use entry, or
neither in use (and none compressed). -/
theorem LookupRel.cases {l1 l2 : Nat → Option XrefEntry} (h : LookupRel l1 l2) (n : Nat) :
    (∃ off g, l1 n = some (.inUse off g) ∧ l2 n = some (.inUse off g)) ∨
      ((l1 n = none ∨ ∃ a g, l1 n = some (.free a g)) ∧
        (l2 n = none ∨ ∃ a g, l2 n = some (.free a g))) := by
  have hs := h.strip_eq n
  have c1 := h.nc1 n
  have c2 := h.nc2 n
  rcases h1 : l1 n with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩) <;>
    rcases h2 : l2 n with _ | (⟨a', g'⟩ | ⟨off', g'⟩ | ⟨c', i'⟩) <;>
    simp_all [strip]

/-- `errOffset` only reads in-use entries. -/
theorem errOffset_eq {l1 l2 : Nat → Option XrefEntry} (h : LookupRel l1 l2) (n : Nat) :
    errOffset l1 n = errOffset l2 n := by
  unfold errOffset
  rcases h.cases n with ⟨off, g, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]


/-! ## Fuel: resolution is stable above the number of in-use objects -/

/-- The number of object numbers of `S` not in `V` (the in-use objects still resolvable). -/
def cnt : List Nat → List Nat → Nat
  | [], _ => 0
  | y :: ys, V => (if y ∈ V then 0 else 1) + cnt ys V

/-- Visiting one more object never increases `cnt`. -/
theorem cnt_cons_le (S V : List Nat) (x : Nat) : cnt S (x :: V) ≤ cnt S V := by
  induction S with
  | nil => simp [cnt]
  | cons y ys ih =>
    simp only [cnt, List.mem_cons]
    by_cases h1 : y = x <;> by_cases h2 : y ∈ V <;> simp [h1, h2] <;> omega

/-- Visiting an object of `S` not yet visited decreases `cnt`. -/
theorem cnt_cons_lt {S V : List Nat} {x : Nat} (hx : x ∈ S) (hv : x ∉ V) :
    cnt S (x :: V) < cnt S V := by
  induction S with
  | nil => simp at hx
  | cons y ys ih =>
    have hle := cnt_cons_le ys V x
    simp only [cnt, List.mem_cons]
    by_cases h1 : y = x
    · subst h1; simp [hv]; omega
    · have hx' : x ∈ ys := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm h1
        · exact h
      have := ih hx'
      by_cases h2 : y ∈ V <;> simp [h1, h2] <;> omega

/-- `cnt` is at most the length. -/
theorem cnt_le (S V : List Nat) : cnt S V ≤ S.length := by
  induction S with
  | nil => simp [cnt]
  | cons y ys ih => simp only [cnt, List.length_cons]; split <;> omega

/-- **Fuel stability and lookup agreement for `/Length` resolution.** For two lookups related
by `LookupRel` (same in-use entries, `free` versus absent, nothing compressed) whose in-use
object numbers lie in `S`, resolution with any two fuels above `cnt S V` agrees. In particular
(`l1 = l2`) the result is independent of the fuel once it exceeds the number of in-use objects
not being visited. -/
theorem resolve_agree {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (h : LookupRel l1 l2) (limits : Limits) (bytes : ByteArray) (S : List Nat)
    (hS : ∀ n off g, l1 n = some (.inUse off g) → n ∈ S) :
    ∀ f1 f2 V ref, cnt S V < f1 → cnt S V < f2 →
      Agree (resolveLengthAux pre l1 limits bytes f1 V ref).2
        (resolveLengthAux pre l2 limits bytes f2 V ref).2 := by
  intro f1
  induction f1 with
  | zero => intro f2 V ref h1; omega
  | succ k ih =>
    intro f2 V ref hk hj
    obtain ⟨j, rfl⟩ : ∃ j, f2 = j + 1 := ⟨f2 - 1, by omega⟩
    rw [resolveLengthAux, resolveLengthAux]
    by_cases hv : ref.1 ∈ V
    · simp only [hv, ↓reduceIte]
      rw [errOffset_eq h]; exact Agree.refl _
    · simp only [hv, ↓reduceIte]
      rcases h.cases ref.1 with ⟨off, g, h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        simp only
        split
        · rename_i hg
          rcases hp : parseLengthObj limits bytes off ref.1 ref.2 with e | o
          · exact Agree.refl _
          · cases o
            all_goals try exact Agree.refl _
            rename_i m hh
            have hlt := cnt_cons_lt (hS _ _ _ h1) hv
            exact ih j _ _ (by omega) (by omega)
        · exact Agree.refl _
      · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;>
          rw [h1, h2] <;> exact Or.inr ⟨_, _, rfl, rfl⟩

/-- **Exact form of `resolve_agree`** (task 12.7d): since Core reports a free and a missing
`/Length` target with the same message (`Length.lengthMissingMsg`), resolution with related
lookups and fuels above `cnt S V` gives **equal** results. -/
theorem resolve_eq {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (h : LookupRel l1 l2) (limits : Limits) (bytes : ByteArray) (S : List Nat)
    (hS : ∀ n off g, l1 n = some (.inUse off g) → n ∈ S) :
    ∀ f1 f2 V ref, cnt S V < f1 → cnt S V < f2 →
      (resolveLengthAux pre l1 limits bytes f1 V ref).2 =
        (resolveLengthAux pre l2 limits bytes f2 V ref).2 := by
  intro f1
  induction f1 with
  | zero => intro f2 V ref h1; omega
  | succ k ih =>
    intro f2 V ref hk hj
    obtain ⟨j, rfl⟩ : ∃ j, f2 = j + 1 := ⟨f2 - 1, by omega⟩
    rw [resolveLengthAux, resolveLengthAux]
    by_cases hv : ref.1 ∈ V
    · simp only [hv, ↓reduceIte]
      rw [errOffset_eq h]
    · simp only [hv, ↓reduceIte]
      rcases h.cases ref.1 with ⟨off, g, h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        simp only
        split
        · rename_i hg
          rcases hp : parseLengthObj limits bytes off ref.1 ref.2 with e | o
          · rfl
          · cases o
            all_goals try rfl
            rename_i m hh
            have hlt := cnt_cons_lt (hS _ _ _ h1) hv
            exact ih j _ _ (by omega) (by omega)
        · rfl
      · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;>
          rw [h1, h2]

/-- **Fuel monotonicity of `/Length` resolution** (any lookup, compressed entries included):
if resolution succeeds with fuel `f`, it performs the same parses and gives the same result
with any fuel `f' ≥ f`. -/
theorem resolveLengthAux_mono (pre : Core.Xref.ObjStm.Pre) (lookup : Nat → Option XrefEntry)
    (limits : Limits) (bytes : ByteArray) :
    ∀ f f' V ref v, f ≤ f' → (resolveLengthAux pre lookup limits bytes f V ref).2 = .ok v →
      resolveLengthAux pre lookup limits bytes f' V ref =
        resolveLengthAux pre lookup limits bytes f V ref := by
  intro f
  induction f using Nat.strongRecOn with
  | _ f ih =>
  intro f' V ref v hff hok
  by_cases hv : ref.1 ∈ V
  · rw [resolveLengthAux.eq_def] at hok
    simp [hv] at hok
  cases f with
  | zero =>
    rw [resolveLengthAux.eq_def] at hok
    simp [hv] at hok
  | succ k =>
  obtain ⟨k', rfl⟩ : ∃ k', f' = k' + 1 := ⟨f' - 1, by omega⟩
  rw [resolveLengthAux] at hok
  rw [resolveLengthAux, resolveLengthAux]
  simp only [hv, ↓reduceIte] at hok ⊢
  rcases hl : lookup ref.1 with _ | (⟨a, g⟩ | ⟨off, g'⟩ | ⟨c, idx⟩)
  · rfl
  · rfl
  · rw [hl] at hok
    by_cases hg : g' = ref.2
    · simp only [hg, ↓reduceIte] at hok ⊢
      rcases hp : parseLengthObj limits bytes off ref.1 ref.2 with e | o
      · rfl
      · rw [hp] at hok
        cases o
        all_goals try rfl
        rename_i m hh
        simp only at hok ⊢
        rw [ih k (by omega) k' _ _ v (by omega) hok]
    · simp only [hg, ↓reduceIte]
  · rw [hl] at hok
    by_cases hcy : c = ref.1 ∨ c ∈ V
    · simp only [hcy, ↓reduceIte]
    · simp only [hcy, ↓reduceIte] at hok ⊢
      rcases hc : lookup c with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
      · rfl
      · rfl
      · rw [hc] at hok
        by_cases hg : g = 0
        · simp only [hg, ↓reduceIte] at hok ⊢
          rcases hph : parseContainerHead limits bytes off c with e | ⟨d, p⟩
          · rfl
          · rw [hph] at hok
            simp only at hok ⊢
            have hr1 : ∃ x, (containerLength
                (fun v r => resolveLengthAux pre lookup limits bytes k v r)
                (c :: ref.1 :: V) d p).2 = .ok x := by
              rcases h1 : (containerLength
                  (fun v r => resolveLengthAux pre lookup limits bytes k v r)
                  (c :: ref.1 :: V) d p).2 with e | x
              · rw [h1] at hok; simp [containerMember] at hok
              · exact ⟨x, rfl⟩
            have hcl : containerLength
                (fun v r => resolveLengthAux pre lookup limits bytes k' v r) (c :: ref.1 :: V) d p =
                containerLength
                (fun v r => resolveLengthAux pre lookup limits bytes k v r)
                (c :: ref.1 :: V) d p := by
              obtain ⟨x, hx⟩ := hr1
              unfold containerLength at hx ⊢
              split
              · rename_i m hh hm
                rw [hm] at hx
                exact ih k (by omega) k' _ _ x (by omega) hx
              · rfl
            rw [hcl]
            rcases hm : containerMember pre limits bytes off c ref.1 idx d p
                (containerLength (fun v r => resolveLengthAux pre lookup limits bytes k v r)
                  (c :: ref.1 :: V) d p).2 with e | o
            · rfl
            · rw [hm] at hok
              cases o
              all_goals try rfl
              simp only at hok ⊢
              rw [ih _ (by omega) _ _ _ v (by omega) hok]
        · simp only [hg, ↓reduceIte]
      · rfl

/-! ## Lifting to `lengthOf` and the object parse -/

/-- At the call point, a resolver that fails makes the whole object parse fail with its
error. -/
theorem parseIndirectWith_err {limits : Limits} {bytes : ByteArray} {pos n : Nat} {d : Dict}
    {p : Nat} (hc : callPoint limits bytes pos = some (n, d, p)) (e : Error) :
    parseIndirectWith (fun _ _ _ => .error e) limits bytes pos = .error e := by
  unfold callPoint at hc
  unfold parseIndirectWith
  rcases hh : Core.ObjParse.parseHeader bytes pos with e' | ⟨n', g, q⟩
  · rw [hh] at hc; cases hc
  rw [hh] at hc
  simp only at hc ⊢
  unfold Core.ObjParse.parseIndirectBodyWith
  rcases ho : Core.ObjParse.parseObject limits bytes q with e' | ⟨o, r⟩
  · rw [ho] at hc; cases hc
  rw [ho] at hc
  simp only at hc ⊢
  rcases hk : Core.Lex.next bytes r with e' | _ | ⟨t, r2⟩
  · rw [hk] at hc; cases hc
  · rw [hk] at hc; cases hc
  rw [hk] at hc
  cases t with
  | keyword k => ?_
  | _ => simp at hc
  simp only at hc ⊢
  by_cases h1 : k = Core.ObjParse.kwEndobj
  · simp [h1] at hc
  by_cases h2 : k = Core.ObjParse.kwStream
  · simp only [h2, ↓reduceIte] at hc ⊢
    cases o with
    | dict d' => ?_
    | _ => simp at hc
    simp only at hc ⊢
    unfold Core.ObjParse.parseStreamBodyWith
    rcases hs : Core.ObjParse.streamDataStart bytes r2 with _ | st
    · rw [hs] at hc; cases hc
    · rfl
  · simp [h1, h2] at hc

/-- The object parse only depends on its resolver at the call point: replace it by the
constant resolver of that value. -/
theorem parseIndirectWith_const {lenF : Nat → Core.ObjParse.LengthResolver} {limits : Limits}
    {bytes : ByteArray} {pos n : Nat} {d : Dict} {p : Nat}
    (hc : callPoint limits bytes pos = some (n, d, p)) :
    parseIndirectWith lenF limits bytes pos =
      parseIndirectWith (fun _ _ _ => lenF n d p) limits bytes pos :=
  parseIndirectWith_congr (fun n' d' p' h => by rw [hc] at h; cases h; rfl)

/-- Resolvers that agree at the call point give agreeing object parses. -/
theorem parseIndirectWith_agree {lenF lenG : Nat → Core.ObjParse.LengthResolver}
    {limits : Limits} {bytes : ByteArray} {pos : Nat}
    (h : ∀ n d p, callPoint limits bytes pos = some (n, d, p) →
      Agree (lenF n d p) (lenG n d p)) :
    Agree (parseIndirectWith lenF limits bytes pos) (parseIndirectWith lenG limits bytes pos) := by
  rcases hc : callPoint limits bytes pos with _ | ⟨n, d, p⟩
  · exact Or.inl (parseIndirectWith_congr (fun n d p h' => by rw [hc] at h'; cases h'))
  · rw [parseIndirectWith_const hc, parseIndirectWith_const (lenF := lenG) hc]
    rcases h n d p hc with he | ⟨m, m', h1, h2⟩
    · rw [he]; exact Agree.refl _
    · rw [h1, h2, parseIndirectWith_err hc, parseIndirectWith_err hc]
      exact Or.inr ⟨m, m', rfl, rfl⟩

/-- `lengthOf` agrees for related lookups and fuels above `cnt S [self]`. -/
theorem lengthOf_agree {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (h : LookupRel l1 l2) (limits : Limits) (bytes : ByteArray) (S : List Nat)
    (hS : ∀ n off g, l1 n = some (.inUse off g) → n ∈ S) (f1 f2 self : Nat)
    (h1 : cnt S [self] < f1) (h2 : cnt S [self] < f2) (d : Dict) (at_ : Nat) :
    Agree (lengthOf pre l1 limits bytes f1 self d at_)
      (lengthOf pre l2 limits bytes f2 self d at_) := by
  unfold lengthOf lengthDict
  rcases hd : Dict.lookup d Core.ObjParse.nameLength with _ | o
  · exact Agree.refl _
  · cases o
    case ref m g =>
      simp only
      unfold resolveLength
      rcases resolve_agree (pre := pre) h limits bytes S hS f1 f2 [self] (m, g) h1 h2 with
        he | ⟨e1, e2, he1, he2⟩
      · rw [he]; exact Agree.refl _
      · rw [he1, he2]; exact Or.inr ⟨e1, e2, rfl, rfl⟩
    all_goals exact Agree.refl _

/-- `lengthOf` is **equal** for related lookups and fuels above `cnt S [self]` (task 12.7d). -/
theorem lengthOf_eq {pre : Core.Xref.ObjStm.Pre} {l1 l2 : Nat → Option XrefEntry}
    (h : LookupRel l1 l2) (limits : Limits) (bytes : ByteArray) (S : List Nat)
    (hS : ∀ n off g, l1 n = some (.inUse off g) → n ∈ S) (f1 f2 self : Nat)
    (h1 : cnt S [self] < f1) (h2 : cnt S [self] < f2) (d : Dict) (at_ : Nat) :
    lengthOf pre l1 limits bytes f1 self d at_ = lengthOf pre l2 limits bytes f2 self d at_ := by
  unfold lengthOf lengthDict
  rcases hd : Dict.lookup d Core.ObjParse.nameLength with _ | o
  · rfl
  · cases o
    case ref m g =>
      simp only
      unfold resolveLength
      rw [resolve_eq (pre := pre) h limits bytes S hS f1 f2 [self] (m, g) h1 h2]
    all_goals rfl

/-- **Fuel monotonicity of the object parse** (`Length.parseIndirectResolved`, any lookup): a
parse that succeeds with fuel `f` gives the same result with any fuel `f' ≥ f`. -/
theorem parseIndirectResolved_mono {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {f f' pos : Nat} {pre : Core.Xref.ObjStm.Pre}
    {r : IndirectObject × Nat} (hff : f ≤ f')
    (h : parseIndirectResolved lookup limits bytes f pos pre = .ok r) :
    parseIndirectResolved lookup limits bytes f' pos pre = .ok r := by
  rw [parseIndirectResolved_eq_with] at h ⊢
  rcases hc : callPoint limits bytes pos with _ | ⟨n, d, p⟩
  · rw [parseIndirectWith_congr (lenG := lengthOf pre lookup limits bytes f)
      (fun n d p h' => by rw [hc] at h'; cases h')]
    exact h
  · rw [parseIndirectWith_const hc] at h ⊢
    suffices hl : lengthOf pre lookup limits bytes f' n d p =
        lengthOf pre lookup limits bytes f n d p by
      rw [hl]; exact h
    rcases hle : lengthOf pre lookup limits bytes f n d p with e | x
    · rw [hle, parseIndirectWith_err hc] at h; cases h
    · unfold lengthOf lengthDict at hle ⊢
      rcases hd : Dict.lookup d Core.ObjParse.nameLength with _ | o
      · rw [hd] at hle; exact hle
      · cases o
        case ref m g =>
          rw [hd] at hle
          simp only at hle ⊢
          unfold resolveLength at hle ⊢
          rcases hr : (resolveLengthAux pre lookup limits bytes f [n] (m, g)).2 with e | len
          · rw [hr] at hle; cases hle
          · rw [resolveLengthAux_mono pre lookup limits bytes f f' [n] (m, g) len hff hr]
            exact hle
        all_goals (rw [hd] at hle; exact hle)

/-- **Fuel monotonicity of `ObjStm.fetchCompressed`** (any lookup): a fetch that succeeds with
fuel `f` gives the same result with any fuel `f' ≥ f`. -/
theorem fetchCompressed_mono {pre : Core.Xref.ObjStm.Pre} {lookup : Nat → Option XrefEntry}
    {limits : Limits} {bytes : ByteArray} {f f' num : Nat} {o : PdfObject} (hff : f ≤ f')
    (h : Core.Xref.ObjStm.fetchCompressed pre lookup limits bytes f num = .ok o) :
    Core.Xref.ObjStm.fetchCompressed pre lookup limits bytes f' num = .ok o := by
  unfold Core.Xref.ObjStm.fetchCompressed Core.Xref.ObjStm.fetchCompressedTrace at h ⊢
  rcases hl : lookup num with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, idx⟩)
  all_goals rw [hl] at h
  · exact h
  · exact h
  · exact h
  by_cases hcn : c = num
  · simp only [hcn, ↓reduceIte] at h ⊢; exact h
  simp only [hcn, ↓reduceIte] at h ⊢
  rcases hc : lookup c with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c', i'⟩)
  all_goals rw [hc] at h
  · exact h
  · exact h
  · by_cases hg : g = 0
    · simp only [hg, ↓reduceIte] at h ⊢
      rcases hp : parseIndirectResolved lookup limits bytes f off pre with e | r
      · rw [hp] at h; simp at h
      · rw [parseIndirectResolved_mono hff hp]
        rw [hp] at h; exact h
    · simp only [hg, ↓reduceIte] at h ⊢; exact h
  · exact h

/-! ## `getObject` on documents with related sections -/

/-- **`getObject` agrees** on two unencrypted documents over the same bytes whose lookups are
related by `LookupRel`, when both fuels (`objectCount`) exceed the number of in-use objects. -/
theorem getObject_agree {d d' : OpenDoc} (hb : d.bytes = d'.bytes) (hc : d.crypt = none)
    (hc' : d'.crypt = none) (h : LookupRel d.lookup d'.lookup) (S : List Nat)
    (hS : ∀ n off g, d.lookup n = some (.inUse off g) → n ∈ S)
    (hf : S.length < d.objectCount) (hf' : S.length < d'.objectCount) (limits : Limits)
    (num gen : Nat) : Agree (d.getObject limits num gen) (d'.getObject limits num gen) := by
  have hpre : d.pre = d'.pre := by unfold OpenDoc.pre; rw [hc, hc']
  unfold OpenDoc.getObject OpenDoc.getObjectTrace
  rcases h.cases num with ⟨off, g, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    simp only
    by_cases hg : g = gen
    · simp only [hg, ↓reduceIte, OpenDoc.decrypt, hc, hc']
      rw [parseIndirectResolved_eq_with, parseIndirectResolved_eq_with, ← hb, ← hpre]
      have ha := parseIndirectWith_agree
        (lenF := lengthOf d.pre d.lookup limits d.bytes d.objectCount)
        (lenG := lengthOf d.pre d'.lookup limits d.bytes d'.objectCount)
        (limits := limits) (bytes := d.bytes) (pos := off)
        (fun n dd p _ => lengthOf_agree h limits d.bytes S hS _ _ n
          (Nat.lt_of_le_of_lt (cnt_le S [n]) hf) (Nat.lt_of_le_of_lt (cnt_le S [n]) hf') dd p)
      rcases ha with he | ⟨m, m', e1, e2⟩
      · rw [he]; exact Agree.refl _
      · rw [e1, e2]; exact Or.inr ⟨m, m', rfl, rfl⟩
    · simp only [hg, ↓reduceIte]; exact Agree.refl _
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2] <;>
      exact Agree.refl _

/-- **`getObject` is equal** on two unencrypted documents over the same bytes whose lookups
are related by `LookupRel`, when both fuels (`objectCount`) exceed the number of in-use
objects (task 12.7d: the exact form of `getObject_agree`). -/
theorem getObject_eq {d d' : OpenDoc} (hb : d.bytes = d'.bytes) (hc : d.crypt = none)
    (hc' : d'.crypt = none) (h : LookupRel d.lookup d'.lookup) (S : List Nat)
    (hS : ∀ n off g, d.lookup n = some (.inUse off g) → n ∈ S)
    (hf : S.length < d.objectCount) (hf' : S.length < d'.objectCount) (limits : Limits)
    (num gen : Nat) : d.getObject limits num gen = d'.getObject limits num gen := by
  have hpre : d.pre = d'.pre := by unfold OpenDoc.pre; rw [hc, hc']
  unfold OpenDoc.getObject OpenDoc.getObjectTrace
  rcases h.cases num with ⟨off, g, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    simp only
    by_cases hg : g = gen
    · simp only [hg, ↓reduceIte, OpenDoc.decrypt, hc, hc']
      rw [parseIndirectResolved_eq_with, parseIndirectResolved_eq_with, ← hb, ← hpre]
      rw [parseIndirectWith_congr (lenF := lengthOf d.pre d.lookup limits d.bytes d.objectCount)
        (lenG := lengthOf d.pre d'.lookup limits d.bytes d'.objectCount)
        (fun n dd p _ => lengthOf_eq h limits d.bytes S hS _ _ n
          (Nat.lt_of_le_of_lt (cnt_le S [n]) hf) (Nat.lt_of_le_of_lt (cnt_le S [n]) hf') dd p)]
    · simp only [hg, ↓reduceIte]
  · rcases h1 with h1 | ⟨a, g, h1⟩ <;> rcases h2 with h2 | ⟨a', g', h2⟩ <;> rw [h1, h2]

/-! ## The hypothesis with free entries -/

/-- Condition H2' on one strict entry: a free entry is allowed for **every** object number;
a compressed entry is not; an in-use entry points at the newest scan hit of its number with
the same generation. -/
def EntryOkFree (raw : List (Nat × Nat × Nat)) : Nat × XrefEntry → Prop
  | (_, .free _ _) => True
  | (_, .compressed _ _) => False
  | (n, .inUse off g) => 1 ≤ n ∧ newestHit raw n = some (n, g, off)

/-- `EntryOkFree` is decidable. -/
instance (raw : List (Nat × Nat × Nat)) : DecidablePred (EntryOkFree raw) := fun x =>
  match x with
  | (_, .free _ _) => inferInstanceAs (Decidable True)
  | (_, .compressed _ _) => inferInstanceAs (Decidable False)
  | (n, .inUse off g) =>
    inferInstanceAs (Decidable (1 ≤ n ∧ newestHit raw n = some (n, g, off)))

/-- **The C4 hypothesis with free entries**: `Hyp` with H2 relaxed to `EntryOkFree` (H1, H3–H6
unchanged). A free entry `n ≥ 1` can have no scan hit: by H3 every hit has an in-use entry,
and the section has one entry per number. -/
def HypFree (limits : Limits) (bytes : ByteArray) (d : OpenDoc) : Prop :=
  (0, XrefEntry.free 0 65535) ∈ d.xref.entries ∧
  (∀ x ∈ d.xref.entries, EntryOkFree (hits limits bytes) x) ∧
  (∀ x ∈ hits limits bytes, ∃ e ∈ d.xref.entries, e.1 = x.1 ∧ isInUse e.2 = true) ∧
  (newestHits (hits limits bytes)).length ≤ limits.maxObjects ∧
  trailerOk limits bytes d = true ∧
  d.crypt.isNone = true

/-- `HypFree` is decidable. -/
instance instDecidableHypFree (limits : Limits) (bytes : ByteArray) (d : OpenDoc) :
    Decidable (HypFree limits bytes d) := by
  unfold HypFree; infer_instance

/-- **The checker**: the strict path succeeds and its document satisfies `HypFree`. -/
def checkFree (limits : Limits) (bytes : ByteArray) : Bool :=
  match strictOpen limits bytes with
  | .ok d => decide (HypFree limits bytes d)
  | .error _ => false

/-- `HypFree` is weaker than `Hyp`. -/
theorem Hyp.toFree {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : Hyp limits bytes d) : HypFree limits bytes d := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, fun x hx => ?_, h3, h4, h5, h6⟩
  have := h2 x hx
  obtain ⟨n, e⟩ := x
  cases e with
  | free a g => trivial
  | compressed _ _ => exact this.elim
  | inUse off g => exact this

/-- Under `HypFree`, the strict and the repaired sections have the same in-use entries. -/
theorem inUse_mem_iff {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : HypFree limits bytes d) (n off g : Nat) :
    (n, XrefEntry.inUse off g) ∈ d.xref.entries ↔
      (n, XrefEntry.inUse off g) ∈ (scanSection limits bytes).entries := by
  obtain ⟨-, hent, hcov, hcap, -, -⟩ := h
  simp only [scanSection, toEntries, scanObjects_eq limits bytes hcap, List.mem_cons,
    List.mem_map]
  constructor
  · intro hx
    obtain ⟨h1, hn⟩ := hent _ hx
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
        have hok := hent _ he
        simp only at hk
        subst hk
        obtain ⟨-, hn⟩ := hok
        rw [hy] at hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨-, rfl, rfl⟩ := hn
        exact he

/-- The repaired section has no compressed entry. -/
theorem scanSection_no_compressed (limits : Limits) (bytes : ByteArray) (n c i : Nat) :
    (n, XrefEntry.compressed c i) ∉ (scanSection limits bytes).entries := by
  simp [scanSection, toEntries]

/-- Lookups with the same in-use entries and no compressed entry are related. -/
theorem lookupRel_of {l1 l2 : Nat → Option XrefEntry}
    (hin : ∀ n off g, l1 n = some (.inUse off g) ↔ l2 n = some (.inUse off g))
    (nc1 : ∀ n c i, l1 n ≠ some (.compressed c i))
    (nc2 : ∀ n c i, l2 n ≠ some (.compressed c i)) :
    LookupRel l1 l2 := by
  refine ⟨fun n => ?_, nc1, nc2⟩
  have hi := hin n
  have c1 := nc1 n
  have c2 := nc2 n
  rcases h1 : l1 n with _ | (⟨a, g⟩ | ⟨off, g⟩ | ⟨c, i⟩) <;>
    rcases h2 : l2 n with _ | (⟨a', g'⟩ | ⟨off', g'⟩ | ⟨c', i'⟩) <;>
    simp_all [strip]

/-! ## C4 with free entries -/

/-- `validate` succeeds on a document with the same `/Root` and agreeing `getObject`. -/
theorem validate_agree {limits : Limits} {d₁ d₂ : OpenDoc}
    (hr : d₁.trailer.root? = d₂.trailer.root?)
    (hg : ∀ num gen, Agree (d₂.getObject limits num gen) (d₁.getObject limits num gen))
    (h : validate limits d₁ = .ok d₁) : validate limits d₂ = .ok d₂ := by
  unfold validate at h ⊢
  rw [← hr]
  split at h
  · cases h
  · rename_i n g _
    split at h
    · cases h
    · rename_i heq
      rw [((hg n g).ok_iff _).mpr heq]
    all_goals cases h

/-- **C4 with free entries, exact form (repair conservativity; task 12.7d).** If the strict
path opens `bytes` as `d` and `HypFree limits bytes d` holds (free entries allowed for every
object number), the repair path also succeeds; its document is flagged `repaired`, has the
same bytes, the same in-use entries and the same `/Root` as `d`, and for **every** `num gen`
its `getObject` is **equal** to `d`'s. The sections themselves may differ: free entries
`n ≥ 1` are absent from the repaired one. -/
theorem c4_free_eq {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : HypFree limits bytes d) :
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  have hin := inUse_mem_iff hh
  obtain ⟨hz, hent, -, -, htr, hpl⟩ := hh
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
    have hc : d.crypt = none := Option.isNone_iff_eq_none.mp hpl
    have hnd1 := d.xref.keys_nodup
    have hnd2 := (scanSection limits bytes).keys_nodup
    have hl1 : ∀ m, d.lookup m = Core.Xref.Chain.lookupEntry m d.xref.entries :=
      WritePrefix.lookup_eq d
    have hl2 : ∀ m, d'.lookup m =
        Core.Xref.Chain.lookupEntry m (scanSection limits bytes).entries :=
      WritePrefix.lookup_eq d'
    have hrel : LookupRel d.lookup d'.lookup := lookupRel_of
      (fun n off g => by
        rw [hl1, hl2, Unambiguous.lookupEntry_eq_some_iff hnd1,
          Unambiguous.lookupEntry_eq_some_iff hnd2]
        exact hin n off g)
      (fun n c i h => by
        rw [hl1, Unambiguous.lookupEntry_eq_some_iff hnd1] at h
        exact hent _ h)
      (fun n c i h => by
        rw [hl2, Unambiguous.lookupEntry_eq_some_iff hnd2] at h
        exact scanSection_no_compressed _ _ _ _ _ h)
    let S := (d.xref.entries.filter (fun x => isInUse x.2)).map (·.1)
    let S' := ((scanSection limits bytes).entries.filter (fun x => isInUse x.2)).map (·.1)
    have hS : ∀ n off g, d.lookup n = some (.inUse off g) → n ∈ S := by
      intro n off g h
      rw [hl1, Unambiguous.lookupEntry_eq_some_iff hnd1] at h
      exact List.mem_map.mpr ⟨(n, .inUse off g), List.mem_filter.mpr ⟨h, rfl⟩, rfl⟩
    have hf : S.length < d.objectCount := by
      simp only [S, List.length_map, OpenDoc.objectCount, d.index_eq, List.size_toArray]
      exact List.length_filter_lt_length_iff_exists.mpr ⟨_, hz, by simp [isInUse]⟩
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
      (List.Sublist.map (·.1) (List.filter_sublist (l := d.xref.entries))).nodup hnd1
    have hf' : S.length < d'.objectCount := by
      have h1 := hSnd.length_le_of_subset hSS
      have h2 : S'.length < (scanSection limits bytes).entries.length := by
        simp only [S', List.length_map]
        exact List.length_filter_lt_length_iff_exists.mpr
          ⟨(0, .free 0 65535), by simp [scanSection], by simp [isInUse]⟩
      simp only [d', OpenDoc.objectCount, OpenDoc.mk', List.size_toArray]
      omega
    have hg : ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen :=
      fun num gen =>
        (getObject_eq (by rw [hbytes]; rfl) hc rfl hrel S hS hf hf' limits num gen).symm
    have hv : validate limits d' = .ok d' :=
      validate_agree hroot.symm (fun num gen => Or.inl (hg num gen)) hval
    refine ⟨d', ?_, rfl, by rw [hbytes]; rfl, fun n off g => (hin n off g).symm, hroot, hg⟩
    unfold repairOpen
    rw [hrep]
    simp only
    rw [withCrypt_plain (d := d') henc]
    exact hv
  · cases htr

/-- **C4 with free entries (repair conservativity).** `c4_free_eq` with its last conjunct
weakened to `Agree` (equal results, or both `malformed 0` errors; in particular the same
successes, `Agree.ok_iff`). Kept with this statement for its users; since task 12.7d the
`Agree` is always the left disjunct (equality). -/
theorem c4_free {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (hs : strictOpen limits bytes = .ok d) (hh : HypFree limits bytes d) :
    ∃ d', repairOpen limits bytes = .ok d' ∧ d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, Agree (d'.getObject limits num gen) (d.getObject limits num gen) := by
  obtain ⟨d', h1, h2, h3, h4, h5, h6⟩ := c4_free_eq hs hh
  exact ⟨d', h1, h2, h3, h4, h5, fun num gen => Or.inl (h6 num gen)⟩

/-- **C4 with free entries, exact form, from the checker** (task 12.7d). -/
theorem c4_free_eq_check {limits : Limits} {bytes : ByteArray}
    (hc : checkFree limits bytes = true) :
    ∃ d d', strictOpen limits bytes = .ok d ∧ repairOpen limits bytes = .ok d' ∧
      d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, d'.getObject limits num gen = d.getObject limits num gen := by
  unfold checkFree at hc
  split at hc
  · rename_i d hs
    obtain ⟨d', h⟩ := c4_free_eq hs (of_decide_eq_true hc)
    exact ⟨d, d', hs, h⟩
  · cases hc

/-- **C4 with free entries, from the checker.** -/
theorem c4_free_check {limits : Limits} {bytes : ByteArray} (hc : checkFree limits bytes = true) :
    ∃ d d', strictOpen limits bytes = .ok d ∧ repairOpen limits bytes = .ok d' ∧
      d'.repaired = true ∧ d'.bytes = d.bytes ∧
      (∀ n off g, (n, XrefEntry.inUse off g) ∈ d'.xref.entries ↔
        (n, XrefEntry.inUse off g) ∈ d.xref.entries) ∧
      d'.trailer.root? = d.trailer.root? ∧
      ∀ num gen, Agree (d'.getObject limits num gen) (d.getObject limits num gen) := by
  unfold checkFree at hc
  split at hc
  · rename_i d hs
    obtain ⟨d', h⟩ := c4_free hs (of_decide_eq_true hc)
    exact ⟨d, d', hs, h⟩
  · cases hc

/-! ## Fixtures -/

/-- A strictly openable file with a **free entry for object 4** (`0000000000 00001 f`, a
deleted object) and a content stream (object 5) whose `/Length` is the indirect `6 0 R`, so
`getObject 5 0` runs `/Length` resolution with the section length as fuel (7 strictly, 6
after repair). -/
def freeEntryBytes : ByteArray :=
  "%PDF-1.7\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n3 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 5 0 R >>\nendobj\n5 0 obj\n<< /Length 6 0 R >>\nstream\nBT ET\nendstream\nendobj\n6 0 obj\n5\nendobj\nxref\n0 7\n0000000000 65535 f \n0000000009 00000 n \n0000000058 00000 n \n0000000115 00000 n \n0000000000 00001 f \n0000000202 00000 n \n0000000260 00000 n \ntrailer\n<< /Size 7 /Root 1 0 R >>\nstartxref\n277\n%%EOF\n".toUTF8

/-- `freeEntryBytes` with object 5's `/Length` pointing at the free object 4 (`4 0 R`):
both paths reject the stream, with different `malformed 0` messages. -/
def freeLengthBytes : ByteArray :=
  "%PDF-1.7\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n3 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 5 0 R >>\nendobj\n5 0 obj\n<< /Length 4 0 R >>\nstream\nBT ET\nendstream\nendobj\n6 0 obj\n5\nendobj\nxref\n0 7\n0000000000 65535 f \n0000000009 00000 n \n0000000058 00000 n \n0000000115 00000 n \n0000000000 00001 f \n0000000202 00000 n \n0000000260 00000 n \ntrailer\n<< /Size 7 /Root 1 0 R >>\nstartxref\n277\n%%EOF\n".toUTF8

/-- Test helper: an error's constructor, offset and message (`"ok"` for a success). -/
def errText : Except Error IndirectBody → String
  | .error (.malformed off m) => s!"malformed {off}: {m}"
  | .error _ => "other error"
  | .ok _ => "ok"

/-- Test helper: `getObject num 0` on the strict and on the repair path, as error texts. -/
def bothErr (bytes : ByteArray) (num : Nat) : Option (String × String) :=
  match strictOpen Limits.default bytes, repairOpen Limits.default bytes with
  | .ok d, .ok d' => some (errText (d.getObject Limits.default num 0),
      errText (d'.getObject Limits.default num 0))
  | _, _ => none

/-- Test helper: the section lengths (the `/Length` fuel) on the strict and repair paths. -/
def counts (bytes : ByteArray) : Option (Nat × Nat) :=
  match strictOpen Limits.default bytes, repairOpen Limits.default bytes with
  | .ok d, .ok d' => some (d.objectCount, d'.objectCount)
  | _, _ => none

-- A free entry `n ≥ 1`: 12.7's checker rejects the file, `checkFree` accepts it (non-vacuity).
#guard check Limits.default freeEntryBytes = false
#guard checkFree Limits.default freeEntryBytes = true
#guard (match strictOpen Limits.default freeEntryBytes with
  | .ok d => d.lookup 4 == some (.free 0 1)
  | .error _ => false)
-- The sections differ in length (the `/Length` fuel) and `getObject` still agrees exactly.
#guard counts freeEntryBytes = some (7, 6)
#guard both freeEntryBytes 1 = some ("dict", "dict")
#guard both freeEntryBytes 4 = some ("null", "null")
#guard both freeEntryBytes 5 = some ("other", "other")
#guard bothErr freeEntryBytes 5 = some ("ok", "ok")
#guard both freeEntryBytes 6 = some ("other", "other")

-- A `/Length` naming a free object (strict path) or a missing one (repair path) fails with
-- the same `malformed 0` error since task 12.7d, so `getObject` is equal (`c4_free_eq`).
-- Before 12.7d the messages differed ("free object 4" against "not in the xref").
#guard checkFree Limits.default freeLengthBytes = true
#guard bothErr freeLengthBytes 5 = some (
  "malformed 0: /Length refers to object 4, which is free or not in the xref",
  "malformed 0: /Length refers to object 4, which is free or not in the xref")
#guard (match strictOpen Limits.default freeLengthBytes,
    repairOpen Limits.default freeLengthBytes with
  | .ok d, .ok d' => (List.range 8).all fun n =>
      errText (d.getObject Limits.default n 0) == errText (d'.getObject Limits.default n 0)
  | _, _ => false)

-- 12.7's fixtures: `repair-diff.pdf` still fails (H2' on object 3, H3 on object 2), and the
-- corrected file passes (`Hyp.toFree`).
#guard checkFree Limits.default repairDiffBytes = false
#guard checkFree Limits.default repairFixedBytes = true

end SafePdf.Spec.RepairAgreeFree
