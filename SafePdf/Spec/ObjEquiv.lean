import SafePdf.Core.ObjParse
import SafePdf.Spec.Object
import SafePdf.Spec.LexEquiv

/-!
# Object-parser equivalence: efficient parser = grammar spec (Plan.md §4 C5, §5.1 step 3)

Task 1.8. The efficient object parser `SafePdf.Core.ObjParse.parseObj` (bytes, positions, lazy
lexing with `Core.Lex.next`) agrees with the executable grammar spec
`SafePdf.Spec.Object.parse` (a token list), hence with the relation `Parses`
(`Spec.Object.parse_eq_ok_iff`).

## Statement

The core parser lexes lazily: it never looks at bytes after the object's last token (plus the
two-token reference lookahead). The spec parses a token list. The theorems therefore assume the
remainder of the input lexes:

* `LexFrom bytes p ps` — lexing with `Core.Lex.next` from `p` yields the tokens of `ps`, each with
  its end position, then end of input. `lexFrom_of_lexAll` builds it from
  `Spec.Lex.lexAll (bytes.data.toList.drop p) = .ok ts` (with `ps.map Prod.fst = ts`).
* `parseObj_ok_iff` / `parseObj_error_iff` — on a positioned stream: success with `(o, r)` iff the
  spec succeeds with `o`, leaving a suffix `rs` of the stream (`ps = pre ++ rs`), and
  `r = endAfter pos pre` (end of the last consumed token); failure iff failure.
* `parseObj_ok_iff_lexAll` / `parseObj_error_iff_lexAll` — the same with the spec lexer only:
  `r = bytes.size - l.length`, where `l` is the input after the consumed spec tokens
  (`dropToks`).
* `parseObj_of_spec_full` (for task 1.7) — if all of `bytes` lexes to `ts` and `parse F ts`
  consumes all of `ts`, then `parseObj F bytes 0 = .ok (o, bytes.size - l.length)` with `l`
  whitespace/comments only; `parseObj_of_spec_full_size` gives `bytes.size` exactly when no
  trailing whitespace/comment follows the last token.

## Proof

`Agree R q ps x y` relates an implementation result (position) and a spec result (token rest):
both fail, or both succeed with `R`-related payloads and the spec rest is a suffix of `ps` whose
start is the implementation position. One induction on the number of tokens `n` proves agreement
for `parseObjTok`/`parse` (`ObjAgreeN`), `parseArray`/`parseItems` (`ArrAgreeN`, accumulator
`acc.reverse ++ ·`) and `parseDict`/`parseEntries` (`DictAgreeN`, `hasKey acc ↔ · ∈ seen`):
objects at `n` use containers at `n` (the opening token is not in the stream after it);
containers at `n + 1` use objects and containers at `n`. The loops are unfolded through
equation lemmas (`parseArray_some`, `parseDict_key_some`, …) instead of `split` on their dependent
`match _h : Lex.next …`; the dead progress guards are discharged by `parseObjTok_pos` and
`parse_length_lt`. Error offsets and messages are not compared (spec errors carry none).
-/

namespace SafePdf.Spec.ObjEquiv

open SafePdf
open SafePdf.Spec.LexEquiv (restAt)

/-! ## Positioned token streams -/

/-- `LexFrom bytes p ps`: lexing with `Core.Lex.next` from `p` yields exactly the tokens of `ps`,
each paired with the position just after it, and then end of input. -/
inductive LexFrom (bytes : ByteArray) : Nat → List (Token × Nat) → Prop
  /-- End of input: only whitespace and comments remain. -/
  | nil {p : Nat} : Core.Lex.next bytes p = .ok none → LexFrom bytes p []
  /-- One more token `t` ending at `q`. -/
  | cons {p q : Nat} {t : Token} {ps : List (Token × Nat)} :
      Core.Lex.next bytes p = .ok (some (t, q)) → LexFrom bytes q ps →
      LexFrom bytes p ((t, q) :: ps)

/-- The position reached from `q` after the tokens `pre`: the end of the last of them, or `q`
when `pre` is empty. -/
def endAfter : Nat → List (Token × Nat) → Nat
  | q, [] => q
  | _, (_, q') :: pre => endAfter q' pre

/-- `endAfter` over a concatenation. -/
theorem endAfter_append (q : Nat) (pre pre' : List (Token × Nat)) :
    endAfter q (pre ++ pre') = endAfter (endAfter q pre) pre' := by
  induction pre generalizing q with
  | nil => rfl
  | cons x pre ih => obtain ⟨t, q'⟩ := x; exact ih q'

/-- A stream that lexes from `q` lexes, after its prefix `pre`, from `endAfter q pre`. -/
theorem LexFrom.drop {bytes : ByteArray} {q : Nat} {pre rs : List (Token × Nat)}
    (h : LexFrom bytes q (pre ++ rs)) : LexFrom bytes (endAfter q pre) rs := by
  induction pre generalizing q with
  | nil => exact h
  | cons x pre ih =>
    obtain ⟨t, q'⟩ := x
    cases h with
    | cons _ h' => exact ih h'

/-- **Agreement** of an implementation result (position) with a spec result (rest of the token
list) over the positioned stream `ps` read from `q`: both fail, or both succeed with payloads
related by `R`, and the spec rest is a suffix `rs` of the stream whose start is the implementation
position. -/
def Agree {α β : Type} (R : α → β → Prop) (q : Nat) (ps : List (Token × Nat)) :
    Except Error (α × Nat) → Except Spec.Object.Err (β × List Token) → Prop
  | .ok (a, r), .ok (b, rest) =>
    R a b ∧ ∃ pre rs, ps = pre ++ rs ∧ rest = rs.map Prod.fst ∧ r = endAfter q pre
  | .error _, .error _ => True
  | .ok _, .error _ => False
  | .error _, .ok _ => False

/-! ## References (G1) -/

/-- The keyword constants of the two parsers coincide. -/
theorem kwR_eq : Core.ObjParse.kwR = Spec.Object.kwR := rfl

/-- `keywordObj` of the implementation is that of the spec. -/
theorem keywordObj_eq (kw : List UInt8) :
    Core.ObjParse.keywordObj kw = Spec.Object.keywordObj kw := rfl

/-- `refOk` decides `RefOk`. -/
theorem refOk_iff (n g : Int) : Core.ObjParse.refOk n g = true ↔ Spec.Object.RefOk n g := by
  simp [Core.ObjParse.refOk, Spec.Object.RefOk, and_assoc]

/-- `parseIntTail` agrees with `parseIntOrRef` (G1). -/
theorem parseIntTail_agree (bytes : ByteArray) (pos : Nat) (n : Int) (q : Nat)
    (ps : List (Token × Nat)) (hl : LexFrom bytes q ps) :
    Agree (· = ·) q ps (Core.ObjParse.parseIntTail bytes pos n q)
      (Spec.Object.parseIntOrRef n (ps.map Prod.fst)) := by
  have intOk : Agree (· = ·) q ps (.ok (PdfObject.int n, q))
      (.ok (PdfObject.int n, ps.map Prod.fst)) :=
    ⟨rfl, [], ps, rfl, rfl, rfl⟩
  cases hl with
  | nil h =>
    simp only [Core.ObjParse.parseIntTail, h, List.map_nil]
    exact intOk
  | @cons _ q1 t1 ps1 h1 hl1 =>
    cases t1 with
    | int g =>
      cases hl1 with
      | nil h2 =>
        simp only [Core.ObjParse.parseIntTail, h1, h2]
        exact intOk
      | @cons _ q2 t2 ps2 h2 hl2 =>
        cases t2 with
        | keyword kw =>
          by_cases hk : kw = Spec.Object.kwR
          · subst hk
            by_cases hr : Spec.Object.RefOk n g
            · have hr' : Core.ObjParse.refOk n g = true := (refOk_iff n g).2 hr
              simp only [Core.ObjParse.parseIntTail, h1, h2, kwR_eq, hr', ↓reduceIte,
                List.map_cons, Spec.Object.parseIntOrRef, hr]
              exact ⟨rfl, [(.int g, q1), (.keyword Spec.Object.kwR, q2)], ps2, rfl, rfl, rfl⟩
            · have hr' : Core.ObjParse.refOk n g = false := by
                cases h : Core.ObjParse.refOk n g
                · rfl
                · exact absurd ((refOk_iff n g).1 h) hr
              simp only [Core.ObjParse.parseIntTail, h1, h2, kwR_eq, hr', ↓reduceIte,
                List.map_cons, Spec.Object.parseIntOrRef, hr]
              trivial
          · have hk' : ¬ kw = Core.ObjParse.kwR := by rw [kwR_eq]; exact hk
            simp only [Core.ObjParse.parseIntTail, h1, h2, hk', ↓reduceIte, List.map_cons,
              Spec.Object.parseIntOrRef, hk]
            exact intOk
        | _ =>
          simp only [Core.ObjParse.parseIntTail, h1, h2, List.map_cons,
            Spec.Object.parseIntOrRef]
          exact intOk
    | _ =>
      simp only [Core.ObjParse.parseIntTail, h1, List.map_cons, Spec.Object.parseIntOrRef]
      exact intOk

/-! ## Unfolding the implementation loops -/

open Core.ObjParse in
/-- `parseArray` at end of input fails. -/
theorem parseArray_none {fuel : Nat} {bytes : ByteArray} {pos : Nat} {acc : List PdfObject}
    (h : Core.Lex.next bytes pos = .ok none) : ∃ e, parseArray fuel bytes pos acc = .error e := by
  rw [parseArray]; split <;> simp_all

open Core.ObjParse in
/-- `parseArray` after a token `t` ending at `q`. -/
theorem parseArray_some {fuel : Nat} {bytes : ByteArray} {pos q : Nat} {t : Token}
    {acc : List PdfObject} (h : Core.Lex.next bytes pos = .ok (some (t, q))) :
    parseArray fuel bytes pos acc =
      if t = .arrayClose then .ok (acc.reverse, q)
      else
        match parseObjTok fuel bytes pos t q with
        | .error e => .error e
        | .ok (o, r) =>
          if pos < r then parseArray fuel bytes r (o :: acc)
          else .error (.malformed pos "internal: no progress") := by
  rw [parseArray]
  split
  · simp_all
  · simp_all
  · rename_i t' q' heq
    rw [h] at heq
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl

open Core.ObjParse in
/-- `parseDict` at end of input fails. -/
theorem parseDict_none {fuel : Nat} {bytes : ByteArray} {pos : Nat}
    {acc : List (Name × PdfObject)} {sn : KeySet} (h : Core.Lex.next bytes pos = .ok none) :
    ∃ e, parseDict fuel bytes pos acc sn = .error e := by
  rw [parseDict]; split <;> simp_all

open Core.ObjParse in
/-- `parseDict` at `>>`. -/
theorem parseDict_close {fuel : Nat} {bytes : ByteArray} {pos q : Nat}
    {acc : List (Name × PdfObject)} {sn : KeySet}
    (h : Core.Lex.next bytes pos = .ok (some (.dictClose, q))) :
    parseDict fuel bytes pos acc sn = .ok (acc.reverse, q) := by
  rw [parseDict]
  split
  · simp_all
  · simp_all
  · rename_i t' q' heq
    rw [h] at heq
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl

open Core.ObjParse in
/-- `parseDict` at a token that is neither `>>` nor a name fails. -/
theorem parseDict_other {fuel : Nat} {bytes : ByteArray} {pos q : Nat} {t : Token}
    {acc : List (Name × PdfObject)} {sn : KeySet}
    (h : Core.Lex.next bytes pos = .ok (some (t, q)))
    (h1 : t ≠ .dictClose) (h2 : ∀ k, t ≠ .name k) :
    ∃ e, parseDict fuel bytes pos acc sn = .error e := by
  rw [parseDict]
  split
  · simp
  · simp
  · rename_i t' q' heq
    rw [h] at heq
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split
    · exact absurd rfl h1
    · exact absurd rfl (h2 _)
    · simp

open Core.ObjParse in
/-- `parseDict` at a name key: a duplicate fails. -/
theorem parseDict_dup {fuel : Nat} {bytes : ByteArray} {pos q : Nat} {k : Name}
    {acc : List (Name × PdfObject)} {sn : KeySet}
    (h : Core.Lex.next bytes pos = .ok (some (.name k, q)))
    (hk : sn.contains k.bytes = true) : ∃ e, parseDict fuel bytes pos acc sn = .error e := by
  rw [parseDict]
  split
  · simp
  · simp
  · rename_i t' q' heq
    rw [h] at heq
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [hk]

open Core.ObjParse in
/-- `parseDict` at a fresh name key followed by end of input fails. -/
theorem parseDict_key_none {fuel : Nat} {bytes : ByteArray} {pos q : Nat} {k : Name}
    {acc : List (Name × PdfObject)} {sn : KeySet}
    (h : Core.Lex.next bytes pos = .ok (some (.name k, q)))
    (hk : sn.contains k.bytes = false) (h2 : Core.Lex.next bytes q = .ok none) :
    ∃ e, parseDict fuel bytes pos acc sn = .error e := by
  rw [parseDict]
  split
  · simp
  · simp
  · rename_i t' q' heq
    rw [h] at heq
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hk, Bool.false_eq_true, ↓reduceIte]
    split <;> simp_all

open Core.ObjParse in
/-- `parseDict` at a fresh name key followed by the value's first token `t2` ending at `q2`. -/
theorem parseDict_key_some {fuel : Nat} {bytes : ByteArray} {pos q q2 : Nat} {k : Name}
    {t2 : Token} {acc : List (Name × PdfObject)} {sn : KeySet}
    (h : Core.Lex.next bytes pos = .ok (some (.name k, q)))
    (hk : sn.contains k.bytes = false) (h2 : Core.Lex.next bytes q = .ok (some (t2, q2))) :
    parseDict fuel bytes pos acc sn =
      match parseObjTok fuel bytes q t2 q2 with
      | .error e => .error e
      | .ok (v, r) =>
        if pos < r then parseDict fuel bytes r ((k, v) :: acc) (sn.insert k.bytes)
        else .error (.malformed pos "internal: no progress") := by
  rw [parseDict]
  split
  · simp_all
  · simp_all
  · rename_i t' q' heq
    rw [h] at heq
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hk, Bool.false_eq_true, ↓reduceIte]
    split
    · simp_all
    · simp_all
    · rename_i t'' q'' heq2
      rw [h2] at heq2
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at heq2
      obtain ⟨rfl, rfl⟩ := heq2
      rfl

/-! ## The induction -/

open Core.ObjParse Spec.Object

/-- Agreement of `parseObjTok` with `parse` when at most `n` tokens follow the first one. -/
def ObjAgreeN (bytes : ByteArray) (n : Nat) : Prop :=
  ∀ fuel pos t q ps, LexFrom bytes q ps → ps.length ≤ n → q ≤ bytes.size →
    Agree (· = ·) q ps (parseObjTok fuel bytes pos t q) (parse fuel (t :: ps.map Prod.fst))

/-- Agreement of `parseArray` with `parseItems` on streams of at most `n` tokens. -/
def ArrAgreeN (bytes : ByteArray) (n : Nat) : Prop :=
  ∀ fuel pos ps acc, LexFrom bytes pos ps → ps.length ≤ n →
    Agree (fun a b => a = acc.reverse ++ b) pos ps (parseArray fuel bytes pos acc)
      (parseItems fuel (ps.map Prod.fst))

/-- Agreement of `parseDict` with `parseEntries` on streams of at most `n` tokens, when the
accumulator's keys are the keys seen. -/
def DictAgreeN (bytes : ByteArray) (n : Nat) : Prop :=
  ∀ fuel pos ps acc seen sn, LexFrom bytes pos ps → ps.length ≤ n →
    (∀ k, hasKey acc k = true ↔ k ∈ seen) → SeenOf sn acc →
    Agree (fun a b => a = acc.reverse ++ b) pos ps (parseDict fuel bytes pos acc sn)
      (parseEntries fuel seen (ps.map Prod.fst))

/-- Objects agree given that arrays and dictionaries agree on the same streams. -/
theorem obj_step (bytes : ByteArray) (n : Nat) (hA : ArrAgreeN bytes n)
    (hD : DictAgreeN bytes n) : ObjAgreeN bytes n := by
  intro fuel pos t q ps hl hn hq
  have scalar : ∀ o : PdfObject, Agree (· = ·) q ps (.ok (o, q)) (.ok (o, ps.map Prod.fst)) :=
    fun o => ⟨rfl, [], ps, rfl, rfl, rfl⟩
  cases t with
  | int i =>
    rw [parseObjTok]; simp only [parse]
    exact parseIntTail_agree bytes pos i q ps hl
  | real d => rw [parseObjTok]; simp only [parse]; exact scalar _
  | litString s => rw [parseObjTok]; simp only [parse]; exact scalar _
  | hexString s => rw [parseObjTok]; simp only [parse]; exact scalar _
  | name k => rw [parseObjTok]; simp only [parse]; exact scalar _
  | keyword kw =>
    rw [parseObjTok]; simp only [parse, keywordObj_eq]
    cases Spec.Object.keywordObj kw with
    | none => trivial
    | some o => exact scalar o
  | arrayOpen =>
    cases fuel with
    | zero => rw [parseObjTok]; simp only [parse]; trivial
    | succ f =>
      rw [parseObjTok]; simp only [parse]
      have h := hA f q ps [] hl hn
      cases hX : parseArray f bytes q [] with
      | error e =>
        cases hY : parseItems f (ps.map Prod.fst) with
        | error e' => trivial
        | ok y => rw [hX, hY] at h; exact h.elim
      | ok x =>
        cases hY : parseItems f (ps.map Prod.fst) with
        | error e' => rw [hX, hY] at h; exact h.elim
        | ok y =>
          rw [hX, hY] at h
          obtain ⟨xs, r⟩ := x
          obtain ⟨ys, rest⟩ := y
          obtain ⟨h1, h2⟩ := h
          simp only [List.reverse_nil, List.nil_append] at h1
          subst h1
          exact ⟨rfl, h2⟩
  | dictOpen =>
    cases fuel with
    | zero => rw [parseObjTok]; simp only [parse]; trivial
    | succ f =>
      rw [parseObjTok]; simp only [parse]
      have h := hD f q ps [] [] ∅ hl hn (by simp [hasKey]) seenOf_nil
      cases hX : parseDict f bytes q [] ∅ with
      | error e =>
        cases hY : parseEntries f [] (ps.map Prod.fst) with
        | error e' => trivial
        | ok y => rw [hX, hY] at h; exact h.elim
      | ok x =>
        cases hY : parseEntries f [] (ps.map Prod.fst) with
        | error e' => rw [hX, hY] at h; exact h.elim
        | ok y =>
          rw [hX, hY] at h
          obtain ⟨xs, r⟩ := x
          obtain ⟨ys, rest⟩ := y
          obtain ⟨h1, h2⟩ := h
          simp only [List.reverse_nil, List.nil_append] at h1
          subst h1
          exact ⟨rfl, h2⟩
  | arrayClose => rw [parseObjTok]; simp only [parse]; trivial
  | dictClose => rw [parseObjTok]; simp only [parse]; trivial
  | braceOpen => rw [parseObjTok]; simp only [parse]; trivial
  | braceClose => rw [parseObjTok]; simp only [parse]; trivial

/-- Two failures agree. -/
theorem agree_err {α β : Type} {R : α → β → Prop} {q : Nat} {ps : List (Token × Nat)}
    {x : Except Error (α × Nat)} {y : Except Spec.Object.Err (β × List Token)}
    (hx : ∃ e, x = .error e) (hy : ∃ e, y = .error e) : Agree R q ps x y := by
  obtain ⟨e, rfl⟩ := hx; obtain ⟨e', rfl⟩ := hy; trivial

/-- Arrays agree on empty streams. -/
theorem arr_zero (bytes : ByteArray) : ArrAgreeN bytes 0 := by
  intro fuel pos ps acc hl hn
  cases hl with
  | nil h => exact agree_err (parseArray_none h) ⟨.unexpectedEnd, by simp [parseItems]⟩
  | cons _ _ => simp at hn

/-- Dictionaries agree on empty streams. -/
theorem dict_zero (bytes : ByteArray) : DictAgreeN bytes 0 := by
  intro fuel pos ps acc seen sn hl hn _ _
  cases hl with
  | nil h => exact agree_err (parseDict_none h) ⟨.unexpectedEnd, by simp [parseEntries]⟩
  | cons _ _ => simp at hn

/-- Arrays agree on streams of `n + 1` tokens, given objects on `n` and arrays on `n`. -/
theorem arr_step (bytes : ByteArray) (n : Nat) (hO : ObjAgreeN bytes n)
    (hA : ArrAgreeN bytes n) : ArrAgreeN bytes (n + 1) := by
  intro fuel pos ps acc hl hn
  cases hl with
  | nil h => exact agree_err (parseArray_none h) ⟨.unexpectedEnd, by simp [parseItems]⟩
  | @cons _ q t ps1 h1 hl1 =>
    have hq := Core.Lex.next_pos _ _ _ _ h1
    have hn1 : ps1.length ≤ n := by simp at hn; omega
    rw [parseArray_some h1]
    by_cases ht : t = .arrayClose
    · subst ht
      simp only [↓reduceIte, List.map_cons, parseItems]
      exact ⟨by simp, [(.arrayClose, q)], ps1, rfl, rfl, rfl⟩
    · simp only [ht, ↓reduceIte, List.map_cons]
      rw [parseItems]
      rotate_left
      · exact ht
      have hO' := hO fuel pos t q ps1 hl1 hn1 hq.2
      cases hX : parseObjTok fuel bytes pos t q with
      | error e =>
        cases hY : parse fuel (t :: ps1.map Prod.fst) with
        | error e' => trivial
        | ok y => rw [hX, hY] at hO'; exact hO'.elim
      | ok x =>
        cases hY : parse fuel (t :: ps1.map Prod.fst) with
        | error e' => rw [hX, hY] at hO'; exact hO'.elim
        | ok y =>
          rw [hX, hY] at hO'
          obtain ⟨o, r⟩ := x
          obtain ⟨o', mid⟩ := y
          obtain ⟨rfl, pre, rs, rfl, rfl, rfl⟩ := hO'
          have hpr : pos < endAfter q pre := by
            have := parseObjTok_pos fuel bytes pos t q o _ hq.2 hX
            omega
          have hlt : (rs.map Prod.fst).length < ((pre ++ rs).map Prod.fst).length + 1 := by
            have := parse_length_lt hY; simpa using this
          simp only [hpr, ↓reduceIte, hlt, ↓reduceDIte]
          have hA' := hA fuel (endAfter q pre) rs (o :: acc) (LexFrom.drop hl1)
            (by simp at hn1; omega)
          cases hX2 : parseArray fuel bytes (endAfter q pre) (o :: acc) with
          | error e =>
            cases hY2 : parseItems fuel (rs.map Prod.fst) with
            | error e' => trivial
            | ok y => rw [hX2, hY2] at hA'; exact hA'.elim
          | ok x =>
            cases hY2 : parseItems fuel (rs.map Prod.fst) with
            | error e' => rw [hX2, hY2] at hA'; exact hA'.elim
            | ok y =>
              rw [hX2, hY2] at hA'
              obtain ⟨xs, r2⟩ := x
              obtain ⟨os, rest⟩ := y
              obtain ⟨h1, pre2, rs2, rfl, rfl, rfl⟩ := hA'
              refine ⟨by simp [h1], (t, q) :: (pre ++ pre2), rs2, by simp, rfl, ?_⟩
              simp only [endAfter, endAfter_append]

/-- Updating the accumulator and the seen keys together keeps them in step. -/
theorem hasKey_cons {acc : List (Name × PdfObject)} {seen : List Name}
    (hk : ∀ k, hasKey acc k = true ↔ k ∈ seen) (k : Name) (v : PdfObject) :
    ∀ k', hasKey ((k, v) :: acc) k' = true ↔ k' ∈ k :: seen := by
  intro k'
  have := hk k'
  simp only [hasKey, List.any_cons, Bool.or_eq_true, beq_iff_eq, List.mem_cons] at this ⊢
  rw [this, eq_comm]

/-- Dictionaries agree on streams of `n + 1` tokens, given objects on `n` and dictionaries on
`n`. -/
theorem dict_step (bytes : ByteArray) (n : Nat) (hO : ObjAgreeN bytes n)
    (hD : DictAgreeN bytes n) : DictAgreeN bytes (n + 1) := by
  intro fuel pos ps acc seen sn hl hn hk hsn
  cases hl with
  | nil h => exact agree_err (parseDict_none h) ⟨.unexpectedEnd, by simp [parseEntries]⟩
  | @cons _ q t ps1 h1 hl1 =>
    have hq := Core.Lex.next_pos _ _ _ _ h1
    have hn1 : ps1.length ≤ n := by simp at hn; omega
    cases t with
    | dictClose =>
      rw [parseDict_close h1]
      simp only [List.map_cons, parseEntries]
      exact ⟨by simp, [(.dictClose, q)], ps1, rfl, rfl, rfl⟩
    | name k =>
      by_cases hdup : hasKey acc k = true
      · exact agree_err (parseDict_dup h1 (by rw [hsn]; exact hdup))
          ⟨.duplicateKey, by simp [parseEntries, (hk k).1 hdup]⟩
      have hkf : hasKey acc k = false := by simpa using hdup
      have hkf' : sn.contains k.bytes = false := by rw [hsn]; exact hkf
      have hks : k ∉ seen := fun hm => hdup ((hk k).2 hm)
      cases hl1 with
      | nil h2 =>
        exact agree_err (parseDict_key_none h1 hkf' h2)
          ⟨.unexpectedEnd, by simp [parseEntries, hks, parse]⟩
      | @cons _ q2 t2 ps2 h2 hl2 =>
        have hq2 := Core.Lex.next_pos _ _ _ _ h2
        rw [parseDict_key_some h1 hkf' h2]
        simp only [List.map_cons, parseEntries, hks, ↓reduceIte]
        have hO' := hO fuel q t2 q2 ps2 hl2 (by simp at hn1; omega) hq2.2
        cases hX : parseObjTok fuel bytes q t2 q2 with
        | error e =>
          cases hY : parse fuel (t2 :: ps2.map Prod.fst) with
          | error e' => trivial
          | ok y => rw [hX, hY] at hO'; exact hO'.elim
        | ok x =>
          cases hY : parse fuel (t2 :: ps2.map Prod.fst) with
          | error e' => rw [hX, hY] at hO'; exact hO'.elim
          | ok y =>
            rw [hX, hY] at hO'
            obtain ⟨v, r⟩ := x
            obtain ⟨v', mid⟩ := y
            obtain ⟨rfl, pre, rs, rfl, rfl, rfl⟩ := hO'
            have hpr : pos < endAfter q2 pre := by
              have := parseObjTok_pos fuel bytes q t2 q2 v _ hq2.2 hX
              omega
            have hlt : (rs.map Prod.fst).length < (t2 :: (pre ++ rs).map Prod.fst).length := by
              have := parse_length_lt hY; simpa using this
            simp only [hpr, ↓reduceIte, hlt, ↓reduceDIte]
            have hD' := hD fuel (endAfter q2 pre) rs ((k, v) :: acc) (k :: seen)
              (sn.insert k.bytes) (LexFrom.drop hl2) (by simp at hn1; omega) (hasKey_cons hk k v)
              (seenOf_cons hsn k v)
            cases hX2 : parseDict fuel bytes (endAfter q2 pre) ((k, v) :: acc) (sn.insert k.bytes) with
            | error e =>
              cases hY2 : parseEntries fuel (k :: seen) (rs.map Prod.fst) with
              | error e' => trivial
              | ok y => rw [hX2, hY2] at hD'; exact hD'.elim
            | ok x =>
              cases hY2 : parseEntries fuel (k :: seen) (rs.map Prod.fst) with
              | error e' => rw [hX2, hY2] at hD'; exact hD'.elim
              | ok y =>
                rw [hX2, hY2] at hD'
                obtain ⟨d, r2⟩ := x
                obtain ⟨es, rest⟩ := y
                obtain ⟨h3, pre2, rs2, rfl, rfl, rfl⟩ := hD'
                refine ⟨by simp [h3], (.name k, q) :: (t2, q2) :: (pre ++ pre2), rs2, by simp,
                  rfl, ?_⟩
                simp only [endAfter, endAfter_append]
    | _ =>
      exact agree_err (parseDict_other h1 (by simp) (by simp))
        ⟨.nonNameKey, by simp [parseEntries]⟩

/-- **Agreement for all stream lengths.** -/
theorem agree_all (bytes : ByteArray) (n : Nat) :
    ObjAgreeN bytes n ∧ ArrAgreeN bytes n ∧ DictAgreeN bytes n := by
  induction n with
  | zero =>
    exact ⟨obj_step bytes 0 (arr_zero bytes) (dict_zero bytes), arr_zero bytes, dict_zero bytes⟩
  | succ n ih =>
    have hA := arr_step bytes n ih.1 ih.2.1
    have hD := dict_step bytes n ih.1 ih.2.2
    exact ⟨obj_step bytes (n + 1) hA hD, hA, hD⟩

/-- Agreement over the stream after a token extends to the stream including it. -/
theorem Agree.cons {α β : Type} {R : α → β → Prop} {p q : Nat} {t : Token}
    {ps : List (Token × Nat)} {x : Except Error (α × Nat)}
    {y : Except Spec.Object.Err (β × List Token)} (h : Agree R q ps x y) :
    Agree R p ((t, q) :: ps) x y := by
  rcases x with e | ⟨a, r⟩ <;> rcases y with e' | ⟨b, rest⟩
  · trivial
  · exact h.elim
  · exact h.elim
  · obtain ⟨h1, pre, rs, rfl, rfl, rfl⟩ := h
    exact ⟨h1, (t, q) :: pre, rs, rfl, rfl, rfl⟩

/-- `parseObj` agrees with `parse` on the positioned stream lexed from `pos`. -/
theorem parseObj_agree (fuel : Nat) (bytes : ByteArray) (pos : Nat) (ps : List (Token × Nat))
    (hl : LexFrom bytes pos ps) :
    Agree (· = ·) pos ps (parseObj fuel bytes pos) (parse fuel (ps.map Prod.fst)) := by
  cases hl with
  | nil h =>
    exact agree_err ⟨.malformed pos "unexpected end of input", by simp [parseObj, h]⟩
      ⟨.unexpectedEnd, by simp [parse]⟩
  | @cons _ q t ps1 h1 hl1 =>
    have hq := Core.Lex.next_pos _ _ _ _ h1
    simp only [parseObj, h1, List.map_cons]
    exact Agree.cons ((agree_all bytes ps1.length).1 fuel pos t q ps1 hl1 (Nat.le_refl _) hq.2)

/-! ## Main theorems (positioned streams) -/

/-- **Equivalence, success (positioned streams).** If lexing from `pos` yields the positioned
stream `ps`, then `parseObj` succeeds with `(o, r)` iff the spec `parse` succeeds on the tokens of
`ps` with `o`, leaving a suffix `rs` of the stream, and `r` is the end of the last consumed token
`endAfter pos pre` (`ps = pre ++ rs`). -/
theorem parseObj_ok_iff {fuel : Nat} {bytes : ByteArray} {pos : Nat} {ps : List (Token × Nat)}
    (hl : LexFrom bytes pos ps) {o : PdfObject} {r : Nat} :
    parseObj fuel bytes pos = .ok (o, r) ↔
      ∃ pre rs, ps = pre ++ rs ∧ parse fuel (ps.map Prod.fst) = .ok (o, rs.map Prod.fst) ∧
        r = endAfter pos pre := by
  have h := parseObj_agree fuel bytes pos ps hl
  constructor
  · intro hx
    rw [hx] at h
    cases hy : parse fuel (ps.map Prod.fst) with
    | error e => rw [hy] at h; exact h.elim
    | ok y =>
      rw [hy] at h
      obtain ⟨o', rest⟩ := y
      obtain ⟨rfl, pre, rs, hps, rfl, rfl⟩ := h
      exact ⟨pre, rs, hps, rfl, rfl⟩
  · rintro ⟨pre, rs, hps, hy, rfl⟩
    rw [hy] at h
    cases hx : parseObj fuel bytes pos with
    | error e => rw [hx] at h; exact h.elim
    | ok x =>
      rw [hx] at h
      obtain ⟨o', r'⟩ := x
      obtain ⟨rfl, pre', rs', hps', hrs, rfl⟩ := h
      have hlen : rs.length = rs'.length := by
        have := congrArg List.length hrs; simpa using this
      have := List.append_inj' (hps.symm.trans hps') hlen
      rw [this.1]

/-- **Equivalence, failure (positioned streams).** If lexing from `pos` yields the positioned
stream `ps`, then `parseObj` fails iff the spec `parse` fails on the tokens of `ps`. -/
theorem parseObj_error_iff {fuel : Nat} {bytes : ByteArray} {pos : Nat}
    {ps : List (Token × Nat)} (hl : LexFrom bytes pos ps) :
    (∃ e, parseObj fuel bytes pos = .error e) ↔
      (∃ e, parse fuel (ps.map Prod.fst) = .error e) := by
  have h := parseObj_agree fuel bytes pos ps hl
  rcases hx : parseObj fuel bytes pos with e | x <;> rcases hy : parse fuel (ps.map Prod.fst) with
    e' | y <;> rw [hx, hy] at h
  · exact ⟨fun _ => ⟨e', rfl⟩, fun _ => ⟨e, rfl⟩⟩
  · exact h.elim
  · exact h.elim
  · simp

/-! ## From the spec lexer to positioned streams -/

/-- A token of the core lexer is a token of the spec lexer on the rest of the input, the rest
after it being the input from the core's end position. -/
theorem spec_next_of_core {bytes : ByteArray} {p q : Nat} {t : Token}
    (h : Core.Lex.next bytes p = .ok (some (t, q))) :
    Spec.Lex.next (restAt bytes p) = .ok (some (t, restAt bytes q)) := by
  rw [LexEquiv.next_eq_tr] at h
  rcases hs : Spec.Lex.next (restAt bytes p) with e | _ | ⟨t', r⟩ <;> rw [hs] at h
  · simp [LexEquiv.tr] at h
  · simp [LexEquiv.tr] at h
  · simp only [LexEquiv.tr, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [LexEquiv.restAt_of_suffix bytes p r (LexEquiv.next_suffix _ _ _ hs)]

/-- End of input for the core lexer is end of input for the spec lexer. -/
theorem spec_next_none_of_core {bytes : ByteArray} {p : Nat}
    (h : Core.Lex.next bytes p = .ok none) : Spec.Lex.next (restAt bytes p) = .ok none := by
  rw [LexEquiv.next_eq_tr] at h
  rcases hs : Spec.Lex.next (restAt bytes p) with e | _ | ⟨t', r⟩ <;> rw [hs] at h <;>
    first | rfl | simp [LexEquiv.tr] at h

/-- A successful spec `lexAll` on the input from `pos` is a positioned core stream from `pos`. -/
theorem lexFrom_of_lexAll (bytes : ByteArray) (pos : Nat) (ts : List Token)
    (h : Spec.Lex.lexAll (restAt bytes pos) = .ok ts) :
    ∃ ps, LexFrom bytes pos ps ∧ ps.map Prod.fst = ts := by
  suffices H : ∀ n pos ts, (restAt bytes pos).length ≤ n →
      Spec.Lex.lexAll (restAt bytes pos) = .ok ts →
      ∃ ps, LexFrom bytes pos ps ∧ ps.map Prod.fst = ts from
    H _ pos ts (Nat.le_refl _) h
  intro n
  induction n with
  | zero =>
    intro pos ts hn h
    have hnil : restAt bytes pos = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hs : Spec.Lex.next (restAt bytes pos) = .ok none := by rw [hnil]; rfl
    rw [LexEquiv.lexAll_of_none hs] at h
    cases h
    refine ⟨[], .nil ?_, rfl⟩
    rw [LexEquiv.next_eq_tr, hs]; rfl
  | succ n ih =>
    intro pos ts hn h
    rcases hs : Spec.Lex.next (restAt bytes pos) with e | _ | ⟨t, r⟩
    · rw [LexEquiv.lexAll_of_error hs] at h; cases h
    · rw [LexEquiv.lexAll_of_none hs] at h
      cases h
      refine ⟨[], .nil ?_, rfl⟩
      rw [LexEquiv.next_eq_tr, hs]; rfl
    · rw [LexEquiv.lexAll_of_some hs] at h
      have hr := LexEquiv.restAt_of_suffix bytes pos r (LexEquiv.next_suffix _ _ _ hs)
      have hlt := Spec.Lex.next_consumes hs
      cases hall : Spec.Lex.lexAll r with
      | error e => rw [hall] at h; cases h
      | ok ts' =>
        rw [hall] at h
        cases h
        rw [← hr] at hall
        obtain ⟨ps', hl', hm⟩ := ih (bytes.size - r.length) ts' (by rw [hr]; omega) hall
        refine ⟨(t, bytes.size - r.length) :: ps', .cons ?_ hl', by simp [hm]⟩
        rw [LexEquiv.next_eq_tr, hs]; rfl

/-- The input after `k` tokens of the spec lexer (`none` if fewer than `k` tokens remain). -/
def dropToks : Nat → List UInt8 → Option (List UInt8)
  | 0, l => some l
  | k + 1, l =>
    match Spec.Lex.next l with
    | .ok (some (_, r)) => dropToks k r
    | _ => none

/-- Along a positioned stream, the input after the tokens `pre` is the input from
`endAfter pos pre`. -/
theorem dropToks_endAfter {bytes : ByteArray} {pos : Nat} {pre rs : List (Token × Nat)}
    (h : LexFrom bytes pos (pre ++ rs)) :
    dropToks pre.length (restAt bytes pos) = some (restAt bytes (endAfter pos pre)) := by
  induction pre generalizing pos with
  | nil => rfl
  | cons x pre ih =>
    obtain ⟨t, q⟩ := x
    cases h with
    | cons h1 h' =>
      simp only [List.length_cons, dropToks, spec_next_of_core h1, endAfter]
      exact ih h'

/-! ## Main theorems (spec lexer) -/

/-- **Equivalence, success (Plan.md §4 C5, §5.1 step 3).** If the spec lexer tokenizes the input
from `pos` into `ts`, then `parseObj fuel bytes pos` succeeds with `(o, r)` iff the spec
`parse fuel ts` succeeds with `(o, rest)` and `r` is the position after the consumed tokens: the
input left after the first `ts.length - rest.length` spec tokens has `bytes.size - r` bytes. -/
theorem parseObj_ok_iff_lexAll {fuel : Nat} {bytes : ByteArray} {pos : Nat} {ts : List Token}
    (hlex : Spec.Lex.lexAll (bytes.data.toList.drop pos) = .ok ts) {o : PdfObject} {r : Nat} :
    parseObj fuel bytes pos = .ok (o, r) ↔
      ∃ rest l, parse fuel ts = .ok (o, rest) ∧
        dropToks (ts.length - rest.length) (bytes.data.toList.drop pos) = some l ∧
        r = bytes.size - l.length := by
  obtain ⟨ps, hl, rfl⟩ := lexFrom_of_lexAll bytes pos ts hlex
  rw [parseObj_ok_iff hl]
  constructor
  · rintro ⟨pre, rs, rfl, hp, rfl⟩
    have hx : parseObj fuel bytes pos = .ok (o, endAfter pos pre) :=
      (parseObj_ok_iff hl).2 ⟨pre, rs, rfl, hp, rfl⟩
    have hb := (parseObj_pos hx).2
    refine ⟨rs.map Prod.fst, restAt bytes (endAfter pos pre), hp, ?_, ?_⟩
    · have hk : ((pre ++ rs).map Prod.fst).length - (rs.map Prod.fst).length = pre.length := by
        simp
      rw [hk]
      exact dropToks_endAfter hl
    · rw [LexEquiv.length_restAt]; omega
  · rintro ⟨rest, l, hp, hd, rfl⟩
    have h := parseObj_agree fuel bytes pos ps hl
    rw [hp] at h
    cases hx : parseObj fuel bytes pos with
    | error e => rw [hx] at h; exact h.elim
    | ok x =>
      rw [hx] at h
      obtain ⟨o', r'⟩ := x
      obtain ⟨rfl, pre, rs, rfl, rfl, rfl⟩ := h
      have hb := (parseObj_pos hx).2
      have hk : ((pre ++ rs).map Prod.fst).length - (rs.map Prod.fst).length = pre.length := by
        simp
      rw [hk] at hd
      have hd' := dropToks_endAfter hl
      have hl' : l = restAt bytes (endAfter pos pre) := by
        have := hd.symm.trans hd'
        simpa using this
      refine ⟨pre, rs, rfl, hp, ?_⟩
      rw [hl', LexEquiv.length_restAt]; omega

/-- **Equivalence, failure (Plan.md §4 C5, §5.1 step 3).** If the spec lexer tokenizes the input
from `pos` into `ts`, then `parseObj fuel bytes pos` fails iff the spec `parse fuel ts` fails. -/
theorem parseObj_error_iff_lexAll {fuel : Nat} {bytes : ByteArray} {pos : Nat} {ts : List Token}
    (hlex : Spec.Lex.lexAll (bytes.data.toList.drop pos) = .ok ts) :
    (∃ e, parseObj fuel bytes pos = .error e) ↔ (∃ e, parse fuel ts = .error e) := by
  obtain ⟨ps, hl, rfl⟩ := lexFrom_of_lexAll bytes pos ts hlex
  exact parseObj_error_iff hl

/-! ## Whole-input corollaries (for the round trip, task 1.7) -/

/-- **Whole input is one object.** If the spec lexer tokenizes all of `bytes` into `ts` and the
spec parses all of `ts` as `o`, then `parseObj F bytes 0` returns `o` and the position right after
the last token, `bytes.size - l.length`, where `l` (the input after all `ts.length` spec tokens)
holds only whitespace and comments. -/
theorem parseObj_of_spec_full {F : Nat} {bytes : ByteArray} {ts : List Token} {o : PdfObject}
    (hlex : Spec.Lex.lexAll bytes.data.toList = .ok ts) (hp : parse F ts = .ok (o, [])) :
    ∃ l, dropToks ts.length bytes.data.toList = some l ∧ Spec.Lex.next l = .ok none ∧
      parseObj F bytes 0 = .ok (o, bytes.size - l.length) := by
  have hlex0 : Spec.Lex.lexAll (restAt bytes 0) = .ok ts := by simpa [restAt] using hlex
  obtain ⟨ps, hl, rfl⟩ := lexFrom_of_lexAll bytes 0 _ hlex0
  have h := parseObj_agree F bytes 0 ps hl
  rw [hp] at h
  cases hx : parseObj F bytes 0 with
  | error e => rw [hx] at h; exact h.elim
  | ok x =>
    rw [hx] at h
    obtain ⟨o', r⟩ := x
    obtain ⟨rfl, pre, rs, rfl, hrs, rfl⟩ := h
    have hrs' : rs = [] := by
      have := congrArg List.length hrs; simp at this; exact List.eq_nil_of_length_eq_zero this.symm
    subst hrs'
    simp only [List.append_nil] at hl ⊢
    have hb := (parseObj_pos hx).2
    have hd := dropToks_endAfter (rs := []) (by simpa using hl)
    refine ⟨restAt bytes (endAfter 0 pre), ?_, ?_, ?_⟩
    · simpa [restAt] using hd
    · have hl2 := LexFrom.drop (pre := pre) (rs := []) (by simpa using hl)
      cases hl2 with
      | nil h0 => exact spec_next_none_of_core h0
    · rw [LexEquiv.length_restAt]
      congr
      omega

/-- `parseObj_of_spec_full` when the input ends with its last token (no trailing whitespace or
comment): the parser returns `o` at `bytes.size`. -/
theorem parseObj_of_spec_full_size {F : Nat} {bytes : ByteArray} {ts : List Token}
    {o : PdfObject} (hlex : Spec.Lex.lexAll bytes.data.toList = .ok ts)
    (hp : parse F ts = .ok (o, [])) (hend : dropToks ts.length bytes.data.toList = some []) :
    parseObj F bytes 0 = .ok (o, bytes.size) := by
  obtain ⟨l, hd, -, hx⟩ := parseObj_of_spec_full hlex hp
  rw [hend] at hd
  cases hd
  simpa using hx

/-- `parseObj_of_spec_full` stated with the grammar relation `Parses`. -/
theorem parseObj_of_parses_full {F : Nat} {bytes : ByteArray} {ts : List Token} {o : PdfObject}
    (hlex : Spec.Lex.lexAll bytes.data.toList = .ok ts) (hp : Parses F ts o []) :
    ∃ l, dropToks ts.length bytes.data.toList = some l ∧ Spec.Lex.next l = .ok none ∧
      parseObj F bytes 0 = .ok (o, bytes.size - l.length) :=
  parseObj_of_spec_full hlex (parse_eq_ok_iff.2 hp)

section Tests

#guard dropToks 1 "12 0 R ".toUTF8.toList == some " 0 R ".toUTF8.toList
#guard dropToks 3 "12 0 R ".toUTF8.toList == some " ".toUTF8.toList
#guard dropToks 4 "12 0 R ".toUTF8.toList == none

end Tests

end SafePdf.Spec.ObjEquiv
