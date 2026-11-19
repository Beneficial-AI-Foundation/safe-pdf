import SafePdf.Core.Xref.Chain

/-!
# Prefix stability of cross-reference sections (task 2.12)

Plan.md §4 S6 (unambiguous, version-stable interpretation), §5.2 (the xref layer), §6 Phase 2;
ISO 32000-2 §7.5.6 (incremental updates append bytes to the file).

An incremental update appends bytes: the new file `b'` *extends* the old one `b`
(`Extends b b'`: at least as long, same bytes below `b.size`). The parsers read `bytes.size`
in their range checks, so a parse in `b` that ran into the end of `b` may read differently in
`b'` (a keyword or number can continue, a lookahead can find a new token). This file proves
that this never happens for the sections of a file with a valid `startxref`:

* Every lexer and parser function (`Core.Lex`, `Core.ObjParse`, the classic-table reader of
  `Core.Xref`, the xref-stream reader of `Core.Xref.Stream`) gives the same successful result in
  `b'` as in `b` provided its *frontier* (the position after its last token, where the lexer
  may peek one byte, and for objects the tokens of the `n g R` lookahead, `Follow`) lies
  strictly inside `b` (the `*_ext` lemmas). Range checks against the size (`entryOk`,
  `mkEntry`, stream data bounds) are monotone in the size.
* In a file whose `startxref` is found, the file ends with `%%EOF` and optional whitespace
  (`findStartxref_last`), while a classic section ends with `>` (`parseXrefTable_last`) and an
  xref stream with `endobj` (`parseIndirect_last`); so their frontier lies strictly inside the
  file (`parseXrefTable_end_lt`, `parseIndirect_end_lt`).
* Hence `section_stable` and `stream_stable`: at an offset where a section (table or stream)
  of `b` parses, the section parse, the `xref` keyword test and the xref-stream parse agree in
  `b'`, which is `Spec.Unambiguous.SameAt` (discharged there by `sameAt_of_extends`).

Only successful parses are claimed stable; errors may differ (`b'` may complete what `b` cut
short).
-/

namespace SafePdf.Spec.PrefixStable

open SafePdf SafePdf.Core

/-! ## Extensions of an input -/

/-- `b'` extends `b`: it is at least as long and agrees with `b` on every byte of `b`. -/
structure Extends (b b' : ByteArray) : Prop where
  /-- `b'` is at least as long. -/
  le : b.size ≤ b'.size
  /-- `b'` agrees with `b` below `b.size`. -/
  eq : ∀ i, i < b.size → b'[i]? = b[i]?

/-- An input extends itself. -/
theorem Extends.refl (b : ByteArray) : Extends b b := ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-- Appending bytes extends an input. -/
theorem Extends.append (b s : ByteArray) : Extends b (b ++ s) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getElem?_pos b i hi, getElem?_pos (b ++ s) i (by simp; omega)]
  simp [ByteArray.getElem_append_left hi]

/-- Reading an in-range byte of `b` in `b'`. -/
theorem Extends.get {b b' : ByteArray} (hE : Extends b b') {i : Nat} (h : i < b.size)
    (h' : i < b'.size) : b'[i] = b[i] := by
  have := hE.eq i h
  rw [getElem?_pos b' i h', getElem?_pos b i h] at this
  exact Option.some.inj this

/-- An in-range index of `b` is in range in `b'`. -/
theorem Extends.lt {b b' : ByteArray} (hE : Extends b b') {i : Nat} (h : i < b.size) :
    i < b'.size :=
  Nat.lt_of_lt_of_le h hE.le

/-! ## The lexer -/

/-- Skipping whitespace that stops inside `b` is the same in `b'`. -/
theorem skipWs_ext {b b' : ByteArray} (hE : Extends b b') (pos : Nat) (c : Bool)
    (h : Lex.skipWs b pos c < b.size) : Lex.skipWs b' pos c = Lex.skipWs b pos c := by
  fun_induction Lex.skipWs b pos c with
  | case1 pos hp bb ih =>
    rw [Lex.skipWs]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    exact ih h
  | case2 pos c hp bb hc hw ih =>
    rw [Lex.skipWs]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at hw
    simp only [Bool.not_eq_true] at hc
    simp only [hc, hw, Bool.false_eq_true, ↓reduceIte]
    exact ih h
  | case3 pos c hp bb hc hw hpc ih =>
    rw [Lex.skipWs]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at hw hpc
    simp only [Bool.not_eq_true] at hc
    simp only [hc, hw, hpc, Bool.false_eq_true, ↓reduceIte]
    exact ih h
  | case4 pos c hp bb hc hw hpc =>
    rw [Lex.skipWs]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at hw hpc
    simp only [Bool.not_eq_true] at hc
    simp only [hc, hw, hpc, Bool.false_eq_true, ↓reduceIte]
  | case5 pos c hp => omega

/-- A regular run that ends inside `b` (the stop byte was read) is the same in `b'`. -/
theorem readRun_ext {b b' : ByteArray} (hE : Extends b b') (pos : Nat) (acc : List UInt8)
    (h : (Lex.readRun b pos acc).2 < b.size) : Lex.readRun b' pos acc = Lex.readRun b pos acc := by
  fun_induction Lex.readRun b pos acc with
  | case1 pos acc hp bb hr ih =>
    rw [Lex.readRun]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at hr
    simp only [hr, ↓reduceIte]
    exact ih h
  | case2 pos acc hp bb hr =>
    rw [Lex.readRun]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at hr
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
  | case3 pos acc hp => simp at h; omega

/-- A byte lookup that agrees: either in range of `b` (equal in `b'`) or `none` in `b`. -/
theorem Extends.getOpt {b b' : ByteArray} (hE : Extends b b') {i : Nat} (h : i < b.size) :
    b'[i]? = b[i]? := hE.eq i h

/-- An octal escape whose end lies inside `b` reads the same in `b'`. -/
theorem octalAt_ext {b b' : ByteArray} (hE : Extends b b') (q : Nat) (c : UInt8)
    (h : (Lex.octalAt b q c).2 < b.size) : Lex.octalAt b' q c = Lex.octalAt b q c := by
  have hlt := Lex.lt_octalAt b q c
  have h1 : q + 1 < b.size := by omega
  unfold Lex.octalAt at h ⊢
  rw [hE.getOpt h1]
  by_cases h2 : q + 2 < b.size
  · rw [hE.getOpt h2]
  · have hn : b[q + 2]? = none := getElem?_neg b (q + 2) h2
    rw [hn] at h
    split
    · rename_i d1 hd1
      rw [hd1] at h
      split
      · rename_i hd
        simp only [hd, ↓reduceIte] at h
        omega
      · rfl
    · rfl

/-- An escape whose end lies inside `b` reads the same in `b'`. -/
theorem escapeAt_ext {b b' : ByteArray} (hE : Extends b b') (q : Nat) (c : UInt8)
    (h : (Lex.escapeAt b q c).2 < b.size) : Lex.escapeAt b' q c = Lex.escapeAt b q c := by
  have hlt := Lex.lt_escapeAt b q c
  have hq : q + 1 < b.size := by omega
  unfold Lex.escapeAt at h ⊢
  rw [hE.getOpt hq]
  repeat' split
  all_goals first
    | rfl
    | (simp only [*, ↓reduceIte, Bool.false_eq_true] at h
       rw [octalAt_ext hE q c h])

/-- A terminated literal string reads the same in `b'` (it never reached the end of `b`). -/
theorem litStr_ext {b b' : ByteArray} (hE : Extends b b') (pos depth : Nat) (acc : List UInt8)
    (h : (Lex.litStr b pos depth acc).isSome) :
    Lex.litStr b' pos depth acc = Lex.litStr b pos depth acc := by
  fun_induction Lex.litStr b pos depth acc with
  | case1 pos depth acc hp bb h92 h1 r ih =>
    obtain ⟨⟨s, q⟩, hsq⟩ := Option.isSome_iff_exists.mp h
    have hb := Lex.litStr_bounds b _ _ _ _ _ hsq
    rw [Lex.litStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h92
    simp only [h92, ↓reduceIte, hE.lt h1, ↓reduceDIte, hE.get h1]
    rw [escapeAt_ext hE _ _ (by simp only [r] at hb; omega)]
    exact ih h
  | case2 => simp at h
  | case3 pos depth acc hp bb h92 h40 ih =>
    rw [Lex.litStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h92 h40
    simp only [h92, h40, ↓reduceIte, Bool.false_eq_true]
    exact ih h
  | case4 pos depth acc hp bb h92 h40 h41 hd =>
    rw [Lex.litStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h92 h40 h41
    simp only [h92, h40, h41, hd, ↓reduceIte, Bool.false_eq_true]
  | case5 pos depth acc hp bb h92 h40 h41 hd ih =>
    rw [Lex.litStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h92 h40 h41
    simp only [h92, h40, h41, hd, ↓reduceIte, Bool.false_eq_true]
    exact ih h
  | case6 pos depth acc hp bb h92 h40 h41 h13 ih =>
    rw [Lex.litStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h92 h40 h41 h13
    simp only [h92, h40, h41, h13, ↓reduceIte, Bool.false_eq_true]
    simp only [dite_eq_ite] at ih
    by_cases h1 : pos + 1 < b.size
    · rw [hE.getOpt h1]
      exact ih h
    · have hn : b[pos + 1]? = none := getElem?_neg b (pos + 1) h1
      simp only [hn] at h
      obtain ⟨⟨s, q⟩, hsq⟩ := Option.isSome_iff_exists.mp h
      have hb := Lex.litStr_bounds b _ _ _ _ _ hsq
      simp at hb
      omega
  | case7 pos depth acc hp bb h92 h40 h41 h13 ih =>
    rw [Lex.litStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h92 h40 h41 h13
    simp only [h92, h40, h41, h13, ↓reduceIte, Bool.false_eq_true]
    exact ih h
  | case8 => simp at h

/-- A terminated hex string reads the same in `b'`. -/
theorem hexStr_ext {b b' : ByteArray} (hE : Extends b b') (pos : Nat) (hi : Option UInt8)
    (acc : List UInt8) {s : List UInt8} {q : Nat} (h : Lex.hexStr b pos hi acc = .ok (s, q)) :
    Lex.hexStr b' pos hi acc = .ok (s, q) := by
  fun_induction Lex.hexStr b pos hi acc with
  | case1 pos hi acc hp bb h62 =>
    rw [Lex.hexStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h62
    simp only [h62, ↓reduceIte]
    exact h
  | case2 pos hi acc hp bb h62 hw ih =>
    rw [Lex.hexStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h62 hw
    simp only [h62, hw, ↓reduceIte, Bool.false_eq_true]
    exact ih h
  | case3 pos acc hp bb h62 hw d hv ih =>
    rw [Lex.hexStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h62 hw hv
    simp only [h62, hw, hv, ↓reduceIte, Bool.false_eq_true]
    exact ih h
  | case4 pos acc hp bb h62 hw d hv x ih =>
    rw [Lex.hexStr]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at h62 hw hv
    simp only [h62, hw, hv, ↓reduceIte, Bool.false_eq_true]
    exact ih h
  | case5 => simp at h
  | case6 => simp at h

/-- A name ending inside `b` (its stop byte was read) reads the same in `b'`. -/
theorem nameRun_ext {b b' : ByteArray} (hE : Extends b b') (pos : Nat) (acc : List UInt8)
    {s : List UInt8} {q : Nat} (h : Lex.nameRun b pos acc = .ok (s, q)) (hq : q < b.size) :
    Lex.nameRun b' pos acc = .ok (s, q) := by
  fun_induction Lex.nameRun b pos acc with
  | case1 pos acc hp bb hr =>
    rw [Lex.nameRun]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at hr
    simp only [hr, ↓reduceIte]
    exact h
  | case2 => simp at h
  | case3 pos acc hp bb hr h35 v1 v2 hv2 hv1 d hd ih =>
    have h1 := Lex.lt_size_of_bind_eq_some hv1
    have h2 := Lex.lt_size_of_bind_eq_some hv2
    rw [Lex.nameRun]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at hr h35
    simp only [hr, h35, ↓reduceIte, Bool.false_eq_true, hE.getOpt h1, hE.getOpt h2, hv1, hv2]
    simp only [d] at hd ih h
    simp only [hd, ↓reduceIte, Bool.false_eq_true]
    exact ih h
  | case4 => simp at h
  | case5 pos acc hp bb hr h35 ih =>
    rw [Lex.nameRun]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    simp only [bb] at hr h35
    simp only [hr, h35, ↓reduceIte, Bool.false_eq_true]
    exact ih h
  | case6 pos acc hp =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    omega

/-- A token ending strictly inside `b` is lexed the same way in `b'`. -/
theorem tokenOf_ext {b b' : ByteArray} (hE : Extends b b') (p : Nat) (c : UInt8)
    {t : Token} {q : Nat} (h : Lex.tokenOf b p c = .ok (some (t, q))) (hq : q < b.size) :
    Lex.tokenOf b' p c = .ok (some (t, q)) := by
  unfold Lex.tokenOf at h ⊢
  split at h
  · rename_i c1; simp only [c1, ↓reduceIte]; exact h
  split at h
  · rename_i c1 c2; simp only [c1, c2, ↓reduceIte, Bool.false_eq_true]; exact h
  split at h
  · rename_i c1 c2 c3; simp only [c1, c2, c3, ↓reduceIte, Bool.false_eq_true]; exact h
  split at h
  · rename_i c1 c2 c3 c4; simp only [c1, c2, c3, c4, ↓reduceIte, Bool.false_eq_true]; exact h
  split at h
  · rename_i c1 c2 c3 c4 c5
    simp only [c1, c2, c3, c4, c5, ↓reduceIte, Bool.false_eq_true]
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      rw [hE.getOpt (show p + 1 < b.size by omega)]
      rename_i c6
      simp only [c6, ↓reduceIte]
      rw [h.1, h.2]
    · rename_i c6
      cases hx : Lex.hexStr b (p + 1) none [] with
      | error k => simp [hx, Lex.liftAt] at h
      | ok v =>
        obtain ⟨s, q'⟩ := v
        rw [hx] at h
        simp only [Lex.liftAt, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        have hb := Lex.hexStr_bounds b _ _ _ _ _ hx
        rw [hE.getOpt (show p + 1 < b.size by omega)]
        simp only [c6, ↓reduceIte, Bool.false_eq_true]
        rw [hexStr_ext hE _ _ _ hx]
        simp only [Lex.liftAt, h.1, h.2]
  split at h
  · rename_i c1 c2 c3 c4 c5 c6
    simp only [c1, c2, c3, c4, c5, c6, ↓reduceIte, Bool.false_eq_true]
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      rw [hE.getOpt (show p + 1 < b.size by omega)]
      rename_i c7
      simp only [c7, ↓reduceIte]
      rw [h.1, h.2]
    · simp at h
  split at h
  · rename_i c1 c2 c3 c4 c5 c6 c7
    simp only [c1, c2, c3, c4, c5, c6, c7, ↓reduceIte, Bool.false_eq_true]
    split at h
    · rename_i s' q' hx
      rw [litStr_ext hE _ _ _ (by rw [hx]; rfl), hx]
      exact h
    · simp at h
  split at h
  · simp at h
  split at h
  · rename_i c1 c2 c3 c4 c5 c6 c7 c8 c9
    simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, ↓reduceIte, Bool.false_eq_true]
    cases hx : Lex.nameRun b (p + 1) [] with
    | error k => simp [hx, Lex.liftAt] at h
    | ok v =>
      obtain ⟨s, q'⟩ := v
      rw [hx] at h
      simp only [Lex.liftAt, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      rw [nameRun_ext hE _ _ hx (by omega)]
      simp only [Lex.liftAt, h.1, h.2]
  · rename_i c1 c2 c3 c4 c5 c6 c7 c8 c9
    simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, ↓reduceIte, Bool.false_eq_true]
    have hrun : (Lex.readRun b (p + 1) [c]).2 = q := by
      revert h
      unfold Lex.runToken
      split
      rename_i run q' hrq
      rw [hrq]
      split <;> simp
    rw [readRun_ext hE _ _ (by omega)]
    exact h

/-- `tokenAt` version of `tokenOf_ext`. -/
theorem tokenAt_ext {b b' : ByteArray} (hE : Extends b b') (p : Nat) {t : Token} {q : Nat}
    (h : Lex.tokenAt b p = .ok (some (t, q))) (hq : q < b.size) :
    Lex.tokenAt b' p = .ok (some (t, q)) := by
  unfold Lex.tokenAt at h ⊢
  split at h
  · rename_i hp
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp]
    exact tokenOf_ext hE p _ h hq
  · simp at h

/-- **Lexer prefix stability.** A token lexed at `pos` that ends strictly before the end of
`b` (so the lexer never saw the end of input) is lexed the same way in any extension. -/
theorem next_ext {b b' : ByteArray} (hE : Extends b b') (pos : Nat) {t : Token} {q : Nat}
    (h : Lex.next b pos = .ok (some (t, q))) (hq : q < b.size) :
    Lex.next b' pos = .ok (some (t, q)) := by
  unfold Lex.next at h ⊢
  have hpq := Lex.tokenAt_pos b _ t q h
  rw [skipWs_ext hE pos false (by omega)]
  exact tokenAt_ext hE _ h hq

/-- `next_ext` as an equation of the two lexer calls. -/
theorem next_eq {b b' : ByteArray} (hE : Extends b b') {pos : Nat} {t : Token} {q : Nat}
    (h : Lex.next b pos = .ok (some (t, q))) (hq : q < b.size) :
    Lex.next b' pos = Lex.next b pos :=
  (next_ext hE pos h hq).trans h.symm

/-! ## Objects -/

/-- The token at `p` exists and ends strictly before the end of `b`. -/
def NextLt (b : ByteArray) (p : Nat) : Prop :=
  ∃ t q, Lex.next b p = .ok (some (t, q)) ∧ q < b.size

/-- What follows an object ending at `r` (the lookahead of `n g R` reads up to two tokens):
a token ending before the end of `b`, and, if that token is an integer, another one. -/
def Follow (b : ByteArray) (r : Nat) : Prop :=
  NextLt b r ∧ ∀ g q, Lex.next b r = .ok (some (.int g, q)) → NextLt b q

/-- A position followed by a token is before the end of the input. -/
theorem NextLt.lt {b : ByteArray} {p : Nat} (h : NextLt b p) : p < b.size := by
  obtain ⟨t, q, h1, hq⟩ := h
  have := Lex.next_pos _ _ _ _ h1
  omega

/-- Error positions agree when the token start is inside `b`. -/
theorem errAt_ext {b b' : ByteArray} (hE : Extends b b') {pos : Nat}
    (h : Lex.skipWs b pos false < b.size) : ObjParse.errAt b' pos = ObjParse.errAt b pos := by
  funext msg
  unfold ObjParse.errAt ObjParse.tokStart
  rw [skipWs_ext hE pos false h]

/-- The token start of a lexed token is inside the input. -/
theorem skipWs_lt_of_next {b : ByteArray} {pos : Nat} {t : Token} {q : Nat}
    (h : Lex.next b pos = .ok (some (t, q))) : Lex.skipWs b pos false < b.size := by
  unfold Lex.next at h
  have := Lex.tokenAt_pos b _ t q h
  unfold Lex.tokenAt at h
  split at h
  · assumption
  · simp at h

/-- The `n g R` lookahead after an integer gives the same result in `b'` when the tokens
that follow the object (`Follow`) end inside `b`. -/
theorem parseIntTail_ext {b b' : ByteArray} (hE : Extends b b') {pos : Nat} {n : Int} {q : Nat}
    {o : PdfObject} {r : Nat} (hpos : Lex.skipWs b pos false < b.size)
    (h : ObjParse.parseIntTail b pos n q = .ok (o, r))
    (hf : Follow b r) : ObjParse.parseIntTail b' pos n q = .ok (o, r) := by
  have h0 := h
  rw [ObjParse.parseIntTail, errAt_ext hE hpos]
  unfold ObjParse.parseIntTail at h
  split at h
  · simp at h
  · rename_i g q2 h1
    have p1 := Lex.next_pos _ _ _ _ h1
    have h01 := h
    split at h
    · simp at h
    · rename_i kw q3 h2
      have p2 := Lex.next_pos _ _ _ _ h2
      split at h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have := hf.1.lt
          rw [next_ext hE q h1 (by omega)]
          simp only
          rw [next_eq hE h2 (by omega)]
          exact h01
        · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨t1, q1, e1, l1⟩ := hf.1
        rw [h1] at e1
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨t2, q2', e2, l2⟩ := hf.2 g q2 h1
        rw [next_ext hE _ h1 l1]
        simp only
        rw [next_eq hE e2 l2]
        exact h01
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨t1, q1, e1, l1⟩ := hf.1
      rw [h1] at e1
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      obtain ⟨t2, q2', e2, l2⟩ := hf.2 g q2 h1
      rw [next_ext hE _ h1 l1]
      simp only
      rw [next_eq hE e2 l2]
      exact h01
  · next _ a hne ha =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨t1, q1, e1, l1⟩ := hf.1
    rw [next_ext hE _ e1 l1]
    rw [e1] at ha
    split
    · simp at *
    · next _ g q2 heq =>
      exfalso
      rw [heq] at ha
      exact hne g q2 (by simpa using ha.symm)
    · rfl

/-- After `parseIntTail`, either the object ends with the integer, or the token after the
integer ends within the object. -/
theorem parseIntTail_next {b : ByteArray} {pos : Nat} {n : Int} {q : Nat} {o : PdfObject}
    {r : Nat} (h : ObjParse.parseIntTail b pos n q = .ok (o, r)) :
    r = q ∨ ∃ t q', Lex.next b q = .ok (some (t, q')) ∧ q' ≤ r := by
  unfold ObjParse.parseIntTail at h
  split at h
  · simp at h
  · rename_i g q2 h1
    split at h
    · simp at h
    · rename_i kw q3 h2
      have p2 := Lex.next_pos _ _ _ _ h2
      split at h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact Or.inr ⟨_, _, h1, by omega⟩
        · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact Or.inl h.2.symm
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inl h.2.symm
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl h.2.symm

/-- A successful array body starts with a token ending within it. -/
theorem parseArray_first {fuel : Nat} {b : ByteArray} {p : Nat} {acc : List PdfObject}
    {xs : List PdfObject} {r : Nat} (h : ObjParse.parseArray fuel b p acc = .ok (xs, r)) :
    ∃ t q, Lex.next b p = .ok (some (t, q)) ∧ q ≤ r := by
  unfold ObjParse.parseArray at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    refine ⟨t, q, h1, ?_⟩
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
    · split at h
      · simp at h
      · rename_i o r1 h2
        have := ObjParse.parseObjTok_pos fuel b p t q o r1 h1'.2 h2
        split at h
        · have := ObjParse.parseArray_pos fuel b _ _ xs r h
          omega
        · simp at h

/-- A successful dictionary body starts with a token ending within it. -/
theorem parseDict_first {fuel : Nat} {b : ByteArray} {p : Nat} {acc : List (Name × PdfObject)}
    {d : List (Name × PdfObject)} {r : Nat} (h : ObjParse.parseDict fuel b p acc = .ok (d, r)) :
    ∃ t q, Lex.next b p = .ok (some (t, q)) ∧ q ≤ r ∧ (∀ g, t ≠ .int g) := by
  unfold ObjParse.parseDict at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    refine ⟨t, q, h1, ?_⟩
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨by omega, fun g hg => by cases hg⟩
    · refine ⟨?_, fun g hg => by cases hg⟩
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
        · rename_i t2 q2 h2
          have h2' := Lex.next_pos _ _ _ _ h2
          split at h
          · simp at h
          · rename_i v r1 h3
            have := ObjParse.parseObjTok_pos fuel b q t2 q2 v r1 h2'.2 h3
            split at h
            · have := ObjParse.parseDict_pos fuel b _ _ d r h
              omega
            · simp at h
    · simp at h

/-- What follows a value inside an array: the rest of a successful array body. -/
theorem follow_of_parseArray {fuel : Nat} {b : ByteArray} {p : Nat} {acc : List PdfObject}
    {xs : List PdfObject} {r : Nat} (h : ObjParse.parseArray fuel b p acc = .ok (xs, r))
    (hr : r < b.size) : Follow b p := by
  obtain ⟨t, q, h1, hq⟩ := parseArray_first h
  refine ⟨⟨t, q, h1, by omega⟩, fun g q' he => ?_⟩
  rw [h1] at he
  simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold ObjParse.parseArray at h
  rw [h1] at h
  simp only [reduceCtorEq, ↓reduceIte] at h
  split at h
  · simp at h
  · rename_i o r1 h2
    unfold ObjParse.parseObjTok at h2
    split at h
    · have hr1 := ObjParse.parseArray_pos fuel b _ _ xs r h
      rcases parseIntTail_next h2 with e | ⟨t2, q2, e2, l2⟩
      · subst e
        obtain ⟨t3, q3, e3, l3⟩ := parseArray_first h
        exact ⟨t3, q3, e3, by omega⟩
      · exact ⟨t2, q2, e2, by omega⟩
    · simp at h

/-- What follows a value inside a dictionary: the rest of a successful dictionary body. -/
theorem follow_of_parseDict {fuel : Nat} {b : ByteArray} {p : Nat}
    {acc : List (Name × PdfObject)} {d : List (Name × PdfObject)} {r : Nat}
    (h : ObjParse.parseDict fuel b p acc = .ok (d, r)) (hr : r < b.size) : Follow b p := by
  obtain ⟨t, q, h1, hq, hni⟩ := parseDict_first h
  refine ⟨⟨t, q, h1, by omega⟩, fun g q' he => ?_⟩
  rw [h1] at he
  simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at he
  exact absurd he.1 (hni g)

mutual

/-- **Objects are prefix-stable** when what follows them (`Follow`) ends inside `b`. -/
theorem parseObjTok_ext {b b' : ByteArray} (hE : Extends b b') (fuel pos : Nat) (t : Token)
    (q : Nat) {o : PdfObject} {r : Nat} (hpos : Lex.skipWs b pos false < b.size)
    (h : ObjParse.parseObjTok fuel b pos t q = .ok (o, r)) (hf : Follow b r) :
    ObjParse.parseObjTok fuel b' pos t q = .ok (o, r) := by
  rw [ObjParse.parseObjTok.eq_def, errAt_ext hE hpos]
  unfold ObjParse.parseObjTok at h
  split at h
  · exact parseIntTail_ext hE hpos h hf
  all_goals first
    | exact h
    | skip
  · split at h
    · simp at h
    · rename_i f
      split at h
      · rename_i xs r' h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := hf.1.lt
        rw [parseArray_ext hE f q [] h1 this]
      · simp at h
  · split at h
    · simp at h
    · rename_i f
      split at h
      · rename_i d r' h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := hf.1.lt
        rw [parseDict_ext hE f q [] h1 this]
      · simp at h
termination_by (fuel, b.size - q)
decreasing_by all_goals (apply Prod.Lex.left; omega)

/-- An array body ending strictly inside `b` parses the same way in `b'`. -/
theorem parseArray_ext {b b' : ByteArray} (hE : Extends b b') (fuel pos : Nat)
    (acc : List PdfObject) {xs : List PdfObject} {r : Nat}
    (h : ObjParse.parseArray fuel b pos acc = .ok (xs, r)) (hr : r < b.size) :
    ObjParse.parseArray fuel b' pos acc = .ok (xs, r) := by
  obtain ⟨t0, q0, h10, hq0⟩ := parseArray_first h
  unfold ObjParse.parseArray at h ⊢
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    rw [h10] at h1
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    split
    · rename_i e he
      rw [next_ext hE pos h10 (by omega)] at he
      cases he
    · rename_i he
      rw [next_ext hE pos h10 (by omega)] at he
      cases he
    · rename_i t' q' he
      rw [next_ext hE pos h10 (by omega)] at he
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      split at h
      · rename_i hc
        simp only [hc, ↓reduceIte]
        exact h
      · rename_i hc
        simp only [hc, ↓reduceIte]
        split at h
        · simp at h
        · rename_i o r1 h2
          split at h
          · rename_i hr1
            have hf := follow_of_parseArray h hr
            rw [parseObjTok_ext hE fuel pos t0 q0 (skipWs_lt_of_next h10) h2 hf]
            simp only [hr1, ↓reduceDIte]
            exact parseArray_ext hE fuel r1 (o :: acc) h hr
          · simp at h
termination_by (fuel, b.size - pos)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; omega)

/-- A dictionary body ending strictly inside `b` parses the same way in `b'`. -/
theorem parseDict_ext {b b' : ByteArray} (hE : Extends b b') (fuel pos : Nat)
    (acc : List (Name × PdfObject)) {d : List (Name × PdfObject)} {r : Nat}
    (h : ObjParse.parseDict fuel b pos acc = .ok (d, r)) (hr : r < b.size) :
    ObjParse.parseDict fuel b' pos acc = .ok (d, r) := by
  obtain ⟨t0, q0, h10, hq0, -⟩ := parseDict_first h
  have hpos := skipWs_lt_of_next h10
  rw [ObjParse.parseDict, errAt_ext hE hpos]
  unfold ObjParse.parseDict at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    rw [h10] at h1
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    split
    · rename_i e he
      rw [next_ext hE pos h10 (by omega)] at he
      cases he
    · rename_i he
      rw [next_ext hE pos h10 (by omega)] at he
      cases he
    · rename_i t' q' he
      rw [next_ext hE pos h10 (by omega)] at he
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      split at h
      · exact h
      · rename_i k
        split at h
        · simp at h
        · rename_i hk
          simp only [hk, ↓reduceIte, Bool.false_eq_true]
          split at h
          · simp at h
          · simp at h
          · rename_i t2 q2 h2
            have h2' := Lex.next_pos _ _ _ _ h2
            split at h
            · simp at h
            · rename_i v r1 h3
              have := ObjParse.parseObjTok_pos fuel b q0 t2 q2 v r1 h2'.2 h3
              split at h
              · rename_i hr1
                have := ObjParse.parseDict_pos fuel b _ _ d r h
                split
                · rename_i e he
                  rw [next_ext hE q0 h2 (by omega)] at he
                  cases he
                · rename_i he
                  rw [next_ext hE q0 h2 (by omega)] at he
                  cases he
                · rename_i t2' q2' he
                  rw [next_ext hE q0 h2 (by omega)] at he
                  simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at he
                  obtain ⟨rfl, rfl⟩ := he
                  have hf := follow_of_parseDict h hr
                  rw [parseObjTok_ext hE fuel q0 t2 q2 (skipWs_lt_of_next h2) h3 hf]
                  simp only [hr1, ↓reduceDIte]
                  exact parseDict_ext hE fuel r1 _ h hr
              · simp at h
      · simp at h
termination_by (fuel, b.size - pos)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; omega)

end

/-- `parseObj` version of `parseObjTok_ext`. -/
theorem parseObj_ext {b b' : ByteArray} (hE : Extends b b') {fuel pos : Nat} {o : PdfObject}
    {r : Nat} (h : ObjParse.parseObj fuel b pos = .ok (o, r)) (hf : Follow b r) :
    ObjParse.parseObj fuel b' pos = .ok (o, r) := by
  unfold ObjParse.parseObj at h ⊢
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    have := ObjParse.parseObjTok_pos fuel b pos t q o r h1'.2 h
    have := hf.1.lt
    rw [next_ext hE pos h1 (by omega)]
    exact parseObjTok_ext hE fuel pos t q (skipWs_lt_of_next h1) h hf

/-- A dictionary object needs no lookahead after its closing `>>`. -/
theorem parseObj_dict_ext {b b' : ByteArray} (hE : Extends b b') {fuel pos : Nat} {d : Dict}
    {r : Nat} (h : ObjParse.parseObj fuel b pos = .ok (.dict d, r)) (hr : r < b.size) :
    ObjParse.parseObj fuel b' pos = .ok (.dict d, r) := by
  unfold ObjParse.parseObj at h ⊢
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    have := ObjParse.parseObjTok_pos fuel b pos t q _ r h1'.2 h
    rw [next_ext hE pos h1 (by omega)]
    show ObjParse.parseObjTok fuel b' pos t q = _
    rw [ObjParse.parseObjTok.eq_def, errAt_ext hE (skipWs_lt_of_next h1)]
    unfold ObjParse.parseObjTok at h
    split at h
    · exfalso
      unfold ObjParse.parseIntTail at h
      repeat' split at h
      all_goals simp at h
    all_goals first
      | exact h
      | skip
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
    · split at h
      · simp at h
      · rename_i f
        split at h
        · rename_i d' r' h2
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hd, rfl⟩ := h
          rw [parseDict_ext hE f q [] h2 hr]
          simp only [Except.ok.injEq, Prod.mk.injEq, and_true]
          exact hd
        · simp at h

/-- A byte range inside `b` extracts the same bytes from `b'`. -/
theorem extract_ext {b b' : ByteArray} (hE : Extends b b') {i j : Nat} (hj : j ≤ b.size) :
    b'.extract i j = b.extract i j := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, ByteArray.size_data]
    have := hE.le
    omega
  · intro k h1 h2
    simp only [Array.getElem_extract]
    simp only [Array.size_extract, ByteArray.size_data] at h2
    have hk : i + k < b.size := by omega
    have := hE.get hk (hE.lt hk)
    simp only [ByteArray.getElem_eq_getElem_data] at this
    exact this

/-- The EOL after `stream` reads the same in `b'`. -/
theorem streamDataStart_ext {b b' : ByteArray} (hE : Extends b b') {p s : Nat}
    (h : ObjParse.streamDataStart b p = some s) : ObjParse.streamDataStart b' p = some s := by
  unfold ObjParse.streamDataStart at h ⊢
  have hp : p < b.size := by
    apply Classical.byContradiction
    intro hn
    rw [getElem?_neg b p hn] at h
    simp at h
  rw [hE.getOpt hp]
  split at h
  · rename_i h13
    simp only [h13, ↓reduceIte]
    split at h
    · rename_i h10
      have hp1 : p + 1 < b.size := Lex.lt_size_of_getElem?_eq_some h10
      rw [hE.getOpt hp1]
      simp only [h10, ↓reduceIte]
      exact h
    · simp at h
  · rename_i h13
    simp only [h13, ↓reduceIte]
    exact h

/-- An optional EOL ending inside `b` is skipped the same way in `b'`. -/
theorem skipEol_ext {b b' : ByteArray} (hE : Extends b b') {p : Nat}
    (h : ObjParse.skipEol b p < b.size) : ObjParse.skipEol b' p = ObjParse.skipEol b p := by
  have := ObjParse.le_skipEol b p
  unfold ObjParse.skipEol at h ⊢
  rw [hE.getOpt (show p < b.size by unfold ObjParse.skipEol at this; omega)]
  split
  · by_cases hp1 : p + 1 < b.size
    · rw [hE.getOpt hp1]
    · rename_i h13
      simp only [h13, ↓reduceIte] at h
      rw [getElem?_neg b (p + 1) hp1] at h
      simp at h
      omega
  · rfl

/-- An expected keyword ending strictly inside `b` reads the same in `b'`. -/
theorem expectKeyword_ext {b b' : ByteArray} (hE : Extends b b') {pos : Nat} {kw : List UInt8}
    {msg : String} {r : Nat} (h : ObjParse.expectKeyword b pos kw msg = .ok r) (hr : r < b.size) :
    ObjParse.expectKeyword b' pos kw msg = .ok r := by
  unfold ObjParse.expectKeyword at h ⊢
  split at h
  · simp at h
  · rename_i k q hq
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      rw [next_ext hE pos hq hr]
      simp only [*, ↓reduceIte]
    · simp at h
  · simp at h

/-- A stream body ending strictly inside `b` parses the same way in `b'` (any length
resolver). -/
theorem parseStreamBodyWith_ext {b b' : ByteArray} (hE : Extends b b')
    {len : ObjParse.LengthResolver} {p : Nat} {d : Dict} {st : Stream} {r : Nat}
    (h : ObjParse.parseStreamBodyWith len b p d = .ok (st, r)) (hr : r < b.size) :
    ObjParse.parseStreamBodyWith len b' p d = .ok (st, r) := by
  unfold ObjParse.parseStreamBodyWith at h ⊢
  split at h
  · simp at h
  · rename_i s hs
    rw [streamDataStart_ext hE hs]
    simp only
    split at h
    · simp at h
    · rename_i l hl
      split at h
      · rename_i hle
        simp only [show s + l ≤ b'.size by have := hE.le; omega, ↓reduceIte]
        dsimp only at h
        split at h
        · rename_i k e2 he
          have he2 := Lex.tokenAt_pos b _ _ _ he
          split at h
          · rename_i hk
            split at h
            · rename_i r0 hr0
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := ObjParse.expectKeyword_pos hr0
              have hs1 := ObjParse.le_skipEol b (s + l)
              rw [skipEol_ext hE (by omega), tokenAt_ext hE _ he (by omega)]
              simp only [hk, ↓reduceIte]
              rw [expectKeyword_ext hE hr0 hr, extract_ext hE (by omega)]
            · simp at h
          · simp at h
        · simp at h
        · simp at h
      · simp at h

/-- An indirect-object body ending strictly inside `b` parses the same way in `b'`. -/
theorem parseIndirectBodyWith_ext {b b' : ByteArray} (hE : Extends b b')
    {len : ObjParse.LengthResolver} {limits : Limits} {p : Nat} {body : IndirectBody} {r : Nat}
    (h : ObjParse.parseIndirectBodyWith len limits b p = .ok (body, r)) (hr : r < b.size) :
    ObjParse.parseIndirectBodyWith len limits b' p = .ok (body, r) := by
  unfold ObjParse.parseIndirectBodyWith at h ⊢
  split at h
  · simp at h
  · rename_i o r1 h1
    split at h
    · simp at h
    · rename_i k r2 h2
      have p2 := Lex.next_pos _ _ _ _ h2
      have hr2 : r2 < b.size := by
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          omega
        · split at h
          · split at h
            · split at h
              · rename_i s0 r3 h3
                obtain ⟨st, q1, -, -, q4, -, -⟩ := ObjParse.parseStreamBodyWith_ok h3
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                omega
              · simp at h
            · simp at h
          · simp at h
      have hf : Follow b r1 :=
        ⟨⟨_, _, h2, hr2⟩, fun g q he => by rw [h2] at he; simp at he⟩
      unfold ObjParse.parseObject at h1 ⊢
      rw [parseObj_ext hE h1 hf]
      simp only
      rw [next_ext hE r1 h2 hr2]
      simp only
      split at h
      · rename_i hk
        simp only [hk, ↓reduceIte]
        exact h
      · rename_i hk
        simp only [hk, ↓reduceIte]
        split at h
        · rename_i hks
          simp only [hks, ↓reduceIte]
          split at h
          · rename_i d
            split at h
            · rename_i s0 r3 h3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [parseStreamBodyWith_ext hE h3 hr]
            · simp at h
          · simp at h
        · simp at h
    · simp at h

/-- An `n g obj` header ending strictly inside `b` reads the same in `b'`. -/
theorem parseHeader_ext {b b' : ByteArray} (hE : Extends b b') {pos : Nat} {n g : Int} {q : Nat}
    (h : ObjParse.parseHeader b pos = .ok (n, g, q)) (hq : q < b.size) :
    ObjParse.parseHeader b' pos = .ok (n, g, q) := by
  unfold ObjParse.parseHeader at h ⊢
  split at h
  · rename_i n0 q1 h1
    have p1 := Lex.next_pos _ _ _ _ h1
    split at h
    · rename_i g0 q2 h2
      have p2 := Lex.next_pos _ _ _ _ h2
      split at h
      · rename_i k q3 h3
        have p3 := Lex.next_pos _ _ _ _ h3
        split at h
        · rename_i hk
          split at h
          · rename_i hr
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            rw [next_ext hE pos h1 (by omega)]
            simp only
            rw [next_ext hE q1 h2 (by omega)]
            simp only
            rw [next_ext hE q2 h3 hq]
            simp only [hk, hr, ↓reduceIte]
          · simp at h
        · simp at h
      · simp at h
      · simp at h
    · simp at h
    · simp at h
  · simp at h
  · simp at h

/-- **Indirect objects are prefix-stable**: an indirect object (with a direct `/Length`) that
parses at `pos` and ends strictly before the end of `b` parses the same way in any
extension of `b`. -/
theorem parseIndirect_ext {b b' : ByteArray} (hE : Extends b b') {limits : Limits} {pos : Nat}
    {io : IndirectObject} {r : Nat} (h : ObjParse.parseIndirect limits b pos = .ok (io, r))
    (hr : r < b.size) : ObjParse.parseIndirect limits b' pos = .ok (io, r) := by
  unfold ObjParse.parseIndirect at h ⊢
  split at h
  · simp at h
  · rename_i n g q hh
    split at h
    · rename_i body r1 hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := (ObjParse.parseIndirectBodyWith_ok hb).1
      rw [parseHeader_ext hE hh (by omega)]
      simp only
      unfold ObjParse.parseIndirectBody at hb ⊢
      rw [parseIndirectBodyWith_ext hE hb hr]
    · simp at h

/-! ## Classic cross-reference tables -/

/-- A keyword found in `b` is found at the same place in any extension. -/
theorem matchAt_true_ext {b b' : ByteArray} (hE : Extends b b') {p : Nat} {kw : List UInt8}
    (h : Xref.matchAt b p kw = true) : Xref.matchAt b' p kw = true := by
  induction kw generalizing p with
  | nil => rfl
  | cons c cs ih =>
    simp only [Xref.matchAt, Bool.and_eq_true, beq_iff_eq] at h ⊢
    have hp := Lex.lt_size_of_getElem?_eq_some h.1
    rw [hE.getOpt hp]
    exact ⟨h.1, ih h.2⟩

/-- A keyword test entirely inside `b` gives the same answer in any extension. -/
theorem matchAt_ext {b b' : ByteArray} (hE : Extends b b') {p : Nat} {kw : List UInt8}
    (h : p + kw.length ≤ b.size) : Xref.matchAt b' p kw = Xref.matchAt b p kw := by
  induction kw generalizing p with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons] at h
    simp only [Xref.matchAt]
    rw [hE.getOpt (show p < b.size by omega), ih (by omega)]

/-- Skipping whitespace that stops inside `b` is the same in `b'`. -/
theorem skipWhite_ext {b b' : ByteArray} (hE : Extends b b') (p : Nat)
    (h : Xref.skipWhite b p < b.size) : Xref.skipWhite b' p = Xref.skipWhite b p := by
  fun_induction Xref.skipWhite b p with
  | case1 p hp hw ih =>
    rw [Xref.skipWhite]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp, hw, ↓reduceIte]
    exact ih h
  | case2 p hp hw =>
    rw [Xref.skipWhite]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp, hw, ↓reduceIte, Bool.false_eq_true]
  | case3 p hp => omega

/-- Skipping spaces that stops inside `b` is the same in `b'`. -/
theorem spacesAt_ext {b b' : ByteArray} (hE : Extends b b') (p : Nat)
    (h : Xref.spacesAt b p < b.size) : Xref.spacesAt b' p = Xref.spacesAt b p := by
  fun_induction Xref.spacesAt b p with
  | case1 p hp hw ih =>
    rw [Xref.spacesAt]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp, hw, ↓reduceIte]
    exact ih h
  | case2 p hp hw =>
    rw [Xref.spacesAt]
    simp only [hE.lt hp, ↓reduceDIte, hE.get hp, hw, ↓reduceIte, Bool.false_eq_true]
  | case3 p hp => omega

/-- The digit test at an in-range position is the same in `b'`. -/
theorem digitAt_ext {b b' : ByteArray} (hE : Extends b b') {p : Nat} (h : p < b.size) :
    Xref.digitAt b' p = Xref.digitAt b p := by
  unfold Xref.digitAt
  rw [hE.getOpt h]

/-- `digitsAt` does not move backwards. -/
theorem le_digitsAt (b : ByteArray) (p acc f : Nat) : p ≤ (Xref.digitsAt b p acc f).2 := by
  induction f generalizing p acc with
  | zero => simp [Xref.digitsAt]
  | succ f ih =>
    simp only [Xref.digitsAt]
    split
    · split
      · rename_i x hx hd
        have := ih (p + 1) (acc * 10 + (x.toNat - 48)); omega
      · simp
    · simp

/-- A digit run ending inside `b` reads the same in `b'`. -/
theorem digitsAt_ext {b b' : ByteArray} (hE : Extends b b') (p acc f : Nat)
    (h : (Xref.digitsAt b p acc f).2 < b.size) :
    Xref.digitsAt b' p acc f = Xref.digitsAt b p acc f := by
  induction f generalizing p acc with
  | zero => rfl
  | succ f ih =>
    have hp : p < b.size := by have := le_digitsAt b p acc (f + 1); omega
    simp only [Xref.digitsAt] at h ⊢
    rw [hE.getOpt hp]
    split
    · split
      · rename_i x hx hd
        rw [hx] at h
        simp only [hd, ↓reduceIte] at h
        exact ih _ _ h
      · rfl
    · rfl

/-- A number ending inside `b` reads the same in `b'`. -/
theorem natAt_ext {b b' : ByteArray} (hE : Extends b b') {p v e : Nat}
    (h : Xref.natAt b p = some (v, e)) (he : e < b.size) : Xref.natAt b' p = some (v, e) := by
  unfold Xref.natAt at h ⊢
  split at h
  rename_i v' e' hd
  have hv : (v', e') = (v, e) := by
    by_cases hc : (p < e' && !Xref.digitAt b e') = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h; exact h
    · simp [hc] at h
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  rw [digitsAt_ext hE p 0 10 (by rw [hd]; exact he), hd]
  simp only
  rw [digitAt_ext hE he]
  exact h

/-- An EOL ending inside `b` reads the same in `b'`. -/
theorem eolAt_ext {b b' : ByteArray} (hE : Extends b b') {p e : Nat}
    (h : Xref.eolAt b p = some e) (he : e < b.size) : Xref.eolAt b' p = some e := by
  have := Xref.eolAt_pos h
  unfold Xref.eolAt at h ⊢
  rw [hE.getOpt (show p < b.size by omega)]
  split
  · rename_i h13
    simp only [h13, ↓reduceIte] at h
    by_cases hp1 : p + 1 < b.size
    · rw [hE.getOpt hp1]; exact h
    · rw [getElem?_neg b (p + 1) hp1] at h
      simp at h
      omega
  · rename_i h13
    simp only [h13, ↓reduceIte] at h
    exact h

/-- A subsection header ending inside `b` reads the same in `b'`. -/
theorem header_ext {b b' : ByteArray} (hE : Extends b b') {q st c e : Nat}
    (h : Xref.header b q = some (st, c, e)) (he : e < b.size) :
    Xref.header b' q = some (st, c, e) := by
  unfold Xref.header at h ⊢
  split at h
  · simp at h
  · rename_i st' e1 h1
    have p1 := Xref.natAt_pos h1
    split at h
    · rename_i hsp
      split at h
      · simp at h
      · rename_i c' e2 h2
        have p2 := Xref.natAt_pos h2
        have s1 := Xref.le_spacesAt b e1
        have s2 := Xref.le_spacesAt b e2
        split at h
        · simp at h
        · rename_i e3 h3
          have p3 := Xref.eolAt_pos h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [natAt_ext hE h1 (by omega)]
          simp only
          rw [hE.getOpt (show e1 < b.size by omega)]
          simp only [hsp, ↓reduceIte]
          rw [spacesAt_ext hE e1 (by omega), natAt_ext hE h2 (by omega)]
          simp only
          rw [spacesAt_ext hE e2 (by omega), eolAt_ext hE h3 he]
    · simp at h

/-- A 20-byte entry inside `b` reads the same in `b'`. -/
theorem entryAt_ext {b b' : ByteArray} (hE : Extends b b') {p : Nat} (h : p + 20 ≤ b.size) :
    Xref.entryAt b' p = Xref.entryAt b p := by
  rw [Xref.entryAt_eq, Xref.entryAt_eq]
  congr 1
  have hle := hE.le
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
    omega
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList]
    simp only [List.length_take, List.length_drop, Array.length_toList,
      ByteArray.size_data] at h2
    have hk : p + k < b.size := by omega
    have := hE.get hk (hE.lt hk)
    simpa [ByteArray.getElem_eq_getElem_data] using this

/-- The entry range check is monotone in the input size. -/
theorem entryOk_mono {n n' : Nat} (hn : n ≤ n') {e : Xref.XrefEntry} (h : Xref.entryOk n e = true) :
    Xref.entryOk n' e = true := by
  cases e <;> simp_all [Xref.entryOk] <;> omega

/-- Entries inside `b` read the same in `b'` (their range checks are monotone in the size). -/
theorem entries_ext {b b' : ByteArray} (hE : Extends b b') (k : Nat) (p num : Nat)
    (acc : List (Nat × Xref.XrefEntry)) {l : List (Nat × Xref.XrefEntry)}
    (h : Xref.entries b p num k acc = .ok l) (hk : p + 20 * k ≤ b.size) :
    Xref.entries b' p num k acc = .ok l := by
  induction k generalizing p num acc with
  | zero => exact h
  | succ k ih =>
    simp only [Xref.entries] at h ⊢
    rw [entryAt_ext hE (by omega)]
    split at h
    · simp at h
    · rename_i e he
      split at h
      · rename_i hok
        simp only [entryOk_mono hE.le hok, ↓reduceIte]
        exact ih _ _ _ h (by omega)
      · simp at h

/-- The subsection loop ends at least 7 bytes (`trailer`) after it starts. -/
theorem sections_pos {limits : Limits} {b : ByteArray} {q total : Nat}
    {acc l : List (Nat × Xref.XrefEntry)} {t : Nat}
    (h : Xref.sections limits b q total acc = .ok (l, t)) : q + 7 ≤ t := by
  fun_induction Xref.sections limits b q total acc with
  | case1 => simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
  | case7 q total acc hm st c e hh hl1 hl2 hs acc' he hq ih =>
    have := ih h
    have := Xref.le_skipWhite b (e + 20 * c)
    omega
  | _ => simp at h

/-- The subsection loop ending inside `b` gives the same result in `b'`. -/
theorem sections_ext {b b' : ByteArray} (hE : Extends b b') {limits : Limits} (q total : Nat)
    (acc : List (Nat × Xref.XrefEntry)) {l : List (Nat × Xref.XrefEntry)} {t : Nat}
    (h : Xref.sections limits b q total acc = .ok (l, t)) (ht : t < b.size) :
    Xref.sections limits b' q total acc = .ok (l, t) := by
  fun_induction Xref.sections limits b q total acc with
  | case1 q total acc hm =>
    rw [Xref.sections]
    simp only [matchAt_true_ext hE hm, ↓reduceIte]
    exact h
  | case7 q total acc hm st c e hh hl1 hl2 hs acc' he hq ih =>
    have h7 := sections_pos h
    have hw := Xref.le_skipWhite b (e + 20 * c)
    rw [Xref.sections]
    rw [matchAt_ext hE (by simp [Xref.kwTrailer]; omega)]
    simp only [hm, ↓reduceIte, Bool.false_eq_true]
    rw [header_ext hE hh (by omega)]
    simp only [hl1, hl2, ↓reduceIte, show ¬ b'.size < e + 20 * c by have := hE.le; omega,
      ↓reduceDIte]
    rw [entries_ext hE c e st acc he (by omega)]
    simp only [hq, ↓reduceDIte]
    rw [skipWhite_ext hE _ (by omega)]
    exact ih h
  | _ => simp at h

/-- The trailer dictionary ending inside `b` reads the same in `b'`. -/
theorem finish_ext {b b' : ByteArray} (hE : Extends b b') {limits : Limits} {pos t : Nat}
    {acc : List (Nat × Xref.XrefEntry)} {sec : Xref.XrefSection} {tr : Xref.Trailer} {r : Nat}
    (h : Xref.finish limits b pos t acc = .ok (sec, tr, r)) (hr : r < b.size) :
    Xref.finish limits b' pos t acc = .ok (sec, tr, r) := by
  unfold Xref.finish at h ⊢
  split at h
  · simp at h
  · rename_i d r1 h1
    have hr1 : r1 = r := by
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact h.2.2
    subst hr1
    unfold ObjParse.parseObject at h1 ⊢
    rw [parseObj_dict_ext hE h1 hr]
    exact h
  · simp at h

/-- **Classic tables are prefix-stable**: a table (and trailer) that parses at `pos` and
ends strictly before the end of `b` parses the same way in any extension of `b`. -/
theorem parseXrefTable_ext {b b' : ByteArray} (hE : Extends b b') {limits : Limits} {pos : Nat}
    {sec : Xref.XrefSection} {tr : Xref.Trailer} {r : Nat}
    (h : Xref.parseXrefTable limits b pos = .ok (sec, tr, r)) (hr : r < b.size) :
    Xref.parseXrefTable limits b' pos = .ok (sec, tr, r) := by
  unfold Xref.parseXrefTable at h ⊢
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    split at h
    · simp at h
    · rename_i acc t hs
      have h7 := sections_pos hs
      have hw := Xref.le_skipWhite b (pos + 4)
      have hfin := h
      unfold Xref.finish at hfin
      have htr : t < r := by
        split at hfin
        · simp at hfin
        · rename_i d r1 h1
          have := ObjParse.parseObj_pos h1
          split at hfin
          · simp at hfin
          · split at hfin
            · simp at hfin
            · simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
              omega
        · simp at hfin
      rw [matchAt_true_ext hE hc.1, hE.getOpt (show pos + 4 < b.size by omega)]
      simp only [hc.2, Bool.and_self, ↓reduceIte]
      rw [skipWhite_ext hE _ (by omega), sections_ext hE _ _ _ hs (by omega)]
      exact finish_ext hE h hr
  · simp at h

/-! ## Cross-reference streams -/

/-- An xref-stream entry accepted for an input size is accepted for a larger one. -/
theorem mkEntry_mono {n n' size k t f2 f3 at_ : Nat} (hn : n ≤ n') {e : Xref.XrefEntry}
    (h : Xref.Stream.mkEntry n size k t f2 f3 at_ = .ok e) :
    Xref.Stream.mkEntry n' size k t f2 f3 at_ = .ok e := by
  unfold Xref.Stream.mkEntry at h ⊢
  by_cases h0 : t = 0
  · simp only [h0, ↓reduceIte] at h ⊢; exact h
  · by_cases h1 : t = 1
    · simp only [h1, ↓reduceIte, Nat.one_ne_zero] at h ⊢
      by_cases hs : n ≤ f2
      · simp [hs] at h
      · simp only [hs, ↓reduceIte] at h
        simp only [show ¬ n' ≤ f2 by omega, ↓reduceIte]
        exact h
    · simp only [h0, h1, ↓reduceIte] at h ⊢; exact h

/-- Xref-stream rows accepted for an input size are accepted for a larger one. -/
theorem rows_mono {n n' size at_ : Nat} (hn : n ≤ n') (data : ByteArray) (w : Xref.Stream.Widths)
    (k : Nat) (m p : Nat) (acc : List (Nat × Xref.XrefEntry)) {l : List (Nat × Xref.XrefEntry)}
    (h : Xref.Stream.rows n size at_ data w m p k acc = .ok l) :
    Xref.Stream.rows n' size at_ data w m p k acc = .ok l := by
  induction k generalizing m p acc with
  | zero => exact h
  | succ k ih =>
    simp only [Xref.Stream.rows] at h ⊢
    split at h
    · simp at h
    · rename_i e he
      rw [mkEntry_mono hn he]
      exact ih _ _ _ h

/-- Xref-stream subsections accepted for an input size are accepted for a larger one. -/
theorem subsections_mono {n n' size at_ : Nat} (hn : n ≤ n') (data : ByteArray)
    (w : Xref.Stream.Widths) (p : Nat) (subs : List (Nat × Nat))
    (acc : List (Nat × Xref.XrefEntry)) {l : List (Nat × Xref.XrefEntry)}
    (h : Xref.Stream.subsections n size at_ data w p subs acc = .ok l) :
    Xref.Stream.subsections n' size at_ data w p subs acc = .ok l := by
  induction subs generalizing p acc with
  | nil => exact h
  | cons sc rest ih =>
    obtain ⟨st, c⟩ := sc
    simp only [Xref.Stream.subsections] at h ⊢
    split at h
    · simp at h
    · rename_i acc' ha
      rw [rows_mono hn data w c st p acc ha]
      exact ih _ _ h

/-- An xref stream starts with a digit (of its object number). -/
theorem digitAt_of_parseXrefStream {limits : Limits} {b : ByteArray} {off : Nat}
    {x : Xref.XrefSection × Xref.Trailer}
    (h : Xref.Stream.parseXrefStream limits b off = .ok x) : Xref.digitAt b off = true := by
  cases hd : Xref.digitAt b off
  · unfold Xref.Stream.parseXrefStream at h
    simp [hd] at h
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rfl

/-- At a position without a digit the xref-stream parser fails at once. -/
theorem parseXrefStream_of_not_digit {limits : Limits} {b : ByteArray} {off : Nat}
    (hd : Xref.digitAt b off = false) :
    Xref.Stream.parseXrefStream limits b off =
      .error (.malformed off "expected an xref keyword or an xref stream object") := by
  unfold Xref.Stream.parseXrefStream
  simp only [hd, Bool.not_false, ↓reduceIte]
  rfl

/-- **Xref streams are prefix-stable** when their indirect object ends strictly inside `b`. -/
theorem parseXrefStream_ext {b b' : ByteArray} (hE : Extends b b') {limits : Limits} {off : Nat}
    {x : Xref.XrefSection × Xref.Trailer}
    (h : Xref.Stream.parseXrefStream limits b off = .ok x)
    (hr : ∀ io r, ObjParse.parseIndirect limits b off = .ok (io, r) → r < b.size) :
    Xref.Stream.parseXrefStream limits b' off = .ok x := by
  have hd : Xref.digitAt b off = true := digitAt_of_parseXrefStream h
  have hoff : off < b.size := by
    unfold Xref.digitAt at hd
    split at hd
    · rename_i x hx; exact Lex.lt_size_of_getElem?_eq_some hx
    · simp at hd
  unfold Xref.Stream.parseXrefStream at h ⊢
  rw [digitAt_ext hE hoff]
  simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hp : ObjParse.parseIndirect limits b off with
  | error e =>
    rw [hp] at h
    simp [bind, Except.bind] at h
  | ok v =>
    obtain ⟨io, r⟩ := v
    rw [parseIndirect_ext hE hp (hr io r hp)]
    rw [hp] at h
    have hle := hE.le
    generalize b.size = n at h hle
    generalize b'.size = n' at hle ⊢
    simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h ⊢
    split at h
    · rename_i st hb
      try simp only [hb]
      split at h
      · simp at h
      · rename_i hty
        try simp only [hty, ↓reduceIte, Bool.false_eq_true]
        split at h
        · simp at h
        · rename_i tr htr
          try simp only [htr]
          split at h
          · simp at h
          · rename_i w hw
            try simp only [hw]
            split at h
            · simp at h
            · rename_i subs hs
              try simp only [hs]
              split at h
              · simp at h
              · rename_i hany
                try simp only [hany, ↓reduceIte, Bool.false_eq_true]
                split at h
                · simp at h
                · rename_i hmax
                  try simp only [hmax, ↓reduceIte]
                  split at h
                  · simp at h
                  · rename_i data hdata
                    try simp only [hdata]
                    split at h
                    · simp at h
                    · rename_i hsz
                      try simp only [hsz, ↓reduceIte, Bool.false_eq_true]
                      split at h
                      · simp at h
                      · rename_i acc hacc
                        rw [subsections_mono hle _ _ _ _ _ hacc]
                        exact h
    · simp at h

/-! ## The last token of a section -/

/-- A number token is an integer or a real. -/
theorem parseNumber_shape {l : List UInt8} {t : Token} (h : Lex.parseNumber l = some t) :
    (∃ i, t = .int i) ∨ (∃ d, t = .real d) := by
  unfold Lex.parseNumber at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h
       subst h
       first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)

/-- A classified run is the keyword itself or a number. -/
theorem classifyRun_shape {run : List UInt8} {t : Token} (h : Lex.classifyRun run = .ok t) :
    t = .keyword run ∨ Lex.parseNumber run = some t := by
  unfold Lex.classifyRun at h
  split at h
  · split at h
    · split at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact Or.inr ‹_›
      · simp at h
    · simp only [Except.ok.injEq] at h
      exact Or.inl h.symm
  · simp only [Except.ok.injEq] at h
    exact Or.inl h.symm

/-- A non-empty regular run ends with the byte before its end position. -/
theorem readRun_last {b : ByteArray} {pos : Nat} {acc l : List UInt8} {q : Nat}
    (h : Lex.readRun b pos acc = (l, q)) :
    (q = pos ∧ l = acc.reverse) ∨ (pos < q ∧ l.getLast? = b[q - 1]?) := by
  fun_induction Lex.readRun b pos acc with
  | case1 pos acc hp bb hr ih =>
    rcases ih h with ⟨rfl, rfl⟩ | ⟨hq, hl⟩
    · refine Or.inr ⟨by omega, ?_⟩
      simp only [List.reverse_cons, List.getLast?_concat, Nat.add_sub_cancel]
      rw [getElem?_pos b pos hp]
    · exact Or.inr ⟨by omega, hl⟩
  | case2 pos acc hp bb hr =>
    simp only [Prod.mk.injEq] at h
    exact Or.inl ⟨h.2.symm, h.1.symm⟩
  | case3 pos acc hp =>
    simp only [Prod.mk.injEq] at h
    exact Or.inl ⟨h.2.symm, h.1.symm⟩

/-- A keyword of at least two bytes lexed by `next` ends with its last byte. -/
theorem next_keyword_last {b : ByteArray} {p : Nat} {k : List UInt8} {q : Nat}
    (h : Lex.next b p = .ok (some (.keyword k, q))) (hk : 2 ≤ k.length) :
    b[q - 1]? = k.getLast? := by
  unfold Lex.next Lex.tokenAt at h
  split at h
  · rename_i hs
    unfold Lex.tokenOf at h
    repeat' (split at h; (first | (simp at h; done) | skip))
    all_goals first
      | (simp [Lex.liftAt] at h; done)
      | skip
    all_goals first
      | (split at h <;> simp_all [Lex.liftAt]; done)
      | skip
    · unfold Lex.liftAt at h
      split at h <;> simp at h
    · unfold Lex.liftAt at h
      split at h <;> simp at h
    · unfold Lex.runToken at h
      split at h
      rename_i run q' hrq
      split at h
      · rename_i t ht
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases classifyRun_shape ht with e | e
        · simp only [Token.keyword.injEq] at e
          subst e
          rcases readRun_last hrq with ⟨-, e2⟩ | ⟨-, e2⟩
          · subst e2; simp at hk
          · exact e2.symm
        · rcases parseNumber_shape e with ⟨i, hi⟩ | ⟨d, hd⟩
          · cases hi
          · cases hd
      · simp at h
  · simp at h

/-- `>>` lexed by `next` ends with `>`. -/
theorem next_dictClose_last {b : ByteArray} {p q : Nat}
    (h : Lex.next b p = .ok (some (.dictClose, q))) : b[q - 1]? = some 62 := by
  unfold Lex.next Lex.tokenAt at h
  split at h
  · rename_i hs
    unfold Lex.tokenOf at h
    repeat' (split at h; (first | (simp at h; done) | skip))
    all_goals first
      | (simp [Lex.liftAt] at h; done)
      | skip
    all_goals first
      | (split at h <;> simp_all [Lex.liftAt]; done)
      | skip
    all_goals first
      | (rename_i h62
         simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨-, rfl⟩ := h
         simp only [beq_iff_eq] at h62
         rw [show Lex.skipWs b p false + 2 - 1 = Lex.skipWs b p false + 1 by omega]
         exact h62)
      | (unfold Lex.liftAt at h
         split at h <;> simp at h
         done)
      | (unfold Lex.runToken at h
         split at h
         rename_i run q' hrq
         split at h
         · rename_i t ht
           simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h
           rcases classifyRun_shape ht with e | e
           · cases e
           · rcases parseNumber_shape e with ⟨i, hi⟩ | ⟨d, hd⟩
             · cases hi
             · cases hd
         · simp at h)
  · simp at h

/-- A dictionary body ends with `>`. -/
theorem parseDict_last (fuel : Nat) (b : ByteArray) (p : Nat) (acc : List (Name × PdfObject))
    {d : List (Name × PdfObject)} {r : Nat} (h : ObjParse.parseDict fuel b p acc = .ok (d, r)) :
    b[r - 1]? = some 62 := by
  unfold ObjParse.parseDict at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact next_dictClose_last h1
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · exact parseDict_last fuel b _ _ h
            · simp at h
    · simp at h
termination_by b.size - p
decreasing_by omega

/-- A classic section (its trailer dictionary) ends with `>`. -/
theorem parseXrefTable_last {limits : Limits} {b : ByteArray} {o : Nat} {sec : Xref.XrefSection}
    {tr : Xref.Trailer} {r : Nat} (h : Xref.parseXrefTable limits b o = .ok (sec, tr, r)) :
    b[r - 1]? = some 62 := by
  unfold Xref.parseXrefTable at h
  split at h
  · split at h
    · simp at h
    · unfold Xref.finish at h
      split at h
      · simp at h
      · rename_i d r1 h1
        have hr1 : r1 = r := by
          split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              exact h.2.2
        subst hr1
        unfold ObjParse.parseObject ObjParse.parseObj at h1
        split at h1
        · simp at h1
        · simp at h1
        · unfold ObjParse.parseObjTok at h1
          split at h1
          · exfalso
            unfold ObjParse.parseIntTail at h1
            repeat' split at h1
            all_goals simp at h1
          all_goals first
            | (simp at h1; done)
            | skip
          · split at h1
            · rename_i o' ho
              simp only [Except.ok.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, -⟩ := h1
              unfold ObjParse.keywordObj at ho
              repeat' split at ho
              all_goals simp at ho
            · simp at h1
          · split at h1
            · simp at h1
            · split at h1 <;> simp at h1
          · split at h1
            · simp at h1
            · split at h1
              · rename_i d' r' h2
                simp only [Except.ok.injEq, Prod.mk.injEq] at h1
                obtain ⟨-, rfl⟩ := h1
                exact parseDict_last _ _ _ _ h2
              · simp at h1
      · simp at h
  · simp at h

/-- An indirect object ends with the keyword `endobj`. -/
theorem parseIndirect_last {limits : Limits} {b : ByteArray} {o : Nat} {io : IndirectObject}
    {r : Nat} (h : ObjParse.parseIndirect limits b o = .ok (io, r)) :
    ∃ p, Lex.next b p = .ok (some (.keyword ObjParse.kwEndobj, r)) := by
  unfold ObjParse.parseIndirect at h
  split at h
  · simp at h
  · split at h
    · rename_i body r1 hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      unfold ObjParse.parseIndirectBody ObjParse.parseIndirectBodyWith at hb
      split at hb
      · simp at hb
      · rename_i ob r2 h2
        split at hb
        · simp at hb
        · rename_i k r3 h3
          split at hb
          · rename_i hk
            simp only [Except.ok.injEq, Prod.mk.injEq] at hb
            obtain ⟨-, rfl⟩ := hb
            exact ⟨r2, hk ▸ h3⟩
          · split at hb
            · split at hb
              · split at hb
                · rename_i s0 r4 h4
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hb
                  obtain ⟨-, rfl⟩ := hb
                  unfold ObjParse.parseStreamBodyWith at h4
                  split at h4
                  · simp at h4
                  · split at h4
                    · simp at h4
                    · split at h4
                      · dsimp only at h4
                        split at h4
                        · split at h4
                          · split at h4
                            · rename_i r5 h5
                              simp only [Except.ok.injEq, Prod.mk.injEq] at h4
                              obtain ⟨-, rfl⟩ := h4
                              unfold ObjParse.expectKeyword at h5
                              split at h5
                              · simp at h5
                              · rename_i k6 q6 h6
                                split at h5
                                · rename_i hk6
                                  simp only [Except.ok.injEq] at h5
                                  subst h5
                                  exact ⟨_, hk6 ▸ h6⟩
                                · simp at h5
                              · simp at h5
                            · simp at h4
                          · simp at h4
                        · simp at h4
                        · simp at h4
                      · simp at h4
                · simp at hb
              · simp at hb
            · simp at hb
        · simp at hb
    · simp at h

/-- The input of a file whose `startxref` is found ends with `F` (of `%%EOF`) or whitespace. -/
theorem skipWhite_last {b : ByteArray} {p : Nat} (h : Xref.skipWhite b p = b.size)
    (hp : p < b.size) : ∃ c, b[b.size - 1]? = some c ∧ Lex.isWhite c = true := by
  fun_induction Xref.skipWhite b p with
  | case1 p hp' hw ih =>
    by_cases h1 : p + 1 < b.size
    · exact ih h h1
    · refine ⟨b[p], ?_, hw⟩
      rw [show b.size - 1 = p by omega, getElem?_pos b p hp']
  | case2 p hp' hw => omega
  | case3 p hp' => omega

/-- A file whose `startxref` is found ends with `F` (of `%%EOF`) or whitespace. -/
theorem findStartxref_last {b : ByteArray} {window s : Nat}
    (h : Xref.findStartxref b window = .ok s) :
    0 < b.size ∧ (b[b.size - 1]? = some 70 ∨
      ∃ c, b[b.size - 1]? = some c ∧ Lex.isWhite c = true) := by
  unfold Xref.findStartxref Xref.findStartxrefIn at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · rename_i off e he
        split at h
        · rename_i hm
          split at h
          · rename_i hw
            have hm' := hm
            simp only [Xref.matchAt, Xref.kwEOF, Bool.and_eq_true, beq_iff_eq] at hm'
            have h4 := Lex.lt_size_of_getElem?_eq_some hm'.2.2.2.2.1
            refine ⟨by omega, ?_⟩
            by_cases h5 : Xref.skipWhite b e + 5 < b.size
            · exact Or.inr (skipWhite_last hw h5)
            · left
              rw [show b.size - 1 = Xref.skipWhite b e + 4 by
                have := Xref.le_skipWhite b (Xref.skipWhite b e + 5); omega]
              exact hm'.2.2.2.2.1
          · simp at h
        · simp at h
    · simp at h

/-- A byte known to be `c` at `r - 1` is not the last byte of a file whose `startxref` is
found, when `c` is neither `F` nor whitespace: the token ending at `r` ends before the end. -/
theorem end_lt_of_last {b : ByteArray} {start r : Nat} {c : UInt8}
    (hs : Xref.findStartxref b = .ok start) (hl : b[r - 1]? = some c) (hc70 : c ≠ 70)
    (hcw : Lex.isWhite c = false) : r < b.size := by
  have hlt := Lex.lt_size_of_getElem?_eq_some hl
  obtain ⟨hpos, hend⟩ := findStartxref_last hs
  apply Classical.byContradiction
  intro hn
  have hr : r - 1 = b.size - 1 := by omega
  rw [hr] at hl
  rcases hend with he | ⟨c', he, hw⟩
  · rw [hl] at he
    exact hc70 (Option.some.inj he)
  · rw [hl] at he
    cases he
    rw [hcw] at hw
    cases hw

/-- In a file whose `startxref` is found, a classic section ends strictly before the end. -/
theorem parseXrefTable_end_lt {limits : Limits} {b : ByteArray} {start o : Nat}
    (hs : Xref.findStartxref b = .ok start) {sec : Xref.XrefSection} {tr : Xref.Trailer}
    {r : Nat} (h : Xref.parseXrefTable limits b o = .ok (sec, tr, r)) : r < b.size :=
  end_lt_of_last hs (parseXrefTable_last h) (by decide) (by decide)

/-- In a file whose `startxref` is found, an indirect object ends strictly before the end. -/
theorem parseIndirect_end_lt {limits : Limits} {b : ByteArray} {start o : Nat}
    (hs : Xref.findStartxref b = .ok start) {io : IndirectObject} {r : Nat}
    (h : ObjParse.parseIndirect limits b o = .ok (io, r)) : r < b.size := by
  obtain ⟨p, hp⟩ := parseIndirect_last h
  have := next_keyword_last hp (by decide)
  exact end_lt_of_last hs (c := 106) (by rw [this]; rfl) (by decide) (by decide)

/-! ## Sections are stable under appending -/

/-- The byte at `o` decides the `xref` keyword test against a digit. -/
theorem matchAt_xref_of_digit {b : ByteArray} {o : Nat} (hd : Xref.digitAt b o = true) :
    Xref.matchAt b o Xref.kwXref = false := by
  unfold Xref.digitAt at hd
  split at hd
  · rename_i c hc
    simp only [Xref.matchAt, Xref.kwXref, hc, Bool.and_eq_false_iff]
    left
    cases hx : (some c == some (120 : UInt8))
    · rfl
    · simp only [beq_iff_eq, Option.some.injEq] at hx
      subst hx
      simp [Lex.isDigit] at hd
  · simp at hd

/-- The `xref` keyword is not a digit. -/
theorem digitAt_of_matchAt_xref {b : ByteArray} {o : Nat}
    (hm : Xref.matchAt b o Xref.kwXref = true) : Xref.digitAt b o = false := by
  simp only [Xref.matchAt, Xref.kwXref, Bool.and_eq_true, beq_iff_eq] at hm
  unfold Xref.digitAt
  rw [hm.1]
  decide

/-- **Xref streams are prefix-stable** (in a file whose `startxref` is found): an xref stream
that parses at `o` in `b` parses the same way in every extension `b'` of `b`. -/
theorem parseXrefStream_stable {b b' : ByteArray} (hE : Extends b b') {start : Nat}
    (hs : Xref.findStartxref b = .ok start) {limits : Limits} {o : Nat}
    {x : Xref.XrefSection × Xref.Trailer} (h : Xref.Stream.parseXrefStream limits b o = .ok x) :
    Xref.Stream.parseXrefStream limits b' o = .ok x :=
  parseXrefStream_ext hE h (fun _ _ hp => parseIndirect_end_lt hs hp)

/-- **Classic tables are prefix-stable** (in a file whose `startxref` is found). -/
theorem parseXrefTable_stable {b b' : ByteArray} (hE : Extends b b') {start : Nat}
    (hs : Xref.findStartxref b = .ok start) {limits : Limits} {o : Nat}
    {sec : Xref.XrefSection} {tr : Xref.Trailer} {r : Nat}
    (h : Xref.parseXrefTable limits b o = .ok (sec, tr, r)) :
    Xref.parseXrefTable limits b' o = .ok (sec, tr, r) :=
  parseXrefTable_ext hE h (parseXrefTable_end_lt hs h)

/-- **An xref-stream offset reads the same in every extension**: the section parse, the
`xref` keyword test and the xref-stream parse agree. -/
theorem stream_stable {b b' : ByteArray} (hE : Extends b b') {start : Nat}
    (hs : Xref.findStartxref b = .ok start) {limits : Limits} {o : Nat}
    {x : Xref.XrefSection × Xref.Trailer} (h : Xref.Stream.parseXrefStream limits b o = .ok x) :
    Xref.Chain.parseSection limits b' o = Xref.Chain.parseSection limits b o ∧
      Xref.matchAt b' o Xref.kwXref = Xref.matchAt b o Xref.kwXref ∧
      Xref.Stream.parseXrefStream limits b' o = Xref.Stream.parseXrefStream limits b o := by
  have hd := digitAt_of_parseXrefStream h
  have hd' := digitAt_of_parseXrefStream (parseXrefStream_stable hE hs h)
  have hm := matchAt_xref_of_digit hd
  have hm' := matchAt_xref_of_digit hd'
  have h' := parseXrefStream_stable hE hs h
  refine ⟨?_, by rw [hm, hm'], by rw [h, h']⟩
  unfold Xref.Chain.parseSection
  simp only [hm, hm', Bool.false_eq_true, ↓reduceIte, h, h']

/-- **A section offset reads the same in every extension** (in a file whose `startxref` is
found): if the section at `o` parses (classic table or xref stream), the section parse, the
`xref` keyword test and the xref-stream parse agree in `b` and `b'`. -/
theorem section_stable {b b' : ByteArray} (hE : Extends b b') {start : Nat}
    (hs : Xref.findStartxref b = .ok start) {limits : Limits} {o : Nat}
    {x : Xref.XrefSection × Xref.Trailer} (h : Xref.Chain.parseSection limits b o = .ok x) :
    Xref.Chain.parseSection limits b' o = Xref.Chain.parseSection limits b o ∧
      Xref.matchAt b' o Xref.kwXref = Xref.matchAt b o Xref.kwXref ∧
      Xref.Stream.parseXrefStream limits b' o = Xref.Stream.parseXrefStream limits b o := by
  cases hm : Xref.matchAt b o Xref.kwXref
  · have h' := h
    unfold Xref.Chain.parseSection at h'
    simp only [hm, Bool.false_eq_true, ↓reduceIte] at h'
    have := stream_stable hE hs h'
    rw [hm] at this
    exact this
  · have hm' := matchAt_true_ext hE hm
    have hd := digitAt_of_matchAt_xref hm
    have hd' := digitAt_of_matchAt_xref hm'
    unfold Xref.Chain.parseSection at h ⊢
    simp only [hm, hm', ↓reduceIte] at h ⊢
    split at h
    · rename_i sec tr r ht
      rw [parseXrefTable_stable hE hs ht, parseXrefStream_of_not_digit hd,
        parseXrefStream_of_not_digit hd']
      simp
    · simp at h

end SafePdf.Spec.PrefixStable
