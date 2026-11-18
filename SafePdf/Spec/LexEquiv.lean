import SafePdf.Spec.Lex
import SafePdf.Core.Lex

/-!
# Lexer equivalence: efficient tokenizer = denotational spec (Plan.md §4 C5, §5.1 step 3)

Task 1.6, the first spec/impl/equivalence triple of the project. The efficient tokenizer
`SafePdf.Core.Lex.next` (over a `ByteArray` and a position) is proven equal to the
denotational spec `SafePdf.Spec.Lex.next` (over the rest of the input as a list), as fixed by
the interface contract in `SafePdf/Core/Token.lean`:

* `next_eq`: `Core.Lex.next bytes pos` is `Spec.Lex.next (bytes.data.toList.drop pos)` with
  the spec's rest `r` translated to the position `bytes.size - r.length` and error offsets
  shifted by `pos`. It holds for every `pos` (no hypothesis): past the end both sides are
  `ok none`.
* `lexAll_eq`: `Core.Lex.lexAll bytes = Spec.Lex.lexAll bytes.data.toList`, exactly (both
  report absolute offsets for whole-input lexing).

## Proof pattern (seed for `docs/proof-patterns.md`)

1. **One bridge.** `restAt bytes p := bytes.data.toList.drop p`. `restAt_cons`
   (`p < size → restAt p = bytes[p] :: restAt (p+1)`), `restAt_nil`, `length_restAt`
   (`size - p`) and `getElem?_eq_head?` translate every array access into list structure.
2. **One lemma per scanner,** by `fun_induction` on the core function (its position
   recursion), with every accumulator generalized: the core result equals the spec function
   applied to `restAt bytes pos`, with `acc.reverse ++ ·` on the payload and
   `bytes.size - rest.length` as the position (`readRun_eq`, `hexStr_eq`, `nameRun_eq`,
   `litStr_eq`, `skipWs_rest`). Pure list functions (`parseNumber_eq`) go by structural
   induction.
3. **Unfold the spec one step at a time** with `rw [f.eq_def]` under `conv => lhs`, never
   `simp [f]` on a well-founded definition; small step lemmas (`litBody_open`, …) keep the
   case proofs short.
4. **Dependent matches** in the spec (`match h : bs with`) block `simp` rewriting of the
   discriminant: first `generalize hr : restAt bytes (q+1) = cs`, keeping the facts you need
   about `cs` (`bytes[q+1]? = cs.head?`, `restAt (q+2) = cs.tail`), then `cases cs`.
5. **Finite byte facts** (`hexVal?` vs `hexVal`, octal and digit arithmetic, class
   inclusions) are closed by `decide` over all 256 bytes.
6. **Dispatch** (`tokenAt_eq`): `by_cases` on each first byte in the core's order, `subst`
   the byte, and let `simp` evaluate both `if` chains; errors line up via `off + base = p`.
7. **Iteration** (`lexAll_go_eq`): a spec rest is a suffix of the input (`next_suffix`), so
   it is `restAt` of its position (`restAt_of_suffix`); then `fun_induction` on the core
   loop, with the spec loop unfolded through equation lemmas (`lexAll_of_some`, …) rather
   than `split` on its dependent `match h : next l`.
-/

namespace SafePdf.Spec.LexEquiv

open SafePdf


/-! ## Bridging positions and lists -/

/-- The input from position `p` on, as the spec sees it: `bytes.data.toList.drop p`. -/
def restAt (bytes : ByteArray) (p : Nat) : List UInt8 := bytes.data.toList.drop p

/-- **Bridging lemma.** Inside the input, the rest at `p` is the byte at `p` followed by the rest at
`p + 1`. -/
theorem restAt_cons {bytes : ByteArray} {p : Nat} (h : p < bytes.size) :
    restAt bytes p = bytes[p] :: restAt bytes (p + 1) := by
  unfold restAt
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp
  rfl

/-- At or past the end of input the rest is empty. -/
theorem restAt_nil {bytes : ByteArray} {p : Nat} (h : bytes.size ≤ p) : restAt bytes p = [] := by
  unfold restAt; simp; omega

/-- The rest at `p` has `bytes.size - p` bytes, so a spec rest `r` sits at position
`bytes.size - r.length`. -/
theorem length_restAt (bytes : ByteArray) (p : Nat) : (restAt bytes p).length = bytes.size - p := by
  simp [restAt]

/-- The rest at `p + 1` is the tail of the rest at `p` (also past the end). -/
theorem restAt_succ (bytes : ByteArray) (p : Nat) :
    restAt bytes (p + 1) = (restAt bytes p).tail := by
  simp [restAt, List.tail_drop]

/-- An optional byte lookup is the head of the rest. -/
theorem getElem?_eq_head? (bytes : ByteArray) (p : Nat) : bytes[p]? = (restAt bytes p).head? := by
  unfold restAt
  simp
  by_cases h : p < bytes.size
  · rw [getElem?_pos bytes p h, getElem?_pos bytes.data p h]; rfl
  · rw [getElem?_neg bytes p h, getElem?_neg bytes.data p h]

/-- A successful lookup at `q` splits the rest at `q`. -/
theorem restAt_of_getElem? {bytes : ByteArray} {q : Nat} {c : UInt8} (h : bytes[q]? = some c) :
    restAt bytes q = c :: restAt bytes (q + 1) := by
  rw [getElem?_eq_head?] at h
  rw [restAt_succ]
  cases hr : restAt bytes q with
  | nil => simp [hr] at h
  | cons x t => simp [hr] at h; simp [h]

/-- A failed lookup at `q` means the rest at `q` is empty. -/
theorem restAt_nil_of_getElem? {bytes : ByteArray} {q : Nat} (h : bytes[q]? = none) :
    restAt bytes q = [] := by
  rw [getElem?_eq_head?] at h
  simpa using h

/-! ## Byte classes and arithmetic -/

/-- The two lexers share the whitespace class. -/
theorem core_isWhite (b : UInt8) : Core.Lex.isWhite b = Spec.Lex.isWhite b := rfl

/-- The two lexers share the regular-byte class. -/
theorem core_isRegular (b : UInt8) : Core.Lex.isRegular b = Spec.Lex.isRegular b := rfl

/-- The two lexers share the digit class. -/
theorem core_isDigit (b : UInt8) : Core.Lex.isDigit b = Spec.Lex.isDigit b := rfl

/-- The two lexers share the octal-digit class. -/
theorem core_isOctal (b : UInt8) : Core.Lex.isOctal b = Spec.Lex.isOctal b := rfl

attribute [local simp] core_isWhite core_isRegular core_isDigit core_isOctal

/-- For a digit, the `UInt8` subtraction of the core equals the `Nat` subtraction of the spec. -/
theorem digit_sub (b : UInt8) (h : Spec.Lex.isDigit b = true) : (b - 48).toNat = b.toNat - 48 := by
  revert b h; decide

/-- The core hex-digit value (`UInt8`) is the spec value (`Nat`) cast to a byte (checked on all 256
bytes). -/
theorem hexVal?_eq : ∀ b : UInt8, Core.Lex.hexVal? b = (Spec.Lex.hexVal b).map UInt8.ofNat := by
  decide

/-- Spec hex-digit values (defaulting to 0) are below 16 (checked on all 256 bytes). -/
theorem hexVal_lt_aux : ∀ b : UInt8, (Spec.Lex.hexVal b).getD 0 < 16 := by decide

/-- A spec hex-digit value is below 16. -/
theorem hexVal_lt {b : UInt8} {v : Nat} (h : Spec.Lex.hexVal b = some v) : v < 16 := by
  have := hexVal_lt_aux b; rw [h] at this; simpa using this

/-- Hex digits are regular bytes (checked on all 256 bytes). -/
theorem isRegular_of_hexVal_aux : ∀ b : UInt8,
    (Spec.Lex.hexVal b).isSome = true → Spec.Lex.isRegular b = true := by decide

/-- A byte with a hex-digit value is regular. -/
theorem isRegular_of_hexVal {b : UInt8} {v : Nat} (h : Spec.Lex.hexVal b = some v) :
    Spec.Lex.isRegular b = true := isRegular_of_hexVal_aux b (by simp [h])

/-- A regular byte is not NUL (checked on all 256 bytes). -/
theorem ne_zero_of_regular_aux :
    ∀ b : UInt8, Spec.Lex.isRegular b = true → (b == 0) = false := by
  decide

/-- For an octal digit, the spec's `UInt8.ofNat (c.toNat - 48)` is the core's `c - 48`. -/
theorem ofNat_octal_aux :
    ∀ c : UInt8, Spec.Lex.isOctal c = true → UInt8.ofNat (c.toNat - 48) = c - 48 := by
  decide

/-- Horner form of a three-digit octal value in `UInt8` arithmetic. -/
theorem oct3 (a b c : UInt8) : a * 64 + b * 8 + c = (a * 8 + b) * 8 + c := by
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_add, UInt8.toNat_mul]
  omega

/-- Packing two nibbles below 16 in `UInt8` arithmetic agrees with `Nat`, and is zero exactly when
the `Nat` value is. -/
theorem nib_byte {x y : Nat} (hx : x < 16) (hy : y < 16) :
    UInt8.ofNat x * 16 + UInt8.ofNat y = UInt8.ofNat (x * 16 + y) ∧
      ((UInt8.ofNat x * 16 + UInt8.ofNat y == 0) = true ↔ x * 16 + y = 0) := by
  have e : UInt8.ofNat x * 16 + UInt8.ofNat y = UInt8.ofNat (x * 16 + y) := by
    apply UInt8.toNat_inj.mp
    simp [UInt8.toNat_add, UInt8.toNat_mul, UInt8.toNat_ofNat] <;> omega
  refine ⟨e, ?_⟩
  rw [e]
  constructor
  · intro h
    have := congrArg UInt8.toNat (beq_iff_eq.mp h)
    simp at this; omega
  · intro h; rw [h]; rfl

/-! ## Whitespace and comments -/

/-- **Whitespace.** The core skip (from `pos`, in or out of a comment) lands where the spec skip's
rest begins. -/
theorem skipWs_rest (bytes : ByteArray) (pos : Nat) (c : Bool) :
    restAt bytes (Core.Lex.skipWs bytes pos c) =
      (if c then Spec.Lex.skipComment else Spec.Lex.skipWs) (restAt bytes pos) := by
  fun_induction Core.Lex.skipWs bytes pos c
  case case1 p h b ih =>
    rw [ih, restAt_cons h]
    cases hb : (bytes[p] == 10 || bytes[p] == 13) <;> simp_all [b, Spec.Lex.skipComment]
  case case2 p h b _ hw ih =>
    rw [ih, restAt_cons h]
    simp_all [b, Spec.Lex.skipWs, Spec.Lex.isWhite, Core.Lex.isWhite]
  case case3 p h b _ hw h37 ih =>
    rw [ih, restAt_cons h]
    simp_all [b, Spec.Lex.skipWs, Spec.Lex.isWhite, Core.Lex.isWhite]
  case case4 p h b _ hw h37 =>
    rw [restAt_cons h]
    simp_all [b, Spec.Lex.skipWs, Spec.Lex.isWhite, Core.Lex.isWhite]
  case case5 p c h =>
    rw [restAt_nil (by omega)]
    cases c <;> simp [Spec.Lex.skipWs, Spec.Lex.skipComment]

/-- The core skip either does not move (at or past the end) or stays within the input. -/
theorem skipWs_bound (bytes : ByteArray) (pos : Nat) (c : Bool) :
    Core.Lex.skipWs bytes pos c = pos ∨ Core.Lex.skipWs bytes pos c ≤ bytes.size := by
  fun_induction Core.Lex.skipWs bytes pos c <;> omega

/-! ## Regular runs and numbers -/

/-- **Regular runs.** `readRun` with reversed accumulator `acc` is `regularRun` on the rest, its end
position the spec rest's position. -/
theorem readRun_eq (bytes : ByteArray) (pos : Nat) (acc : List UInt8) (hp : pos ≤ bytes.size) :
    Core.Lex.readRun bytes pos acc =
      (acc.reverse ++ (Spec.Lex.regularRun (restAt bytes pos)).1,
        bytes.size - (Spec.Lex.regularRun (restAt bytes pos)).2.length) := by
  fun_induction Core.Lex.readRun bytes pos acc
  case case1 p acc h b hr ih =>
    rw [ih (by omega), restAt_cons h]
    simp_all [b, Spec.Lex.regularRun, Spec.Lex.isRegular, Core.Lex.isRegular, Spec.Lex.isWhite,
      Core.Lex.isWhite, Spec.Lex.isDelim, Core.Lex.isDelim]
  case case2 p acc h b hr =>
    have hr' : Spec.Lex.isRegular bytes[p] = false := by
      have : Core.Lex.isRegular bytes[p] = false := by simpa [b] using hr
      exact this
    rw [restAt_cons h]
    simp only [Spec.Lex.regularRun, hr', Bool.false_eq_true, ite_false, List.length_cons,
      length_restAt, List.append_nil]
    simp; omega
  case case3 p acc h =>
    rw [restAt_nil (by omega)]
    simp [Spec.Lex.regularRun]; omega

/-- `readDigits` is `digitRun` followed by a decimal fold of the digits. -/
theorem readDigits_eq (l : List UInt8) (m n : Nat) :
    Core.Lex.readDigits l m n =
      ((Spec.Lex.digitRun l).1.foldl (fun acc d => acc * 10 + (d.toNat - 48)) m,
        n + (Spec.Lex.digitRun l).1.length, (Spec.Lex.digitRun l).2) := by
  induction l generalizing m n with
  | nil => simp [Core.Lex.readDigits, Spec.Lex.digitRun]
  | cons b r ih =>
    by_cases hs : Spec.Lex.isDigit b = true
    · simp [Core.Lex.readDigits, Spec.Lex.digitRun, hs, ih, digit_sub b hs]
      omega
    · simp [Core.Lex.readDigits, Spec.Lex.digitRun, hs]

/-- When `digitRun` consumes everything, its prefix is the whole list and all bytes are digits. -/
theorem digitRun_snd_nil (l : List UInt8) (h : (Spec.Lex.digitRun l).2 = []) :
    (Spec.Lex.digitRun l).1 = l ∧ l.all Spec.Lex.isDigit = true := by
  induction l with
  | nil => simp [Spec.Lex.digitRun]
  | cons b r ih =>
    by_cases hb : Spec.Lex.isDigit b = true
    · simp only [Spec.Lex.digitRun, hb, ite_true] at h ⊢
      have := ih h
      simp_all
    · simp [Spec.Lex.digitRun, hb] at h

/-- When `digitRun` stops early, not all bytes are digits. -/
theorem digitRun_snd_cons (l : List UInt8) (x : UInt8) (r : List UInt8)
    (h : (Spec.Lex.digitRun l).2 = x :: r) : l.all Spec.Lex.isDigit = false := by
  induction l with
  | nil => simp [Spec.Lex.digitRun] at h
  | cons b t ih =>
    by_cases hb : Spec.Lex.isDigit b = true
    · simp only [Spec.Lex.digitRun, hb, ite_true] at h
      simp [hb, ih h]
    · simp_all

/-- The sign-independent part of `parseNumber_eq`, after the sign is split off. -/
local macro "num_tac" body:term : tactic => `(tactic| (
  simp only [readDigits_eq]
  rcases hd : Spec.Lex.digitRun $body with ⟨ip, after⟩
  simp only
  cases after with
  | nil =>
    cases ip <;> simp [Core.Lex.applySign, Spec.Lex.digitsVal]
  | cons d frac =>
    by_cases d46 : (d == 46) = true
    · rcases hd2 : Spec.Lex.digitRun frac with ⟨ip2, l4⟩
      cases l4 with
      | nil =>
        have h := digitRun_snd_nil frac (by rw [hd2])
        rw [hd2] at h
        obtain ⟨h1, hall⟩ := h
        simp only at h1
        subst h1
        cases ip <;> cases ip2 <;>
          simp [d46, hall, hd2, Core.Lex.applySign, Spec.Lex.digitsVal, List.foldl_append]
      | cons x r =>
        have hall := digitRun_snd_cons frac x r (by rw [hd2])
        simp [d46, hall, hd2]
    · simp [d46]))

/-- **Numbers.** The core number parser is the spec's `lexNumber`. -/
theorem parseNumber_eq (l : List UInt8) : Core.Lex.parseNumber l = Spec.Lex.lexNumber l := by
  rcases l with _ | ⟨b, r⟩
  · rfl
  · by_cases h43 : (b == 43) = true
    · simp only [Core.Lex.parseNumber, Spec.Lex.lexNumber, Core.Lex.splitSign, h43, ite_true]
      num_tac r
    · by_cases h45 : (b == 45) = true
      · simp only [Core.Lex.parseNumber, Spec.Lex.lexNumber, Core.Lex.splitSign, h43, h45,
          ite_true, ite_false, Bool.false_eq_true]
        num_tac r
      · simp only [Core.Lex.parseNumber, Spec.Lex.lexNumber, Core.Lex.splitSign, h43, h45,
          ite_false, Bool.false_eq_true]
        num_tac (b :: r)

/-! ## Hex strings -/

/-- **Hex strings.** `hexStr` with pending high nibble `hi` and reversed accumulator `acc` is
`hexBody` followed by `packNibbles` of the pending nibble and the new ones. -/
theorem hexStr_eq (bytes : ByteArray) (pos : Nat) (hi : Option UInt8) (acc : List UInt8) :
    Core.Lex.hexStr bytes pos hi acc =
      match Spec.Lex.hexBody (restAt bytes pos) with
      | .ok (ns, r) => .ok (acc.reverse ++ Spec.Lex.packNibbles (hi.toList.map UInt8.toNat ++ ns),
          bytes.size - r.length)
      | .error k => .error k := by
  fun_induction Core.Lex.hexStr bytes pos hi acc
  case case1 p hi acc h b h62 =>
    rw [restAt_cons h]
    have : bytes[p] = 62 := by simpa [b] using h62
    cases hi <;>
      simp [Spec.Lex.hexBody, this, length_restAt, Spec.Lex.packNibbles, Core.Lex.pushOpt] <;>
      omega
  case case2 p hi acc h b h62 hw ih =>
    rw [restAt_cons h, ih]
    have h1 : (bytes[p] == 62) = false := by simpa [b] using h62
    have h2 : Spec.Lex.isWhite bytes[p] = true := by simpa [b] using hw
    simp [Spec.Lex.hexBody, h1, h2]
  case case3 p acc h b h62 hw v hv ih =>
    rw [restAt_cons h, ih]
    have h1 : (bytes[p] == 62) = false := by simpa [b] using h62
    have h2 : Spec.Lex.isWhite bytes[p] = false := by simpa [b] using hw
    rw [hexVal?_eq] at hv
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp hv
    have hlt : (UInt8.ofNat v').toNat = v' := by have := hexVal_lt hv'; simp; omega
    cases hb : Spec.Lex.hexBody (restAt bytes (p + 1)) with
    | error e => simp [Spec.Lex.hexBody, h1, h2, b, hv', hb, Except.map]
    | ok q =>
      obtain ⟨ns, r⟩ := q
      simp [Spec.Lex.hexBody, h1, h2, b, hv', hb, Except.map, hlt]
  case case4 p acc h b h62 hw v hv x ih =>
    rw [restAt_cons h, ih]
    have h1 : (bytes[p] == 62) = false := by simpa [b] using h62
    have h2 : Spec.Lex.isWhite bytes[p] = false := by simpa [b] using hw
    rw [hexVal?_eq] at hv
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp hv
    cases hb : Spec.Lex.hexBody (restAt bytes (p + 1)) with
    | error e => simp [Spec.Lex.hexBody, h1, h2, b, hv', hb, Except.map]
    | ok q =>
      obtain ⟨ns, r⟩ := q
      simp [Spec.Lex.hexBody, h1, h2, b, hv', hb, Except.map, Spec.Lex.packNibbles]
  case case5 p hi acc h b h62 hw hv =>
    rw [restAt_cons h]
    have h1 : (bytes[p] == 62) = false := by simpa [b] using h62
    have h2 : Spec.Lex.isWhite bytes[p] = false := by simpa [b] using hw
    rw [hexVal?_eq] at hv
    have hv' : Spec.Lex.hexVal bytes[p] = none := by simpa [b] using hv
    simp [Spec.Lex.hexBody, h1, h2, hv']
  case case6 p hi acc h =>
    rw [restAt_nil (by omega)]
    simp [Spec.Lex.hexBody]

/-! ## Names -/

/-- A successful hex lookup at `q` splits the rest at `q` and gives the spec value. -/
theorem hex_lookup {bytes : ByteArray} {q : Nat} {v : UInt8}
    (h : bytes[q]?.bind Core.Lex.hexVal? = some v) :
    ∃ c x, restAt bytes q = c :: restAt bytes (q + 1) ∧ Spec.Lex.hexVal c = some x ∧
      v = UInt8.ofNat x ∧ q < bytes.size := by
  cases hq : bytes[q]? with
  | none => simp [hq] at h
  | some c =>
    simp only [hq, Option.bind_some, hexVal?_eq] at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨c, x, restAt_of_getElem? hq, hx, rfl, ?_⟩
    have := congrArg List.length (restAt_of_getElem? hq)
    simp [length_restAt] at this; omega

/-- `regularRun` on a regular first byte. -/
theorem regularRun_reg {b : UInt8} (h : Spec.Lex.isRegular b = true) (l : List UInt8) :
    Spec.Lex.regularRun (b :: l) = (b :: (Spec.Lex.regularRun l).1, (Spec.Lex.regularRun l).2) := by
  simp [Spec.Lex.regularRun, h]

/-- `regularRun` on a non-regular first byte. -/
theorem regularRun_nonreg {b : UInt8} (h : Spec.Lex.isRegular b = false) (l : List UInt8) :
    Spec.Lex.regularRun (b :: l) = ([], b :: l) := by
  simp [Spec.Lex.regularRun, h]

/-- A non-empty run prefix comes from a list with the same head. -/
theorem regularRun_fst_cons {l r : List UInt8} {c : UInt8}
    (h : (Spec.Lex.regularRun l).1 = c :: r) :
    ∃ t, l = c :: t ∧ (Spec.Lex.regularRun t).1 = r := by
  cases l with
  | nil => simp [Spec.Lex.regularRun] at h
  | cons b t =>
    by_cases hb : Spec.Lex.isRegular b = true
    · rw [regularRun_reg hb] at h
      simp at h
      exact ⟨t, by rw [h.1], h.2⟩
    · rw [regularRun_nonreg (by simpa using hb)] at h
      simp at h

/-- **Names.** `nameRun` with reversed accumulator `acc` is `decodeName` on the regular run, ending
where the run ends. -/
theorem nameRun_eq (bytes : ByteArray) (pos : Nat) (acc : List UInt8) (hp : pos ≤ bytes.size) :
    Core.Lex.nameRun bytes pos acc =
      match Spec.Lex.decodeName (Spec.Lex.regularRun (restAt bytes pos)).1 with
      | .ok n =>
        .ok (acc.reverse ++ n, bytes.size - (Spec.Lex.regularRun (restAt bytes pos)).2.length)
      | .error k => .error k := by
  fun_induction Core.Lex.nameRun bytes pos acc
  case case1 p acc h b hr =>
    have hr' : Spec.Lex.isRegular bytes[p] = false := by simpa [b] using hr
    rw [restAt_cons h, regularRun_nonreg hr']
    simp [Spec.Lex.decodeName, length_restAt]; omega
  case case2 p acc h b hr h35 v1 v2 hv2 hv1 d hd =>
    obtain ⟨c1, x, e1, hx, rfl, -⟩ := hex_lookup hv1
    obtain ⟨c2, y, e2, hy, rfl, -⟩ := hex_lookup hv2
    have h35' : bytes[p] = 35 := by simpa [b] using h35
    obtain ⟨-, hz⟩ := nib_byte (hexVal_lt hx) (hexVal_lt hy)
    rw [restAt_cons h, e1, e2, h35', regularRun_reg (by decide),
      regularRun_reg (isRegular_of_hexVal hx),
      regularRun_reg (isRegular_of_hexVal hy)]
    simp [Spec.Lex.decodeName, hx, hy, hz.mp hd]
  case case3 p acc h b hr h35 v1 v2 hv2 hv1 d hd ih =>
    obtain ⟨c1, x, e1, hx, rfl, -⟩ := hex_lookup hv1
    obtain ⟨c2, y, e2, hy, rfl, hlt⟩ := hex_lookup hv2
    have h35' : bytes[p] = 35 := by simpa [b] using h35
    obtain ⟨he, hz⟩ := nib_byte (hexVal_lt hx) (hexVal_lt hy)
    have hnz : ¬ (x * 16 = 0 ∧ y = 0) := fun h0 => hd (hz.mpr (by omega))
    rw [show p + 1 + 1 = p + 2 by omega] at e1
    rw [show p + 2 + 1 = p + 3 by omega] at e2
    rw [ih (by omega), restAt_cons h, e1, e2, h35', regularRun_reg (by decide),
      regularRun_reg (isRegular_of_hexVal hx), regularRun_reg (isRegular_of_hexVal hy)]
    simp only [d, he]
    cases hdn : Spec.Lex.decodeName (Spec.Lex.regularRun (restAt bytes (p + 3))).1 with
    | error k => simp [Spec.Lex.decodeName, hx, hy, hnz, hdn, Except.map]
    | ok n => simp [Spec.Lex.decodeName, hx, hy, hnz, hdn, Except.map]
  case case4 p acc h b hr h35 hno =>
    have h35' : bytes[p] = 35 := by simpa [b] using h35
    rw [restAt_cons h, h35', regularRun_reg (by decide)]
    suffices Spec.Lex.decodeName (35 :: (Spec.Lex.regularRun (restAt bytes (p + 1))).1) =
        .error .badNameEscape by rw [this]
    rw [Spec.Lex.decodeName.eq_def]
    simp only [show ((35 : UInt8) == 35) = true from rfl, ite_true]
    split
    · rename_i c1 c2 r hr12
      split
      · rename_i x y hx hy
        exfalso
        obtain ⟨t1, e1, ht1⟩ := regularRun_fst_cons hr12
        obtain ⟨t2, e2, -⟩ := regularRun_fst_cons ht1
        have g1 : bytes[p + 1]? = some c1 := by rw [getElem?_eq_head?, e1]; rfl
        have g2 : bytes[p + 2]? = some c2 := by
          rw [getElem?_eq_head?, show p + 2 = p + 1 + 1 by omega, restAt_succ, e1, e2]; rfl
        apply hno (UInt8.ofNat x) (UInt8.ofNat y)
        · simp [g1, hexVal?_eq, hx]
        · simp [g2, hexVal?_eq, hy]
      · rfl
    · rfl
  case case5 p acc h b hr h35 ih =>
    have hr' : Spec.Lex.isRegular bytes[p] = true := by simpa [b] using hr
    have h35' : (bytes[p] == 35) = false := by simpa [b] using h35
    rw [ih (by omega), restAt_cons h, regularRun_reg hr']
    have h0 := ne_zero_of_regular_aux _ hr'
    cases hdn : Spec.Lex.decodeName (Spec.Lex.regularRun (restAt bytes (p + 1))).1 with
    | error k =>
      rw [Spec.Lex.decodeName.eq_def]; simp [h35', h0, hdn, Except.map]
    | ok n =>
      rw [Spec.Lex.decodeName.eq_def]; simp [h35', h0, hdn, Except.map, b]
  case case6 p acc h =>
    rw [restAt_nil (by omega)]
    simp [Spec.Lex.decodeName, Spec.Lex.regularRun]; omega

/-! ## Literal strings -/

/-- **Literal-string escapes.** One backslash escape in `litBody` is what `escapeAt` decodes: the
optional byte, then the body from the position after the escape. -/
theorem litBody_escape (bytes : ByteArray) (d q : Nat) (hq : q < bytes.size) :
    Spec.Lex.litBody d (92 :: restAt bytes q) =
      (Spec.Lex.litBody d (restAt bytes (Core.Lex.escapeAt bytes q bytes[q]).2)).map
        (fun p => ((Core.Lex.escapeAt bytes q bytes[q]).1.toList ++ p.1, p.2)) := by
  rw [restAt_cons hq]
  generalize hc : bytes[q] = c
  have g1 : bytes[q + 1]? = (restAt bytes (q + 1)).head? := getElem?_eq_head? _ _
  have r2 : restAt bytes (q + 2) = (restAt bytes (q + 1)).tail := restAt_succ _ _
  have g2 : bytes[q + 2]? = (restAt bytes (q + 1)).tail.head? := by rw [getElem?_eq_head?, r2]
  have r3 : restAt bytes (q + 3) = (restAt bytes (q + 1)).tail.tail := by
    rw [show q + 3 = q + 2 + 1 by omega, restAt_succ, r2]
  generalize hr1 : restAt bytes (q + 1) = cs at g1 r2 g2 r3 ⊢
  conv => lhs; rw [Spec.Lex.litBody.eq_def]
  simp only [show ((92 : UInt8) == 92) = true from rfl, ite_true]
  unfold Core.Lex.escapeAt
  by_cases h110 : (c == 110) = true
  · simp [hr1, h110]
  by_cases h114 : (c == 114) = true
  · simp [hr1, h110, h114]
  by_cases h116 : (c == 116) = true
  · simp [hr1, h110, h114, h116]
  by_cases h98 : (c == 98) = true
  · simp [hr1, h110, h114, h116, h98]
  by_cases h102 : (c == 102) = true
  · simp [hr1, h110, h114, h116, h98, h102]
  simp only [h110, h114, h116, h98, h102, Bool.false_eq_true, ite_false]
  by_cases ho : Spec.Lex.isOctal c = true
  · simp only [ho, core_isOctal, ite_true]
    unfold Core.Lex.octalAt
    have o0 := ofNat_octal_aux c ho
    rw [g1]
    cases cs with
    | nil => simp [hr1, o0]
    | cons d1 cs2 =>
      by_cases ho1 : Spec.Lex.isOctal d1 = true
      · have o1 := ofNat_octal_aux d1 ho1
        rw [g2]
        cases cs2 with
        | nil => simp [ho1, o0, o1, r2]
        | cons d2 cs3 =>
          by_cases ho2 : Spec.Lex.isOctal d2 = true
          · simp [ho1, ho2, o0, o1, ofNat_octal_aux d2 ho2, oct3, r3]
          · simp [ho1, ho2, o0, o1, r2]
      · simp [hr1, ho1, o0]
  simp only [ho, core_isOctal, Bool.false_eq_true, ite_false]
  by_cases h13 : (c == 13) = true
  · simp only [h13, ite_true]
    rw [g1]
    cases cs with
    | nil => simp [hr1]
    | cons d1 cs2 =>
      by_cases h10 : (d1 == 10) = true
      · simp [h10, r2]
      · simp [hr1, h10]
  simp only [h13, Bool.false_eq_true, ite_false]
  by_cases h10 : (c == 10) = true
  · simp [hr1, h10]
  · simp [hr1, h10]

/-- `litBody` on empty input is unterminated. -/
theorem litBody_nil (d : Nat) : Spec.Lex.litBody d [] = none := by
  rw [Spec.Lex.litBody.eq_def]

/-- A trailing backslash is unterminated. -/
theorem litBody_bs_nil (d : Nat) : Spec.Lex.litBody d [92] = none := by
  rw [Spec.Lex.litBody.eq_def]; simp

/-- `litBody` on an unescaped `(`. -/
theorem litBody_open (d : Nat) (l : List UInt8) :
    Spec.Lex.litBody d (40 :: l) =
      (Spec.Lex.litBody (d + 1) l).map (fun p => (40 :: p.1, p.2)) := by
  conv => lhs; rw [Spec.Lex.litBody.eq_def]
  simp

/-- `litBody` on the closing `)` at depth 0. -/
theorem litBody_close0 (l : List UInt8) : Spec.Lex.litBody 0 (41 :: l) = some ([], l) := by
  rw [Spec.Lex.litBody.eq_def]; simp

/-- `litBody` on a nested `)`. -/
theorem litBody_close (d : Nat) (l : List UInt8) :
    Spec.Lex.litBody (d + 1) (41 :: l) =
      (Spec.Lex.litBody d l).map (fun p => (41 :: p.1, p.2)) := by
  conv => lhs; rw [Spec.Lex.litBody.eq_def]
  simp

/-- A trailing CR is unterminated. -/
theorem litBody_cr_nil (d : Nat) : Spec.Lex.litBody d [13] = none := by
  rw [Spec.Lex.litBody.eq_def]; simp

/-- `litBody` on an unescaped CR (optionally followed by LF): one LF. -/
theorem litBody_cr (d : Nat) (c : UInt8) (l : List UInt8) :
    Spec.Lex.litBody d (13 :: c :: l) =
      (Spec.Lex.litBody d (if c == 10 then l else c :: l)).map (fun p => (10 :: p.1, p.2)) := by
  conv => lhs; rw [Spec.Lex.litBody.eq_def]
  by_cases h : (c == 10) = true <;> simp [h]

/-- `litBody` on any other byte: the byte itself. -/
theorem litBody_other (d : Nat) (b : UInt8) (l : List UInt8) (h92 : (b == 92) = false)
    (h40 : (b == 40) = false) (h41 : (b == 41) = false) (h13 : (b == 13) = false) :
    Spec.Lex.litBody d (b :: l) = (Spec.Lex.litBody d l).map (fun p => (b :: p.1, p.2)) := by
  conv => lhs; rw [Spec.Lex.litBody.eq_def]
  simp [h92, h40, h41, h13]

/-- Reversing after `pushOpt` appends the optional byte. -/
theorem pushOpt_reverse (o : Option UInt8) (acc : List UInt8) :
    (Core.Lex.pushOpt o acc).reverse = acc.reverse ++ o.toList := by
  cases o <;> simp [Core.Lex.pushOpt]

/-- **Literal strings.** `litStr` at core depth `depth ≥ 1` with reversed accumulator `acc` is
`litBody (depth - 1)` on the rest, ending at the spec rest's position. -/
theorem litStr_eq (bytes : ByteArray) (pos depth : Nat) (acc : List UInt8) (hd : 1 ≤ depth) :
    Core.Lex.litStr bytes pos depth acc =
      (Spec.Lex.litBody (depth - 1) (restAt bytes pos)).map
        (fun p => (acc.reverse ++ p.1, bytes.size - p.2.length)) := by
  fun_induction Core.Lex.litStr bytes pos depth acc
  case case1 p depth acc h b h92 h1 r ih =>
    have e : bytes[p] = 92 := by simpa [b] using h92
    rw [ih hd, restAt_cons h, e, litBody_escape bytes _ _ h1]
    simp [Option.map_map, Function.comp_def, pushOpt_reverse, r]
  case case2 p depth acc h b h92 h1 =>
    have e : bytes[p] = 92 := by simpa [b] using h92
    rw [restAt_cons h, e, restAt_nil (by omega), litBody_bs_nil]; rfl
  case case3 p depth acc h b h92 h40 ih =>
    have e : bytes[p] = 40 := by simpa [b] using h40
    rw [ih (by omega), restAt_cons h, e, litBody_open]
    simp [Option.map_map, Function.comp_def, b, e]
    rw [show depth - 1 + 1 = depth by omega]
  case case4 p depth acc h b h92 h40 h41 hle =>
    have e : bytes[p] = 41 := by simpa [b] using h41
    rw [restAt_cons h, e, show depth - 1 = 0 by omega, litBody_close0]
    simp [length_restAt]; omega
  case case5 p depth acc h b h92 h40 h41 hle ih =>
    have e : bytes[p] = 41 := by simpa [b] using h41
    rw [ih (by omega), restAt_cons h, e, show depth - 1 = (depth - 1 - 1) + 1 by omega,
      litBody_close]
    simp [Option.map_map, Function.comp_def, b, e]
  case case6 p depth acc h b h92 h40 h41 h13 ih =>
    have e : bytes[p] = 13 := by simpa [b] using h13
    have ih' := ih hd
    simp only [dite_eq_ite] at ih'
    rw [ih', restAt_cons h, e]
    have g1 : bytes[p + 1]? = (restAt bytes (p + 1)).head? := getElem?_eq_head? _ _
    have r2 : restAt bytes (p + 2) = (restAt bytes (p + 1)).tail := restAt_succ _ _
    generalize hr1 : restAt bytes (p + 1) = cs at g1 r2 ⊢
    cases cs with
    | nil =>
      simp [g1, hr1, litBody_cr_nil]
      rw [Spec.Lex.litBody.eq_def]
    | cons c cs =>
      rw [litBody_cr]
      by_cases h10 : (c == 10) = true
      · simp [g1, h10, r2, Option.map_map, Function.comp_def]
      · simp [g1, h10, hr1, Option.map_map, Function.comp_def]
  case case7 p depth acc h b h92 h40 h41 h13 ih =>
    rw [ih hd, restAt_cons h, litBody_other _ _ _ (by simpa [b] using h92) (by simpa [b] using h40)
      (by simpa [b] using h41) (by simpa [b] using h13)]
    simp [Option.map_map, Function.comp_def, b]
  case case8 p depth acc h =>
    rw [restAt_nil (by omega)]
    rw [Spec.Lex.litBody.eq_def]; simp

/-! ## Dispatch and the main theorem -/

/-- Translate a spec result (rest as a list) into a core result (rest as the
position `size - rest.length`), shifting error offsets by `base`. -/
def tr (base size : Nat) : Except LexError (Option (Token × List UInt8)) →
    Except LexError (Option (Token × Nat))
  | .ok none => .ok none
  | .ok (some (t, r)) => .ok (some (t, size - r.length))
  | .error e => .error { e with offset := e.offset + base }

/-- **Dispatch.** The core token at `p` is the spec `nextAt off` on the rest at `p`, translated,
whenever `off + base = p` (spec errors carry `off`, core errors `p`). -/
theorem tokenAt_eq (bytes : ByteArray) (p off base : Nat) (hob : off + base = p) :
    Core.Lex.tokenAt bytes p = tr base bytes.size (Spec.Lex.nextAt off (restAt bytes p)) := by
  unfold Core.Lex.tokenAt
  by_cases h : p < bytes.size
  case neg =>
    simp only [h, ↓reduceDIte]; rw [restAt_nil (by omega)]; rfl
  simp only [h, ↓reduceDIte]
  rw [restAt_cons h]
  unfold Core.Lex.tokenOf
  rw [hexStr_eq, nameRun_eq _ _ _ (by omega), litStr_eq _ _ _ _ (Nat.le_refl 1),
    readRun_eq _ _ _ (by omega)]
  generalize bytes[p] = b
  have g1 : bytes[p + 1]? = (restAt bytes (p + 1)).head? := getElem?_eq_head? _ _
  have r2 : restAt bytes (p + 2) = (restAt bytes (p + 1)).tail := restAt_succ _ _
  have hl : (restAt bytes (p + 1)).length = bytes.size - (p + 1) := length_restAt _ _
  generalize restAt bytes (p + 1) = cs at g1 r2 hl ⊢
  simp only [Spec.Lex.nextAt]
  by_cases h91 : (b == 91) = true
  · simp at h91; subst h91; simp [tr]; omega
  by_cases h93 : (b == 93) = true
  · simp at h93; subst h93; simp [tr]; omega
  by_cases h123 : (b == 123) = true
  · simp at h123; subst h123; simp [tr]; omega
  by_cases h125 : (b == 125) = true
  · simp at h125; subst h125; simp [tr]; omega
  by_cases h60 : (b == 60) = true
  · simp at h60; subst h60
    simp only [tr, show ((60 : UInt8) == 91) = false from rfl,
      show ((60 : UInt8) == 93) = false from rfl,
      show ((60 : UInt8) == 123) = false from rfl, show ((60 : UInt8) == 125) = false from rfl,
      show ((60 : UInt8) == 41) = false from rfl, show ((60 : UInt8) == 62) = false from rfl,
      show ((60 : UInt8) == 60) = true from rfl, Bool.false_eq_true, ite_false, ite_true]
    cases cs with
    | nil => simp [g1, Spec.Lex.hexBody, Core.Lex.liftAt, hob]
    | cons c cs' =>
      by_cases hc : (c == 60) = true
      · simp [g1, hc]; simp at hl; omega
      · cases Spec.Lex.hexBody (c :: cs') with
        | error k => simp [g1, hc, Core.Lex.liftAt, hob]
        | ok q => obtain ⟨ns, r⟩ := q; simp [g1, hc, Core.Lex.liftAt]
  by_cases h62 : (b == 62) = true
  · simp at h62; subst h62
    simp only [tr, show ((62 : UInt8) == 91) = false from rfl,
      show ((62 : UInt8) == 93) = false from rfl,
      show ((62 : UInt8) == 123) = false from rfl, show ((62 : UInt8) == 125) = false from rfl,
      show ((62 : UInt8) == 41) = false from rfl, show ((62 : UInt8) == 62) = true from rfl,
      show ((62 : UInt8) == 60) = false from rfl, Bool.false_eq_true, ite_false, ite_true]
    cases cs with
    | nil => simp [g1, hob]
    | cons c cs' =>
      by_cases hc : (c == 62) = true
      · simp [g1, hc]; simp at hl; omega
      · simp [g1, hc, hob]
  by_cases h40 : (b == 40) = true
  · simp at h40; subst h40
    cases Spec.Lex.litBody 0 cs with
    | none => simp [tr, hob]
    | some q => obtain ⟨s, r⟩ := q; simp [tr]
  by_cases h41 : (b == 41) = true
  · simp at h41; subst h41; simp [tr, hob]
  by_cases h47 : (b == 47) = true
  · simp at h47; subst h47
    cases Spec.Lex.decodeName (Spec.Lex.regularRun cs).1 with
    | error k => simp [tr, Core.Lex.liftAt, hob]
    | ok n => simp [tr, Core.Lex.liftAt]
  simp only [h91, h93, h123, h125, h60, h62, h40, h41, h47, Bool.false_eq_true, ite_false]
  simp only [Core.Lex.runToken, Core.Lex.classifyRun, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, parseNumber_eq]
  by_cases hs : Spec.Lex.startsNumber b = true
  · have hs' : (b == 43 || b == 45 || b == 46 || Spec.Lex.isDigit b) = true := hs
    simp only [hs, hs', core_isDigit, ite_true]
    cases Spec.Lex.lexNumber (b :: (Spec.Lex.regularRun cs).1) with
    | none => simp [tr, hob]
    | some t => simp [tr]
  · have hs' : (b == 43 || b == 45 || b == 46 || Spec.Lex.isDigit b) = false := by
      have : Spec.Lex.startsNumber b = false := by simpa using hs
      exact this
    simp only [hs, hs', core_isDigit, Bool.false_eq_true, ite_false]
    simp [tr]

/-- `tr` is the `match` in the statement of `next_eq`. -/
theorem tr_eq (pos size : Nat) (r : Except LexError (Option (Token × List UInt8))) :
    (match r with
      | .ok none => .ok none
      | .ok (some (t, rest)) => .ok (some (t, size - rest.length))
      | .error e => .error { e with offset := e.offset + pos }) = tr pos size r := by
  rcases r with e | _ | ⟨t, r⟩ <;> rfl

/-- **Main theorem (Plan.md §4 C5, §5.1 step 3).** The efficient tokenizer equals the denotational
spec: `Core.Lex.next bytes pos` is `Spec.Lex.next` on the input from `pos`, with the rest
translated to a position and error offsets shifted by `pos`. Holds for every `pos`; past the end
both sides are `ok none`. -/
theorem next_eq (bytes : ByteArray) (pos : Nat) :
    Core.Lex.next bytes pos =
      match Spec.Lex.next (bytes.data.toList.drop pos) with
      | .ok none => .ok none
      | .ok (some (t, rest)) => .ok (some (t, bytes.size - rest.length))
      | .error e => .error { e with offset := e.offset + pos } := by
  rw [tr_eq]
  show _ = tr pos bytes.size (Spec.Lex.next (restAt bytes pos))
  unfold Core.Lex.next Spec.Lex.next
  have hs := skipWs_rest bytes pos false
  simp only [Bool.false_eq_true, ite_false] at hs
  rw [← hs, length_restAt, length_restAt]
  apply tokenAt_eq
  have h1 := Core.Lex.le_skipWs bytes pos false
  have h2 := skipWs_bound bytes pos false
  omega

/-! ## Suffixes: a spec rest is a position in the input -/

/-- Mapping a function that keeps the rest preserves a suffix bound on the rest. -/
theorem map_suffix {r t : List UInt8} {x : Option (List UInt8 × List UInt8)}
    {f : List UInt8 × List UInt8 → List UInt8 × List UInt8} (hf : ∀ p, (f p).2 = p.2)
    (ih : ∀ s, x = some (s, r) → r <:+ t) {s : List UInt8} (h : x.map f = some (s, r)) :
    r <:+ t := by
  cases hx : x with
  | none => simp [hx] at h
  | some p =>
    obtain ⟨s', r'⟩ := p
    rw [hx] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have := hf (s', r')
    rw [h] at this
    simp at this
    subst this
    exact ih s' hx

/-- Close `r <:+ x₁ :: … :: r` for up to five explicit heads. -/
local macro "suf_close" : tactic => `(tactic| first
  | exact ⟨[], rfl⟩
  | exact ⟨[_], rfl⟩
  | exact ⟨[_, _], rfl⟩
  | exact ⟨[_, _, _], rfl⟩
  | exact ⟨[_, _, _, _], rfl⟩
  | exact ⟨[_, _, _, _, _], rfl⟩)

/-- The rest after a literal-string body is a suffix of the input. -/
theorem litBody_suffix (d : Nat) (l s r : List UInt8) (h : Spec.Lex.litBody d l = some (s, r)) :
    r <:+ l := by
  fun_induction Spec.Lex.litBody d l generalizing s
  all_goals first
    | (simp at h; done)
    | (rename_i ih; exact List.IsSuffix.trans (map_suffix (by intro; rfl) ih h) (by suf_close))
    | (rename_i ih; exact List.IsSuffix.trans (ih _ h) (by suf_close))
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; suf_close)
    | skip



/-- Skipping whitespace or a comment body returns a suffix of the input. -/
theorem skipWs_suffix (l : List UInt8) :
    Spec.Lex.skipWs l <:+ l ∧ Spec.Lex.skipComment l <:+ l := by
  induction l with
  | nil => simp [Spec.Lex.skipWs, Spec.Lex.skipComment]
  | cons b bs ih =>
    constructor
    · simp only [Spec.Lex.skipWs]
      split
      · exact List.IsSuffix.trans ih.1 (List.suffix_cons _ _)
      · split
        · exact List.IsSuffix.trans ih.2 (List.suffix_cons _ _)
        · exact List.suffix_refl _
    · simp only [Spec.Lex.skipComment]
      split
      · exact List.IsSuffix.trans ih.1 (List.suffix_cons _ _)
      · exact List.IsSuffix.trans ih.2 (List.suffix_cons _ _)

/-- The rest after a regular run is a suffix of the input. -/
theorem regularRun_suffix (l : List UInt8) : (Spec.Lex.regularRun l).2 <:+ l := by
  induction l with
  | nil => simp [Spec.Lex.regularRun]
  | cons b bs ih =>
    simp only [Spec.Lex.regularRun]
    split
    · exact List.IsSuffix.trans ih (List.suffix_cons _ _)
    · exact List.suffix_refl _

/-- The rest after a hex-string body is a suffix of the input. -/
theorem hexBody_suffix (l : List UInt8) (ns : List Nat) (r : List UInt8)
    (h : Spec.Lex.hexBody l = .ok (ns, r)) : r <:+ l := by
  induction l generalizing ns r with
  | nil => simp [Spec.Lex.hexBody] at h
  | cons b bs ih =>
    simp only [Spec.Lex.hexBody] at h
    split at h
    · simp at h; rw [← h.2]; exact List.suffix_cons _ _
    split at h
    · exact List.IsSuffix.trans (ih _ _ h) (List.suffix_cons _ _)
    split at h
    · cases hb : Spec.Lex.hexBody bs with
      | error e => simp [hb, Except.map] at h
      | ok p =>
        obtain ⟨ns', r'⟩ := p
        simp [hb, Except.map] at h
        rw [← h.2]
        exact List.IsSuffix.trans (ih _ _ hb) (List.suffix_cons _ _)
    · cases h

/-- The rest after a token is a suffix of the input. -/
theorem nextAt_suffix (off : Nat) (l : List UInt8) (t : Token) (r : List UInt8)
    (h : Spec.Lex.nextAt off l = .ok (some (t, r))) : r <:+ l := by
  cases l with
  | nil => simp [Spec.Lex.nextAt] at h
  | cons b bs =>
    have hr := regularRun_suffix bs
    unfold Spec.Lex.nextAt at h
    simp only at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨-, rfl⟩ := h
         first
           | exact List.suffix_cons _ _
           | exact ⟨[_, _], rfl⟩
           | exact List.IsSuffix.trans hr (List.suffix_cons _ _)
           | exact List.IsSuffix.trans (litBody_suffix _ _ _ _ ‹_›) (List.suffix_cons _ _)
           | exact List.IsSuffix.trans (hexBody_suffix _ _ _ ‹_›) (List.suffix_cons _ _))
      | skip



/-- The rest returned by `Spec.Lex.next` is a suffix of its input. -/
theorem next_suffix (l : List UInt8) (t : Token) (r : List UInt8)
    (h : Spec.Lex.next l = .ok (some (t, r))) : r <:+ l :=
  List.IsSuffix.trans (nextAt_suffix _ _ _ _ h) (skipWs_suffix l).1

/-- A suffix `r` of the rest at `pos` is the rest at position `bytes.size - r.length`. -/
theorem restAt_of_suffix (bytes : ByteArray) (pos : Nat) (r : List UInt8)
    (h : r <:+ restAt bytes pos) : restAt bytes (bytes.size - r.length) = r := by
  obtain ⟨pre, hpre⟩ := h
  have hl := congrArg List.length hpre
  simp only [List.length_append, length_restAt] at hl
  have e : r = restAt bytes (pos + pre.length) := by
    unfold restAt at hpre ⊢
    rw [← List.drop_drop, ← hpre]
    simp
  by_cases hp : pos ≤ bytes.size
  · rw [show bytes.size - r.length = pos + pre.length by omega] at *; exact e.symm
  · have : r = [] := by
      apply List.eq_nil_of_length_eq_zero; omega
    subst this
    simp [restAt_nil]

/-! ## Whole-input lexing (`lexAll`) -/

/-- `next_eq` in terms of `restAt` and `tr`. -/
theorem next_eq_tr (bytes : ByteArray) (pos : Nat) :
    Core.Lex.next bytes pos = tr pos bytes.size (Spec.Lex.next (restAt bytes pos)) := by
  rw [next_eq, tr_eq]; rfl

/-- Spec `lexAll` when the first `next` fails. -/
theorem lexAll_of_error {l : List UInt8} {e : LexError} (h : Spec.Lex.next l = .error e) :
    Spec.Lex.lexAll l = .error e := by
  rw [Spec.Lex.lexAll.eq_def]
  split <;> rename_i h' <;> rw [h] at h' <;> simp_all

/-- Spec `lexAll` at end of input. -/
theorem lexAll_of_none {l : List UInt8} (h : Spec.Lex.next l = .ok none) :
    Spec.Lex.lexAll l = .ok [] := by
  rw [Spec.Lex.lexAll.eq_def]
  split <;> rename_i h' <;> rw [h] at h' <;> simp_all

/-- Spec `lexAll` after one token: recurse on the rest, shifting error offsets. -/
theorem lexAll_of_some {l : List UInt8} {t : Token} {r : List UInt8}
    (h : Spec.Lex.next l = .ok (some (t, r))) :
    Spec.Lex.lexAll l =
      match Spec.Lex.lexAll r with
      | .error e => .error { e with offset := e.offset + (l.length - r.length) }
      | .ok ts => .ok (t :: ts) := by
  conv => lhs; rw [Spec.Lex.lexAll.eq_def]
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i t' r' h'
    rw [h] at h'
    simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rfl

/-- **Whole-input lexing, generalized.** The core loop from `pos` with reversed accumulator `acc` is
the spec `lexAll` on the rest at `pos`, error offsets shifted by `pos`. -/
theorem lexAll_go_eq (bytes : ByteArray) (pos : Nat) (acc : List Token) :
    Core.Lex.lexAll.go bytes pos acc =
      match Spec.Lex.lexAll (restAt bytes pos) with
      | .ok ts => .ok (acc.reverse ++ ts)
      | .error e => .error { e with offset := e.offset + pos } := by
  fun_induction Core.Lex.lexAll.go bytes pos acc
  case case1 pos acc e hn =>
    rw [next_eq_tr] at hn
    rcases h : Spec.Lex.next (restAt bytes pos) with e' | _ | ⟨t', r⟩
    · rw [h] at hn; simp [tr] at hn; simp [lexAll_of_error h, hn]
    · rw [h] at hn; simp [tr] at hn
    · rw [h] at hn; simp [tr] at hn
  case case2 pos acc hn =>
    rw [next_eq_tr] at hn
    rcases h : Spec.Lex.next (restAt bytes pos) with e' | _ | ⟨t', r⟩
    · rw [h] at hn; simp [tr] at hn
    · simp [lexAll_of_none h]
    · rw [h] at hn; simp [tr] at hn
  case case3 pos acc t pos' hn ih =>
    rw [next_eq_tr] at hn
    rcases h : Spec.Lex.next (restAt bytes pos) with e' | _ | ⟨t', r⟩
    · rw [h] at hn; simp [tr] at hn
    · rw [h] at hn; simp [tr] at hn
    · rw [h] at hn
      simp only [tr, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      have hlt := Spec.Lex.next_consumes h
      have hr := restAt_of_suffix bytes pos r (next_suffix _ _ _ h)
      rw [length_restAt] at hlt
      rw [ih, hr, lexAll_of_some h, length_restAt]
      cases Spec.Lex.lexAll r with
      | ok ts => simp
      | error e => simp; omega

/-- **Whole-input lexing.** The core `lexAll` equals the spec `lexAll` on the whole input, exactly
(both report absolute error offsets). -/
theorem lexAll_eq (bytes : ByteArray) :
    Core.Lex.lexAll bytes = Spec.Lex.lexAll bytes.data.toList := by
  unfold Core.Lex.lexAll
  rw [lexAll_go_eq]
  have : restAt bytes 0 = bytes.data.toList := by simp [restAt]
  rw [this]
  cases Spec.Lex.lexAll bytes.data.toList <;> simp

end SafePdf.Spec.LexEquiv
