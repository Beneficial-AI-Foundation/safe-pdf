import SafePdf.Core.Print
import SafePdf.Spec.Lex
import SafePdf.Spec.Object
import SafePdf.Spec.LexEquiv

/-!
# Printer round trip (Plan.md §5.1, §6 Phase 1 exit criterion M1, task 1.7; ISO 32000-2 §7.2–7.3)

The M1 headline `parse (print o) = o` for the printer `SafePdf.Core.Print`, against the
denotational lexer (`Spec.Lex`) and grammar (`Spec.Object`), and transferred to the efficient
tokenizer through `LexEquiv.lexAll_eq`.

## Hypotheses

The round trip holds for objects that are `PdfObject.Canonical` (canonical reals, NUL-free
names, distinct keys) **and** `Print.RefsInRange` (every reference `n g R` has `1 ≤ n` and
`g ≤ 65535`; `Canonical` does not include this, but the grammar's G1 rejects other
references), parsed with fuel `F ≥ o.depth`. All three are decidable. The `#guard`s at the
end show the round trip failing outside them.

## Proof structure

* **(A) Lexing** (`lexAll_print`): one lemma per token kind (`lex_int`, `lex_real`,
  `lex_name`, `lex_hex`, `lex_keyword`, delimiters, gathered in `lex_tok`) shows that
  `Spec.Lex.nextAt` reads `tokBytes t ++ rest` back as `t` when `rest` ends a regular run
  (`StopsRun`), and that `skipWs` does not move before it; then `lexAll_render` iterates over
  the space-separated rendering. Finite byte facts (hex digits, name-safe bytes, digit
  classes) are checked by `decide` over all 256 bytes; numbers rely on `natDigits_spec`
  (`digitsVal` inverts the digit printer) and on canonical decimals being their own normal
  form.
* **(B) Parsing** (`parse_printTokens`): mutual structural recursion over the object
  (`parses_print`, `parses_items`, `parses_entries`) builds a `Spec.Object.Parses` derivation
  for `printTokens o ++ r` whenever `r` does not start with `g R` (`NoIntR`). The reference
  lookahead G1 is discharged by `noIntR_print`: printed tokens never start with keyword `R`,
  and a printed reference's second token is an integer, so an integer item is never followed
  by `g R`.
* **Round trip**: `roundTrip_spec` (spec lexer + spec parser) and `roundTrip_core_spec`
  (efficient tokenizer + spec parser), via `roundTrip_core`.

The full statement for the efficient parser,
`Core.ObjParse.parseObject limits (print o) 0 = .ok (o, (print o).size)`, needs the parser
equivalence of task 1.8 and is not proven here.
-/

namespace SafePdf.Spec.RoundTrip

open SafePdf
open SafePdf.Core.Print
open SafePdf.Spec.Lex (isWhite isRegular isDigit hexVal regularRun digitRun digitsVal
  lexNumber startsNumber hexBody packNibbles decodeName nextAt next skipWs)

/-! ## Finite byte facts (checked on all bytes) -/

/-- Digit bytes are digits and denote their value. -/
theorem digitByte_spec : ∀ d : Fin 10,
    isDigit (digitByte d) = true ∧ (digitByte d).toNat - 48 = d := by decide

/-- Digits are regular, and are not `+`, `-`, `.`. -/
theorem digit_facts : ∀ b : UInt8, isDigit b = true →
    isRegular b = true ∧ (b == 43) = false ∧ (b == 45) = false ∧ (b == 46) = false := by
  decide

/-- A regular byte is none of the bytes `nextAt` dispatches on, nor whitespace or `%`. -/
theorem regular_facts : ∀ b : UInt8, isRegular b = true →
    (b == 91) = false ∧ (b == 93) = false ∧ (b == 123) = false ∧ (b == 125) = false ∧
    (b == 41) = false ∧ (b == 62) = false ∧ (b == 60) = false ∧ (b == 40) = false ∧
    (b == 47) = false ∧ isWhite b = false ∧ (b == 37) = false := by
  decide

/-- Hex-digit facts for both nibbles of every byte. -/
theorem hexDigit_facts : ∀ b : UInt8,
    hexVal (hexDigit (b / 16)) = some (b.toNat / 16) ∧
    hexVal (hexDigit (b % 16)) = some (b.toNat % 16) ∧
    isRegular (hexDigit (b / 16)) = true ∧ isRegular (hexDigit (b % 16)) = true ∧
    UInt8.ofNat (b.toNat / 16 * 16 + b.toNat % 16) = b ∧
    (b = 0 ∨ b.toNat / 16 * 16 + b.toNat % 16 ≠ 0) := by
  decide

/-- Name-safe bytes are regular, not `#`, not NUL. -/
theorem nameSafe_facts : ∀ b : UInt8, nameSafe b = true →
    isRegular b = true ∧ (b == 35) = false ∧ (b == 0) = false := by
  decide

/-! ## List helpers for the lexer -/

/-- `rest` ends a regular run: it is empty or starts with a non-regular byte. -/
def StopsRun : List UInt8 → Prop
  | [] => True
  | b :: _ => isRegular b = false

/-- A regular run over an all-regular prefix stops exactly where the prefix ends. -/
theorem regularRun_append (w rest : List UInt8) (hw : w.all isRegular = true)
    (hs : StopsRun rest) : regularRun (w ++ rest) = (w, rest) := by
  induction w with
  | nil =>
    cases rest with
    | nil => rfl
    | cons b r => simp only [StopsRun] at hs; simp [regularRun, hs]
  | cons b w ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    simp [regularRun, hw.1, ih hw.2]

/-- A digit run over an all-digit list consumes it all. -/
theorem digitRun_all (ds : List UInt8) (h : ds.all isDigit = true) : digitRun ds = (ds, []) := by
  induction ds with
  | nil => rfl
  | cons b ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [digitRun, h.1, ih h.2]

/-- A digit run stops at a `.` after an all-digit prefix. -/
theorem digitRun_dot (ip frac : List UInt8) (h : ip.all isDigit = true) :
    digitRun (ip ++ 46 :: frac) = (ip, 46 :: frac) := by
  induction ip with
  | nil => simp [digitRun, isDigit]
  | cons b ip ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [digitRun, h.1, ih h.2]

/-- `digitsVal` of a list with one more digit at the end. -/
theorem digitsVal_snoc (l : List UInt8) (d : UInt8) :
    digitsVal (l ++ [d]) = digitsVal l * 10 + (d.toNat - 48) := by
  simp [digitsVal, List.foldl_append]

/-- Leading zeros do not change `digitsVal`. -/
theorem digitsVal_zeros (k : Nat) (l : List UInt8) :
    digitsVal (List.replicate k 48 ++ l) = digitsVal l := by
  have h0 : ∀ k, (List.replicate k (48 : UInt8)).foldl
      (fun acc d => acc * 10 + (d.toNat - 48)) 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ', List.foldl_append, ih]; rfl
  simp only [digitsVal, List.foldl_append, h0]

/-- The digits of `n` are digits and denote `n`, and there is at least one. -/
theorem natDigits_spec (n : Nat) :
    (natDigits n).all isDigit = true ∧ digitsVal (natDigits n) = n ∧ natDigits n ≠ [] := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits]
    split
    · rename_i h
      have := digitByte_spec ⟨n, h⟩
      simp only at this
      refine ⟨by simp [this.1], ?_, by simp⟩
      simp [digitsVal, this.2]
    · rename_i h
      have := digitByte_spec ⟨n % 10, Nat.mod_lt _ (by omega)⟩
      simp only at this
      obtain ⟨h1, h2, -⟩ := ih (n / 10) (by omega)
      refine ⟨by simp [h1, this.1], ?_, by simp⟩
      rw [digitsVal_snoc, h2, this.2]
      omega

/-- The signed value `lexNumber` assigns. -/
def sgnVal (neg : Bool) (v : Nat) : Int := if neg then -(v : Int) else v

/-- `lexNumber` on an optionally signed, non-empty digit string: an integer. -/
theorem lexNumber_int (neg : Bool) (ds : List UInt8) (hd : ds.all isDigit = true)
    (hne : ds ≠ []) :
    lexNumber (signBytes neg ++ ds) = some (.int (sgnVal neg (digitsVal ds))) := by
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons d ds' => exact ⟨d, ds', rfl⟩
  have hdr := digitRun_all _ hd
  have hdd : isDigit d = true := by simp only [List.all_cons, Bool.and_eq_true] at hd; exact hd.1
  obtain ⟨-, h43, h45, -⟩ := digit_facts d hdd
  cases neg <;> simp [lexNumber, signBytes, sgnVal, h43, h45, hdr]

/-- `lexNumber` on an optionally signed `ip.frac` with a non-empty digit string `ip`: a
normalized real. -/
theorem lexNumber_real (neg : Bool) (ip frac : List UInt8) (hip : ip.all isDigit = true)
    (hne : ip ≠ []) (hfrac : frac.all isDigit = true) :
    lexNumber (signBytes neg ++ (ip ++ 46 :: frac)) =
      some (.real (Decimal.normalize ⟨sgnVal neg (digitsVal (ip ++ frac)), frac.length⟩)) := by
  obtain ⟨d, ip', rfl⟩ : ∃ d ip', ip = d :: ip' := by
    cases ip with
    | nil => exact absurd rfl hne
    | cons d ip' => exact ⟨d, ip', rfl⟩
  have hdr := digitRun_dot _ frac hip
  simp only [List.cons_append] at hdr
  have hfrac' : ∀ x ∈ frac, isDigit x = true := List.all_eq_true.mp hfrac
  have hdd : isDigit d = true := by
    simp only [List.all_cons, Bool.and_eq_true] at hip; exact hip.1
  obtain ⟨-, h43, h45, -⟩ := digit_facts d hdd
  cases neg <;> simp [lexNumber, signBytes, sgnVal, h43, h45, hdr] <;> exact hfrac'

/-! ## One token -/

/-- Skipping whitespace stops at once at a byte that is neither whitespace nor `%`. -/
theorem skipWs_head (b : UInt8) (l : List UInt8) (hw : isWhite b = false) (h37 : (b == 37) = false) :
    skipWs (b :: l) = b :: l := by
  simp [skipWs, hw, h37]

/-- `nextAt` on a regular run `b :: w` ended by `rest`: a number or a keyword. -/
theorem nextAt_run (off : Nat) (b : UInt8) (w rest : List UInt8) (hb : isRegular b = true)
    (hw : w.all isRegular = true) (hs : StopsRun rest) :
    nextAt off (b :: (w ++ rest)) =
      if startsNumber b then
        (match lexNumber (b :: w) with
          | some t => .ok (some (t, rest))
          | none => .error ⟨off, .badNumber⟩)
      else .ok (some (.keyword (b :: w), rest)) := by
  obtain ⟨h91, h93, h123, h125, h41, h62, h60, h40, h47, -, -⟩ := regular_facts b hb
  simp only [nextAt, h91, h93, h123, h125, h41, h62, h60, h40, h47, regularRun_append w rest hw hs,
    Bool.false_eq_true, ↓reduceIte]
  split <;> rfl

/-- An optionally signed number word `signBytes neg ++ body` (body starting with a digit, all
regular) followed by `rest`: `nextAt` returns what `lexNumber` gives, and `skipWs` stops at
once. -/
theorem lex_signed (neg : Bool) (body rest : List UInt8) (t : Token)
    (hb : body.all isRegular = true) (hd : ∃ d r, body = d :: r ∧ isDigit d = true)
    (hlex : lexNumber (signBytes neg ++ body) = some t) (hs : StopsRun rest) :
    (∀ off, nextAt off (signBytes neg ++ body ++ rest) = .ok (some (t, rest))) ∧
      skipWs (signBytes neg ++ body ++ rest) = signBytes neg ++ body ++ rest := by
  obtain ⟨d, r, rfl, hdd⟩ := hd
  cases neg
  · obtain ⟨hreg, -, -, -⟩ := digit_facts d hdd
    obtain ⟨-, -, -, -, -, -, -, -, -, hw, h37⟩ := regular_facts d hreg
    have hr : r.all isRegular = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hb; exact hb.2
    have hsn : startsNumber d = true := by simp [startsNumber, hdd]
    simp only [signBytes, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hlex ⊢
    refine ⟨fun off => ?_, skipWs_head _ _ hw h37⟩
    rw [List.cons_append, nextAt_run off d r rest hreg hr hs]
    simp [hsn, hlex]
  · have hsn : startsNumber 45 = true := by decide
    simp only [signBytes, ↓reduceIte, List.cons_append, List.nil_append] at hlex ⊢
    refine ⟨fun off => ?_, skipWs_head _ _ (by decide) (by decide)⟩
    rw [← List.cons_append, nextAt_run off 45 (d :: r) rest (by decide) hb hs]
    simp [hsn, hlex]

/-- The integer value of `intBytes`. -/
theorem sgnVal_int (i : Int) : sgnVal (decide (i < 0)) i.natAbs = i := by
  by_cases h : i < 0
  · simp [sgnVal, h]; omega
  · simp [sgnVal, h]; omega

/-- An integer token lexes back. -/
theorem lex_int (i : Int) (rest : List UInt8) (hs : StopsRun rest) :
    (∀ off, nextAt off (tokBytes (.int i) ++ rest) = .ok (some (.int i, rest))) ∧
      skipWs (tokBytes (.int i) ++ rest) = tokBytes (.int i) ++ rest := by
  obtain ⟨hd, hv, hne⟩ := natDigits_spec i.natAbs
  have hreg : (natDigits i.natAbs).all isRegular = true := by
    rw [List.all_eq_true] at hd ⊢; exact fun x hx => (digit_facts x (hd x hx)).1
  have hhead : ∃ d r, natDigits i.natAbs = d :: r ∧ isDigit d = true := by
    cases h : natDigits i.natAbs with
    | nil => exact absurd h hne
    | cons d r => rw [h] at hd; simp only [List.all_cons, Bool.and_eq_true] at hd; exact ⟨d, r, rfl, hd.1⟩
  have hlex := lexNumber_int (decide (i < 0)) _ hd hne
  rw [hv, sgnVal_int] at hlex
  exact lex_signed _ _ rest _ hreg hhead hlex hs

/-- The padded digits of a real are digits, at least `scale + 1` of them, denoting `|m|`. -/
theorem paddedDigits_spec (d : Decimal) :
    (paddedDigits d).all isDigit = true ∧ d.scale + 1 ≤ (paddedDigits d).length ∧
      digitsVal (paddedDigits d) = d.mantissa.natAbs := by
  obtain ⟨hd, hv, -⟩ := natDigits_spec d.mantissa.natAbs
  refine ⟨?_, ?_, ?_⟩
  · simp only [paddedDigits, List.all_append, hd, Bool.and_true]
    rw [List.all_eq_true]; intro x hx
    rw [List.eq_of_mem_replicate hx]; decide
  · simp only [paddedDigits, List.length_append, List.length_replicate]; omega
  · simp only [paddedDigits, digitsVal_zeros, hv]

/-- A canonical real token lexes back. -/
theorem lex_real (d : Decimal) (hc : d.IsCanonical) (rest : List UInt8) (hs : StopsRun rest) :
    (∀ off, nextAt off (tokBytes (.real d) ++ rest) = .ok (some (.real d, rest))) ∧
      skipWs (tokBytes (.real d) ++ rest) = tokBytes (.real d) ++ rest := by
  obtain ⟨hd, hlen, hv⟩ := paddedDigits_spec d
  generalize hp : paddedDigits d = p at hd hlen hv
  have hip : (p.take (p.length - d.scale)).all isDigit = true := by
    rw [List.all_eq_true] at hd ⊢; exact fun x hx => hd x (List.mem_of_mem_take hx)
  have hfr : (p.drop (p.length - d.scale)).all isDigit = true := by
    rw [List.all_eq_true] at hd ⊢; exact fun x hx => hd x (List.mem_of_mem_drop hx)
  have hfl : (p.drop (p.length - d.scale)).length = d.scale := by
    simp only [List.length_drop]; omega
  have hne : p.take (p.length - d.scale) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_nil] at this
    omega
  have hlex := lexNumber_real (decide (d.mantissa < 0)) _ _ hip hne hfr
  rw [List.take_append_drop, hv, sgnVal_int, hfl] at hlex
  have hnorm : Decimal.normalize ⟨d.mantissa, d.scale⟩ = d :=
    Decimal.normalize_of_isCanonical d hc
  rw [hnorm] at hlex
  have hreg : (p.take (p.length - d.scale) ++ 46 :: p.drop (p.length - d.scale)).all
      isRegular = true := by
    rw [List.all_eq_true] at hip hfr ⊢
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (digit_facts x (hip x hx)).1
    · rcases List.mem_cons.mp hx with rfl | hx
      · decide
      · exact (digit_facts x (hfr x hx)).1
  have hhead : ∃ c r, p.take (p.length - d.scale) ++ 46 :: p.drop (p.length - d.scale) =
      c :: r ∧ isDigit c = true := by
    cases h : p.take (p.length - d.scale) with
    | nil => exact absurd h hne
    | cons c r =>
      rw [h] at hip
      simp only [List.all_cons, Bool.and_eq_true] at hip
      exact ⟨c, _, rfl, hip.1⟩
  have := lex_signed _ _ rest _ hreg hhead hlex hs
  simp only [tokBytes, realBytes, hp]
  exact this

/-- Escaped name bytes are regular. -/
theorem nameBody_regular (bytes : List UInt8) : (bytes.flatMap nameByte).all isRegular = true := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.all_append, ih, Bool.and_true]
    unfold nameByte
    split
    · rename_i h; simp [(nameSafe_facts b h).1]
    · obtain ⟨-, -, h1, h2, -, -⟩ := hexDigit_facts b
      simp [hexPair, h1, h2]; decide

/-- A name-safe byte is written as itself. -/
theorem nameByte_safe {b : UInt8} (h : nameSafe b = true) : nameByte b = [b] := by
  simp [nameByte, h]

/-- Any other byte is written `#XX`. -/
theorem nameByte_esc {b : UInt8} (h : nameSafe b = false) : nameByte b = 35 :: hexPair b := by
  simp [nameByte, h]

/-- Decoding escaped name bytes gives the bytes back when none is NUL. -/
theorem decodeName_body (bytes : List UInt8) (h : (0 : UInt8) ∉ bytes) :
    decodeName (bytes.flatMap nameByte) = .ok bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, not_or] at h
    have ih' := ih h.2
    simp only [List.flatMap_cons]
    cases hs : nameSafe b
    · rw [nameByte_esc hs]
      obtain ⟨hh, hl, -, -, hb, hnz⟩ := hexDigit_facts b
      have hnz' : ¬ (b.toNat / 16 * 16 = 0 ∧ b.toNat % 16 = 0) := by
        rcases hnz with hz | hz
        · exact absurd hz.symm h.1
        · omega
      simp [decodeName, hexPair, hh, hl, hnz', hb, ih', Except.map]
    · rw [nameByte_safe hs]
      obtain ⟨-, h35, h0⟩ := nameSafe_facts b hs
      conv => lhs; rw [decodeName.eq_def]
      simp [h35, h0, ih', Except.map]

/-- A canonical name token lexes back. -/
theorem lex_name (n : Name) (hc : n.isCanonical = true) (rest : List UInt8) (hs : StopsRun rest) :
    (∀ off, nextAt off (tokBytes (.name n) ++ rest) = .ok (some (.name n, rest))) ∧
      skipWs (tokBytes (.name n) ++ rest) = tokBytes (.name n) ++ rest := by
  have h0 : (0 : UInt8) ∉ n.bytes := by
    simpa [Name.isCanonical] using hc
  refine ⟨fun off => ?_, skipWs_head _ _ (by decide) (by decide)⟩
  simp only [tokBytes, nameBytes, List.cons_append]
  simp [nextAt, regularRun_append _ rest (nameBody_regular n.bytes) hs, decodeName_body _ h0]

/-- The nibbles of a byte string, as `hexBody` reads them. -/
def nibbles (s : List UInt8) : List Nat := s.flatMap fun b => [b.toNat / 16, b.toNat % 16]

/-- `hexBody` reads the printed hex digits and the closing `>`. -/
theorem hexBody_print (s rest : List UInt8) :
    hexBody (hexBytes s ++ 62 :: rest) = .ok (nibbles s, rest) := by
  induction s with
  | nil => simp [hexBytes, nibbles, hexBody]
  | cons b bs ih =>
    obtain ⟨hh, hl, rh, rl, -, -⟩ := hexDigit_facts b
    obtain ⟨-, -, -, -, -, h62h, -, -, -, wh, -⟩ := regular_facts _ rh
    obtain ⟨-, -, -, -, -, h62l, -, -, -, wl, -⟩ := regular_facts _ rl
    simp only [hexBytes, nibbles, List.flatMap_cons] at ih ⊢
    simp [hexPair, hexBody, hh, hl, h62h, h62l, wh, wl, ih, Except.map]

/-- Packing the nibbles of a byte string gives it back. -/
theorem packNibbles_nibbles (s : List UInt8) : packNibbles (nibbles s) = s := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨-, -, -, -, hb, -⟩ := hexDigit_facts b
    simp only [nibbles, List.flatMap_cons] at ih ⊢
    simp [packNibbles, hb, ih]

/-- A hex-string token lexes back. -/
theorem lex_hex (s rest : List UInt8) :
    (∀ off, nextAt off (tokBytes (.hexString s) ++ rest) = .ok (some (.hexString s, rest))) ∧
      skipWs (tokBytes (.hexString s) ++ rest) = tokBytes (.hexString s) ++ rest := by
  refine ⟨fun off => ?_, skipWs_head _ _ (by decide) (by decide)⟩
  simp only [tokBytes, List.cons_append, List.append_assoc, List.nil_append]
  obtain ⟨c, cs, hc, hc60⟩ : ∃ c cs, hexBytes s ++ 62 :: rest = c :: cs ∧ (c == 60) = false := by
    cases s with
    | nil => exact ⟨62, rest, rfl, by decide⟩
    | cons b bs =>
      obtain ⟨-, -, rh, -, -, -⟩ := hexDigit_facts b
      obtain ⟨-, -, -, -, -, -, h60, -, -, -, -⟩ := regular_facts _ rh
      exact ⟨_, _, by simp [hexBytes, hexPair]; rfl, h60⟩
  have hb := hexBody_print s rest
  rw [hc] at hb ⊢
  simp [nextAt, hc60, hb, packNibbles_nibbles]

/-- A keyword (a regular run not starting like a number) lexes back. -/
theorem lex_keyword (b : UInt8) (w : List UInt8) (hb : isRegular b = true)
    (hw : w.all isRegular = true) (hsn : startsNumber b = false) (rest : List UInt8)
    (hs : StopsRun rest) :
    (∀ off, nextAt off (b :: w ++ rest) = .ok (some (.keyword (b :: w), rest))) ∧
      skipWs (b :: w ++ rest) = b :: w ++ rest := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hw', h37⟩ := regular_facts b hb
  refine ⟨fun off => ?_, skipWs_head _ _ hw' h37⟩
  rw [List.cons_append, nextAt_run off b w rest hb hw hs]
  simp [hsn]

/-- **One token.** Every printable token, followed by input that ends a regular run, is read
back by `nextAt` (at any offset), and `skipWs` does not move before it. -/
theorem lex_tok (t : Token) (ht : printableTok t = true) (rest : List UInt8)
    (hs : StopsRun rest) :
    (∀ off, nextAt off (tokBytes t ++ rest) = .ok (some (t, rest))) ∧
      skipWs (tokBytes t ++ rest) = tokBytes t ++ rest := by
  cases t with
  | int i => exact lex_int i rest hs
  | real d => exact lex_real d ht rest hs
  | hexString s => exact lex_hex s rest
  | name n => exact lex_name n ht rest hs
  | keyword kw =>
    simp only [printableTok, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with ((rfl | rfl) | rfl) | rfl
    · exact lex_keyword 82 [] (by decide) rfl (by decide) rest hs
    · exact lex_keyword 116 _ (by decide) rfl (by decide) rest hs
    · exact lex_keyword 102 _ (by decide) rfl (by decide) rest hs
    · exact lex_keyword 110 _ (by decide) rfl (by decide) rest hs
  | arrayOpen =>
    exact ⟨fun off => by simp [tokBytes, nextAt], skipWs_head _ _ (by decide) (by decide)⟩
  | arrayClose =>
    exact ⟨fun off => by simp [tokBytes, nextAt], skipWs_head _ _ (by decide) (by decide)⟩
  | dictOpen =>
    exact ⟨fun off => by simp [tokBytes, nextAt], skipWs_head _ _ (by decide) (by decide)⟩
  | dictClose =>
    exact ⟨fun off => by simp [tokBytes, nextAt], skipWs_head _ _ (by decide) (by decide)⟩
  | litString _ | braceOpen | braceClose => simp [printableTok] at ht

/-- `next` reads a printable token at the start of the input. -/
theorem next_tok (t : Token) (ht : printableTok t = true) (rest : List UInt8)
    (hs : StopsRun rest) : next (tokBytes t ++ rest) = .ok (some (t, rest)) := by
  obtain ⟨h1, h2⟩ := lex_tok t ht rest hs
  unfold next
  rw [h2, h1]

/-- `next` skips one space and reads a printable token. -/
theorem next_sp_tok (t : Token) (ht : printableTok t = true) (rest : List UInt8)
    (hs : StopsRun rest) : next (32 :: (tokBytes t ++ rest)) = .ok (some (t, rest)) := by
  obtain ⟨h1, h2⟩ := lex_tok t ht rest hs
  have hsk : skipWs (32 :: (tokBytes t ++ rest)) = tokBytes t ++ rest := by
    have h32 : ∀ l, skipWs (32 :: l) = skipWs l := fun l => by simp [skipWs, isWhite]
    rw [h32, h2]
  unfold next
  rw [hsk, h1]

/-! ## Token sequences -/

/-- What follows a rendered token (`renderTail`) ends a regular run. -/
theorem stopsRun_renderTail (ts : List Token) : StopsRun (renderTail ts) := by
  cases ts with
  | nil => trivial
  | cons t ts => simp only [renderTail, StopsRun]; decide

/-- Lexing the tokens after the first one (each preceded by a space) gives them back. -/
theorem lexAll_renderTail (ts : List Token) (h : ts.all printableTok = true) :
    Spec.Lex.lexAll (renderTail ts) = .ok ts := by
  induction ts with
  | nil => exact LexEquiv.lexAll_of_none rfl
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [renderTail, LexEquiv.lexAll_of_some (next_sp_tok t h.1 _ (stopsRun_renderTail ts)),
      ih h.2]

/-- **Lexing half for token lists.** Lexing a rendered list of printable tokens gives it back. -/
theorem lexAll_render (ts : List Token) (h : ts.all printableTok = true) :
    Spec.Lex.lexAll (render ts) = .ok ts := by
  cases ts with
  | nil => exact LexEquiv.lexAll_of_none rfl
  | cons t ts =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [render, LexEquiv.lexAll_of_some (next_tok t h.1 _ (stopsRun_renderTail ts)),
      lexAll_renderTail ts h.2]

/-! ## Printed tokens are printable -/

mutual
/-- The tokens printed for a canonical object are all printable. -/
theorem printTokens_printable : (o : PdfObject) → o.isCanonical = true →
    (printTokens o).all printableTok = true
  | .null, _ | .bool true, _ | .bool false, _ | .int _, _ | .string _, _ | .ref _ _, _ => rfl
  | .real d, h => by simpa [printTokens, printableTok, PdfObject.isCanonical] using h
  | .name n, h => by simpa [printTokens, printableTok, PdfObject.isCanonical] using h
  | .array xs, h => by
    simp only [PdfObject.isCanonical] at h
    simp [printTokens, printableTok, printItems_printable xs h]
  | .dict es, h => by
    simp only [PdfObject.isCanonical, Bool.and_eq_true] at h
    simp [printTokens, printableTok, printEntries_printable es h.1.2 h.2]

/-- `printTokens_printable` for array members. -/
theorem printItems_printable : (xs : List PdfObject) → PdfObject.isCanonicalList xs = true →
    (printItems xs).all printableTok = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [PdfObject.isCanonicalList, Bool.and_eq_true] at h
    simp only [printItems, List.all_append, printTokens_printable x h.1,
      printItems_printable xs h.2, Bool.and_self]

/-- `printTokens_printable` for dictionary entries (keys canonical too). -/
theorem printEntries_printable : (es : List (Name × PdfObject)) →
    es.all (fun e => e.1.isCanonical) = true → PdfObject.isCanonicalDict es = true →
    (printEntries es).all printableTok = true
  | [], _, _ => rfl
  | (k, v) :: es, hk, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hk
    simp only [PdfObject.isCanonicalDict, Bool.and_eq_true] at h
    simp only [printEntries, List.all_cons, List.all_append, printableTok, hk.1,
      printTokens_printable v h.1, printEntries_printable es hk.2 h.2, Bool.and_self]
end

/-- **(A) Lexing half.** The spec lexer reads the printed bytes of a canonical object back as
exactly the printed tokens. -/
theorem lexAll_print (o : PdfObject) (hc : o.Canonical) :
    Spec.Lex.lexAll (printObj o) = .ok (printTokens o) :=
  lexAll_render _ (printTokens_printable o hc)

/-! ## Parsing the printed tokens -/

/-- `r` does not start with the keyword `R`. -/
def NoR (r : List Token) : Prop := ∀ r', r ≠ .keyword Spec.Object.kwR :: r'

/-- `r` does not start with `g R` (so an integer before `r` is not a reference, G1). -/
def NoIntR (r : List Token) : Prop := ¬ ∃ g rest, r = .int g :: .keyword Spec.Object.kwR :: rest

/-- Printed tokens never start with the keyword `R`. -/
theorem noR_print (o : PdfObject) (r : List Token) : NoR (printTokens o ++ r) := by
  intro r' h
  cases o with
  | bool b => cases b <;> simp [printTokens, kwTrue, kwFalse, Spec.Object.kwR] at h
  | _ => simp [printTokens, kwNull, Spec.Object.kwR] at h

/-- Printed tokens followed by something not starting with `R` never start with `g R`. -/
theorem noIntR_print (o : PdfObject) (r : List Token) (hr : NoR r) :
    NoIntR (printTokens o ++ r) := by
  rintro ⟨g, rest, h⟩
  cases o with
  | int i =>
    simp only [printTokens, List.cons_append, List.nil_append, List.cons.injEq] at h
    exact hr _ h.2
  | bool b => cases b <;> simp [printTokens] at h
  | _ => simp [printTokens] at h

/-- Array items followed by `]` never start with `R`. -/
theorem noR_items (xs : List PdfObject) (r : List Token) :
    NoR (printItems xs ++ .arrayClose :: r) := by
  cases xs with
  | nil => intro r' h; simp [printItems] at h
  | cons x xs => rw [printItems, List.append_assoc]; exact noR_print x _

/-- Array items followed by `]` never start with `g R`. -/
theorem noIntR_items (xs : List PdfObject) (r : List Token) :
    NoIntR (printItems xs ++ .arrayClose :: r) := by
  cases xs with
  | nil => rintro ⟨g, rest, h⟩; simp [printItems] at h
  | cons x xs =>
    rw [printItems, List.append_assoc]; exact noIntR_print x _ (noR_items xs r)

/-- Dictionary entries followed by `>>` never start with `g R`. -/
theorem noIntR_entries (es : List (Name × PdfObject)) (r : List Token) :
    NoIntR (printEntries es ++ .dictClose :: r) := by
  rintro ⟨g, rest, h⟩
  cases es with
  | nil => simp [printEntries] at h
  | cons e es => obtain ⟨k, v⟩ := e; simp [printEntries] at h

mutual
/-- **(B) Parsing half, generalized.** The printed tokens of a canonical object with references
in range and depth at most `F`, followed by `r` (not starting with `g R`), derive the object
with rest `r`. -/
theorem parses_print : (o : PdfObject) → ∀ {F : Nat} {r : List Token}, o.isCanonical = true →
    refsInRange o = true → o.depth ≤ F → NoIntR r →
    Spec.Object.Parses F (printTokens o ++ r) o r
  | .null, _, _, _, _, _, _ => .null
  | .bool true, _, _, _, _, _, _ => .true_
  | .bool false, _, _, _, _, _, _ => .false_
  | .int _, _, _, _, _, _, hr => .int hr
  | .real _, _, _, _, _, _, _ => .real
  | .string _, _, _, _, _, _, _ => .hexString
  | .name _, _, _, _, _, _, _ => .name
  | .ref n g, F, r, _, hrange, _, _ => by
    simp only [refsInRange, Bool.and_eq_true, decide_eq_true_eq] at hrange
    have h := Spec.Object.Parses.ref (fuel := F) (rest := r) (n := (n : Int)) (g := (g : Int))
      ⟨by omega, by omega, by omega⟩
    simpa [printTokens, kwR, Spec.Object.kwR] using h
  | .array xs, F, r, hc, hrange, hd, _ => by
    cases F with
    | zero => simp [PdfObject.depth] at hd
    | succ f =>
      simp only [PdfObject.depth] at hd
      simp only [PdfObject.isCanonical] at hc
      simp only [refsInRange] at hrange
      have h := parses_items xs (f := f) (r := r) hc hrange (by omega)
      simpa [printTokens] using Spec.Object.Parses.array h
  | .dict es, F, r, hc, hrange, hd, _ => by
    cases F with
    | zero => simp [PdfObject.depth] at hd
    | succ f =>
      have hnd := PdfObject.Canonical.keys_nodup hc
      simp only [PdfObject.depth] at hd
      simp only [PdfObject.isCanonical, Bool.and_eq_true] at hc
      simp only [refsInRange] at hrange
      have h := parses_entries es (f := f) (r := r) hc.2 hrange (by omega)
      simpa [printTokens] using Spec.Object.Parses.dict h hnd

/-- `parses_print` for array members, through the closing `]`. -/
theorem parses_items : (xs : List PdfObject) → ∀ {f : Nat} {r : List Token},
    PdfObject.isCanonicalList xs = true → refsInRangeList xs = true →
    PdfObject.depthList xs ≤ f →
    Spec.Object.ParsesItems f (printItems xs ++ .arrayClose :: r) xs r
  | [], _, _, _, _, _ => .nil
  | x :: xs, f, r, hc, hrange, hd => by
    simp only [PdfObject.isCanonicalList, Bool.and_eq_true] at hc
    simp only [refsInRangeList, Bool.and_eq_true] at hrange
    simp only [PdfObject.depthList] at hd
    rw [printItems, List.append_assoc]
    exact .cons (parses_print x hc.1 hrange.1 (by omega) (noIntR_items xs r))
      (parses_items xs hc.2 hrange.2 (by omega))

/-- `parses_print` for dictionary entries, through the closing `>>`. -/
theorem parses_entries : (es : List (Name × PdfObject)) → ∀ {f : Nat} {r : List Token},
    PdfObject.isCanonicalDict es = true → refsInRangeDict es = true →
    PdfObject.depthDict es ≤ f →
    Spec.Object.ParsesEntries f (printEntries es ++ .dictClose :: r) es r
  | [], _, _, _, _, _ => .nil
  | (k, v) :: es, f, r, hc, hrange, hd => by
    simp only [PdfObject.isCanonicalDict, Bool.and_eq_true] at hc
    simp only [refsInRangeDict, Bool.and_eq_true] at hrange
    simp only [PdfObject.depthDict] at hd
    rw [printEntries, List.cons_append, List.append_assoc]
    exact .cons (parses_print v hc.1 hrange.1 (by omega) (noIntR_entries es r))
      (parses_entries es hc.2 hrange.2 (by omega))
end

/-- **(B) Parsing half.** The spec parser reads the printed tokens of a canonical object with
references in range and depth at most `F` back as the object, consuming all tokens. -/
theorem parse_printTokens (o : PdfObject) (F : Nat) (hc : o.Canonical) (hr : RefsInRange o)
    (hd : o.depth ≤ F) : Spec.Object.parse F (printTokens o) = .ok (o, []) := by
  have h := parses_print o (F := F) (r := []) hc hr hd (by rintro ⟨g, rest, h⟩; cases h)
  rw [List.append_nil] at h
  exact h.parse_eq

/-! ## Round trip -/

/-- **Round trip against the spec (M1, Plan.md §6 Phase 1).** Lexing the printed bytes of a
canonical object (references in range, depth at most `F`) with the spec lexer and parsing the
tokens with the spec parser gives the object back, with no tokens left over. -/
theorem roundTrip_spec (o : PdfObject) (F : Nat) (hc : o.Canonical) (hr : RefsInRange o)
    (hd : o.depth ≤ F) :
    Spec.Object.parse F <$> Spec.Lex.lexAll (printObj o) = .ok (.ok (o, [])) := by
  rw [lexAll_print o hc]
  exact congrArg Except.ok (parse_printTokens o F hc hr hd)

/-- **Lexing half for the efficient tokenizer.** `Core.Lex.lexAll` reads the printed bytes of a
canonical object back as exactly the printed tokens (via `LexEquiv.lexAll_eq`). -/
theorem roundTrip_core (o : PdfObject) (hc : o.Canonical) :
    Core.Lex.lexAll (print o) = .ok (printTokens o) := by
  rw [LexEquiv.lexAll_eq]
  simpa [print] using lexAll_print o hc

/-- **Round trip through the efficient tokenizer and the spec parser.** -/
theorem roundTrip_core_spec (o : PdfObject) (F : Nat) (hc : o.Canonical) (hr : RefsInRange o)
    (hd : o.depth ≤ F) :
    Spec.Object.parse F <$> Core.Lex.lexAll (print o) = .ok (.ok (o, [])) := by
  rw [roundTrip_core o hc]
  exact congrArg Except.ok (parse_printTokens o F hc hr hd)

/-! ## Executable checks -/

section Tests

/-- Test helper: spec lex + spec parse (fuel 256) of the printed object gives it back with no
tokens left. -/
private def rtSpec (o : PdfObject) : Bool :=
  match Spec.Object.parse 256 <$> Spec.Lex.lexAll (printObj o) with
  | .ok (.ok (o', [])) => o' == o
  | _ => false

/-- Test helper: the same through the efficient tokenizer on the `ByteArray`. -/
private def rtCore (o : PdfObject) : Bool :=
  match Spec.Object.parse 256 <$> Core.Lex.lexAll (print o) with
  | .ok (.ok (o', [])) => o' == o
  | _ => false

private def nm (s : String) : Name := Name.ofString s

private def samples : List PdfObject :=
  [ .null, .bool true, .bool false, .int 0, .int (-1), .int 12345678901234567890,
    .real ⟨0, 0⟩, .real ⟨5, 0⟩, .real ⟨-35, 1⟩, .real ⟨5, 3⟩, .real ⟨-123456789, 9⟩,
    .string [], .string [0, 40, 41, 92, 255], .name ⟨[]⟩, .name (nm "A B#/c%(x)"),
    .name ⟨[1, 0x23, 0x7F, 0x80, 0xFF]⟩, .ref 1 0, .ref 4294967296 65535,
    .array [], .dict [],
    .array [.int 1, .int 2, .ref 3 0, .int 4, .int 5],
    .array [.int 1, .int 0, .array [.int 2], .ref 1 0],
    .dict [(nm "Type", .name (nm "Page")), (nm "MediaBox",
      .array [.int 0, .int 0, .real ⟨6125, 1⟩, .int 792]), (nm "Parent", .ref 3 0),
      (nm "K", .dict [(nm "", .array [.array [], .dict []]), (nm "N", .null)])] ]

#guard samples.all fun o => o.isCanonical && refsInRange o
#guard samples.all rtSpec
#guard samples.all rtCore
-- reference lookahead (G1): consecutive integers without `R` stay integers
#guard rtSpec (.array [.int 1, .int 2, .int 3, .int 0, .int 7])
#guard rtSpec (.dict [(nm "A", .int 1), (nm "B", .int 0)])
-- deep nesting within the fuel
#guard rtSpec ((List.range 100).foldl (fun o _ => .array [o]) (.int 0))
-- outside the theorem's hypotheses the round trip may fail
#guard !rtSpec (.ref 0 0)
#guard !rtSpec (.real ⟨50, 1⟩)
#guard !rtSpec (.name ⟨[0]⟩)

end Tests

end SafePdf.Spec.RoundTrip
