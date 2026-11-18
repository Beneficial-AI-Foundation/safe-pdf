import SafePdf.Core.Token

/-!
# Denotational lexer spec (Plan.md §5.1, §6 Phase 1, task 1.2; ISO 32000-2 §7.2–7.3)

The small, obviously-correct (and slow) reference lexer of Plan.md §5.1. The efficient
tokenizer `SafePdf.Core.Lex` (task 1.3) is proven equal to it in task 1.6. The interface is
fixed by `SafePdf/Core/Token.lean`:

  `Spec.Lex.next : List UInt8 → Except LexError (Option (Token × List UInt8))`

Every function here is structural recursion over `List UInt8`, except `lexAll`, which
recurses on the rest of the input and terminates because `next` consumes at least one byte
(`next_consumes`).

## Semantics

1. Whitespace (bytes 0, 9, 10, 12, 13, 32; ISO 32000-2 §7.2.3) and comments (`%` up to, not
   including, the next CR or LF or the end of input; §7.2.4) are skipped repeatedly
   (`skipWs`). End of input → `ok none`.
2. Delimiters (§7.2.3): `[ ] { }` are tokens, `<<`/`>>` open/close dictionaries, `<` starts a
   hex string, `(` a literal string, `/` a name; `)` and a lone `>` are
   `unexpectedDelimiter` errors.
3. Any other maximal run of regular bytes (`regularRun`) is a number if it starts with
   `+ - .` or a digit (`lexNumber`, §7.3.3; malformed → `badNumber`), else a keyword.
4. Literal strings (§7.3.4.2): `litBody`, with balanced parentheses, escapes, octal escapes
   (mod 256), line continuations, and CR LF / CR read as LF.
5. Hex strings (§7.3.4.3): `hexBody` collects nibbles skipping whitespace; `packNibbles`
   pads an odd final nibble with 0.
6. Names (§7.3.5): `decodeName` decodes `#xx` in the regular run after `/`; a bad escape is
   `badNameEscape`, a decoded 0 byte is `nulInName`.
7. Every error offset is the offset of the first byte of the offending token, relative to
   the start of the list passed to `next`.
-/

namespace SafePdf.Spec.Lex

/-! ## Character classes -/

/-- PDF whitespace (ISO 32000-2 §7.2.3, Table 1): NUL, TAB, LF, FF, CR, SP. -/
def isWhite (b : UInt8) : Bool :=
  b == 0 || b == 9 || b == 10 || b == 12 || b == 13 || b == 32

/-- PDF delimiters (ISO 32000-2 §7.2.3, Table 2): `( ) < > [ ] { } / %`. -/
def isDelim (b : UInt8) : Bool :=
  b == 40 || b == 41 || b == 60 || b == 62 || b == 91 || b == 93 || b == 123 || b == 125 ||
  b == 47 || b == 37

/-- A regular character: neither whitespace nor a delimiter (ISO 32000-2 §7.2.3). -/
def isRegular (b : UInt8) : Bool := !isWhite b && !isDelim b

/-- An ASCII decimal digit `0`–`9`. -/
def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- An ASCII octal digit `0`–`7`. -/
def isOctal (b : UInt8) : Bool := 48 ≤ b && b ≤ 55

/-- The value of a hexadecimal digit (`0-9`, `a-f`, `A-F`), or `none`. -/
def hexVal (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b && b ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b && b ≤ 70 then some (b.toNat - 55)
  else none

/-! ## Whitespace and comments -/

mutual
/-- Drop leading whitespace and comments (ISO 32000-2 §7.2.3–7.2.4). -/
def skipWs : List UInt8 → List UInt8
  | [] => []
  | b :: bs =>
    if isWhite b then skipWs bs
    else if b == 37 then skipComment bs
    else b :: bs

/-- Drop the body of a comment (after `%`) up to the next CR or LF, then continue skipping
whitespace. The CR/LF itself is whitespace, so it is dropped by `skipWs`. -/
def skipComment : List UInt8 → List UInt8
  | [] => []
  | b :: bs =>
    if b == 10 || b == 13 then skipWs bs
    else skipComment bs
end

/-! ## Regular runs, numbers and keywords -/

/-- Split a list into its maximal prefix of regular bytes and the rest. -/
def regularRun : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | b :: bs =>
    if isRegular b then
      let p := regularRun bs
      (b :: p.1, p.2)
    else ([], b :: bs)

/-- Split a list into its maximal prefix of decimal digits and the rest. -/
def digitRun : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | b :: bs =>
    if isDigit b then
      let p := digitRun bs
      (b :: p.1, p.2)
    else ([], b :: bs)

/-- The natural number denoted by a list of decimal digits (most significant first). -/
def digitsVal (ds : List UInt8) : Nat :=
  ds.foldl (fun acc d => acc * 10 + (d.toNat - 48)) 0

/-- Interpret a regular run that starts with `+ - .` or a digit as a number (ISO 32000-2
§7.3.3): it must match `[+-]?(digits)?(\.(digits)?)?` with at least one digit. Without a
`.` it is an integer; with one it is a real, `Decimal.normalize`d, whose mantissa is the
signed value of all digits and whose scale is the number of digits after the `.`. -/
def lexNumber (run : List UInt8) : Option Token :=
  let (neg, body) : Bool × List UInt8 :=
    match run with
    | b :: r => if b == 43 then (false, r) else if b == 45 then (true, r) else (false, run)
    | [] => (false, [])
  let sgn : Int → Int := fun v => if neg then -v else v
  let (ip, after) := digitRun body
  match after with
  | [] => if ip.isEmpty then none else some (.int (sgn (digitsVal ip)))
  | d :: frac =>
    if d == 46 && frac.all isDigit && !(ip.isEmpty && frac.isEmpty) then
      some (.real (Decimal.normalize ⟨sgn (digitsVal (ip ++ frac)), frac.length⟩))
    else none

/-- Whether a regular run is meant as a number: it starts with `+`, `-`, `.` or a digit. -/
def startsNumber (b : UInt8) : Bool := b == 43 || b == 45 || b == 46 || isDigit b

/-! ## Literal strings -/

/-- Read the body of a literal string after its `(` (ISO 32000-2 §7.3.4.2). `depth` is the
number of currently open unescaped `(` beyond the outer one. Returns the decoded bytes and
the input after the closing `)`, or `none` if the input ends first (unterminated). -/
def litBody : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | _, [] => none
  | depth, b :: bs =>
    if b == 92 then
      -- backslash escape
      match hbs : bs with
      | [] => none
      | c :: cs =>
        if c == 110 then (litBody depth cs).map fun p => (10 :: p.1, p.2)        -- \n
        else if c == 114 then (litBody depth cs).map fun p => (13 :: p.1, p.2)   -- \r
        else if c == 116 then (litBody depth cs).map fun p => (9 :: p.1, p.2)    -- \t
        else if c == 98 then (litBody depth cs).map fun p => (8 :: p.1, p.2)     -- \b
        else if c == 102 then (litBody depth cs).map fun p => (12 :: p.1, p.2)   -- \f
        else if isOctal c then
          match hcs : cs with
          | c2 :: cs2 =>
            if isOctal c2 then
              match hcs2 : cs2 with
              | c3 :: cs3 =>
                if isOctal c3 then
                  let v := (c.toNat - 48) * 64 + (c2.toNat - 48) * 8 + (c3.toNat - 48)
                  (litBody depth cs3).map fun p => (UInt8.ofNat v :: p.1, p.2)
                else
                  let v := (c.toNat - 48) * 8 + (c2.toNat - 48)
                  (litBody depth cs2).map fun p => (UInt8.ofNat v :: p.1, p.2)
              | [] =>
                let v := (c.toNat - 48) * 8 + (c2.toNat - 48)
                (litBody depth cs2).map fun p => (UInt8.ofNat v :: p.1, p.2)
            else (litBody depth cs).map fun p => (UInt8.ofNat (c.toNat - 48) :: p.1, p.2)
          | [] => (litBody depth cs).map fun p => (UInt8.ofNat (c.toNat - 48) :: p.1, p.2)
        else if c == 13 then
          -- line continuation: CR LF or CR
          match _hcs : cs with
          | c2 :: cs2 => if c2 == 10 then litBody depth cs2 else litBody depth cs
          | [] => litBody depth cs
        else if c == 10 then litBody depth cs                                    -- continuation
        else (litBody depth cs).map fun p => (c :: p.1, p.2)  -- \( \) \\ and any other byte
    else if b == 40 then (litBody (depth + 1) bs).map fun p => (40 :: p.1, p.2)
    else if b == 41 then
      match depth with
      | 0 => some ([], bs)
      | d + 1 => (litBody d bs).map fun p => (41 :: p.1, p.2)
    else if b == 13 then
      -- unescaped CR LF or lone CR reads as LF
      match _hbs : bs with
      | c :: cs => if c == 10 then (litBody depth cs).map fun p => (10 :: p.1, p.2)
                   else (litBody depth bs).map fun p => (10 :: p.1, p.2)
      | [] => none
    else (litBody depth bs).map fun p => (b :: p.1, p.2)
termination_by _ l => l.length
decreasing_by all_goals (simp_all; try omega)

/-! ## Hex strings -/

/-- Read the body of a hex string after its `<` (ISO 32000-2 §7.3.4.3): the nibble values in
order and the input after the closing `>`. Whitespace is skipped. Errors: `badHexDigit` for
any other byte, `unterminatedHexString` at end of input. -/
def hexBody : List UInt8 → Except LexErrorKind (List Nat × List UInt8)
  | [] => .error .unterminatedHexString
  | b :: bs =>
    if b == 62 then .ok ([], bs)
    else if isWhite b then hexBody bs
    else match hexVal b with
      | some v => (hexBody bs).map fun p => (v :: p.1, p.2)
      | none => .error .badHexDigit

/-- Pack nibbles pairwise into bytes; an odd final nibble is padded with `0`. -/
def packNibbles : List Nat → List UInt8
  | [] => []
  | [h] => [UInt8.ofNat (h * 16)]
  | h :: l :: rest => UInt8.ofNat (h * 16 + l) :: packNibbles rest

/-! ## Names -/

/-- Decode the regular run after `/` (ISO 32000-2 §7.3.5): `#` followed by two hex digits is
that byte; any other `#` is `badNameEscape`; a decoded (or raw) zero byte is `nulInName`.
Errors are reported for the leftmost offending position. -/
def decodeName : List UInt8 → Except LexErrorKind (List UInt8)
  | [] => .ok []
  | b :: bs =>
    if b == 35 then
      match bs with
      | h :: l :: rest =>
        match hexVal h, hexVal l with
        | some x, some y =>
          if x * 16 + y = 0 then .error .nulInName
          else (decodeName rest).map (UInt8.ofNat (x * 16 + y) :: ·)
        | _, _ => .error .badNameEscape
      | _ => .error .badNameEscape
    else if b == 0 then .error .nulInName
    else (decodeName bs).map (b :: ·)

/-! ## The next token -/

/-- Lex one token from input that starts at a non-whitespace, non-comment byte. `off` is the
offset of that byte (used for error offsets). Every successful result's rest is a suffix of
the input strictly shorter than it (`nextAt_consumes`). -/
def nextAt (off : Nat) : List UInt8 → Except LexError (Option (Token × List UInt8))
  | [] => .ok none
  | b :: bs =>
    let err := fun (k : LexErrorKind) => Except.error (LexError.mk off k)
    if b == 91 then .ok (some (.arrayOpen, bs))
    else if b == 93 then .ok (some (.arrayClose, bs))
    else if b == 123 then .ok (some (.braceOpen, bs))
    else if b == 125 then .ok (some (.braceClose, bs))
    else if b == 41 then err .unexpectedDelimiter
    else if b == 62 then
      match bs with
      | c :: cs => if c == 62 then .ok (some (.dictClose, cs)) else err .unexpectedDelimiter
      | [] => err .unexpectedDelimiter
    else if b == 60 then
      match bs with
      | c :: cs =>
        if c == 60 then .ok (some (.dictOpen, cs))
        else match hexBody bs with
          | .ok (ns, rest) => .ok (some (.hexString (packNibbles ns), rest))
          | .error k => err k
      | [] => err .unterminatedHexString
    else if b == 40 then
      match litBody 0 bs with
      | some (s, rest) => .ok (some (.litString s, rest))
      | none => err .unterminatedString
    else if b == 47 then
      match decodeName (regularRun bs).1 with
      | .ok n => .ok (some (.name ⟨n⟩, (regularRun bs).2))
      | .error k => err k
    else
      let run := b :: (regularRun bs).1
      let rest := (regularRun bs).2
      if startsNumber b then
        match lexNumber run with
        | some t => .ok (some (t, rest))
        | none => err .badNumber
      else .ok (some (.keyword run, rest))

/-- The next token of `l` and the input after it, or `none` at end of input (whitespace and
comments skipped first). Error offsets are relative to the start of `l`. This is the spec
interface `Spec.Lex.next` fixed in `SafePdf/Core/Token.lean`. -/
def next (l : List UInt8) : Except LexError (Option (Token × List UInt8)) :=
  nextAt (l.length - (skipWs l).length) (skipWs l)

/-! ## Consumption -/

mutual
/-- `skipWs` returns a suffix no longer than its input. -/
theorem skipWs_length_le : (l : List UInt8) → (skipWs l).length ≤ l.length
  | [] => by simp [skipWs]
  | b :: bs => by
    have h1 := skipWs_length_le bs
    have h2 := skipComment_length_le bs
    unfold skipWs
    split
    · simp; omega
    · split
      · simp; omega
      · simp

/-- `skipComment` returns a suffix no longer than its input. -/
theorem skipComment_length_le : (l : List UInt8) → (skipComment l).length ≤ l.length
  | [] => by simp [skipComment]
  | b :: bs => by
    have h1 := skipWs_length_le bs
    have h2 := skipComment_length_le bs
    unfold skipComment
    split
    · simp; omega
    · simp; omega
end

/-- The rest after a regular run is no longer than the input. -/
theorem regularRun_snd_length_le : (l : List UInt8) → (regularRun l).2.length ≤ l.length
  | [] => by simp [regularRun]
  | b :: bs => by
    have ih := regularRun_snd_length_le bs
    unfold regularRun
    split
    · simp; omega
    · simp

/-- The rest after a literal-string body is strictly shorter than the input. -/
theorem litBody_length_lt : (d : Nat) → (l : List UInt8) → (s rest : List UInt8) →
    litBody d l = some (s, rest) → rest.length < l.length
  | _, [], _, _, h => by simp [litBody] at h
  | d, b :: bs, s, rest, h => by
    unfold litBody at h
    -- every branch either recurses on a suffix of `bs` or returns `bs`
    have ihd : ∀ (d' : Nat) (t : List UInt8), t.length ≤ bs.length →
        ∀ s', litBody d' t = some (s', rest) → rest.length < (b :: bs).length := by
      intro d' t ht s' h'
      have := litBody_length_lt d' t s' rest h'
      simp; omega
    have ihm : ∀ (d' : Nat) (t : List UInt8) (x : UInt8), t.length ≤ bs.length →
        (litBody d' t).map (fun p => (x :: p.1, p.2)) = some (s, rest) →
        rest.length < (b :: bs).length := by
      intro d' t x ht h'
      cases hl : litBody d' t with
      | none => simp [hl] at h'
      | some p =>
        obtain ⟨s', r'⟩ := p
        simp [hl] at h'
        exact ihd d' t ht s' (by rw [hl, h'.2])
    split at h
    · split at h
      · simp at h
      · rename_i c cs
        split at h
        · exact ihm _ _ _ (by simp) h
        split at h
        · exact ihm _ _ _ (by simp) h
        split at h
        · exact ihm _ _ _ (by simp) h
        split at h
        · exact ihm _ _ _ (by simp) h
        split at h
        · exact ihm _ _ _ (by simp) h
        split at h
        · split at h
          · rename_i c2 cs2
            split at h
            · split at h
              · split at h
                · exact ihm _ _ _ (by simp <;> omega) h
                · exact ihm _ _ _ (by simp <;> omega) h
              · exact ihm _ _ _ (by simp) h
            · exact ihm _ _ _ (by simp) h
          · exact ihm _ _ _ (by simp) h
        split at h
        · split at h
          · split at h
            · exact ihd _ _ (by simp <;> omega) _ h
            · exact ihd _ _ (by simp) _ h
          · exact ihd _ _ (by simp) _ h
        split at h
        · exact ihd _ _ (by simp) _ h
        · exact ihm _ _ _ (by simp) h
    split at h
    · exact ihm _ _ _ (by simp) h
    split at h
    · split at h
      · simp at h; rw [← h.2]; simp
      · exact ihm _ _ _ (by simp) h
    split at h
    · split at h
      · split at h
        · exact ihm _ _ _ (by simp) h
        · exact ihm _ _ _ (by simp) h
      · simp at h
    · exact ihm _ _ _ (by simp) h
termination_by _ l => l.length
decreasing_by simp_all; omega

/-- The rest after a hex-string body is no longer than the input. -/
theorem hexBody_length_le : (l : List UInt8) → (ns : List Nat) → (rest : List UInt8) →
    hexBody l = .ok (ns, rest) → rest.length ≤ l.length
  | [], _, _, h => by simp [hexBody] at h
  | b :: bs, ns, rest, h => by
    unfold hexBody at h
    split at h
    · simp at h; rw [← h.2]; simp
    split at h
    · have := hexBody_length_le bs ns rest h; simp; omega
    split at h
    · cases hb : hexBody bs with
      | error e => simp [hb] at h; cases h
      | ok p =>
        obtain ⟨ns', r'⟩ := p
        simp [hb, Except.map] at h
        have := hexBody_length_le bs ns' r' hb
        rw [← h.2]; simp; omega
    · cases h

/-- `nextAt` consumes input: a token's rest is strictly shorter than the input. -/
theorem nextAt_consumes (off : Nat) (l : List UInt8) (t : Token) (rest : List UInt8)
    (h : nextAt off l = .ok (some (t, rest))) : rest.length < l.length := by
  cases l with
  | nil => simp [nextAt] at h
  | cons b bs =>
    have hr := regularRun_snd_length_le bs
    unfold nextAt at h
    simp only at h
    split at h
    · simp at h; rw [← h.2]; simp
    split at h
    · simp at h; rw [← h.2]; simp
    split at h
    · simp at h; rw [← h.2]; simp
    split at h
    · simp at h; rw [← h.2]; simp
    split at h
    · cases h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h.2]; simp; omega
        · cases h
      · cases h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h.2]; simp; omega
        · split at h
          · rename_i hh
            simp at h; rw [← h.2]
            have := hexBody_length_le _ _ _ hh
            simp at this ⊢; omega
          · cases h
      · cases h
    split at h
    · split at h
      · rename_i hh
        simp at h; rw [← h.2]
        have := litBody_length_lt _ _ _ _ hh
        simp; omega
      · cases h
    split at h
    · split at h
      · simp at h; rw [← h.2]; simp; omega
      · cases h
    split at h
    · split at h
      · simp at h; rw [← h.2]; simp; omega
      · cases h
    · simp at h; rw [← h.2]; simp; omega

/-- **(a)** `next` consumes input: if it returns a token, the rest is strictly shorter than
the input. This justifies the termination of `lexAll` and is used by task 1.6. -/
theorem next_consumes {l : List UInt8} {t : Token} {rest : List UInt8}
    (h : next l = .ok (some (t, rest))) : rest.length < l.length := by
  have h1 := nextAt_consumes _ _ _ _ h
  have h2 := skipWs_length_le l
  omega

/-- `nextAt` on empty input is end of input. -/
theorem nextAt_nil (off : Nat) : nextAt off [] = .ok none := rfl

/-- **(b)** `next` returns `ok none` exactly when only whitespace and comments remain
(`skipWs l = []`), in particular on whitespace/comment-only input. -/
theorem next_eq_none_of_skipWs_nil {l : List UInt8} (h : skipWs l = []) :
    next l = .ok none := by
  simp [next, h, nextAt]

/-- **(b)** `next` on a list of whitespace bytes returns `ok none`. -/
theorem next_white {l : List UInt8} (h : l.all isWhite = true) : next l = .ok none := by
  apply next_eq_none_of_skipWs_nil
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [skipWs, h.1, ih h.2]

/-- Skipping a comment body that contains no CR or LF passes over it entirely. -/
theorem skipComment_append {c : List UInt8}
    (hc : c.all (fun b => !(b == 10 || b == 13)) = true) (r : List UInt8) :
    skipComment (c ++ r) = skipComment r := by
  induction c with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hc
    have hb : (b == 10 || b == 13) = false := by simpa using hc.1
    simp [skipComment, hb, ih hc.2]

/-- A comment `%…` ended by CR or LF is skipped together with its end-of-line byte. -/
theorem skipWs_comment {c : List UInt8}
    (hc : c.all (fun b => !(b == 10 || b == 13)) = true) {e : UInt8}
    (he : (e == 10 || e == 13) = true) (r : List UInt8) :
    skipWs (37 :: (c ++ e :: r)) = skipWs r := by
  have h37 : isWhite 37 = false := by decide
  simp [skipWs, h37, skipComment_append hc, skipComment, he]

/-- **(b)** `next` on a comment that runs to the end of input returns `ok none`. -/
theorem next_comment {c : List UInt8}
    (hc : c.all (fun b => !(b == 10 || b == 13)) = true) : next (37 :: c) = .ok none := by
  apply next_eq_none_of_skipWs_nil
  have h37 : isWhite 37 = false := by decide
  have := skipComment_append hc []
  rw [List.append_nil] at this
  simp [skipWs, h37, this, skipComment]

/-! ## Lexing a whole input -/

/-- Lex the whole input: repeat `next` until end of input. Error offsets are relative to the
start of `l`. Terminates because `next` consumes input (`next_consumes`). -/
def lexAll (l : List UInt8) : Except LexError (List Token) :=
  match h : next l with
  | .error e => .error e
  | .ok none => .ok []
  | .ok (some (t, rest)) =>
    have : rest.length < l.length := next_consumes h
    match lexAll rest with
    | .error e => .error { e with offset := e.offset + (l.length - rest.length) }
    | .ok ts => .ok (t :: ts)
termination_by l.length


/-! ## Examples (evaluated with `#guard`) -/

/-- Test helper: the bytes of an ASCII string. -/
private def bs (s : String) : List UInt8 := s.toUTF8.toList

/-- Test helper: the first token and the rest as a string-free comparable value. -/
private def tok (s : String) : Option (Option (Token × List UInt8)) :=
  match next (bs s) with
  | .ok r => some r
  | .error _ => none

/-- Test helper: the error of `next`, if any. -/
private def err (s : String) : Option LexError :=
  match next (bs s) with
  | .ok _ => none
  | .error e => some e

/-- Test helper: all tokens of an input, or `none` on error. -/
private def all (s : String) : Option (List Token) :=
  match lexAll (bs s) with
  | .ok ts => some ts
  | .error _ => none

-- 1. whitespace, comments, end of input
#guard tok "" == some none
#guard tok " \t\r\n\x0c" == some none
#guard tok "% comment only" == some none
#guard tok "  % c1\r% c2\n  % c3" == some none
#guard tok "%c\n42 x" == some (some (.int 42, bs " x"))
#guard tok "\x00 true" == some (some (.keyword (bs "true"), []))
-- 2. delimiters
#guard all "[ ] { } << >>" == some [.arrayOpen, .arrayClose, .braceOpen, .braceClose, .dictOpen, .dictClose]
#guard all "<</A[1]>>" == some [.dictOpen, .name ⟨bs "A"⟩, .arrayOpen, .int 1, .arrayClose, .dictClose]
#guard err "  )" == some ⟨2, .unexpectedDelimiter⟩
#guard err "> >" == some ⟨0, .unexpectedDelimiter⟩
#guard err ">" == some ⟨0, .unexpectedDelimiter⟩
-- 3. numbers and keywords
#guard all "123 +17 -98 0 -0" == some [.int 123, .int 17, .int (-98), .int 0, .int 0]
#guard tok "-3.50" == some (some (.real ⟨-35, 1⟩, []))
#guard all "5. .5 -.002 +0.0 4.000" == some [.real ⟨5, 0⟩, .real ⟨5, 1⟩, .real ⟨-2, 3⟩, .real ⟨0, 0⟩, .real ⟨4, 0⟩]
#guard err " --5" == some ⟨1, .badNumber⟩
#guard err "+" == some ⟨0, .badNumber⟩
#guard err "." == some ⟨0, .badNumber⟩
#guard err "1.2.3" == some ⟨0, .badNumber⟩
#guard err "12abc" == some ⟨0, .badNumber⟩
#guard all "1 0 R obj T* '" == some [.int 1, .int 0, .keyword (bs "R"), .keyword (bs "obj"), .keyword (bs "T*"), .keyword (bs "'")]
#guard tok "true/x" == some (some (.keyword (bs "true"), bs "/x"))
-- 4. literal strings
#guard tok "(a(b)c)d" == some (some (.litString (bs "a(b)c"), bs "d"))
#guard tok "(\\n\\r\\t\\b\\f\\(\\)\\\\)" == some (some (.litString [10, 13, 9, 8, 12, 40, 41, 92], []))
#guard tok "(\\101\\60\\7\\0538\\400)" == some (some (.litString [65, 48, 7, 43, 56, 0], []))
#guard tok "(a\\\r\nb\\\rc\\\nd\\q)" == some (some (.litString (bs "abcdq"), []))
#guard tok "(a\r\nb\rc\nd)" == some (some (.litString (bs "a\nb\nc\nd"), []))
#guard tok "(\\))" == some (some (.litString (bs ")"), []))
#guard err " (abc" == some ⟨1, .unterminatedString⟩
#guard err "(a(b)" == some ⟨0, .unterminatedString⟩
#guard err "(abc\\" == some ⟨0, .unterminatedString⟩
-- 5. hex strings
#guard tok "<48 65 6C6c6F>x" == some (some (.hexString (bs "Hello"), bs "x"))
#guard tok "<901FA>" == some (some (.hexString [0x90, 0x1F, 0xA0], []))
#guard tok "<>" == some (some (.hexString [], []))
#guard err "  <12G4>" == some ⟨2, .badHexDigit⟩
#guard err "<12 3" == some ⟨0, .unterminatedHexString⟩
#guard err "<" == some ⟨0, .unterminatedHexString⟩
-- 6. names
#guard tok "/Type/Page" == some (some (.name ⟨bs "Type"⟩, bs "/Page"))
#guard tok "/A#20B#2fc" == some (some (.name ⟨bs "A B/c"⟩, []))
#guard tok "/ x" == some (some (.name ⟨[]⟩, bs " x"))
#guard tok "/a;b%c" == some (some (.name ⟨bs "a;b"⟩, bs "%c"))
#guard err " /A#2" == some ⟨1, .badNameEscape⟩
#guard err "/A#zz" == some ⟨0, .badNameEscape⟩
#guard err "/A# 1" == some ⟨0, .badNameEscape⟩
#guard err "/A#00" == some ⟨0, .nulInName⟩
-- 7. lexAll error offsets are relative to its input
#guard (match lexAll (bs "1 2 (x") with
  | .error e => e == ⟨4, .unterminatedString⟩
  | .ok _ => false)

end SafePdf.Spec.Lex
