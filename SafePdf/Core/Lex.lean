import SafePdf.Core.Token

/-!
# Efficient tokenizer (Plan.md §5.1 step 2, §6 Phase 1; ISO 32000-2 §7.2–7.3)

The efficient lexer over a `ByteArray` and a byte position. It implements the interface
contract of `SafePdf/Core/Token.lean`:

`Core.Lex.next : ByteArray → Nat → Except LexError (Option (Token × Nat))`

skips whitespace and comments, then returns the next token and the position just after it,
or `none` at end of input. Error offsets are absolute: the offset of the first byte of the
offending token. Task 1.6 proves it equal to the denotational spec `Spec.Lex.next`.

## Structure (for the equivalence proof, task 1.6)

Every scanner is a small function recursive on the position with the measure
`bytes.size - pos`; each step advances by at least one byte, and lookahead is at most one
byte beyond the current one (two for a name `#xx` escape and three for octal string
escapes, which are consumed, never re-read).

* `skipWs bytes pos inComment` — whitespace and comments; `inComment` is the only state.
* `readRun bytes pos acc` — maximal run of regular bytes; `acc` is the run read so far in
  **reverse**, reversed once at the end.
* `classifyRun` / `parseNumber` / `readDigits` — pure functions on the run (a `List UInt8`),
  structural recursion; numbers accumulate their mantissa over all digits.
* `litStr bytes pos depth acc` — literal string body after `(`; `escapeAt`/`octalAt` decode
  one escape. `acc` reversed; result `none` means unterminated.
* `hexStr bytes pos hi acc` — hex string body after `<`; `hi` is a pending high nibble.
* `nameRun bytes pos acc` — name body after `/`; errors are reported at the first offending
  `#` in left-to-right order.
* `next bytes pos = tokenAt bytes (skipWs bytes pos false)`; `tokenAt` checks bounds and
  calls `tokenOf bytes p bytes[p]`, a plain `if` chain on the first byte (no `let`s, so
  `split` works on it); `runToken` turns a regular run into a number/keyword token.
* `lexAll` repeats `next` (`termination_by bytes.size - pos`, progress from `next_pos`).

All payload accumulators are reversed lists (`b :: acc`), finished with `List.reverse`.

Proven: `next_pos` (a returned position is strictly after the input position and at most
the input size) and its helper bounds.
-/

namespace SafePdf.Core.Lex

open SafePdf

/-! ## Byte classes (ISO 32000-2 §7.2.3) -/

/-- PDF whitespace: NUL, TAB, LF, FF, CR, SP. -/
def isWhite (b : UInt8) : Bool :=
  b == 0 || b == 9 || b == 10 || b == 12 || b == 13 || b == 32

/-- PDF delimiters: `( ) < > [ ] { } / %`. -/
def isDelim (b : UInt8) : Bool :=
  b == 40 || b == 41 || b == 60 || b == 62 || b == 91 || b == 93 || b == 123 || b == 125 ||
    b == 47 || b == 37

/-- Regular bytes: neither whitespace nor delimiter. -/
def isRegular (b : UInt8) : Bool := !isWhite b && !isDelim b

/-- ASCII decimal digit `0`–`9`. -/
def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- ASCII octal digit `0`–`7`. -/
def isOctal (b : UInt8) : Bool := 48 ≤ b && b ≤ 55

/-- The value of a hex digit `0-9a-fA-F`, or `none`. -/
def hexVal? (b : UInt8) : Option UInt8 :=
  if 48 ≤ b && b ≤ 57 then some (b - 48)
  else if 97 ≤ b && b ≤ 102 then some (b - 87)
  else if 65 ≤ b && b ≤ 70 then some (b - 55)
  else none

/-! ## Whitespace and comments -/

/-- Skip whitespace and comments from `pos`; returns the position of the first byte that is
neither, or `bytes.size`. `inComment` is true inside a comment (which ends before CR/LF). -/
def skipWs (bytes : ByteArray) (pos : Nat) (inComment : Bool) : Nat :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if inComment then skipWs bytes (pos + 1) !(b == 10 || b == 13)
    else if isWhite b then skipWs bytes (pos + 1) false
    else if b == 37 then skipWs bytes (pos + 1) true
    else pos
  else pos
termination_by bytes.size - pos

/-! ## Regular runs: numbers and keywords -/

/-- Read the maximal run of regular bytes from `pos`, onto the reversed accumulator `acc`.
Returns the run (in order) and the position after it. -/
def readRun (bytes : ByteArray) (pos : Nat) (acc : List UInt8) : List UInt8 × Nat :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if isRegular b then readRun bytes (pos + 1) (b :: acc) else (acc.reverse, pos)
  else (acc.reverse, pos)
termination_by bytes.size - pos

/-- Read leading decimal digits: `readDigits l m n` returns `(m', n', rest)` where `m'` is `m`
extended by the digits (`m * 10 + d` each), `n'` is `n` plus their count, and `rest` the
remaining list. -/
def readDigits : List UInt8 → Nat → Nat → Nat × Nat × List UInt8
  | [], m, n => (m, n, [])
  | b :: rest, m, n =>
    if isDigit b then readDigits rest (m * 10 + (b - 48).toNat) (n + 1) else (m, n, b :: rest)

/-- Strip an optional leading sign: `(negative?, rest)`. -/
def splitSign (l : List UInt8) : Bool × List UInt8 :=
  match l with
  | b :: r => if b == 43 then (false, r) else if b == 45 then (true, r) else (false, l)
  | [] => (false, [])

/-- Apply a sign to a natural number. -/
def applySign (neg : Bool) (m : Nat) : Int := if neg then -(m : Int) else (m : Int)

/-- Parse a whole run as a number `[+-]?(digits)?(\.(digits)?)?` with at least one digit:
`Token.int` without a `.`, else `Token.real` of the normalized decimal over all digits. -/
def parseNumber (l : List UInt8) : Option Token :=
  let (neg, l1) := splitSign l
  let (m1, n1, l2) := readDigits l1 0 0
  match l2 with
  | [] => if n1 = 0 then none else some (.int (applySign neg m1))
  | b :: l3 =>
    if b == 46 then
      let (m2, n2, l4) := readDigits l3 m1 0
      if l4.isEmpty && n1 + n2 != 0 then
        some (.real (Decimal.normalize ⟨applySign neg m2, n2⟩))
      else none
    else none

/-- Classify a regular run: one starting with `+ - .` or a digit must be a number (else
`badNumber`); any other run is a keyword. -/
def classifyRun (run : List UInt8) : Except LexErrorKind Token :=
  match run with
  | b :: _ =>
    if b == 43 || b == 45 || b == 46 || isDigit b then
      match parseNumber run with
      | some t => .ok t
      | none => .error .badNumber
    else .ok (.keyword run)
  | [] => .ok (.keyword [])

/-! ## Literal strings (§7.3.4.2) -/

/-- Octal escape: `q` is the position of the first octal digit `c`; read up to two more
octal digits. Returns the byte (value mod 256) and the position after the digits. -/
def octalAt (bytes : ByteArray) (q : Nat) (c : UInt8) : UInt8 × Nat :=
  let v0 := (c - 48).toNat
  match bytes[q + 1]? with
  | some d1 =>
    if isOctal d1 then
      let v1 := v0 * 8 + (d1 - 48).toNat
      match bytes[q + 2]? with
      | some d2 =>
        if isOctal d2 then (UInt8.ofNat (v1 * 8 + (d2 - 48).toNat), q + 3)
        else (UInt8.ofNat v1, q + 2)
      | none => (UInt8.ofNat v1, q + 2)
    else (UInt8.ofNat v0, q + 1)
  | none => (UInt8.ofNat v0, q + 1)

/-- Decode the escape whose escaped byte `c` is at position `q` (just after the backslash).
Returns the decoded byte (`none` for a line continuation) and the position after it. -/
def escapeAt (bytes : ByteArray) (q : Nat) (c : UInt8) : Option UInt8 × Nat :=
  if c == 110 then (some 10, q + 1)        -- `n`
  else if c == 114 then (some 13, q + 1)   -- `r`
  else if c == 116 then (some 9, q + 1)    -- `t`
  else if c == 98 then (some 8, q + 1)     -- `b`
  else if c == 102 then (some 12, q + 1)   -- `f`
  else if isOctal c then
    let r := octalAt bytes q c
    (some r.1, r.2)
  else if c == 13 then (none, if bytes[q + 1]? == some 10 then q + 2 else q + 1)
  else if c == 10 then (none, q + 1)
  else (some c, q + 1)                     -- `(`, `)`, `\` and any other byte

/-- `octalAt` consumes at least the first digit. -/
theorem lt_octalAt (bytes : ByteArray) (q : Nat) (c : UInt8) : q < (octalAt bytes q c).2 := by
  unfold octalAt
  split
  · split
    · split
      · split <;> simp
      · simp
    · simp
  · simp

/-- `escapeAt` consumes at least the escaped byte. -/
theorem lt_escapeAt (bytes : ByteArray) (q : Nat) (c : UInt8) :
    q < (escapeAt bytes q c).2 := by
  unfold escapeAt
  repeat' split
  all_goals simp [lt_octalAt]

/-- Push an optional byte onto a reversed accumulator. -/
def pushOpt (o : Option UInt8) (acc : List UInt8) : List UInt8 :=
  match o with
  | some x => x :: acc
  | none => acc

/-- Literal string body from `pos` (after the opening `(`) at nesting `depth` (starting at
`1`), onto the reversed accumulator `acc`. Returns the decoded bytes and the position after
the closing `)`, or `none` if the input ends first. -/
def litStr (bytes : ByteArray) (pos depth : Nat) (acc : List UInt8) :
    Option (List UInt8 × Nat) :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if b == 92 then
      if h1 : pos + 1 < bytes.size then
        let r := escapeAt bytes (pos + 1) bytes[pos + 1]
        litStr bytes r.2 depth (pushOpt r.1 acc)
      else none
    else if b == 40 then litStr bytes (pos + 1) (depth + 1) (b :: acc)
    else if b == 41 then
      if depth ≤ 1 then some (acc.reverse, pos + 1)
      else litStr bytes (pos + 1) (depth - 1) (b :: acc)
    else if b == 13 then
      litStr bytes (if bytes[pos + 1]? == some 10 then pos + 2 else pos + 1) depth (10 :: acc)
    else litStr bytes (pos + 1) depth (b :: acc)
  else none
termination_by bytes.size - pos
decreasing_by
  all_goals first
    | omega
    | (have := lt_escapeAt bytes (pos + 1) bytes[pos + 1]; omega)
    | (split <;> omega)

/-! ## Hex strings (§7.3.4.3) -/

/-- Hex string body from `pos` (after `<`); `hi` is a pending high nibble, `acc` the reversed
decoded bytes. Returns the bytes and the position after `>`. -/
def hexStr (bytes : ByteArray) (pos : Nat) (hi : Option UInt8) (acc : List UInt8) :
    Except LexErrorKind (List UInt8 × Nat) :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if b == 62 then .ok ((pushOpt (hi.map (· * 16)) acc).reverse, pos + 1)
    else if isWhite b then hexStr bytes (pos + 1) hi acc
    else
      match hexVal? b with
      | some v =>
        match hi with
        | none => hexStr bytes (pos + 1) (some v) acc
        | some x => hexStr bytes (pos + 1) none ((x * 16 + v) :: acc)
      | none => .error .badHexDigit
  else .error .unterminatedHexString
termination_by bytes.size - pos

/-! ## Names (§7.3.5) -/

/-- Name body from `pos` (after `/`): the maximal run of regular bytes with `#xx` decoded,
onto the reversed accumulator `acc`. Returns the name bytes and the position after it. -/
def nameRun (bytes : ByteArray) (pos : Nat) (acc : List UInt8) :
    Except LexErrorKind (List UInt8 × Nat) :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if !isRegular b then .ok (acc.reverse, pos)
    else if b == 35 then
      match (bytes[pos + 1]?).bind hexVal?, (bytes[pos + 2]?).bind hexVal? with
      | some v1, some v2 =>
        let d := v1 * 16 + v2
        if d == 0 then .error .nulInName else nameRun bytes (pos + 3) (d :: acc)
      | _, _ => .error .badNameEscape
    else nameRun bytes (pos + 1) (b :: acc)
  else .ok (acc.reverse, pos)
termination_by bytes.size - pos

/-! ## The tokenizer -/

/-- Lift a sub-scanner result to a token result, reporting errors at absolute offset
`start`. -/
def liftAt (start : Nat) (mk : List UInt8 → Token) :
    Except LexErrorKind (List UInt8 × Nat) → Except LexError (Option (Token × Nat))
  | .ok (s, q) => .ok (some (mk s, q))
  | .error k => .error { offset := start, kind := k }

/-- A keyword or number token from a regular run and its end position; a malformed number
is reported at offset `p`. -/
def runToken (p : Nat) : List UInt8 × Nat → Except LexError (Option (Token × Nat))
  | (run, q) =>
    match classifyRun run with
    | .ok t => .ok (some (t, q))
    | .error k => .error { offset := p, kind := k }

/-- The token whose first byte `b` is at position `p` (`b = bytes[p]`). Whitespace and `%`
never occur here (they were skipped), so the final branch sees a regular byte. -/
def tokenOf (bytes : ByteArray) (p : Nat) (b : UInt8) : Except LexError (Option (Token × Nat)) :=
  if b == 91 then .ok (some (.arrayOpen, p + 1))
  else if b == 93 then .ok (some (.arrayClose, p + 1))
  else if b == 123 then .ok (some (.braceOpen, p + 1))
  else if b == 125 then .ok (some (.braceClose, p + 1))
  else if b == 60 then
    if bytes[p + 1]? == some 60 then .ok (some (.dictOpen, p + 2))
    else liftAt p .hexString (hexStr bytes (p + 1) none [])
  else if b == 62 then
    if bytes[p + 1]? == some 62 then .ok (some (.dictClose, p + 2))
    else .error { offset := p, kind := .unexpectedDelimiter }
  else if b == 40 then
    match litStr bytes (p + 1) 1 [] with
    | some (s, q) => .ok (some (.litString s, q))
    | none => .error { offset := p, kind := .unterminatedString }
  else if b == 41 then .error { offset := p, kind := .unexpectedDelimiter }
  else if b == 47 then liftAt p (fun s => .name ⟨s⟩) (nameRun bytes (p + 1) [])
  else runToken p (readRun bytes (p + 1) [b])

/-- The token starting exactly at `p` (no whitespace skipping): `none` if `p` is at or past
the end of input, else the token and the position just after it. Errors carry offset `p`. -/
def tokenAt (bytes : ByteArray) (p : Nat) : Except LexError (Option (Token × Nat)) :=
  if h : p < bytes.size then tokenOf bytes p bytes[p] else .ok none

/-- The next token at or after `pos`: skip whitespace and comments, then lex one token.
Returns `none` at end of input, else the token and the position just after it. Errors carry
the absolute offset of the token's first byte. -/
def next (bytes : ByteArray) (pos : Nat) : Except LexError (Option (Token × Nat)) :=
  tokenAt bytes (skipWs bytes pos false)

/-! ## Position bounds -/

/-- `skipWs` never moves backwards. -/
theorem le_skipWs (bytes : ByteArray) (pos : Nat) (c : Bool) : pos ≤ skipWs bytes pos c := by
  fun_induction skipWs bytes pos c <;> omega

/-- `readRun` never moves backwards and stays within the input. -/
theorem readRun_bounds (bytes : ByteArray) (pos : Nat) (acc : List UInt8) :
    pos ≤ (readRun bytes pos acc).2 ∧
      (pos ≤ bytes.size → (readRun bytes pos acc).2 ≤ bytes.size) := by
  fun_induction readRun bytes pos acc
  all_goals first | omega | (simp_all; omega) | simp_all

/-- A successful hex string ends after its start and within the input. -/
theorem hexStr_bounds (bytes : ByteArray) (pos : Nat) (hi : Option UInt8) (acc : List UInt8)
    (s : List UInt8) (q : Nat) (h : hexStr bytes pos hi acc = .ok (s, q)) :
    pos < q ∧ q ≤ bytes.size := by
  fun_induction hexStr bytes pos hi acc <;> simp_all <;> omega

/-- A byte lookup that yields something is in bounds. -/
theorem lt_size_of_bind_eq_some {bytes : ByteArray} {i : Nat} {f : UInt8 → Option UInt8}
    {v : UInt8} (h : (bytes[i]?).bind f = some v) : i < bytes.size := by
  apply Classical.byContradiction
  intro hc
  rw [getElem?_neg bytes i hc] at h
  simp at h

/-- A successful name ends at or after its start and within the input. -/
theorem nameRun_bounds (bytes : ByteArray) (pos : Nat) (acc : List UInt8)
    (s : List UInt8) (q : Nat) (h : nameRun bytes pos acc = .ok (s, q)) :
    pos ≤ q ∧ (pos ≤ bytes.size → q ≤ bytes.size) := by
  fun_induction nameRun bytes pos acc
  case case3 =>
    have h2 := lt_size_of_bind_eq_some ‹(bytes[_ + 2]?).bind hexVal? = some _›
    have := ‹nameRun _ _ _ = _ → _› h
    omega
  all_goals first | omega | (simp_all; omega) | (simp_all; done)

/-- A successful literal string ends after its start and within the input. -/
theorem litStr_bounds (bytes : ByteArray) (pos depth : Nat) (acc : List UInt8)
    (s : List UInt8) (q : Nat) (h : litStr bytes pos depth acc = some (s, q)) :
    pos < q ∧ q ≤ bytes.size := by
  fun_induction litStr bytes pos depth acc
  case case1 =>
    rename_i p _ _ _ _ _ _ r ih
    have h1 := ih h
    have h2 : p + 1 < r.2 := lt_escapeAt bytes (p + 1) _
    omega
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)
    | (have ih := ‹litStr _ _ _ _ = some (s, q) → _› h
       first | omega | (split at ih <;> omega))

/-- A byte lookup that yields something is in bounds. -/
theorem lt_size_of_getElem?_eq_some {bytes : ByteArray} {i : Nat} {v : UInt8}
    (h : bytes[i]? = some v) : i < bytes.size := by
  apply Classical.byContradiction
  intro hc
  rw [getElem?_neg bytes i hc] at h
  simp at h

/-- A successful `liftAt` comes from a successful sub-scanner with the same end position. -/
theorem liftAt_ok {start : Nat} {mk : List UInt8 → Token}
    {r : Except LexErrorKind (List UInt8 × Nat)} {t : Token} {q : Nat}
    (h : liftAt start mk r = .ok (some (t, q))) : ∃ s, r = .ok (s, q) := by
  match r, h with
  | .ok (s, q'), h =>
    simp only [liftAt, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨s, by rw [h.2]⟩

/-- A successful `runToken` ends where the run ends. -/
theorem runToken_ok {p : Nat} {r : List UInt8 × Nat} {t : Token} {q : Nat}
    (h : runToken p r = .ok (some (t, q))) : q = r.2 := by
  obtain ⟨run, q'⟩ := r
  simp only [runToken] at h
  split at h <;> simp_all

/-- **Progress.** A token returned by `next bytes pos` ends strictly after `pos` and within
the input. -/
theorem next_pos (bytes : ByteArray) (pos : Nat) (t : Token) (pos' : Nat)
    (h : next bytes pos = .ok (some (t, pos'))) : pos < pos' ∧ pos' ≤ bytes.size := by
  have hp := le_skipWs bytes pos false
  unfold next at h
  generalize skipWs bytes pos false = p at h hp
  unfold tokenAt at h
  by_cases hlt : p < bytes.size
  · rw [dite_eq_left hlt] at h
    generalize bytes[p] = b at h
    unfold tokenOf at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (obtain ⟨s, hs⟩ := liftAt_ok h
         first
           | (have := hexStr_bounds _ _ _ _ _ _ hs; omega)
           | (have := nameRun_bounds _ _ _ _ _ hs; omega))
      | (have hq := runToken_ok h
         have := readRun_bounds bytes (p + 1) [b]
         omega)
      | (simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨-, rfl⟩ := h
         first
           | omega
           | (have := litStr_bounds _ _ _ _ _ _ ‹litStr _ _ _ _ = _›; omega)
           | (have := lt_size_of_getElem?_eq_some
                (by simpa using ‹(bytes[p + 1]? == some _) = true›)
              omega))
  · rw [dite_eq_right hlt] at h
    simp at h

/-! ## Whole-input lexing -/

/-- Lex the whole input with `next` from position `0` to the end (no stream data handling:
for content streams without inline images, and for tests). -/
def lexAll (bytes : ByteArray) : Except LexError (List Token) := go 0 []
where
  /-- Lex from `pos` onto the reversed accumulator `acc`. -/
  go (pos : Nat) (acc : List Token) : Except LexError (List Token) :=
    match _hn : next bytes pos with
    | .error e => .error e
    | .ok none => .ok acc.reverse
    | .ok (some (t, pos')) => go pos' (t :: acc)
  termination_by bytes.size - pos
  decreasing_by have := next_pos bytes pos t pos' _hn; omega

/-! ## Tests -/

section Tests

/-- Test helper: all tokens of a string, or `none` on error. -/
private def toks (s : String) : Option (List Token) :=
  match lexAll s.toUTF8 with
  | .ok ts => some ts
  | .error _ => none

/-- Test helper: the error of lexing a whole string, or `none` on success. -/
private def err (s : String) : Option LexError :=
  match lexAll s.toUTF8 with
  | .ok _ => none
  | .error e => some e

/-- Test helper: `next` on a string at a position, errors dropped. -/
private def nextS (s : String) (pos : Nat) : Option (Option (Token × Nat)) :=
  match next s.toUTF8 pos with
  | .ok r => some r
  | .error _ => none

/-- Test helper: bytes of a string. -/
private def bs (s : String) : List UInt8 := s.toUTF8.toList

-- Rule 2: delimiters
#guard toks "[ ] { } << >>" =
  some [.arrayOpen, .arrayClose, .braceOpen, .braceClose, .dictOpen, .dictClose]
#guard toks "[<<>>]" = some [.arrayOpen, .dictOpen, .dictClose, .arrayClose]
-- Rule 1: whitespace (incl. NUL) and comments
#guard toks "% c\r\n 1 %x\n2%end" = some [.int 1, .int 2]
#guard toks "\x00\t\n\x0c\r " = some []
#guard toks "" = some []
-- Rule 3: integers and reals
#guard toks "123 -17 +5 0 -0" = some [.int 123, .int (-17), .int 5, .int 0, .int 0]
#guard toks "-3.50 5. .5 -.002 0.0 +1.500" =
  some [.real ⟨-35, 1⟩, .real ⟨5, 0⟩, .real ⟨5, 1⟩, .real ⟨-2, 3⟩, .real ⟨0, 0⟩,
    .real ⟨15, 1⟩]
#guard err "--5" = some ⟨0, .badNumber⟩
#guard err "1 1.2.3" = some ⟨2, .badNumber⟩
#guard err "  +" = some ⟨2, .badNumber⟩
#guard err "." = some ⟨0, .badNumber⟩
#guard err "12a" = some ⟨0, .badNumber⟩
-- Rule 3: keywords
#guard toks "true obj R a+b" =
  some [.keyword (bs "true"), .keyword (bs "obj"), .keyword (bs "R"), .keyword (bs "a+b")]
#guard toks "1 0 R/x" = some [.int 1, .int 0, .keyword (bs "R"), .name ⟨bs "x"⟩]
-- Rule 4: literal strings
#guard toks "(a(b)c)" = some [.litString (bs "a(b)c")]
#guard toks "(\\n\\r\\t\\b\\f\\(\\)\\\\)" = some [.litString [10, 13, 9, 8, 12, 40, 41, 92]]
#guard toks "(\\101\\0053\\7\\777)" = some [.litString [65, 5, 51, 7, 255]]
#guard toks "(a\\\r\nb\\\rc\\\nd\\q)" = some [.litString (bs "abcdq")]
#guard toks "(a\r\nb\rc\nd)" = some [.litString (bs "a\nb\nc\nd")]
#guard err "x (ab(c)" = some ⟨2, .unterminatedString⟩
#guard err "(a\\" = some ⟨0, .unterminatedString⟩
-- Rule 5: hex strings
#guard toks "<48 65\n6C6c6F>" = some [.hexString (bs "Hello")]
#guard toks "<7> <>" = some [.hexString [0x70], .hexString []]
#guard err "<4g>" = some ⟨0, .badHexDigit⟩
#guard err "  <41" = some ⟨2, .unterminatedHexString⟩
-- Rule 6: names
#guard toks "/Type /A#42c /" = some [.name ⟨bs "Type"⟩, .name ⟨bs "ABc"⟩, .name ⟨[]⟩]
#guard toks "/a/b//" = some [.name ⟨bs "a"⟩, .name ⟨bs "b"⟩, .name ⟨[]⟩, .name ⟨[]⟩]
#guard err "/ok /a#4 " = some ⟨4, .badNameEscape⟩
#guard err "/a#zz" = some ⟨0, .badNameEscape⟩
#guard err "1 /a#00" = some ⟨2, .nulInName⟩
-- Rule 2/7: unexpected delimiters
#guard err ")" = some ⟨0, .unexpectedDelimiter⟩
#guard err "1 > 2" = some ⟨2, .unexpectedDelimiter⟩
-- Rule 7: positions
#guard nextS "  [1" 0 = some (some (.arrayOpen, 3))
#guard nextS "  [1" 3 = some (some (.int 1, 4))
#guard nextS "  [1" 4 = some none
#guard nextS "  [1" 9 = some none
#guard nextS "x <<" 1 = some (some (.dictOpen, 4))
#guard nextS "(a) " 0 = some (some (.litString (bs "a"), 3))
#guard nextS "<41>x" 0 = some (some (.hexString [0x41], 4))
#guard nextS "/ab cd" 0 = some (some (.name ⟨bs "ab"⟩, 3))

end Tests

end SafePdf.Core.Lex
