import SafePdf.Core.ObjParse

/-!
# Content-stream tokenizer (Plan.md §6 Phase 5, §3 rule 2, §4 S3)

Splits a (decoded) content stream into operators with their operands (ISO 32000-2 §7.8.2,
§8.2, Annex A), for the interpreter `Core.Content.Interp` (task 5.2a). Tokens come from the
strict lexer `Core.Lex.next`; array and dictionary operands (`TJ`, `d`, `BDC`, `DP`, inline
image parameters) are parsed with the object parser `Core.ObjParse.parseObjTok`. An operator
is any `Token.keyword` other than `true`, `false`, `null`.

## Design decisions

* **Never fails** (M5). Recovery rules, each counted as one warning:
  - a lexer error skips to the next whitespace after the offending token and drops the
    pending operands; an *unterminated* literal or hex string ends the stream (the lexer has
    already scanned to the end of input, so resuming inside it would make the scan quadratic);
  - a malformed array/dictionary operand drops the pending operands and resumes at the
    offending token (or just after the opening bracket when the error carries no offset), so
    an unterminated `[ … ` before `TJ` loses only that operator;
  - a stray `]`, `>>`, `{`, `}` is dropped;
  - operands left at the end of the stream are dropped.
* **Inline images** (§8.9.7): after `BI` the parameter dictionary is read token by token up
  to `ID`; the data starts after the single whitespace byte following `ID`. Its end is found
  (1) from `/L` or `/Length` when that many bytes are followed (after whitespace) by `EI`, else
  (2) by a **byte scan** (never lexing binary data) for `EI` preceded by whitespace and followed
  by whitespace, a delimiter or the end of input. The whitespace byte before `EI` is not data.
  One `Op` named `BI` carries the dictionary (unexpanded abbreviations; 5.2b expands and
  decodes) as its single operand and the raw data in `Op.data`. A malformed dictionary skips to
  the `EI` (warning); a missing `EI` takes the data to the end of input (warning).
* **Termination and bounds.** `run` recurses on `bytes.size - pos`; every step moves to
  `jumpPos size pos target = max (pos + 1) (min target size)`, so progress is by construction,
  never assumed from the step's own arithmetic. Each step emits at most one `Op`, hence
  `tokenize_ops_le : ops.size ≤ bytes.size`. The count is also capped at
  `Limits.maxOpsPerPage` (`tokenize_ops_le_max`); reaching the cap stops with
  `truncated = true` and a warning.
* **Known worst case.** A malformed array operand is re-parsed from its next bracket, so input
  like `[1 [1 [1 …` costs `O(maxObjectDepth · n)` token reads; the object parser's depth fuel
  bounds it.
-/

namespace SafePdf.Core.Content

open SafePdf

/-- One content-stream operator with its operands (in source order). For `BI` the single
operand is the inline image dictionary and `data` holds the raw image bytes. -/
structure Op where
  /-- Operands, in source order. -/
  operands : List PdfObject
  /-- The operator keyword's bytes (`re`, `Tj`, `BI`, …). -/
  op : List UInt8
  /-- Byte offset of the operator keyword in the content stream. -/
  offset : Nat
  /-- Inline image data (`BI` only); empty otherwise. -/
  data : ByteArray := ByteArray.empty

instance : Inhabited Op := ⟨⟨[], [], 0, ByteArray.empty⟩⟩

/-- Result of tokenizing a content stream. -/
structure TokResult where
  /-- The operators, in source order. -/
  ops : Array Op
  /-- Number of recovered malformations (see the module doc). -/
  warnings : Nat
  /-- Whether tokenizing stopped at `Limits.maxOpsPerPage`. -/
  truncated : Bool

instance : Inhabited TokResult := ⟨⟨#[], 0, false⟩⟩

namespace Ops

/-- Bytes of the operator `BI`. -/
def kwBI : List UInt8 := [66, 73]

/-- Bytes of the keyword `ID`. -/
def kwID : List UInt8 := [73, 68]

/-- The name `/L` (inline-image abbreviation of `/Length`). -/
def nameL : Name := ⟨[76]⟩

/-- The next position of a step: `target` clamped into `(pos, size]`. -/
def jumpPos (size pos target : Nat) : Nat := max (pos + 1) (min target size)

/-- `jumpPos` always makes progress. -/
theorem lt_jumpPos (size pos target : Nat) : pos < jumpPos size pos target := by
  unfold jumpPos; omega

/-- `jumpPos` stays within the input when the step started inside it. -/
theorem jumpPos_le {size pos : Nat} (target : Nat) (h : pos < size) :
    jumpPos size pos target ≤ size := by
  unfold jumpPos; omega

/-- `jumpPos` is the target itself when the target is a valid next position. -/
theorem jumpPos_eq {size pos target : Nat} (h1 : pos < target) (h2 : target ≤ size) :
    jumpPos size pos target = target := by
  unfold jumpPos; omega

/-- The first whitespace position at or after `p` (or `bytes.size`). -/
def skipToWs (bytes : ByteArray) (p : Nat) : Nat :=
  if h : p < bytes.size then
    if Lex.isWhite bytes[p] then p else skipToWs bytes (p + 1)
  else p
termination_by bytes.size - p

/-- The first non-whitespace position at or after `p` (no comment handling: used between
inline image data and `EI` only). -/
def skipWhite (bytes : ByteArray) (p : Nat) : Nat :=
  if h : p < bytes.size then
    if Lex.isWhite bytes[p] then skipWhite bytes (p + 1) else p
  else p
termination_by bytes.size - p

/-- Whether `EI` starts at `p` and is followed by whitespace, a delimiter or the end. -/
def isEIAt (bytes : ByteArray) (p : Nat) : Bool :=
  bytes[p]? == some 69 && bytes[p + 1]? == some 73 &&
    (match bytes[p + 2]? with
     | none => true
     | some b => Lex.isWhite b || Lex.isDelim b)

/-- Byte scan from `i` for an `EI` that ends inline image data: preceded by whitespace and
satisfying `isEIAt`. Returns the position of the `E`. -/
def findEI (bytes : ByteArray) (i : Nat) : Option Nat :=
  if h : i + 1 < bytes.size then
    if 1 ≤ i && (match bytes[i - 1]? with | some b => Lex.isWhite b | none => false) &&
        isEIAt bytes i then some i
    else findEI bytes (i + 1)
  else none
termination_by bytes.size - i

/-- A nonnegative integer value of `/L` or `/Length` in an inline image dictionary. -/
def inlineLength (d : Dict) : Option Nat :=
  let v := match Dict.get? d nameL with
    | some v => some v
    | none => Dict.get? d ObjParse.nameLength
  match v with
  | some (.int n) => if 0 ≤ n then some n.toNat else none
  | _ => none

/-- End of inline image data starting at `start`: `(dataEnd, positionAfterEI)`. -/
def imageEnd (bytes : ByteArray) (d : Dict) (start : Nat) : Option (Nat × Nat) :=
  let viaLen : Option (Nat × Nat) :=
    match inlineLength d with
    | some l =>
      if start + l ≤ bytes.size then
        let p := skipWhite bytes (start + l)
        if isEIAt bytes p then some (start + l, p + 2) else none
      else none
    | none => none
  match viaLen with
  | some r => some r
  | none =>
    match findEI bytes start with
    | some i => some (max start (i - 1), i + 2)
    | none => none

/-- The inline image dictionary from `pos` up to and including the keyword `ID`, onto the
reversed accumulator `acc`; `none` if malformed (non-name key, duplicate key, bad value,
lexer error, end of input). -/
def inlineDict (fuel : Nat) (bytes : ByteArray) (pos : Nat) (acc : Dict) :
    Option (Dict × Nat) :=
  match _h : Lex.next bytes pos with
  | .ok (some (.keyword kw, q)) => if kw = kwID then some (acc.reverse, q) else none
  | .ok (some (.name k, q)) =>
    if ObjParse.hasKey acc k then none
    else
      match Lex.next bytes q with
      | .ok (some (t2, q2)) =>
        match ObjParse.parseObjTok fuel bytes q t2 q2 with
        | .ok (v, r) => if _hr : pos < r then inlineDict fuel bytes r ((k, v) :: acc) else none
        | .error _ => none
      | _ => none
  | _ => none
termination_by bytes.size - pos
decreasing_by have := Lex.next_pos bytes pos _ _ _h; omega

/-- What one tokenizer step produced: the target of the next position (clamped by
`jumpPos`), the new reversed operand stack, an emitted operator, and warnings. -/
structure StepOut where
  /-- Where to continue (before clamping). -/
  next : Nat
  /-- Pending operands, newest first. -/
  stack : List PdfObject
  /-- The operator completed by this step, if any. -/
  emit : Option Op
  /-- Warnings raised by this step. -/
  warn : Nat

/-- Inline image after the `BI` keyword that started at `pos` and ended at `q`. -/
def inlineImage (limits : Limits) (bytes : ByteArray) (pos q : Nat) (stk : List PdfObject) :
    StepOut :=
  let off := ObjParse.tokStart bytes pos
  let w0 := if stk.isEmpty then 0 else 1
  match inlineDict limits.maxObjectDepth bytes q [] with
  | some (d, r) =>
    let start := match bytes[r]? with
      | some b => if Lex.isWhite b then r + 1 else r
      | none => r
    match imageEnd bytes d start with
    | some (dataEnd, after) =>
      ⟨after, [], some ⟨[.dict d], kwBI, off, bytes.extract start dataEnd⟩, w0⟩
    | none =>
      ⟨bytes.size, [], some ⟨[.dict d], kwBI, off, bytes.extract start bytes.size⟩, w0 + 1⟩
  | none =>
    match findEI bytes q with
    | some i => ⟨i + 2, [], none, w0 + 1⟩
    | none => ⟨bytes.size, [], none, w0 + 1⟩

/-- Where to resume after a malformed array/dictionary operand whose opening token ended at
`q`: the offending token if the error carries an offset beyond `q`, else `q`. -/
def resumeAfter (q : Nat) (e : Error) : Nat :=
  match e with
  | .malformed off _ => max q off
  | _ => q

/-- One tokenizer step at `pos` with pending operands `stk` (newest first); `none` at the end
of input. -/
def step (limits : Limits) (bytes : ByteArray) (pos : Nat) (stk : List PdfObject) :
    Option StepOut :=
  match Lex.next bytes pos with
  | .error e =>
    if e.kind = .unterminatedString || e.kind = .unterminatedHexString then
      some ⟨bytes.size, [], none, 1⟩
    else some ⟨skipToWs bytes (max (pos + 1) (e.offset + 1)), [], none, 1⟩
  | .ok none => none
  | .ok (some (t, q)) =>
    match t with
    | .keyword kw =>
      match ObjParse.keywordObj kw with
      | some o => some ⟨q, o :: stk, none, 0⟩
      | none =>
        if kw = kwBI then some (inlineImage limits bytes pos q stk)
        else some ⟨q, [], some ⟨stk.reverse, kw, ObjParse.tokStart bytes pos, ByteArray.empty⟩, 0⟩
    | .int n => some ⟨q, .int n :: stk, none, 0⟩
    | .real d => some ⟨q, .real d :: stk, none, 0⟩
    | .litString s => some ⟨q, .string s :: stk, none, 0⟩
    | .hexString s => some ⟨q, .string s :: stk, none, 0⟩
    | .name n => some ⟨q, .name n :: stk, none, 0⟩
    | .arrayOpen | .dictOpen =>
      match ObjParse.parseObjTok limits.maxObjectDepth bytes pos t q with
      | .ok (o, r) => some ⟨r, o :: stk, none, 0⟩
      | .error e => some ⟨resumeAfter q e, [], none, 1⟩
    | .arrayClose | .dictClose | .braceOpen | .braceClose => some ⟨q, stk, none, 1⟩

/-- Append an optional operator. -/
def pushOpt (ops : Array Op) : Option Op → Array Op
  | some o => ops.push o
  | none => ops

/-- Size after `pushOpt`. -/
theorem size_pushOpt (ops : Array Op) (o : Option Op) :
    (pushOpt ops o).size = ops.size + (if o.isSome then 1 else 0) := by
  cases o <;> simp [pushOpt]

/-- The tokenizer loop from `pos` with pending operands `stk`, output `ops` and warning count
`warn`. -/
def run (limits : Limits) (bytes : ByteArray) (pos : Nat) (stk : List PdfObject)
    (ops : Array Op) (warn : Nat) : TokResult :=
  if hp : pos < bytes.size then
    match step limits bytes pos stk with
    | none => ⟨ops, warn + (if stk.isEmpty then 0 else 1), false⟩
    | some s =>
      if s.emit.isSome && limits.maxOpsPerPage ≤ ops.size then ⟨ops, warn + 1, true⟩
      else
        have := lt_jumpPos bytes.size pos s.next
        have := jumpPos_le s.next hp
        run limits bytes (jumpPos bytes.size pos s.next) s.stack (pushOpt ops s.emit)
          (warn + s.warn)
  else ⟨ops, warn + (if stk.isEmpty then 0 else 1), false⟩
termination_by bytes.size - pos

/-- **Entry point.** Tokenize a whole content stream. Total; never fails. -/
def tokenize (limits : Limits) (bytes : ByteArray) : TokResult := run limits bytes 0 [] #[] 0

/-- Each step emits at most one operator per byte consumed. -/
theorem run_ops_le (limits : Limits) (bytes : ByteArray) (pos : Nat) (stk : List PdfObject)
    (ops : Array Op) (warn : Nat) :
    (run limits bytes pos stk ops warn).ops.size ≤ ops.size + (bytes.size - pos) := by
  fun_induction run limits bytes pos stk ops warn with
  | case1 => simp
  | case2 => simp
  | case3 pos stk ops warn hp s _ _ ih =>
    have h1 := lt_jumpPos bytes.size pos s.next
    have h2 := jumpPos_le s.next hp
    have h3 := size_pushOpt ops s.emit
    split at h3 <;> omega
  | case4 => simp

/-- The loop never pushes past `Limits.maxOpsPerPage`. -/
theorem run_ops_le_max (limits : Limits) (bytes : ByteArray) (pos : Nat)
    (stk : List PdfObject) (ops : Array Op) (warn : Nat) (h : ops.size ≤ limits.maxOpsPerPage) :
    (run limits bytes pos stk ops warn).ops.size ≤ limits.maxOpsPerPage := by
  fun_induction run limits bytes pos stk ops warn with
  | case1 => exact h
  | case2 => exact h
  | case3 pos stk ops warn hp s _ hc _ _ ih =>
    apply ih
    rw [size_pushOpt]
    cases he : s.emit.isSome
    · simp; exact h
    · simp only [he, Bool.true_and, decide_eq_true_eq, Nat.not_le] at hc
      simp; omega
  | case4 => exact h

/-- **Bound.** A content stream of `n` bytes yields at most `n` operators. -/
theorem tokenize_ops_le (limits : Limits) (bytes : ByteArray) :
    (tokenize limits bytes).ops.size ≤ bytes.size := by
  have := run_ops_le limits bytes 0 [] #[] 0
  simp only [List.size_toArray, List.length_nil, Nat.sub_zero, Nat.zero_add] at this
  exact this

/-- **Bound.** At most `Limits.maxOpsPerPage` operators. -/
theorem tokenize_ops_le_max (limits : Limits) (bytes : ByteArray) :
    (tokenize limits bytes).ops.size ≤ limits.maxOpsPerPage :=
  run_ops_le_max limits bytes 0 [] #[] 0 (Nat.zero_le _)

end Ops

/-! ## Samples -/

section Tests

private def opStr (o : Op) : String := String.ofList (o.op.map (fun b => Char.ofNat b.toNat))

private def tk (s : String) : TokResult := Ops.tokenize {} s.toUTF8

private def names (s : String) : List String := (tk s).ops.toList.map opStr

private def nOperands (s : String) : List Nat := (tk s).ops.toList.map (·.operands.length)

#guard names "0 0 10 20 re f" == ["re", "f"]
#guard nOperands "0 0 10 20 re f" == [4, 0]
#guard names "[(A) -250 (B)] TJ /F1 12 Tf true false null x" == ["TJ", "Tf", "x"]
#guard nOperands "[(A) -250 (B)] TJ /F1 12 Tf true false null x" == [1, 2, 3]
#guard (tk "q 1 0 0 1 0 0 cm Q").warnings == 0
-- inline image: 4 binary bytes, including a fake ` EI` inside data is avoided by `/L`
#guard names "BI /W 2 /H 2 /CS /G /BPC 8 ID \x01\x02\x03\x04 EI Q" == ["BI", "Q"]
#guard ((tk "BI /W 2 /H 2 /CS /G /BPC 8 ID \x01\x02\x03\x04 EI Q").ops[0]?.map
    (·.data.toList)) == some [1, 2, 3, 4]
#guard ((tk "BI /W 2 /H 2 /CS /G /BPC 8 ID \x01\x02\x03\x04 EI Q").ops[0]?.map
    (·.operands.length)) == some 1
#guard ((tk "BI /L 7 ID ab EI c\nEI Q").ops[0]?.map (·.data.size)) == some 7
#guard names "BI /L 7 ID ab EI c\nEI Q" == ["BI", "Q"]
#guard (tk "BI /W 1 ID ab").warnings == 1           -- no EI: data to end
#guard names "BI 5 ID xx EI Q" == ["Q"]              -- malformed dict: skipped
-- lexer garbage mid-stream recovers
#guard names "1 0 0 RG ) 5 w /a#zz x 2 w" == ["RG", "w", "x", "w"]
#guard nOperands "1 0 0 RG ) 5 w /a#zz x 2 w" == [3, 1, 0, 1]
#guard (tk "1 0 0 RG ) 5 w /a#zz x 2 w").warnings == 2
#guard names "1 2 (unterminated" == []
-- unterminated array before an operator: resume at the operator
#guard names "[(A) 1 TJ 0 g" == ["TJ", "g"]
#guard names "] 1 w" == ["w"]
#guard (tk "1 2").warnings == 1
#guard (Ops.tokenize { maxOpsPerPage := 2 } "q q q".toUTF8).truncated
#guard (Ops.tokenize { maxOpsPerPage := 2 } "q q q".toUTF8).ops.size == 2

end Tests

end SafePdf.Core.Content
