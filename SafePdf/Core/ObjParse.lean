import SafePdf.Core.Lex
import SafePdf.Core.Error
import SafePdf.Core.Limits

/-!
# Object parser (Plan.md §5.1, §6 Phase 1; ISO 32000-2 §7.3)

The efficient object parser of the strict path. It drives the tokenizer
`Core.Lex.next : ByteArray → Nat → Except LexError (Option (Token × Nat))` one token at a time
and builds `PdfObject`s (§7.3.2–7.3.10) and indirect objects / streams (§7.3.8, §7.3.10). Its
grammar (rules G1–G6 below) is the one the object grammar spec `SafePdf/Spec/Object.lean`
(task 1.4) defines; task 1.8 proves the two agree.

## Grammar (fuel `F` bounds nesting)

* G1. `int n`, `int g`, `keyword R` is a reference (`n ≥ 1`, `0 ≤ g ≤ 65535`, else an error);
  otherwise `int n` alone is an integer and the following tokens are left unconsumed.
* G2. `real`, `litString`/`hexString`, `name` are scalars.
* G3. Keywords `true`, `false`, `null`; any other keyword, and `{ } ] >>` where an object is
  expected, are errors.
* G4. `[` needs fuel `f + 1`; members are parsed with fuel `f` up to `]`.
* G5. `<<` needs fuel `f + 1`; `(name, object)` pairs (values with fuel `f`) up to `>>`, in
  source order; a non-name key or a duplicate key is an error.
* G6. End of input where an object is expected is an error. Lexer errors propagate.

## Structure (for the equivalence proof, task 1.8)

* `parseObj fuel bytes pos` lexes one token and hands it to `parseObjTok`.
* `parseObjTok fuel bytes pos t q` parses an object whose first token `t` was lexed from `pos`
  and ends at `q`. Mutually recursive with the loops `parseArray` and `parseDict`, which keep
  their members on a reversed accumulator (tail calls, so long arrays use no stack).
* Termination: lexicographic `(fuel, bytes.size - pos)`. Members of a container use fuel
  `f` from `f + 1`; within one container every step lexes a token, so `pos` grows
  (`Lex.next_pos`). The loops resume at the position returned by `parseObjTok`; since its
  progress is only proven afterwards (`parseObjTok_pos`), the loops guard the recursive call
  with `pos < r`. That branch is unreachable (`parseObjTok_pos`), but it keeps the definition
  free of nested-recursion proofs.
* Reference lookahead (G1, `parseIntTail`) lexes at most two more tokens and does not keep
  them: when they do not form `g R`, the integer is returned with the position just after it,
  and the caller lexes those tokens again. A lexer error inside the lookahead is an error
  (rule "a lexer error anywhere is an error").
* Indirect objects: `parseIndirect` = `parseHeader` (`n g obj`, range checks) then
  `parseIndirectBody` = `parseIndirectBodyWith streamLength`. The body is parametric in a
  `LengthResolver` (dictionary, error offset ↦ data length) so `Core.Xref.Length` and
  `Repair` reuse it with an indirect-`/Length` resolver; the framing lemmas
  (`parseStreamBodyWith_ok`, `parseIndirectBodyWith_ok`) hold for every resolver.
* Recursion depth is bounded by the fuel (each nesting level is one `parseObjTok` frame plus
  one loop frame), so a 100 000-deep `[[[…` fails cleanly with `limitExceeded .objectDepth`.

Everything is pure and total.
-/

namespace SafePdf.Core.ObjParse

open SafePdf

/-! ## Keywords and helpers -/

/-- Bytes of the keyword `true`. -/
def kwTrue : List UInt8 := [116, 114, 117, 101]
/-- Bytes of the keyword `false`. -/
def kwFalse : List UInt8 := [102, 97, 108, 115, 101]
/-- Bytes of the keyword `null`. -/
def kwNull : List UInt8 := [110, 117, 108, 108]
/-- Bytes of the keyword `R`. -/
def kwR : List UInt8 := [82]
/-- Bytes of the keyword `obj`. -/
def kwObj : List UInt8 := [111, 98, 106]
/-- Bytes of the keyword `endobj`. -/
def kwEndobj : List UInt8 := [101, 110, 100, 111, 98, 106]
/-- Bytes of the keyword `stream`. -/
def kwStream : List UInt8 := [115, 116, 114, 101, 97, 109]
/-- Bytes of the keyword `endstream`. -/
def kwEndstream : List UInt8 := [101, 110, 100, 115, 116, 114, 101, 97, 109]
/-- The name `/Length`. -/
def nameLength : Name := ⟨[76, 101, 110, 103, 116, 104]⟩

/-- The object a keyword denotes (G3): `true`, `false`, `null`; `none` for any other. -/
def keywordObj (kw : List UInt8) : Option PdfObject :=
  if kw = kwTrue then some (.bool true)
  else if kw = kwFalse then some (.bool false)
  else if kw = kwNull then some .null
  else none

/-- Whether `n g` is an admissible object/generation pair: `n ≥ 1`, `0 ≤ g ≤ 65535`. -/
def refOk (n g : Int) : Bool := decide (1 ≤ n) && decide (0 ≤ g) && decide (g ≤ 65535)

/-- Offset of the token that `Lex.next bytes pos` would return (after whitespace). -/
def tokStart (bytes : ByteArray) (pos : Nat) : Nat := Lex.skipWs bytes pos false

/-- A lexer error as a core error, keeping its offset. -/
def lexErr (e : LexError) : Error := .malformed e.offset s!"lexer: {reprStr e.kind}"

/-- A malformed-input error at the token `Lex.next bytes pos` starts at. -/
def errAt (bytes : ByteArray) (pos : Nat) (msg : String) : Error :=
  .malformed (tokStart bytes pos) msg

/-- Whether a key occurs in a (reversed) accumulator of dictionary entries. -/
def hasKey (acc : List (Name × PdfObject)) (k : Name) : Bool := acc.any (fun e => e.1 == k)

/-! ## References (G1) -/

/-- After `int n` (lexed from `pos`, ending at `q`): a reference `n g R` if the next two
tokens are `int g` and `R`, else the integer `n` ending at `q`. -/
def parseIntTail (bytes : ByteArray) (pos : Nat) (n : Int) (q : Nat) :
    Except Error (PdfObject × Nat) :=
  match Lex.next bytes q with
  | .error e => .error (lexErr e)
  | .ok (some (.int g, q2)) =>
    match Lex.next bytes q2 with
    | .error e => .error (lexErr e)
    | .ok (some (.keyword kw, q3)) =>
      if kw = kwR then
        if refOk n g then .ok (.ref n.toNat g.toNat, q3)
        else .error (errAt bytes pos "bad reference")
      else .ok (.int n, q)
    | .ok _ => .ok (.int n, q)
  | .ok _ => .ok (.int n, q)

/-! ## Objects, arrays, dictionaries (G1–G6) -/

mutual

/-- The object whose first token `t` was lexed from `pos` and ends at `q`, with nesting fuel
`fuel`. Returns the object and the position after its last token. -/
def parseObjTok (fuel : Nat) (bytes : ByteArray) (pos : Nat) (t : Token) (q : Nat) :
    Except Error (PdfObject × Nat) :=
  match t with
  | .int n => parseIntTail bytes pos n q
  | .real d => .ok (.real d, q)
  | .litString s => .ok (.string s, q)
  | .hexString s => .ok (.string s, q)
  | .name n => .ok (.name n, q)
  | .keyword kw =>
    match keywordObj kw with
    | some o => .ok (o, q)
    | none => .error (errAt bytes pos "unexpected keyword")
  | .arrayOpen =>
    match fuel with
    | 0 => .error (.limitExceeded .objectDepth)
    | f + 1 =>
      match parseArray f bytes q [] with
      | .ok (xs, r) => .ok (.array xs, r)
      | .error e => .error e
  | .dictOpen =>
    match fuel with
    | 0 => .error (.limitExceeded .objectDepth)
    | f + 1 =>
      match parseDict f bytes q [] with
      | .ok (d, r) => .ok (.dict d, r)
      | .error e => .error e
  | .arrayClose => .error (errAt bytes pos "unexpected ]")
  | .dictClose => .error (errAt bytes pos "unexpected >>")
  | .braceOpen => .error (errAt bytes pos "unexpected {")
  | .braceClose => .error (errAt bytes pos "unexpected }")
termination_by (fuel, bytes.size - q)

/-- Array members from `pos` (each with fuel `fuel`) up to and including `]`, onto the
reversed accumulator `acc`. Returns the members in source order and the position after `]`. -/
def parseArray (fuel : Nat) (bytes : ByteArray) (pos : Nat) (acc : List PdfObject) :
    Except Error (List PdfObject × Nat) :=
  match _h : Lex.next bytes pos with
  | .error e => .error (lexErr e)
  | .ok none => .error (.malformed pos "unterminated array")
  | .ok (some (t, q)) =>
    if t = .arrayClose then .ok (acc.reverse, q)
    else
      match parseObjTok fuel bytes pos t q with
      | .error e => .error e
      | .ok (o, r) =>
        if _hr : pos < r then parseArray fuel bytes r (o :: acc)
        else .error (.malformed pos "internal: no progress")
termination_by (fuel, bytes.size - pos)
decreasing_by
  all_goals
    have := Lex.next_pos bytes pos _ _ _h
    apply Prod.Lex.right
    omega

/-- Dictionary entries from `pos` (values with fuel `fuel`) up to and including `>>`, onto
the reversed accumulator `acc`. Returns the entries in source order and the position after
`>>`. A key that is not a name, or that is already in `acc`, is an error. -/
def parseDict (fuel : Nat) (bytes : ByteArray) (pos : Nat) (acc : List (Name × PdfObject)) :
    Except Error (List (Name × PdfObject) × Nat) :=
  match _h : Lex.next bytes pos with
  | .error e => .error (lexErr e)
  | .ok none => .error (.malformed pos "unterminated dictionary")
  | .ok (some (t, q)) =>
    match t with
    | .dictClose => .ok (acc.reverse, q)
    | .name k =>
      if hasKey acc k then .error (errAt bytes pos "duplicate dictionary key")
      else
        match _h2 : Lex.next bytes q with
        | .error e => .error (lexErr e)
        | .ok none => .error (.malformed q "unterminated dictionary")
        | .ok (some (t2, q2)) =>
          match parseObjTok fuel bytes q t2 q2 with
          | .error e => .error e
          | .ok (v, r) =>
            if _hr : pos < r then parseDict fuel bytes r ((k, v) :: acc)
            else .error (.malformed pos "internal: no progress")
    | _ => .error (errAt bytes pos "dictionary key is not a name")
termination_by (fuel, bytes.size - pos)
decreasing_by
  all_goals
    have := Lex.next_pos bytes pos _ _ _h
    first
      | (have := Lex.next_pos bytes q _ _ _h2
         apply Prod.Lex.right
         omega)
      | (apply Prod.Lex.right
         omega)

end

/-- The object starting at the next token at or after `pos`, with nesting fuel `fuel`.
Returns the object and the position after its last token. -/
def parseObj (fuel : Nat) (bytes : ByteArray) (pos : Nat) : Except Error (PdfObject × Nat) :=
  match Lex.next bytes pos with
  | .error e => .error (lexErr e)
  | .ok none => .error (.malformed pos "unexpected end of input")
  | .ok (some (t, q)) => parseObjTok fuel bytes pos t q

/-- **Entry point.** The object starting at the next token at or after `pos`, nesting at most
`limits.maxObjectDepth`. Returns the object and the position after its last token. -/
def parseObject (limits : Limits) (bytes : ByteArray) (pos : Nat) :
    Except Error (PdfObject × Nat) :=
  parseObj limits.maxObjectDepth bytes pos

/-! ## Indirect objects and streams (ISO 32000-2 §7.3.8, §7.3.10) -/

/-- Position of the stream data after the `stream` keyword ending at `p`: the keyword must be
followed by CR LF or LF (§7.3.8.1). -/
def streamDataStart (bytes : ByteArray) (p : Nat) : Option Nat :=
  if bytes[p]? = some 13 then
    if bytes[p + 1]? = some 10 then some (p + 2) else none
  else if bytes[p]? = some 10 then some (p + 1)
  else none

/-- Skip one optional end-of-line marker (CR LF, LF or CR) at `p`. -/
def skipEol (bytes : ByteArray) (p : Nat) : Nat :=
  if bytes[p]? = some 13 then
    if bytes[p + 1]? = some 10 then p + 2 else p + 1
  else if bytes[p]? = some 10 then p + 1
  else p

/-- The stream length from the stream dictionary: a direct non-negative integer `/Length`.
An indirect `/Length` is unsupported here; callers that can resolve it pass their own
`LengthResolver` (`Core.Xref.Length`, `Repair`). -/
def streamLength (d : Dict) (at_ : Nat) : Except Error Nat :=
  match Dict.lookup d nameLength with
  | some (.int l) =>
    if 0 ≤ l then .ok l.toNat else .error (.malformed at_ "negative /Length")
  | some (.ref _ _) => .error (.unsupported "indirect /Length")
  | some _ => .error (.malformed at_ "/Length is not an integer")
  | none => .error (.malformed at_ "missing /Length")

/-- How a stream's data length is obtained from its dictionary; the `Nat` is the offset used
in error messages (just after the `stream` keyword). The default is `streamLength`. -/
abbrev LengthResolver := Dict → Nat → Except Error Nat

/-- After `endobj` is expected at `pos`: the position after it. -/
def expectKeyword (bytes : ByteArray) (pos : Nat) (kw : List UInt8) (msg : String) :
    Except Error Nat :=
  match Lex.next bytes pos with
  | .error e => .error (lexErr e)
  | .ok (some (.keyword k, q)) => if k = kw then .ok q else .error (errAt bytes pos msg)
  | .ok _ => .error (errAt bytes pos msg)

/-- The stream body after the `stream` keyword ending at `p`, with dictionary `d` and length
resolver `len`: EOL, exactly `len d p` data bytes, optional EOL, `endstream`, `endobj`.
Returns the stream (dictionary `d` as written) and the position after `endobj`. -/
def parseStreamBodyWith (len : LengthResolver) (bytes : ByteArray) (p : Nat) (d : Dict) :
    Except Error (Stream × Nat) :=
  match streamDataStart bytes p with
  | none => .error (.malformed p "stream keyword not followed by CR LF or LF")
  | some s =>
    match len d p with
    | .error e => .error e
    | .ok len =>
      if s + len ≤ bytes.size then
        let e := skipEol bytes (s + len)
        match Lex.tokenAt bytes e with
        | .ok (some (.keyword k, e2)) =>
          if k = kwEndstream then
            match expectKeyword bytes e2 kwEndobj "expected endobj" with
            | .ok r => .ok (⟨d, bytes.extract s (s + len)⟩, r)
            | .error err => .error err
          else .error (.malformed e "expected endstream")
        | .error err => .error (lexErr err)
        | .ok _ => .error (.malformed e "expected endstream")
      else .error (.malformed s "stream data extends past end of input")

/-- The stream body with a direct `/Length` only (`parseStreamBodyWith streamLength`). -/
def parseStreamBody (bytes : ByteArray) (p : Nat) (d : Dict) : Except Error (Stream × Nat) :=
  parseStreamBodyWith streamLength bytes p d

/-- After `n g obj` (ending at `p`): the body, then `endobj`, or a stream whose length comes
from `len`. -/
def parseIndirectBodyWith (len : LengthResolver) (limits : Limits) (bytes : ByteArray)
    (p : Nat) : Except Error (IndirectBody × Nat) :=
  match parseObject limits bytes p with
  | .error e => .error e
  | .ok (o, r) =>
    match Lex.next bytes r with
    | .error e => .error (lexErr e)
    | .ok (some (.keyword k, r2)) =>
      if k = kwEndobj then .ok (.obj o, r2)
      else if k = kwStream then
        match o with
        | .dict d =>
          match parseStreamBodyWith len bytes r2 d with
          | .ok (s, r3) => .ok (.stream s, r3)
          | .error e => .error e
        | _ => .error (errAt bytes r "stream without a dictionary")
      else .error (errAt bytes r "expected endobj or stream")
    | .ok _ => .error (errAt bytes r "expected endobj or stream")

/-- After `n g obj` (ending at `p`): the body with a direct `/Length` only. -/
def parseIndirectBody (limits : Limits) (bytes : ByteArray) (p : Nat) :
    Except Error (IndirectBody × Nat) :=
  parseIndirectBodyWith streamLength limits bytes p

/-- The header `n g obj` at the next token at or after `pos`, with `n ≥ 1` and
`0 ≤ g ≤ 65535`. Returns `n`, `g` and the position after `obj`. -/
def parseHeader (bytes : ByteArray) (pos : Nat) : Except Error (Int × Int × Nat) :=
  match Lex.next bytes pos with
  | .ok (some (.int n, q1)) =>
    match Lex.next bytes q1 with
    | .ok (some (.int g, q2)) =>
      match Lex.next bytes q2 with
      | .ok (some (.keyword k, q3)) =>
        if k = kwObj then
          if refOk n g then .ok (n, g, q3)
          else .error (errAt bytes pos "bad object number")
        else .error (errAt bytes q2 "expected obj")
      | .error e => .error (lexErr e)
      | .ok _ => .error (errAt bytes q2 "expected obj")
    | .error e => .error (lexErr e)
    | .ok _ => .error (errAt bytes q1 "expected generation number")
  | .error e => .error (lexErr e)
  | .ok _ => .error (errAt bytes pos "expected object number")

/-- **Entry point.** The indirect object `n g obj … endobj` (or a stream object) starting at
the next token at or after `pos`: the header (`parseHeader`, `n ≥ 1`, `0 ≤ g ≤ 65535`), then
the body with a direct stream `/Length` (`parseIndirectBody`). Returns it and the position
after `endobj`. -/
def parseIndirect (limits : Limits) (bytes : ByteArray) (pos : Nat) :
    Except Error (IndirectObject × Nat) :=
  match parseHeader bytes pos with
  | .error e => .error e
  | .ok (n, g, q) =>
    match parseIndirectBody limits bytes q with
    | .ok (b, r) => .ok (⟨n.toNat, g.toNat, b⟩, r)
    | .error e => .error e

/-! ## Progress -/

/-- `parseIntTail` ends at or after the integer and within the input. -/
theorem parseIntTail_pos {bytes : ByteArray} {pos : Nat} {n : Int} {q : Nat} {o : PdfObject}
    {r : Nat} (hq : q ≤ bytes.size) (h : parseIntTail bytes pos n q = .ok (o, r)) :
    q ≤ r ∧ r ≤ bytes.size := by
  unfold parseIntTail at h
  split at h
  · simp at h
  · rename_i g q2 h1
    have h1' := Lex.next_pos _ _ _ _ h1
    split at h
    · simp at h
    · rename_i kw q3 h2
      have h2' := Lex.next_pos _ _ _ _ h2
      split at h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
        · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega

/-- **Progress** of `parseArray`: it ends after `pos` and within the input. -/
theorem parseArray_pos (fuel : Nat) (bytes : ByteArray) (pos : Nat) (acc : List PdfObject)
    (xs : List PdfObject) (r : Nat) (h : parseArray fuel bytes pos acc = .ok (xs, r)) :
    pos < r ∧ r ≤ bytes.size := by
  unfold parseArray at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
    · split at h
      · simp at h
      · split at h
        · rename_i hr
          have := parseArray_pos fuel bytes _ _ xs r h
          omega
        · simp at h
termination_by (fuel, bytes.size - pos)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; omega)

/-- **Progress** of `parseDict`: it ends after `pos` and within the input. -/
theorem parseDict_pos (fuel : Nat) (bytes : ByteArray) (pos : Nat)
    (acc : List (Name × PdfObject)) (d : List (Name × PdfObject)) (r : Nat)
    (h : parseDict fuel bytes pos acc = .ok (d, r)) : pos < r ∧ r ≤ bytes.size := by
  unfold parseDict at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · rename_i hr
              have := parseDict_pos fuel bytes _ _ d r h
              omega
            · simp at h
    · simp at h
termination_by (fuel, bytes.size - pos)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; omega)

/-- **Progress** of `parseObjTok`: the object ends at or after its first token and within the
input. -/
theorem parseObjTok_pos (fuel : Nat) (bytes : ByteArray) (pos : Nat) (t : Token) (q : Nat)
    (o : PdfObject) (r : Nat) (hq : q ≤ bytes.size)
    (h : parseObjTok fuel bytes pos t q = .ok (o, r)) : q ≤ r ∧ r ≤ bytes.size := by
  unfold parseObjTok at h
  split at h
  · exact parseIntTail_pos hq h
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega)
    | (simp at h; done)
    | skip
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
    · simp at h
  · split at h
    · simp at h
    · rename_i f
      split at h
      · rename_i xs r' h1
        have := parseArray_pos f bytes q [] xs r' h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
      · simp at h
  · split at h
    · simp at h
    · rename_i f
      split at h
      · rename_i d r' h1
        have := parseDict_pos f bytes q [] d r' h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
      · simp at h

/-- **Progress** of `parseObj`: the object ends strictly after `pos` and within the input. -/
theorem parseObj_pos {fuel : Nat} {bytes : ByteArray} {pos : Nat} {o : PdfObject} {r : Nat}
    (h : parseObj fuel bytes pos = .ok (o, r)) : pos < r ∧ r ≤ bytes.size := by
  unfold parseObj at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    have := parseObjTok_pos fuel bytes pos t q o r h1'.2 h
    omega

/-- **Progress** of `parseObject`: a parsed object ends strictly after `pos` and within the
input. -/
theorem parseObject_pos {limits : Limits} {bytes : ByteArray} {pos : Nat} {o : PdfObject}
    {r : Nat} (h : parseObject limits bytes pos = .ok (o, r)) : pos < r ∧ r ≤ bytes.size :=
  parseObj_pos h

/-! ## Progress and framing of indirect objects -/

/-- **Progress** of the header. -/
theorem parseHeader_pos {bytes : ByteArray} {pos : Nat} {n g : Int} {q : Nat}
    (h : parseHeader bytes pos = .ok (n, g, q)) : pos < q ∧ q ≤ bytes.size := by
  unfold parseHeader at h
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
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            omega
          · simp at h
        · simp at h
      · simp at h
      · simp at h
    · simp at h
    · simp at h
  · simp at h
  · simp at h

/-- `streamDataStart` is strictly after the keyword end. -/
theorem streamDataStart_lt {bytes : ByteArray} {p s : Nat}
    (h : streamDataStart bytes p = some s) : p < s := by
  unfold streamDataStart at h
  split at h
  · split at h <;> simp at h; omega
  · split at h <;> simp at h; omega

/-- `skipEol` does not move backwards. -/
theorem le_skipEol (bytes : ByteArray) (p : Nat) : p ≤ skipEol bytes p := by
  unfold skipEol
  split
  · split <;> omega
  · split <;> omega

/-- `expectKeyword` moves forward and stays within the input. -/
theorem expectKeyword_pos {bytes : ByteArray} {pos : Nat} {kw : List UInt8} {msg : String}
    {r : Nat} (h : expectKeyword bytes pos kw msg = .ok r) :
    pos < r ∧ r ≤ bytes.size := by
  unfold expectKeyword at h
  split at h
  · simp at h
  · rename_i k q hq
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact Lex.next_pos _ _ _ _ hq
    · simp at h
  · simp at h

/-- **Stream framing.** A stream body parsed (with any length resolver) after the keyword
ending at `p` has data `bytes[st, st + len)` with `p < st`, `st + len ≤ bytes.size`, ending
strictly before the returned position `r ≤ bytes.size`; the dictionary is the one given. -/
theorem parseStreamBodyWith_ok {len : LengthResolver} {bytes : ByteArray} {p : Nat}
    {d : Dict} {s : Stream} {r : Nat} (h : parseStreamBodyWith len bytes p d = .ok (s, r)) :
    ∃ st, p < st ∧ st + s.data.size ≤ bytes.size ∧
      s.data = bytes.extract st (st + s.data.size) ∧ st + s.data.size < r ∧
      r ≤ bytes.size ∧ s.dict = d := by
  unfold parseStreamBodyWith at h
  split at h
  · simp at h
  · rename_i st hst
    have h1 := streamDataStart_lt hst
    split at h
    · simp at h
    · rename_i l _
      split at h
      · rename_i hle
        have h2 := le_skipEol bytes (st + l)
        dsimp only at h
        split at h
        · rename_i k e2 he2
          have h3 := Lex.tokenAt_pos _ _ _ _ he2
          split at h
          · split at h
            · rename_i r' hr'
              have h4 := expectKeyword_pos hr'
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hsz : (bytes.extract st (st + l)).size = l := by
                simp only [ByteArray.size_extract]
                omega
              refine ⟨st, h1, ?_, ?_, ?_, h4.2, rfl⟩
              · simp only [hsz]; omega
              · simp only [hsz]
              · simp only [hsz]; omega
            · simp at h
          · simp at h
        · simp at h
        · simp at h
      · simp at h

/-- **Stream framing** with a direct `/Length` (an instance of `parseStreamBodyWith_ok`). -/
theorem parseStreamBody_ok {bytes : ByteArray} {p : Nat} {d : Dict} {s : Stream} {r : Nat}
    (h : parseStreamBody bytes p d = .ok (s, r)) :
    ∃ st, p < st ∧ st + s.data.size ≤ bytes.size ∧
      s.data = bytes.extract st (st + s.data.size) ∧ st + s.data.size < r ∧
      r ≤ bytes.size ∧ s.dict = d :=
  parseStreamBodyWith_ok h

/-- Progress and stream framing of `parseIndirectBodyWith` (any length resolver). -/
theorem parseIndirectBodyWith_ok {len : LengthResolver} {limits : Limits} {bytes : ByteArray}
    {p : Nat} {b : IndirectBody} {r : Nat}
    (h : parseIndirectBodyWith len limits bytes p = .ok (b, r)) :
    p < r ∧ r ≤ bytes.size ∧
      ∀ s, b = .stream s → ∃ st, p < st ∧ st + s.data.size ≤ bytes.size ∧
        s.data = bytes.extract st (st + s.data.size) := by
  unfold parseIndirectBodyWith at h
  split at h
  · simp at h
  · rename_i o r1 h1
    have p1 := parseObject_pos h1
    split at h
    · simp at h
    · rename_i k r2 h2
      have p2 := Lex.next_pos _ _ _ _ h2
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by omega, p2.2, ?_⟩
        intro s hs
        cases hs
      · split at h
        · split at h
          · split at h
            · rename_i s0 r3 h3
              obtain ⟨st, q1, q2, q3, q4, q5, _⟩ := parseStreamBodyWith_ok h3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨by omega, q5, ?_⟩
              intro s hs
              cases hs
              exact ⟨st, by omega, q2, q3⟩
            · simp at h
          · simp at h
        · simp at h
    · simp at h

/-! ## Depth bound -/

/-- Keyword objects are scalars. -/
theorem keywordObj_depth {kw : List UInt8} {o : PdfObject} (h : keywordObj kw = some o) :
    o.depth = 0 := by
  unfold keywordObj at h
  repeat' split at h
  all_goals (simp only [Option.some.injEq, reduceCtorEq] at h; try (subst h; rfl))

/-- `parseIntTail` yields a scalar (an integer or a reference). -/
theorem parseIntTail_depth {bytes : ByteArray} {pos : Nat} {n : Int} {q : Nat} {o : PdfObject}
    {r : Nat} (h : parseIntTail bytes pos n q = .ok (o, r)) : o.depth = 0 := by
  unfold parseIntTail at h
  repeat' split at h
  all_goals
    first
      | (simp at h; done)
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl)

/-- A list whose members all have depth at most `n` has `depthList` at most `n`. -/
theorem depthList_le {xs : List PdfObject} {n : Nat} (h : ∀ x ∈ xs, x.depth ≤ n) :
    PdfObject.depthList xs ≤ n := by
  induction xs with
  | nil => simp [PdfObject.depthList]
  | cons y ys ih =>
    simp only [PdfObject.depthList]
    have h1 := h y List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

/-- A dictionary whose values all have depth at most `n` has `depthDict` at most `n`. -/
theorem depthDict_le {d : List (Name × PdfObject)} {n : Nat} (h : ∀ e ∈ d, e.2.depth ≤ n) :
    PdfObject.depthDict d ≤ n := by
  induction d with
  | nil => simp [PdfObject.depthDict]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    simp only [PdfObject.depthDict]
    have h1 := h (k, v) List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp at h1
    omega

mutual

/-- **Depth bound** of `parseObjTok`: the object nests at most `fuel` deep. -/
theorem parseObjTok_depth (fuel : Nat) (bytes : ByteArray) (pos : Nat) (t : Token) (q : Nat)
    (o : PdfObject) (r : Nat) (h : parseObjTok fuel bytes pos t q = .ok (o, r)) :
    o.depth ≤ fuel := by
  unfold parseObjTok at h
  split at h
  · have := parseIntTail_depth h; omega
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
       simp [PdfObject.depth])
    | (simp at h; done)
    | skip
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      have := keywordObj_depth ‹_›; omega
    · simp at h
  · split at h
    · simp at h
    · rename_i f
      split at h
      · rename_i xs r' h1
        have := parseArray_depth f bytes q [] xs r' (by simp) h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have := depthList_le this
        simp only [PdfObject.depth]; omega
      · simp at h
  · split at h
    · simp at h
    · rename_i f
      split at h
      · rename_i d r' h1
        have := parseDict_depth f bytes q [] d r' (by simp) h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have := depthDict_le this
        simp only [PdfObject.depth]; omega
      · simp at h
termination_by (fuel, bytes.size - q)
decreasing_by all_goals (apply Prod.Lex.left; omega)

/-- **Depth bound** of `parseArray`: given an accumulator within the bound, every member of
the result nests at most `fuel` deep. -/
theorem parseArray_depth (fuel : Nat) (bytes : ByteArray) (pos : Nat) (acc : List PdfObject)
    (xs : List PdfObject) (r : Nat) (hacc : ∀ x ∈ acc, x.depth ≤ fuel)
    (h : parseArray fuel bytes pos acc = .ok (xs, r)) : ∀ x ∈ xs, x.depth ≤ fuel := by
  unfold parseArray at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      intro x hx; exact hacc x (List.mem_reverse.mp hx)
    · split at h
      · simp at h
      · rename_i o r' h2
        split at h
        · rename_i hr
          have ho := parseObjTok_depth fuel bytes pos t q o r' h2
          refine parseArray_depth fuel bytes r' (o :: acc) xs r ?_ h
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ho
          · exact hacc x hx
        · simp at h
termination_by (fuel, bytes.size - pos)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; have := Lex.next_pos _ _ _ _ h1; omega)
    | (apply Prod.Lex.right; omega)

/-- **Depth bound** of `parseDict`: given an accumulator within the bound, every value of the
result nests at most `fuel` deep. -/
theorem parseDict_depth (fuel : Nat) (bytes : ByteArray) (pos : Nat)
    (acc : List (Name × PdfObject)) (d : List (Name × PdfObject)) (r : Nat)
    (hacc : ∀ e ∈ acc, e.2.depth ≤ fuel)
    (h : parseDict fuel bytes pos acc = .ok (d, r)) : ∀ e ∈ d, e.2.depth ≤ fuel := by
  unfold parseDict at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      intro e he; exact hacc e (List.mem_reverse.mp he)
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
        · rename_i t2 q2 h2
          have h2' := Lex.next_pos _ _ _ _ h2
          split at h
          · simp at h
          · rename_i v r' h3
            split at h
            · rename_i hr
              have hv := parseObjTok_depth fuel bytes q t2 q2 v r' h3
              refine parseDict_depth fuel bytes r' (_ :: acc) d r ?_ h
              intro e he
              rcases List.mem_cons.mp he with rfl | he
              · exact hv
              · exact hacc e he
            · simp at h
    · simp at h
termination_by (fuel, bytes.size - pos)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; omega)

end

/-- **Depth bound** of `parseObj`: the object nests at most `fuel` deep. -/
theorem parseObj_depth {fuel : Nat} {bytes : ByteArray} {pos : Nat} {o : PdfObject} {r : Nat}
    (h : parseObj fuel bytes pos = .ok (o, r)) : o.depth ≤ fuel := by
  unfold parseObj at h
  split at h
  · simp at h
  · simp at h
  · exact parseObjTok_depth _ _ _ _ _ _ _ h

/-- **Depth bound** of `parseObject`: a parsed object nests at most `limits.maxObjectDepth`
deep. -/
theorem parseObject_depth {limits : Limits} {bytes : ByteArray} {pos : Nat} {o : PdfObject}
    {r : Nat} (h : parseObject limits bytes pos = .ok (o, r)) :
    o.depth ≤ limits.maxObjectDepth :=
  parseObj_depth h

/-! ## Duplicate-free dictionary keys -/

/-- Reversing a duplicate-free list keeps it duplicate-free. -/
theorem nodup_reverse {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_reverse]
  exact h.imp (fun hne heq => hne heq.symm)

/-- A key `hasKey` rejects is not among the accumulator's keys. -/
theorem not_mem_keys_of_hasKey {acc : List (Name × PdfObject)} {k : Name}
    (h : ¬ hasKey acc k = true) : k ∉ Dict.keys acc := by
  intro hk
  apply h
  simp only [Dict.keys, List.mem_map] at hk
  obtain ⟨e, he, rfl⟩ := hk
  simp only [hasKey, List.any_eq_true, beq_iff_eq]
  exact ⟨e, he, rfl⟩

/-- `parseDict` keeps keys distinct: from a duplicate-free accumulator, the resulting entries
have distinct keys. -/
theorem parseDict_keys_nodup (fuel : Nat) (bytes : ByteArray) (pos : Nat)
    (acc : List (Name × PdfObject)) (d : List (Name × PdfObject)) (r : Nat)
    (hacc : (Dict.keys acc).Nodup)
    (h : parseDict fuel bytes pos acc = .ok (d, r)) : (Dict.keys d).Nodup := by
  unfold parseDict at h
  split at h
  · simp at h
  · simp at h
  · rename_i t q h1
    have h1' := Lex.next_pos _ _ _ _ h1
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      simp only [Dict.keys, List.map_reverse]
      exact nodup_reverse hacc
    · split at h
      · simp at h
      · rename_i hk
        split at h
        · simp at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · rename_i hr
              refine parseDict_keys_nodup fuel bytes _ (_ :: acc) d r ?_ h
              simp only [Dict.keys, List.map_cons, List.nodup_cons]
              exact ⟨not_mem_keys_of_hasKey hk, hacc⟩
            · simp at h
    · simp at h
termination_by bytes.size - pos
decreasing_by omega

/-- A dictionary produced by `parseObjTok` has distinct keys. -/
theorem parseObjTok_dict_keys_nodup {fuel : Nat} {bytes : ByteArray} {pos : Nat} {t : Token}
    {q : Nat} {d : List (Name × PdfObject)} {r : Nat}
    (h : parseObjTok fuel bytes pos t q = .ok (.dict d, r)) : (Dict.keys d).Nodup := by
  unfold parseObjTok at h
  split at h
  · have := parseIntTail_depth h; simp [PdfObject.depth] at this
  all_goals first
    | (simp at h; done)
    | skip
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      have := keywordObj_depth ‹_›; simp [PdfObject.depth] at this
    · simp at h
  · split at h
    · simp at h
    · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i d' r' h1
        simp only [Except.ok.injEq, Prod.mk.injEq, PdfObject.dict.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact parseDict_keys_nodup _ _ _ [] d' r' (by simp [Dict.keys]) h1
      · simp at h

/-- A top-level dictionary returned by `parseObject` has distinct keys. (Nested dictionaries
are built by the same `parseDict`; `parseDict_keys_nodup` covers each of them.) -/
theorem parseObject_dict_keys_nodup {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {d : List (Name × PdfObject)} {r : Nat}
    (h : parseObject limits bytes pos = .ok (.dict d, r)) : (Dict.keys d).Nodup := by
  unfold parseObject parseObj at h
  split at h
  · simp at h
  · simp at h
  · exact parseObjTok_dict_keys_nodup h

/-! ## Tests -/

section Tests

/-- Test helper: a small depth limit. -/
private def lim2 : Limits := { maxObjectDepth := 2 }

/-- Test helper: summary of a parse result (`ok`, or the error class and offset). -/
private def summ (r : Except Error (PdfObject × Nat)) : Sum String (PdfObject × Nat) :=
  match r with
  | .ok v => .inr v
  | .error (.malformed o _) => .inl s!"malformed@{o}"
  | .error (.limitExceeded k) => .inl s!"limit:{reprStr k}"
  | .error (.unsupported w) => .inl s!"unsupported:{w}"
  | .error (.cycle o _) => .inl s!"cycle@{o}"

/-- Test helper: `parseObject` with default limits on a string, from position 0. -/
private def po (s : String) : Sum String (PdfObject × Nat) :=
  summ (parseObject Limits.default s.toUTF8 0)

/-- Test helper: `parseObject` with depth limit 2. -/
private def po2 (s : String) : Sum String (PdfObject × Nat) :=
  summ (parseObject lim2 s.toUTF8 0)

/-- Test helper: `parseIndirect` with default limits, summarised. -/
private def pind (s : String) : Sum String (Nat × Nat × String × Nat) :=
  match parseIndirect Limits.default s.toUTF8 0 with
  | .ok (io, r) =>
    match io.body with
    | .obj o => .inr (io.num, io.gen, reprStr o, r)
    | .stream st => .inr (io.num, io.gen, s!"stream {reprStr st.dict} {st.data.data.toList}", r)
  | .error (.malformed o _) => .inl s!"malformed@{o}"
  | .error (.limitExceeded k) => .inl s!"limit:{reprStr k}"
  | .error (.unsupported w) => .inl s!"unsupported:{w}"
  | .error (.cycle o _) => .inl s!"cycle@{o}"

/-- Test helper: a name. -/
private def nm (s : String) : Name := Name.ofString s

/-- Test helper: `n` copies of `[`. -/
private def opens (n : Nat) : ByteArray := ⟨Array.replicate n 91⟩

-- G1: references
#guard po "1 0 R" == .inr (.ref 1 0, 5)
#guard po " 12 3 R " == .inr (.ref 12 3, 7)
#guard po "0 0 R" == .inl "malformed@0"
#guard po "1 70000 R" == .inl "malformed@0"
#guard po "1 -1 R" == .inl "malformed@0"
#guard po "1 0 foo" == .inr (.int 1, 1)
#guard po "1 0" == .inr (.int 1, 1)
#guard po "-7" == .inr (.int (-7), 2)
#guard po "[1 0 R 2 0 3 R]" == .inl "malformed@9"
#guard po "[1 0 R 2 0 3 4 R]" == .inr (.array [.ref 1 0, .int 2, .int 0, .ref 3 4], 17)
-- G2/G3: scalars and keywords
#guard po "[true false null 1.50 (a) <41> /N]" ==
  .inr (.array [.bool true, .bool false, .null, .real ⟨15, 1⟩, .string [97], .string [65],
    .name (nm "N")], 34)
#guard po "obj" == .inl "malformed@0"
#guard po "  ]" == .inl "malformed@2"
#guard po "{" == .inl "malformed@0"
-- G4/G5: nesting, order, errors
#guard po "<</A [1 <</B null>>] /C /D>>" ==
  .inr (.dict [(nm "A", .array [.int 1, .dict [(nm "B", .null)]]), (nm "C", .name (nm "D"))], 28)
#guard po "[]" == .inr (.array [], 2)
#guard po "<<>>" == .inr (.dict [], 4)
#guard po "<</A 1 /A 2>>" == .inl "malformed@7"
#guard po "<</A 1 2 3>>" == .inl "malformed@7"
#guard po "<</A>>" == .inl "malformed@4"
#guard po "[1 2" == .inl "malformed@4"
#guard po "<</A 1" == .inl "malformed@6"
#guard po "" == .inl "malformed@0"
-- depth: exactly the fuel, and one more
#guard po2 "[[1]]" == .inr (.array [.array [.int 1]], 5)
#guard po2 "[<<>>]" == .inr (.array [.dict []], 6)
#guard po2 "[[[]]]" == .inl "limit:SafePdf.LimitKind.objectDepth"
#guard po2 "<</A <</B []>>>>" == .inl "limit:SafePdf.LimitKind.objectDepth"
-- 100 000 nested arrays: a clean depth-limit error, recursion bounded by fuel
#guard summ (parseObject Limits.default (opens 100000) 0) ==
  .inl "limit:SafePdf.LimitKind.objectDepth"
-- lexer errors keep their offset
#guard po "[1 (abc" == .inl "malformed@3"
#guard po "<</A#zz 1>>" == .inl "malformed@2"
#guard po "5 )" == .inl "malformed@2"
-- indirect objects and streams
#guard pind "3 0 obj\n<</Type /X>>\nendobj" == .inr (3, 0, reprStr (PdfObject.dict [(nm "Type", .name (nm "X"))]), 27)
#guard pind "1 0 obj 42 endobj x" == .inr (1, 0, reprStr (PdfObject.int 42), 17)
#guard pind "0 0 obj 42 endobj" == .inl "malformed@0"
#guard pind "1 0 obj 42" == .inl "malformed@10"
#guard pind "4 0 obj <</Length 5>> stream\nhello\nendstream endobj" ==
  .inr (4, 0, s!"stream {reprStr [(nm "Length", PdfObject.int 5)]} [104, 101, 108, 108, 111]", 51)
#guard pind "4 0 obj <</Length 5>> stream\r\nhello\r\nendstream\nendobj" ==
  .inr (4, 0, s!"stream {reprStr [(nm "Length", PdfObject.int 5)]} [104, 101, 108, 108, 111]", 53)
#guard pind "4 0 obj <</Length 5>> stream\nhelloendstream endobj" ==
  .inr (4, 0, s!"stream {reprStr [(nm "Length", PdfObject.int 5)]} [104, 101, 108, 108, 111]", 50)
#guard pind "4 0 obj <</Length 5>> stream\rhello\nendstream endobj" == .inl "malformed@28"
#guard pind "4 0 obj <</Length 9>> stream\nhello\nendstream endobj" == .inl "malformed@38"
#guard pind "4 0 obj <</Length 50>> stream\nhello\nendstream endobj" == .inl "malformed@30"
#guard pind "4 0 obj <</Length 7 0 R>> stream\nhello\nendstream endobj" ==
  .inl "unsupported:indirect /Length"
#guard pind "4 0 obj [1] stream\nhello\nendstream endobj" == .inl "malformed@12"
-- the header alone, and the body with another length resolver
#guard (match parseHeader " 4 2 obj x".toUTF8 0 with
  | .ok (n, g, q) => n == 4 && g == 2 && q == 8
  | .error _ => false)
#guard (match parseHeader "0 0 obj".toUTF8 0 with
  | .error (.malformed 0 _) => true
  | _ => false)
#guard (match parseIndirectBodyWith (fun _ _ => .ok 5) Limits.default
    "<</Length 7 0 R>> stream\nhello\nendstream endobj".toUTF8 0 with
  | .ok (.stream s, r) => s.data.toList == [104, 101, 108, 108, 111] && r == 47
  | _ => false)

end Tests

end SafePdf.Core.ObjParse
