import SafePdf.Core.Token

/-!
# Object printer (Plan.md §5.1, §6 Phase 1, task 1.7; ISO 32000-2 §7.2–7.3)

The serializer half of the M1 round-trip `parse (print o) = o` (Plan.md §6 Phase 1, exit
criterion M1). It maps a direct object `PdfObject` back to PDF syntax. The round-trip
theorems live in `SafePdf/Spec/RoundTrip.lean`.

## Design (chosen to make the round-trip proof short)

The printer goes through tokens: `printTokens o` is the token sequence of `o`, `tokBytes t`
the spelling of one token, and `printObj o` joins the spellings of `printTokens o` with
**exactly one space (SP, 0x20) between consecutive tokens** (no leading or trailing
whitespace). The round-trip proof then splits into a lexing half (`lexAll (printObj o) =
printTokens o`, one lemma per token kind) and a parsing half (`parse (printTokens o) = o`).

* **Integers**: optional `-`, then the decimal digits of the absolute value (`natDigits`, no
  leading zeros; `0` is `0`).
* **Reals** (canonical `Decimal` `⟨m, s⟩`): optional `-`, the digits of `|m|` left-padded with
  `0` to at least `s + 1` digits, with a `.` inserted before the last `s` digits; a `.` is
  always present, so `⟨5, 0⟩` prints as `5.`, `⟨-35, 1⟩` as `-3.5`, `⟨5, 3⟩` as `0.005` and
  `⟨0, 0⟩` as `0.`. The lexer reads these back as `Token.real ⟨m, s⟩` because a canonical
  decimal is its own normal form.
* **Strings** are always written as hex strings `<…>` with two **uppercase** hex digits per
  byte (§7.3.4.3); the literal/hex distinction is not part of the object model.
* **Names**: `/` followed by each byte, kept as is when it is a printable ASCII regular byte
  (0x21–0x7E, not a delimiter `( ) < > [ ] { } / %` and not `#`), else written `#XX` with
  uppercase hex digits (§7.3.5). Byte 0 cannot be written (`#00` is illegal); canonical
  names contain none.
* **Keywords** `true`, `false`, `null`; references `n g R`; arrays `[ … ]`; dictionaries
  `<< /k v … >>` with entries in model order.

The printer is total; it is correct (round-trips) on canonical objects
(`PdfObject.Canonical`) whose references are in range (`RefsInRange`: object number `≥ 1`,
generation `≤ 65535`, the range the parser accepts for `n g R`; ISO 32000-2 §7.3.10).
`printableTok` names the tokens the lexer reads back exactly from `tokBytes`.

Everything is pure, total and structurally recursive (except `natDigits`, well-founded on
the number).
-/

namespace SafePdf.Core.Print

open SafePdf

/-! ## Numbers -/

/-- The ASCII byte of the decimal digit `d` (for `d < 10`). -/
def digitByte (d : Nat) : UInt8 := UInt8.ofNat (48 + d)

/-- The decimal digits of `n`, most significant first, without leading zeros (`0` is `[0x30]`). -/
def natDigits (n : Nat) : List UInt8 :=
  if n < 10 then [digitByte n] else natDigits (n / 10) ++ [digitByte (n % 10)]
termination_by n
decreasing_by omega

/-- A minus sign when `neg`, else nothing. -/
def signBytes (neg : Bool) : List UInt8 := if neg then [45] else []

/-- The spelling of an integer (ISO 32000-2 §7.3.3): optional `-`, then decimal digits. -/
def intBytes (i : Int) : List UInt8 := signBytes (decide (i < 0)) ++ natDigits i.natAbs

/-- The digits of `|m|` left-padded with `0` to at least `s + 1` digits. -/
def paddedDigits (d : Decimal) : List UInt8 :=
  List.replicate (d.scale + 1 - (natDigits d.mantissa.natAbs).length) 48 ++
    natDigits d.mantissa.natAbs

/-- The spelling of a real (ISO 32000-2 §7.3.3): optional `-`, the padded digits of the
mantissa with a `.` before the last `scale` digits (a `.` is always written). -/
def realBytes (d : Decimal) : List UInt8 :=
  let p := paddedDigits d
  let k := p.length - d.scale
  signBytes (decide (d.mantissa < 0)) ++ (p.take k ++ 46 :: p.drop k)

/-! ## Strings and names -/

/-- The uppercase ASCII hex digit of a nibble `n < 16`. -/
def hexDigit (n : UInt8) : UInt8 := if n < 10 then 48 + n else 55 + n

/-- The two hex digits of a byte. -/
def hexPair (b : UInt8) : List UInt8 := [hexDigit (b / 16), hexDigit (b % 16)]

/-- The hex digits of a byte string (the body of a hex string, ISO 32000-2 §7.3.4.3). -/
def hexBytes (s : List UInt8) : List UInt8 := s.flatMap hexPair

/-- Bytes written literally inside a name: printable ASCII regular bytes other than `#`. -/
def nameSafe (b : UInt8) : Bool :=
  0x21 ≤ b && b ≤ 0x7E && b != 35 && b != 40 && b != 41 && b != 60 && b != 62 &&
  b != 91 && b != 93 && b != 123 && b != 125 && b != 47 && b != 37

/-- One name byte: itself if `nameSafe`, else `#XX` (ISO 32000-2 §7.3.5). -/
def nameByte (b : UInt8) : List UInt8 := if nameSafe b then [b] else 35 :: hexPair b

/-- The spelling of a name: `/` and the escaped bytes. -/
def nameBytes (n : Name) : List UInt8 := 47 :: n.bytes.flatMap nameByte

/-! ## Tokens -/

/-- The bytes of the keyword `R`. -/
def kwR : List UInt8 := [82]
/-- The bytes of the keyword `true`. -/
def kwTrue : List UInt8 := [116, 114, 117, 101]
/-- The bytes of the keyword `false`. -/
def kwFalse : List UInt8 := [102, 97, 108, 115, 101]
/-- The bytes of the keyword `null`. -/
def kwNull : List UInt8 := [110, 117, 108, 108]

/-- The spelling of one token. Literal strings are spelled as hex strings (the printer never
emits `litString`). -/
def tokBytes : Token → List UInt8
  | .int i => intBytes i
  | .real d => realBytes d
  | .litString s => 60 :: (hexBytes s ++ [62])
  | .hexString s => 60 :: (hexBytes s ++ [62])
  | .name n => nameBytes n
  | .arrayOpen => [91]
  | .arrayClose => [93]
  | .dictOpen => [60, 60]
  | .dictClose => [62, 62]
  | .braceOpen => [123]
  | .braceClose => [125]
  | .keyword kw => kw

/-- The tokens the lexer reads back exactly from `tokBytes`: everything the printer emits
for a canonical object (canonical reals, NUL-free names, the four keywords). -/
def printableTok : Token → Bool
  | .int _ => true
  | .real d => d.isCanonical
  | .hexString _ => true
  | .name n => n.isCanonical
  | .keyword kw => kw == kwR || kw == kwTrue || kw == kwFalse || kw == kwNull
  | .arrayOpen | .arrayClose | .dictOpen | .dictClose => true
  | .litString _ | .braceOpen | .braceClose => false

/-- Spell tokens that follow an earlier token: each one preceded by one space. -/
def renderTail : List Token → List UInt8
  | [] => []
  | t :: ts => 32 :: (tokBytes t ++ renderTail ts)

/-- Spell a token list, separating consecutive tokens by exactly one space. -/
def render : List Token → List UInt8
  | [] => []
  | t :: ts => tokBytes t ++ renderTail ts

/-! ## Objects -/

mutual
/-- The token sequence the printer emits for an object. -/
def printTokens : PdfObject → List Token
  | .null => [.keyword kwNull]
  | .bool true => [.keyword kwTrue]
  | .bool false => [.keyword kwFalse]
  | .int i => [.int i]
  | .real d => [.real d]
  | .string s => [.hexString s]
  | .name n => [.name n]
  | .array xs => .arrayOpen :: (printItems xs ++ [.arrayClose])
  | .dict es => .dictOpen :: (printEntries es ++ [.dictClose])
  | .ref n g => [.int n, .int g, .keyword kwR]

/-- The tokens of array members, in order. -/
def printItems : List PdfObject → List Token
  | [] => []
  | x :: xs => printTokens x ++ printItems xs

/-- The tokens of dictionary entries: each key name followed by its value. -/
def printEntries : List (Name × PdfObject) → List Token
  | [] => []
  | (k, v) :: es => .name k :: (printTokens v ++ printEntries es)
end

/-- The bytes of an object as a list: its tokens separated by single spaces. -/
def printObj (o : PdfObject) : List UInt8 := render (printTokens o)

/-- The bytes of an object (ISO 32000-2 §7.3 syntax). -/
def print (o : PdfObject) : ByteArray := ⟨(printObj o).toArray⟩

/-! ## Reference range -/

mutual
/-- Every reference `n g R` in the object has `1 ≤ n` and `g ≤ 65535` (the range the strict
parser accepts, ISO 32000-2 §7.3.10). -/
def refsInRange : PdfObject → Bool
  | .ref n g => decide (1 ≤ n) && decide (g ≤ 65535)
  | .array xs => refsInRangeList xs
  | .dict es => refsInRangeDict es
  | _ => true

/-- `refsInRange` for every member of a list. -/
def refsInRangeList : List PdfObject → Bool
  | [] => true
  | x :: xs => refsInRange x && refsInRangeList xs

/-- `refsInRange` for every value of a dictionary. -/
def refsInRangeDict : List (Name × PdfObject) → Bool
  | [] => true
  | (_, v) :: es => refsInRange v && refsInRangeDict es
end

/-- `RefsInRange o`: every reference in `o` is in range; decidable. -/
abbrev RefsInRange (o : PdfObject) : Prop := refsInRange o = true

/-! ## Compile-time checks -/

section Tests

private def str (o : PdfObject) : List UInt8 := printObj o
private def bs (s : String) : List UInt8 := s.toUTF8.toList

#guard str .null == bs "null"
#guard str (.bool true) == bs "true"
#guard str (.bool false) == bs "false"
#guard str (.int 0) == bs "0"
#guard str (.int 1234567890123) == bs "1234567890123"
#guard str (.int (-98)) == bs "-98"
#guard str (.real ⟨5, 0⟩) == bs "5."
#guard str (.real ⟨-35, 1⟩) == bs "-3.5"
#guard str (.real ⟨5, 3⟩) == bs "0.005"
#guard str (.real ⟨-5, 3⟩) == bs "-0.005"
#guard str (.real ⟨0, 0⟩) == bs "0."
#guard str (.real ⟨6125, 1⟩) == bs "612.5"
#guard str (.string []) == bs "<>"
#guard str (.string (bs "Hi\n")) == bs "<48690A>"
#guard str (.string [0, 255, 0xab]) == bs "<00FFAB>"
#guard str (.name ⟨[]⟩) == bs "/"
#guard str (.name (Name.ofString "Type")) == bs "/Type"
#guard str (.name (Name.ofString "A B#/c")) == bs "/A#20B#23#2Fc"
#guard str (.name ⟨[0xE9, 0x7F]⟩) == bs "/#E9#7F"
#guard str (.ref 12 0) == bs "12 0 R"
#guard str (.array []) == bs "[ ]"
#guard str (.dict []) == bs "<< >>"
#guard str (.array [.int 1, .int 2, .ref 3 0, .real ⟨15, 1⟩]) == bs "[ 1 2 3 0 R 1.5 ]"
#guard str (.dict [(Name.ofString "Type", .name (Name.ofString "Page")),
    (Name.ofString "Kids", .array [.ref 4 0, .dict []]), (Name.ofString "N", .null)]) ==
  bs "<< /Type /Page /Kids [ 4 0 R << >> ] /N null >>"
#guard (print (.array [.int 1])).size == 5
#guard refsInRange (.array [.ref 1 65535])
#guard !refsInRange (.dict [(Name.ofString "P", .ref 0 0)])
#guard !refsInRange (.ref 1 65536)

end Tests

end SafePdf.Core.Print
