import SafePdf.Core.Object

/-!
# Lexical tokens (Plan.md §6 Phase 1, §5.1; ISO 32000-2 §7.2–7.3)

The token type shared by the denotational lexer spec (`SafePdf/Spec/Lex.lean`, task 1.2)
and the efficient tokenizer (`SafePdf/Core/Lex.lean`, task 1.3). Both lexers produce
exactly these values, so the equivalence theorem (task 1.6) can be stated as plain
equality.

## Interface contract (both lexers implement it)

PDF cannot be tokenized as a whole: the bytes after the `stream` keyword are raw data whose
length comes from the stream dictionary, and inline-image data in content streams is
similar. So the primary interface is one token at a time:

* Spec (task 1.2), over the remaining input as a list:
  `Spec.Lex.next : List UInt8 → Except LexError (Option (Token × List UInt8))`
  skips whitespace and comments, then returns the next token and the rest of the input,
  or `none` at end of input. `LexError.offset` is relative to the start of the list given.
* Core (task 1.3), over a `ByteArray` and a position:
  `Core.Lex.next : ByteArray → Nat → Except LexError (Option (Token × Nat))`
  returns the token and the position just after it. Offsets in errors are absolute.
* Equivalence (task 1.6):
  `Core.Lex.next bytes pos` agrees with `Spec.Lex.next (bytes.data.toList.drop pos)` after
  translating the remaining list to a position (`bytes.size - rest.length`) and shifting
  error offsets by `pos`.

Each side may also offer a convenience `lexAll` that repeats `next` to the end of input
(useful for content streams without inline images, and for tests).

## Lexical decisions (strict path)

* Whitespace: NUL, TAB, LF, FF, CR, SP (§7.2.3). Comments run from `%` to the end of line
  and count as whitespace; the lexer drops them.
* Delimiters: `( ) < > [ ] { } / %` (§7.2.3).
* Numbers (§7.3.3): optional sign, digits, at most one `.`; at least one digit overall.
  Integers become `Token.int`, reals become `Token.real` with a canonical
  (`Decimal.normalize`d) value. A malformed number (`--5`, `+`, `1.2.3`) is an error in the
  strict lexer. Range limits (Annex C) are checked by the parser, not here.
* Literal strings (§7.3.4.2): balanced parentheses; escapes `\n \r \t \b \f \( \) \\`,
  octal `\d`, `\dd`, `\ddd` (high-order overflow ignored, i.e. value mod 256); a backslash
  before an end-of-line is a line continuation; any other escaped character is the
  character itself (backslash dropped). An unescaped end-of-line (CR, LF or CR LF) in the
  string is read as a single LF. Unterminated string → error.
* Hex strings (§7.3.4.3): whitespace ignored; odd digit count → final digit padded with 0;
  non-hex character → error. `<<` is a dictionary opener, not a hex string.
* Names (§7.3.5): `/` followed by regular characters; `#xx` decodes to one byte; a `#` not
  followed by two hex digits → error; a decoded NUL byte → error. The empty name `/` is
  legal.
* Keywords: any other maximal run of regular characters (`true`, `false`, `null`, `R`,
  `obj`, `endobj`, `stream`, `endstream`, `xref`, `trailer`, `startxref`, and content-stream
  operators) is a `Token.keyword` holding its bytes. The parser interprets them.
* A lone `>` (not part of `>>`) or `}`/`{`, `)` outside a string are tokens or errors as
  listed in `Token`/`LexErrorKind`.
-/

namespace SafePdf

/-- A lexical token of the PDF syntax (ISO 32000-2 §7.2–7.3). -/
inductive Token where
  /-- An integer literal. -/
  | int (i : Int)
  /-- A real literal, canonical (`Decimal.normalize`d). -/
  | real (d : Decimal)
  /-- A literal string `( … )`, escapes and line ends decoded. -/
  | litString (bytes : List UInt8)
  /-- A hexadecimal string `< … >`, decoded. -/
  | hexString (bytes : List UInt8)
  /-- A name `/…`, `#xx` sequences decoded. -/
  | name (n : Name)
  /-- `[` -/
  | arrayOpen
  /-- `]` -/
  | arrayClose
  /-- `<<` -/
  | dictOpen
  /-- `>>` -/
  | dictClose
  /-- `{` (PostScript calculator functions only). -/
  | braceOpen
  /-- `}` (PostScript calculator functions only). -/
  | braceClose
  /-- Any other run of regular characters: `true`, `obj`, `R`, operators, … -/
  | keyword (bytes : List UInt8)
  deriving Repr, Inhabited, DecidableEq

/-- What went wrong while lexing. -/
inductive LexErrorKind where
  /-- A malformed number such as `--5`, `+` or `1.2.3`. -/
  | badNumber
  /-- End of input inside a literal string. -/
  | unterminatedString
  /-- End of input inside a hex string. -/
  | unterminatedHexString
  /-- A non-hex, non-whitespace character inside a hex string. -/
  | badHexDigit
  /-- `#` in a name not followed by two hex digits. -/
  | badNameEscape
  /-- A name containing a decoded NUL byte. -/
  | nulInName
  /-- A delimiter that cannot start a token here: `)` or a lone `>`. -/
  | unexpectedDelimiter
  deriving Repr, Inhabited, DecidableEq

/-- A lexing error: its kind and the byte offset where the offending token starts. -/
structure LexError where
  /-- Byte offset of the start of the offending token. -/
  offset : Nat
  /-- What went wrong. -/
  kind : LexErrorKind
  deriving Repr, Inhabited, DecidableEq

end SafePdf
