/-!
# Tcl scripts as data (task 8.2a; Plan.md §8 native app, §10 `SafePdf/Shell/`)

**Copied** from the sibling project bib-lean, `BibLean/Gui/Tcl.lean` (task 5.4 there, its
proof target U3; same author/organisation), with only the namespace changed. Keep the two
copies in step when either changes.

The viewer shell drives Tk by evaluating Tcl scripts. Document data (file names, error
messages that quote document bytes) is untrusted and may contain `[`, `$`, `{`, `"` and
`\`, so a script is never built by pasting strings together: it is a `Script` of `Cmd`s of
`Word`s, and every literal word is rendered by `quote`. `SafePdf/Shell/App/TclLemmas.lean`
proves U3: for every string `s`, Tcl reads `quote s` back as exactly one word equal to `s`.

## The model of Tcl's word rules

"Tcl reads" means `parseWord`, an executable model of the rules of the Tcl manual page
`Tcl(n)` (the "Dodekalogue", Tcl 9.0/9.1; rule numbers are its section numbers) together
with the behaviour of `Tcl_ParseCommand` in `generic/tclParse.c` where the manual is
terse. The model does not cover every rule: on input that needs a rule it does not cover it returns
`none` rather than guessing, so `parseWord x = some (w, r)` is only ever a claim about
the covered rules. Covered:

* [3] Words: words are separated by white space (`isSep`: space, tab, `\v`, `\f`, `\r`,
  the parser's TYPE_SPACE class) and by backslash-newline (`ParseWhiteSpace` treats
  `\` + newline as white space); a word ends at white space or a command terminator.
* [1] Commands: newline and `;` terminate a command (`isCmdEnd`).
* [4] Double quotes: `"…"` up to the next unescaped `"`, which must be followed by white
  space or the end of the command; backslash substitution inside.
* [5] Argument expansion: a word starting `{*}` followed by a non-space character is not
  modelled (`none`); `{*}` followed by white space or a terminator is the literal `*`.
* [6] Braces: `{…}` up to the matching `}`; braces nest; a backslash-escaped brace is not
  counted; no substitution except backslash-newline-white space → one space; the
  backslash and the escaped character are kept; the close brace must be followed by white
  space or the end of the command ("extra characters after close-brace").
* [9] Backslash substitution: `\a \b \f \n \r \t \v`, `\` + newline + spaces/tabs (a
  separator in a bare word, one space in a quoted or braced word), `\ooo` (one to three
  octal digits, stopping before the value exceeds `\377`), and `\c` → `c` for every
  other character `c`.
* [10] Comments: a command whose first word starts with `#` is not modelled (`none`).

Not covered (the model returns `none`): [7] command substitution `[`, [8] variable
substitution `$` (even a `$` Tcl would keep literally), `\x`, `\u`, `\U` escapes, a
backslash as the very last character of the script, and command substitution nesting
(`]` is an ordinary character, as it is at the top level of a script). `quote` never
produces any of these, which is what the round-trip theorems show. Raw NUL characters
are ordinary characters in the model; `quote` never emits one (it writes `\000`), so the
open question of how `Tcl_EvalEx` treats a raw NUL byte never arises.

Following bib-lean's string boundary rule (its progress.md, Decisions), the model works on
`List Char`; `quote` is `String.ofList` of a `List Char` function.
-/

namespace SafePdf.Shell.App.Tcl

/-! ## Character classes -/

/-- Tcl's word-separating white space (TYPE_SPACE in `tclParse.c`; Dodekalogue [3]). -/
def isSep (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\x0b' || c == '\x0c' || c == '\r'

/-- Command terminators (Dodekalogue [1]). -/
def isCmdEnd (c : Char) : Bool :=
  c == '\n' || c == ';'

/-- Spaces and tabs, the white space a backslash-newline swallows (Dodekalogue [9]). -/
def isSpTab (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- Octal digits. -/
def isOct (c : Char) : Bool :=
  '0' ≤ c && c ≤ '7'

/-- Value of an octal digit. -/
def octVal (c : Char) : Nat :=
  c.toNat - '0'.toNat

/-- Drops the spaces and tabs after a backslash-newline. -/
def skipSpTab : List Char → List Char
  | [] => []
  | c :: r => if isSpTab c then skipSpTab r else c :: r

/-- Dropping spaces and tabs never lengthens the input. -/
theorem skipSpTab_length : ∀ l : List Char, (skipSpTab l).length ≤ l.length
  | [] => by simp [skipSpTab]
  | c :: r => by
    have := skipSpTab_length r
    simp only [skipSpTab]; split <;> simp <;> omega

/-- Skips white space between words, including backslash-newline (`ParseWhiteSpace`). -/
def skipSep : List Char → List Char
  | [] => []
  | c :: r =>
    if isSep c then skipSep r
    else if c == '\\' then
      match r with
      | '\n' :: r' => skipSep r'
      | _ => c :: r
    else c :: r

/-- `true` when a word may end here: end of input, white space, a command terminator,
or backslash-newline. -/
def atWordEnd : List Char → Bool
  | [] => true
  | c :: r =>
    isSep c || isCmdEnd c ||
      (c == '\\' && match r with
        | '\n' :: _ => true
        | _ => false)

/-! ## Backslash substitution (Dodekalogue [9]) -/

/-- `backslash d r`: the substitution for `\d` followed by `r` (`d ≠ newline`, which the
callers handle) as the resulting character and how many characters of `r` it consumes.
`none` for the escapes the model does not cover (`\x`, `\u`, `\U`). -/
def backslash (d : Char) (r : List Char) : Option (Char × Nat) :=
  if d == 'a' then some ('\x07', 0)
  else if d == 'b' then some ('\x08', 0)
  else if d == 'f' then some ('\x0c', 0)
  else if d == 'n' then some ('\n', 0)
  else if d == 'r' then some ('\r', 0)
  else if d == 't' then some ('\t', 0)
  else if d == 'v' then some ('\x0b', 0)
  else if d == 'x' || d == 'u' || d == 'U' then none
  else if isOct d then
    match r with
    | e :: r1 =>
      if isOct e then
        let v := octVal d * 8 + octVal e
        match r1 with
        | f :: _ =>
          if isOct f && v * 8 + octVal f ≤ 255 then some (Char.ofNat (v * 8 + octVal f), 2)
          else some (Char.ofNat v, 1)
        | [] => some (Char.ofNat v, 1)
      else some (Char.ofNat (octVal d), 0)
    | [] => some (Char.ofNat (octVal d), 0)
  else some (d, 0)

/-! ## Words -/

/-- A bare word (Dodekalogue [3], [9]): characters up to white space, a terminator or a
backslash-newline, with backslash substitution. Returns the word and the rest, which
starts at the character that ended the word. -/
def bareWord (acc : List Char) : List Char → Option (List Char × List Char)
  | [] => some (acc.reverse, [])
  | c :: r =>
    if isSep c || isCmdEnd c then some (acc.reverse, c :: r)
    else if c == '$' || c == '[' then none
    else if c == '\\' then
      match r with
      | [] => none
      | d :: r' =>
        if d == '\n' then some (acc.reverse, c :: r)
        else match backslash d r' with
          | some (e, k) => bareWord (e :: acc) (r'.drop k)
          | none => none
    else bareWord (c :: acc) r
termination_by l => l.length
decreasing_by all_goals simp <;> omega

/-- The body of a double-quoted word after the opening `"` (Dodekalogue [4], [9]).
Returns the word and the rest after the closing `"`. -/
def quotedWord (acc : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: r =>
    if c == '"' then some (acc.reverse, r)
    else if c == '$' || c == '[' then none
    else if c == '\\' then
      match r with
      | [] => none
      | d :: r' =>
        if d == '\n' then
          have : (skipSpTab r').length ≤ r'.length := skipSpTab_length r'
          quotedWord (' ' :: acc) (skipSpTab r')
        else match backslash d r' with
          | some (e, k) => quotedWord (e :: acc) (r'.drop k)
          | none => none
    else quotedWord (c :: acc) r
termination_by l => l.length
decreasing_by all_goals simp <;> omega

/-- The body of a braced word after the opening `{` (Dodekalogue [6]): up to the matching
`}` at depth 0; returns the word and the rest after the closing brace. -/
def bracedWord (depth : Nat) (acc : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: r =>
    if c == '}' then
      match depth with
      | 0 => some (acc.reverse, r)
      | d + 1 => bracedWord d ('}' :: acc) r
    else if c == '{' then bracedWord (depth + 1) ('{' :: acc) r
    else if c == '\\' then
      match r with
      | [] => none
      | e :: r' =>
        if e == '\n' then
          have : (skipSpTab r').length ≤ r'.length := skipSpTab_length r'
          bracedWord depth (' ' :: acc) (skipSpTab r')
        else bracedWord depth (e :: '\\' :: acc) r'
    else bracedWord depth (c :: acc) r
termination_by l => l.length
decreasing_by all_goals simp <;> omega

/-- `true` when a word starting `{` + `r` is an argument expansion `{*}…` (Dodekalogue
[5]), which the model does not cover. -/
def isExpand : List Char → Bool
  | '*' :: '}' :: r => !atWordEnd r
  | _ => false

/-- Parses one word at the start of the input (no leading white space). Returns the
word's value and the rest of the input, which starts with white space, a terminator or
backslash-newline, or is empty. `none`: not a word, a malformed word, or a rule the model
does not cover. -/
def parseWord : List Char → Option (List Char × List Char)
  | [] => none
  | c :: r =>
    if c == '{' then
      if isExpand r then none
      else match bracedWord 0 [] r with
        | some (w, r') => if atWordEnd r' then some (w, r') else none
        | none => none
    else if c == '"' then
      match quotedWord [] r with
      | some (w, r') => if atWordEnd r' then some (w, r') else none
      | none => none
    else if atWordEnd (c :: r) then none
    else bareWord [] (c :: r)

/-- Parses the words of one command (Dodekalogue [1], [2], [3]) and the rest after its
terminator. A comment ([10]) is not modelled. The length check never fails on real
words (each consumes at least one character); it makes termination evident. -/
def parseCmdFrom (acc : List (List Char)) (l : List Char) :
    Option (List (List Char) × List Char) :=
  match skipSep l with
  | [] => some (acc.reverse, [])
  | c :: r =>
    if isCmdEnd c then some (acc.reverse, r)
    else if acc.isEmpty && c == '#' then none
    else match parseWord (c :: r) with
      | some (w, r') =>
        if r'.length < l.length then parseCmdFrom (w :: acc) r' else none
      | none => none
termination_by l.length

/-- Parses one command: its words and the input after its terminator. -/
def parseCmd (l : List Char) : Option (List (List Char) × List Char) :=
  parseCmdFrom [] l

/-- Parses a whole script into the word lists of its commands. Empty commands (blank
lines) are reported as `[]`; Tcl skips them, and evaluating one is a no-op anyway. -/
def parseScript (l : List Char) : Option (List (List (List Char))) :=
  if l.isEmpty then some []
  else
    match parseCmd l with
    | some (ws, r) =>
      if r.length < l.length then (parseScript r).map (ws :: ·) else none
    | none => none
termination_by l.length

/-! ## Quoting -/

/-- Characters that may appear in a bare word as themselves, with no quoting at all:
ASCII letters and digits and `- . _ : / , + = @ %`. -/
def plainChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '_' || c == ':' || c == '/' || c == ',' ||
    c == '+' || c == '=' || c == '@' || c == '%'

/-- Characters the backslash fallback writes as `\c`. -/
def needsEsc (c : Char) : Bool :=
  c == ' ' || c == ';' || c == '[' || c == ']' || c == '$' || c == '\\' || c == '{' ||
    c == '}' || c == '"' || c == '#'

/-- One character of the backslash fallback. White space and NUL are written as letter or
octal escapes (a backslash before a raw newline would be a backslash-newline). -/
def escChar (c : Char) : List Char :=
  if c = '\n' then ['\\', 'n']
  else if c = '\t' then ['\\', 't']
  else if c = '\r' then ['\\', 'r']
  else if c = '\x0b' then ['\\', 'v']
  else if c = '\x0c' then ['\\', 'f']
  else if c = '\x00' then ['\\', '0', '0', '0']
  else if needsEsc c then ['\\', c]
  else [c]

/-- `braceOK d l`: `l` closes exactly `d` already-open braces, so that `{` + `l` + `}`
(for `d = 0`) is a braced word whose value is exactly `l`: unescaped braces balance and
the depth never drops below zero, no backslash-newline (it would become a space), no
trailing backslash (it would escape the closing brace), no NUL (kept out of scripts) and
no carriage return (`source` and channel line-ending translation would turn it into a
newline; the backslash fallback writes it as `\r`). -/
def braceOK (d : Nat) : List Char → Bool
  | [] => d == 0
  | c :: r =>
    if c == '}' then
      match d with
      | 0 => false
      | d' + 1 => braceOK d' r
    else if c == '{' then braceOK (d + 1) r
    else if c == '\\' then
      match r with
      | [] => false
      | e :: r' => e != '\n' && e != '\x00' && e != '\r' && braceOK d r'
    else if c == '\x00' || c == '\r' then false
    else braceOK d r

/-- The specification of `quote`: a plain bare word when every character is plain;
else brace quoting when it is exact (`braceOK 0`); else every character through
`escChar`. -/
def quoteList (l : List Char) : List Char :=
  if !l.isEmpty && l.all plainChar then l
  else if braceOK 0 l then '{' :: l ++ ['}']
  else l.flatMap escChar

/-- Quotes a string as one Tcl word whose value is the string (U3). -/
def quote (s : String) : String :=
  String.ofList (quoteList s.toList)

/-! ## Scripts -/

/-- A word of a command: a literal string (rendered by `quote`), or a command
substitution `[w₁ … wₙ]` built from words. -/
inductive Word where
  | lit (s : String)
  | subst (words : List Word)
  deriving Inhabited, Repr

/-- A command: its words. -/
structure Cmd where
  words : List Word
  deriving Inhabited, Repr

/-- A script: its commands, evaluated in order. -/
structure Script where
  cmds : List Cmd
  deriving Inhabited, Repr

mutual
/-- Tcl source of a word. -/
def Word.render : Word → String
  | .lit s => quote s
  | .subst ws => "[" ++ Word.renderList ws ++ "]"

/-- Tcl source of a list of words, separated by single spaces. -/
def Word.renderList : List Word → String
  | [] => ""
  | [w] => w.render
  | w :: ws => w.render ++ " " ++ Word.renderList ws
end

/-- Tcl source of a command (without its terminator). -/
def Cmd.render (c : Cmd) : String :=
  Word.renderList c.words

/-- Tcl source of a script: every command followed by a newline. -/
def Script.render (s : Script) : String :=
  String.join (s.cmds.map fun c => c.render ++ "\n")

/-- The command whose words are the given literal strings. -/
def Cmd.ofStrings (ss : List String) : Cmd :=
  ⟨ss.map Word.lit⟩

/-- The script whose commands have the given literal words. -/
def Script.ofStrings (sss : List (List String)) : Script :=
  ⟨sss.map Cmd.ofStrings⟩

/-- `Cmd.ofStrings` of command name and arguments, the usual way to build a command. -/
def cmd (ss : List String) : Cmd :=
  Cmd.ofStrings ss

/-- String-level reading of one word: the word's value and the rest of the source. -/
def parseWordStr (src : String) : Option (String × String) :=
  (parseWord src.toList).map fun (w, r) => (String.ofList w, String.ofList r)

end SafePdf.Shell.App.Tcl
