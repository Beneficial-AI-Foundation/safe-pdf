import SafePdf.Shell.Views.Common

/-!
# `objects` view (Plan.md §6 MVP / visibility track, row M1; task 1.12)

Pretty-printed object tree of every indirect object in a file, diffable against
`qpdf --json`.

**Object discovery.** Phase 1 has no cross-reference table yet (Phase 2), so this unverified
shell code finds objects by a linear token scan: it lexes from offset 0 with
`Core.Lex.next`, and wherever the token stream reads `int n`, `int g`, keyword `obj` it calls
`SafePdf.parseIndirectAt` at the start of the `n` token. On success it resumes after
`endobj` (so stream data is skipped); on failure it records the error and resumes after the
`obj` keyword, except that a failed stream object (`<< … >> stream`) resumes after the next
`endstream` (or at end of input if there is none), so binary stream data is never lexed
(task 1.14: lexing binary data with unbalanced `(` is quadratic, since each unterminated
literal string runs to the end of the input and the scan then skips one byte). A lexer error
skips one byte. Every step advances at least one byte, and the loop carries fuel
`bytes.size + 1`.

**Indirect `/Length`.** A second pass re-parses the objects that failed with `unsupported:
indirect /Length` through `Core.Xref.Length.parseIndirectResolved`, with the scanned headers
(last header per object number) standing in for the cross-reference table.

Later definitions of the same `(num, gen)` win (incremental updates): only the last
occurrence of each pair is shown unless `--all` is given.

**JSON contract** (`--json`, consumed by `Tests/differential/objects.py`, task 1.11): one
line per indirect object, `{"num": N, "gen": G, "offset": O, "value": V}` or
`{"num": N, "gen": G, "offset": O, "error": "message"}`, then
`{"summary": {"objects": K, "errors": E}}`. `V` follows qpdf's JSON v2 conventions: strings
are `"b:<lowercase hex>"`, names `"/Name"` with `#xx` escapes, refs `"N G R"`, reals exact
decimal text with a `.`, streams `{"stream": {"dict": …, "length": L}}`.
-/

namespace SafePdf.Shell.Views.Objects

open SafePdf.Shell

/-! ## Discovery -/

/-- What parsing one discovered indirect object produced. -/
inductive Outcome where
  /-- The object parsed. -/
  | ok (io : IndirectObject)
  /-- `parseIndirectAt` failed. -/
  | err (e : Error)

/-- One `n g obj` header found by the scan. -/
structure Found where
  /-- Object number from the header tokens. -/
  num : Nat
  /-- Generation number from the header tokens. -/
  gen : Nat
  /-- Byte offset of the object-number token. -/
  offset : Nat
  /-- The parse result. -/
  outcome : Outcome

/-- The bytes of the keyword `obj`. -/
def objKeyword : List UInt8 := [111, 98, 106]

/-- Does `pat` occur in `bytes` at offset `i`? -/
def matchesAt (bytes : ByteArray) (i : Nat) : List UInt8 → Bool
  | [] => true
  | b :: rest => bytes[i]? == some b && matchesAt bytes (i + 1) rest

/-- First offset `≥ i` where `pat` occurs, searching at most `fuel` offsets. -/
def findFrom (bytes : ByteArray) (pat : List UInt8) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    if i ≥ bytes.size then none
    else if matchesAt bytes i pat then some i
    else findFrom bytes pat fuel (i + 1)

/-- The bytes of the keyword `endstream`. -/
def endstreamKeyword : List UInt8 := [101, 110, 100, 115, 116, 114, 101, 97, 109]

/-- Where to resume after a failed object whose header ended at `p3`. If the object is a
stream (`<< … >> stream`), its data must not be lexed (binary data with unbalanced `(` makes
every lexer attempt run to the end of the input, which is quadratic): resume after the next
`endstream`, or at the end of the input if there is none. Otherwise resume at `p3`. -/
def resumeAfterError (limits : Limits) (bytes : ByteArray) (p3 : Nat) : Nat :=
  match SafePdf.parseObjectAt limits bytes p3 with
  | .ok (.dict _, r) =>
    match Core.Lex.next bytes r with
    | .ok (some (.keyword kw, r2)) =>
      if kw == Core.ObjParse.kwStream then
        match findFrom bytes endstreamKeyword (bytes.size + 1) r2 with
        | some i => i + endstreamKeyword.length
        | none => bytes.size
      else p3
    | _ => p3
  | _ => p3

/-- Linear scan for `n g obj` headers from `pos`, with `fuel` steps (each advances at least
one byte). -/
def scan (limits : Limits) (bytes : ByteArray) : Nat → Nat → Array Found → Array Found
  | 0, _, acc => acc
  | fuel + 1, pos, acc =>
    match Core.Lex.next bytes pos with
    | .error e => scan limits bytes fuel (max (e.offset + 1) (pos + 1)) acc
    | .ok none => acc
    | .ok (some (tok, p1)) =>
      let skip := max p1 (pos + 1)
      let header : Option (Nat × Nat × Nat) :=
        match tok with
        | .int n =>
          if n < 0 then none else
          match Core.Lex.next bytes p1 with
          | .ok (some (.int g, p2)) =>
            if g < 0 then none else
            match Core.Lex.next bytes p2 with
            | .ok (some (.keyword kw, p3)) =>
              if kw == objKeyword then some (n.toNat, g.toNat, p3) else none
            | _ => none
          | _ => none
        | _ => none
      match header with
      | none => scan limits bytes fuel skip acc
      | some (n, g, p3) =>
        let start := Core.Lex.skipWs bytes pos false
        match SafePdf.parseIndirectAt limits bytes start with
        | .ok (io, p4) =>
          scan limits bytes fuel (max p4 (pos + 1))
            (acc.push { num := n, gen := g, offset := start, outcome := .ok io })
        | .error e =>
          scan limits bytes fuel (max (resumeAfterError limits bytes p3) (pos + 1))
            (acc.push { num := n, gen := g, offset := start, outcome := .err e })

/-- A cross-reference substitute built from the scan: for each object number, the generation
and offset of its last header in file order, sorted by object number. -/
def headerTable (fs : Array Found) : Array (Nat × Nat × Nat) :=
  let indexed := (List.range fs.size).zip fs.toList
  -- Stable sort by object number; within a number, file order is kept.
  let sorted := indexed.mergeSort fun a b => a.2.num ≤ b.2.num
  let rec lasts : List (Nat × Found) → List (Nat × Nat × Nat)
    | [] => []
    | [a] => [(a.2.num, a.2.gen, a.2.offset)]
    | a :: b :: rest =>
      if a.2.num == b.2.num then lasts (b :: rest)
      else (a.2.num, a.2.gen, a.2.offset) :: lasts (b :: rest)
  (lasts sorted).toArray

/-- Lookup in a `headerTable` by binary search. -/
def tableLookup (t : Array (Nat × Nat × Nat)) (n : Nat) : Option Core.Xref.XrefEntry :=
  if t.isEmpty then none else
  match t.binSearch (n, 0, 0) (fun a b => a.1 < b.1) with
  | some (_, g, off) => some (.inUse off g)
  | none => none

/-- Re-parse an object that failed only because its stream `/Length` is indirect, resolving
the reference through the scanned header table (`Core.Xref.Length.parseIndirectResolved`). -/
def resolveFound (limits : Limits) (bytes : ByteArray) (t : Array (Nat × Nat × Nat))
    (f : Found) : Found :=
  match f.outcome with
  | .err (.unsupported what) =>
    if what == "indirect /Length" then
      match Core.Xref.Length.parseIndirectResolved (tableLookup t) limits bytes t.size f.offset
      with
      | .ok (io, _) => { f with outcome := .ok io }
      | .error e => { f with outcome := .err e }
    else f
  | _ => f

/-- All `n g obj` headers in `bytes`, in file order. Streams with an indirect `/Length` are
resolved in a second pass against the offsets of all headers found. -/
def discover (limits : Limits) (bytes : ByteArray) : Array Found :=
  let found := scan limits bytes (bytes.size + 1) 0 #[]
  let t := headerTable found
  found.map (resolveFound limits bytes t)

/-- Keep only the last occurrence of each `(num, gen)`, preserving file order. -/
def lastOnly (fs : Array Found) : List Found :=
  let indexed := (List.range fs.size).zip fs.toList
  let key (p : Nat × Found) : Nat × Nat := (p.2.num, p.2.gen)
  -- Stable sort by key; within a key, file order is kept, so the last one is the winner.
  let sorted := indexed.mergeSort fun a b =>
    let (ka, kb) := (key a, key b)
    ka.1 < kb.1 || (ka.1 == kb.1 && ka.2 ≤ kb.2)
  let rec winners : List (Nat × Found) → List Nat
    | [] => []
    | [a] => [a.1]
    | a :: b :: rest =>
      if key a == key b then winners (b :: rest) else a.1 :: winners (b :: rest)
  let keep := (winners sorted).mergeSort (· ≤ ·)
  let rec pick : List Nat → List (Nat × Found) → List Found
    | [], _ => []
    | _, [] => []
    | k :: ks, (i, f) :: rest =>
      if k == i then f :: pick ks rest else pick (k :: ks) rest
  pick keep indexed

/-! ## Shared rendering -/

/-- Exact decimal text of `mantissa · 10^(-scale)`, always with a `.` and no exponent:
`⟨-35, 1⟩` → `-3.5`, `⟨5, 3⟩` → `0.005`, `⟨5, 0⟩` → `5.0`. -/
def decimalText (d : Decimal) : String :=
  let sign := if d.mantissa < 0 then "-" else ""
  let digits := toString d.mantissa.natAbs
  if d.scale == 0 then sign ++ digits ++ ".0"
  else
    let padded := padLeft (d.scale + 1) '0' digits
    let intLen := padded.length - d.scale
    sign ++ String.ofList (padded.toList.take intLen) ++ "." ++
      String.ofList (padded.toList.drop intLen)

/-- Two lowercase hex digits for a byte. -/
def hexByte (b : UInt8) : String :=
  (hexDigit (b.toNat / 16)).toString ++ (hexDigit (b.toNat % 16)).toString

/-- Lowercase hex of a byte list. -/
def hexText (bs : List UInt8) : String := String.join (bs.map hexByte)

/-- Does a name byte need `#xx`? Outside 0x21–0x7E, a delimiter, or `#`. -/
def nameNeedsEscape (b : UInt8) : Bool :=
  b < 0x21 || b > 0x7E || "()<>[]{}/%#".toList.contains (Char.ofNat b.toNat)

/-- `/Name` with `#xx` (lowercase) escapes; always ASCII. -/
def nameText (n : Name) : String :=
  "/" ++ String.join (n.bytes.map fun b =>
    if nameNeedsEscape b then "#" ++ hexByte b else (Char.ofNat b.toNat).toString)

/-! ## JSON -/

mutual
/-- qpdf-JSON-v2-style encoding of a direct object. -/
def jsonValue : PdfObject → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .int i => toString i
  | .real d => decimalText d
  | .string s => jsonString ("b:" ++ hexText s)
  | .name n => jsonString (nameText n)
  | .ref n g => jsonString s!"{n} {g} R"
  | .array xs => "[" ++ ", ".intercalate (jsonItems xs) ++ "]"
  | .dict d => "{" ++ ", ".intercalate (jsonEntries d) ++ "}"

/-- Encoded array items. -/
def jsonItems : List PdfObject → List String
  | [] => []
  | x :: xs => jsonValue x :: jsonItems xs

/-- Encoded `"/Key": value` dictionary entries, in source order. -/
def jsonEntries : List (Name × PdfObject) → List String
  | [] => []
  | (k, v) :: rest => (jsonString (nameText k) ++ ": " ++ jsonValue v) :: jsonEntries rest
end

/-- Encoding of an indirect object's body. -/
def jsonBody : IndirectBody → String
  | .obj o => jsonValue o
  | .stream st =>
    jsonObject [("stream", jsonObject [("dict", jsonValue (.dict st.dict)),
                                       ("length", toString st.data.size)])]

/-- One JSON line for a discovered object. -/
def jsonLine (f : Found) : String :=
  let head := [("num", toString f.num), ("gen", toString f.gen), ("offset", toString f.offset)]
  match f.outcome with
  | .ok io => jsonObject (head ++ [("value", jsonBody io.body)])
  | .err e => jsonObject (head ++ [("error", jsonString (renderError e))])

/-! ## Text -/

/-- Is every byte printable ASCII (0x20–0x7E)? -/
def printable (s : List UInt8) : Bool := s.all fun b => 0x20 ≤ b && b ≤ 0x7E

/-- Display form of a string: `(text)` (with `\`, `(`, `)` backslash-escaped) when all bytes
are printable ASCII, else `<hex>`. -/
def stringText (s : List UInt8) : String :=
  if printable s then
    "(" ++ String.join (s.map fun b =>
      let c := Char.ofNat b.toNat
      if c == '(' || c == ')' || c == '\\' then "\\" ++ c.toString else c.toString) ++ ")"
  else "<" ++ hexText s ++ ">"

/-- Single-line text of a scalar; `none` for arrays and dictionaries. -/
def scalarText : PdfObject → Option String
  | .null => some "null"
  | .bool b => some (if b then "true" else "false")
  | .int i => some (toString i)
  | .real d => some (decimalText d)
  | .string s => some (stringText s)
  | .name n => some (nameText n)
  | .ref n g => some s!"{n} {g} R"
  | .array _ | .dict _ => none

/-- Arrays of at most this many scalars print on one line. -/
def inlineArrayMax : Nat := 8

/-- Single-line text if the object is a scalar, an empty dictionary, or a short array of
scalars. -/
def inlineText : PdfObject → Option String
  | .array xs =>
    if xs.length ≤ inlineArrayMax then
      match xs.mapM scalarText with
      | some ss => some ("[" ++ " ".intercalate ss ++ "]")
      | none => none
    else none
  | .dict [] => some "<< >>"
  | o => scalarText o

/-- `n` spaces. -/
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

mutual
/-- Indented lines for an object. -/
def textLines (ind : Nat) : PdfObject → List String
  | .array xs =>
    match inlineText (.array xs) with
    | some s => [spaces ind ++ s]
    | none => [spaces ind ++ "["] ++ textItems (ind + 2) xs ++ [spaces ind ++ "]"]
  | .dict d =>
    match inlineText (.dict d) with
    | some s => [spaces ind ++ s]
    | none => [spaces ind ++ "<<"] ++ textEntries (ind + 2) d ++ [spaces ind ++ ">>"]
  | o => [spaces ind ++ (scalarText o).getD ""]

/-- Lines for array items, one item after another. -/
def textItems (ind : Nat) : List PdfObject → List String
  | [] => []
  | x :: xs => textLines ind x ++ textItems ind xs

/-- Lines for dictionary entries, one key per line; a nested value that does not fit on the
key's line follows it, indented further. -/
def textEntries (ind : Nat) : List (Name × PdfObject) → List String
  | [] => []
  | (k, v) :: rest =>
    let here := match inlineText v with
      | some s => [spaces ind ++ nameText k ++ " " ++ s]
      | none => (spaces ind ++ nameText k) :: textLines (ind + 2) v
    here ++ textEntries ind rest
end

/-- Text block for one discovered object. -/
def textBlock (f : Found) : List String :=
  let head := s!"{f.num} {f.gen} obj @{f.offset}"
  match f.outcome with
  | .ok io =>
    match io.body with
    | .obj o => head :: textLines 2 o
    | .stream st => head :: textLines 2 (.dict st.dict) ++ [s!"  stream <{st.data.size} bytes>"]
  | .err e => [head, s!"  error: {renderError e}"]

/-! ## View -/

/-- Number of discovered objects that failed to parse. -/
def errorCount (fs : List Found) : Nat :=
  (fs.filter fun f => match f.outcome with | .err _ => true | .ok _ => false).length

/-- The `objects` view. -/
def view : View where
  name := "objects"
  description := "pretty-printed tree of every indirect object (linear scan; --all keeps \
    superseded definitions)"
  run cfg i := do
    let found := discover cfg.limits i.bytes
    let shown := if cfg.all then found.toList else lastOnly found
    let errs := errorCount shown
    let ok := shown.length - errs
    if cfg.json then
      for f in shown do IO.println (jsonLine f)
      IO.println (jsonObject [("summary", jsonObject [("objects", toString ok),
                                                      ("errors", toString errs)])])
    else
      for f in shown do
        (textBlock f).forM IO.println
      IO.println s!"objects: {ok} found, {errs} errors"

end SafePdf.Shell.Views.Objects
