import SafePdf.Core.Lex
import SafePdf.Core.Font.Encoding

/-!
# ToUnicode CMaps (Plan.md §6 Phase 6, task 6.5; ISO 32000-2 §9.10.3, §9.7.6.2)

A total, bounded parser for the CMap programs of a font's `/ToUnicode` stream (and, for their
`codespacerange` only, of embedded Type0 `/Encoding` CMaps), and the decoding of a shown
string into character codes and Unicode text. The format is a PostScript subset (Adobe Technical
Note #5014 and #5411); this module does not run PostScript: it scans the token stream for the
four operator groups text extraction needs.

## Tokens

The PDF lexer `Core.Lex.next` fits the CMap syntax (hex strings, names, numbers, `[ ]`,
`<< >>`, keywords). It is run leniently (`tokenize`): a lexical error skips one byte past the
offending token's start and lexing continues, so a broken CMap never fails, it only loses the
damaged entries. At most `maxTokens` tokens are read (2²⁰; the input is already bounded by
`Limits.maxDecodedStreamBytes`), so the work is linear in `min(size, maxTokens)`.

## Operators

* `n begincodespacerange <lo> <hi> … endcodespacerange`: a code range of `lo.length` bytes
  (1–4; ranges with mismatched or longer bounds are dropped). Ranges are per-byte rectangles
  (§9.7.6.2): byte `i` of a code must lie in `lo[i]..hi[i]`.
* `n beginbfchar <src> <dst> … endbfchar`: `dst` is a hex string in UTF-16BE (surrogate pairs
  combined; a lone surrogate becomes U+FFFD; a one-byte destination is taken as a Latin-1
  character), or a glyph name (mapped by the Adobe Glyph List, `glyphToUnicode`).
* `n beginbfrange <lo> <hi> <dst> … endbfrange`: code `c` in `lo..hi` (as big-endian numbers
  of equal length) maps to `dst` with its value increased by `c − lo` (the "increment of the
  last byte" of §9.10.3, carrying into the previous bytes when it overflows, as producers that
  exceed one byte expect); the array form `<lo> <hi> [<d₀> <d₁> …]` maps `lo + i` to `dᵢ`.
* `/Name usecmap`: recorded (`CMap.usecmap`) but not followed — predefined CMaps are known
  by name only and nothing external is loaded.
* Everything else (`begincmap`, `CIDSystemInfo`, `cidrange`, `notdefrange`, …) is skipped.

## Caps

At most `maxEntries` (2¹⁷) entries (codespace ranges, `bfchar`s and `bfrange`s together); later
entries are dropped and `CMap.truncated` is set. Ranges are stored, never expanded, so a range
`<00000000> <FFFFFFFF>` costs one entry. Both caps are module constants: `Limits` has no
font-specific fields (the orchestrator may move them there).

## Decoding

`CMap.codes` splits a string into codes (§9.7.6.2): at each position the shortest
codespace range of length `n` that matches the next `n` bytes wins; if none matches, the
shortest codespace length is taken (a partial match); without any codespace, the length of the
first `bfchar`/`bfrange` source, else 1. Each code has 1–4 bytes, never runs past the input,
and the codes concatenate back to the input (`codes_flatten`). `CMap.lookup` looks a code up
in the `bfchar` table (sorted once, binary search), then in the ranges (file order).

## Theorems

`tokenize_length_le` (at most `maxTokens` tokens), `parse_entries_le_tokens` (entries ≤ tokens
read) and `parse_entries_le_max`, `codes_flatten` and `decode_flatten` (decoding consumes the
input exactly), `codes_ne_nil` (every code is non-empty). `parse` is total by construction
(a fold over a finite token list).
-/

namespace SafePdf.Core.Font.CMap

open SafePdf

/-! ## Tokens -/

/-- Maximum number of tokens read from one CMap stream. -/
def maxTokens : Nat := 1 <<< 20

/-- Maximum number of entries (codespace ranges, `bfchar`s, `bfrange`s) kept per CMap. -/
def maxEntries : Nat := 1 <<< 17

/-- Lenient lexing with fuel: at most `fuel` tokens; a lexical error skips past the offending
byte. -/
def tokenizeAux (bytes : ByteArray) : Nat → Nat → List Token → List Token
  | 0, _, acc => acc.reverse
  | fuel + 1, pos, acc =>
    match Lex.next bytes pos with
    | .ok none => acc.reverse
    | .ok (some (t, pos')) => tokenizeAux bytes fuel pos' (t :: acc)
    | .error e =>
      if bytes.size ≤ pos then acc.reverse
      else tokenizeAux bytes fuel (max (pos + 1) (e.offset + 1)) acc

/-- The tokens of a CMap program (at most `maxTokens`), errors skipped. -/
def tokenize (bytes : ByteArray) : List Token := tokenizeAux bytes maxTokens 0 []

/-- `tokenizeAux` adds at most `fuel` tokens. -/
theorem tokenizeAux_length_le (bytes : ByteArray) :
    ∀ (fuel pos : Nat) (acc : List Token),
      (tokenizeAux bytes fuel pos acc).length ≤ fuel + acc.length
  | 0, _, acc => by simp [tokenizeAux]
  | fuel + 1, pos, acc => by
    unfold tokenizeAux
    split
    · simp
    · rename_i t pos' _
      have := tokenizeAux_length_le bytes fuel pos' (t :: acc)
      simp at this ⊢; omega
    · split
      · simp
      · rename_i e _ _
        have := tokenizeAux_length_le bytes fuel (max (pos + 1) (e.offset + 1)) acc
        omega

/-- At most `maxTokens` tokens are produced. -/
theorem tokenize_length_le (bytes : ByteArray) : (tokenize bytes).length ≤ maxTokens := by
  have := tokenizeAux_length_le bytes maxTokens 0 []
  simpa [tokenize] using this

/-! ## Unicode destinations -/

/-- The replacement character U+FFFD. -/
def replacement : Char := Char.ofNat 0xFFFD

/-- Decode UTF-16BE (§9.10.3): surrogate pairs combined, a lone surrogate is U+FFFD, a single
trailing byte is a Latin-1 character. -/
def utf16 : List UInt8 → List Char
  | [] => []
  | [b] => [Char.ofNat b.toNat]
  | h :: l :: rest =>
    let u := h.toNat * 256 + l.toNat
    if 0xD800 ≤ u ∧ u ≤ 0xDBFF then
      match hr : rest with
      | h2 :: l2 :: rest' =>
        let u2 := h2.toNat * 256 + l2.toNat
        if 0xDC00 ≤ u2 ∧ u2 ≤ 0xDFFF then
          Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (u2 - 0xDC00)) :: utf16 rest'
        else replacement :: utf16 rest
      | _ => replacement :: utf16 rest
    else if 0xDC00 ≤ u ∧ u ≤ 0xDFFF then replacement :: utf16 rest
    else Char.ofNat u :: utf16 rest
termination_by bs => bs.length
decreasing_by all_goals (simp_wf; (try subst hr); (try simp); (try omega))

/-- A UTF-16BE destination string as text. -/
def ofUtf16 (bs : List UInt8) : String := String.ofList (utf16 bs)

/-- Big-endian value of a byte string. -/
def beValue (bs : List UInt8) : Nat := bs.foldl (fun a b => a * 256 + b.toNat) 0

/-- `n` as a big-endian byte string of length `len` (mod 256^len). -/
def beBytes (len n : Nat) : List UInt8 :=
  (List.range len).reverse.map fun i => UInt8.ofNat ((n / 256 ^ i) % 256)

/-- A lookup key unique per byte string (a leading 1 marks the length). -/
def keyOf (bs : List UInt8) : Nat := bs.foldl (fun a b => a * 256 + b.toNat) 1

/-! ## The CMap -/

/-- A codespace range: per-byte bounds, `lo.length = hi.length ∈ 1..4`. -/
structure CodeRange where
  /-- Low bytes. -/
  lo : List UInt8
  /-- High bytes. -/
  hi : List UInt8
  deriving Repr, Inhabited, DecidableEq

/-- The destination of a `bfrange`. -/
inductive RangeDst where
  /-- A UTF-16BE base string, incremented by the code's offset. -/
  | base (bytes : List UInt8)
  /-- The array form: one destination per code. -/
  | array (dsts : Array String)
  deriving Repr, Inhabited

/-- A `bfrange` entry. -/
structure BfRange where
  /-- First code. -/
  lo : List UInt8
  /-- Last code (same length as `lo`). -/
  hi : List UInt8
  /-- Destination. -/
  dst : RangeDst
  deriving Repr, Inhabited

/-- A parsed ToUnicode CMap. -/
structure CMap where
  /-- Codespace ranges, in file order. -/
  codespace : List CodeRange := []
  /-- `bfchar` entries (source code, Unicode text), in file order. -/
  chars : List (List UInt8 × String) := []
  /-- `bfrange` entries, in file order. -/
  ranges : List BfRange := []
  /-- The name given to `usecmap`, if any (not followed). -/
  usecmap : Option String := none
  /-- Whether entries were dropped at `maxEntries`. -/
  truncated : Bool := false
  /-- `chars` as `(keyOf src, text)`, sorted by key (built by `parse`). -/
  table : Array (Nat × String) := #[]
  deriving Repr, Inhabited

/-- Number of stored entries. -/
def CMap.entries (m : CMap) : Nat := m.codespace.length + m.chars.length + m.ranges.length

/-! ## Parsing -/

/-- The operator section being read. -/
inductive Mode where
  /-- Outside any section. -/
  | none
  /-- `begincodespacerange`. -/
  | codespace
  /-- `beginbfchar`. -/
  | bfchar
  /-- `beginbfrange`. -/
  | bfrange
  deriving Repr, Inhabited, DecidableEq


/-- One parsed entry, applied to the CMap under the cap. -/
inductive Entry where
  /-- A codespace range. -/
  | cs (r : CodeRange)
  /-- A `bfchar`. -/
  | ch (src : List UInt8) (dst : String)
  /-- A `bfrange`. -/
  | rg (r : BfRange)
  /-- A `usecmap` name. -/
  | use (n : String)

/-- Scanner state: the section and pending operands (no entries: those live in `PState`). -/
structure SState where
  /-- Current section. -/
  mode : Mode := .none
  /-- Pending code operands (at most two, most recent first). -/
  codes : List (List UInt8) := []
  /-- Inside the array of an array-form `bfrange`: its elements so far (reversed). -/
  arr : Option (List String) := none
  /-- The previous token (for `usecmap`). -/
  prev : Option Token := none
  deriving Inhabited

/-- Parser state: scanner state and the CMap built so far (`table` empty until the end). -/
structure PState where
  /-- Scanner state. -/
  s : SState := {}
  /-- The CMap so far. -/
  cmap : CMap := {}
  deriving Inhabited

/-- The bytes of a string token. -/
def strBytes? : Token → Option (List UInt8)
  | .hexString b => some b
  | .litString b => some b
  | _ => none

/-- A `bfchar`/array destination: UTF-16BE string, or a glyph name. -/
def dstText? : Token → Option String
  | .hexString b => some (ofUtf16 b)
  | .litString b => some (ofUtf16 b)
  | .name n => some ((glyphToUnicode (glyphNameOf n.bytes)).getD (String.ofList [replacement]))
  | _ => none

/-- Whether a source code has an acceptable length (1–4 bytes). -/
def okCode (bs : List UInt8) : Bool := 1 ≤ bs.length && bs.length ≤ 4

/-- Keyword bytes. -/
def kw (s : String) : List UInt8 := s.toUTF8.toList

/-- A range entry when its bounds are acceptable. -/
def rangeEntry (lo hi : List UInt8) (d : RangeDst) : Option Entry :=
  if lo.length == hi.length && okCode lo then some (.rg ⟨lo, hi, d⟩) else none

/-- A keyword. -/
def scanKw (s : SState) (k : List UInt8) : SState × Option Entry :=
  if k == kw "begincodespacerange" then ({ s with mode := .codespace, codes := [], arr := none }, none)
  else if k == kw "beginbfchar" then ({ s with mode := .bfchar, codes := [], arr := none }, none)
  else if k == kw "beginbfrange" then ({ s with mode := .bfrange, codes := [], arr := none }, none)
  else if k == kw "endcodespacerange" || k == kw "endbfchar" || k == kw "endbfrange" then
    ({ s with mode := .none, codes := [], arr := none }, none)
  else if k == kw "usecmap" then
    match s.prev with
    | some (.name n) => (s, some (.use (glyphNameOf n.bytes)))
    | _ => (s, none)
  else (s, none)

/-- An operand inside a section (not in an array). -/
def scanOperand (s : SState) (t : Token) : SState × Option Entry :=
  match s.mode with
  | .none => (s, none)
  | .codespace =>
    match strBytes? t, s.codes with
    | some hi, [lo] =>
      if lo.length == hi.length && okCode lo then ({ s with codes := [] }, some (.cs ⟨lo, hi⟩))
      else ({ s with codes := [] }, none)
    | some lo, _ => ({ s with codes := [lo] }, none)
    | none, _ => ({ s with codes := [] }, none)
  | .bfchar =>
    match s.codes with
    | [src] =>
      match dstText? t with
      | some d => ({ s with codes := [] }, if okCode src then some (.ch src d) else none)
      | none => ({ s with codes := [] }, none)
    | _ =>
      match strBytes? t with
      | some b => ({ s with codes := [b] }, none)
      | none => ({ s with codes := [] }, none)
  | .bfrange =>
    match s.codes with
    | [hi, lo] =>
      match strBytes? t with
      | some d => ({ s with codes := [] }, rangeEntry lo hi (.base d))
      | none => ({ s with codes := [] }, none)
    | [lo] =>
      match strBytes? t with
      | some hi => ({ s with codes := [hi, lo] }, none)
      | none => ({ s with codes := [] }, none)
    | _ =>
      match strBytes? t with
      | some lo => ({ s with codes := [lo] }, none)
      | none => ({ s with codes := [] }, none)

/-- One token: the new scanner state and at most one entry. -/
def scan (s : SState) (t : Token) : SState × Option Entry :=
  match t with
  | .keyword k => scanKw s k
  | .arrayOpen =>
    if s.mode == .bfrange && s.codes.length == 2 then ({ s with arr := some [] }, none)
    else (s, none)
  | .arrayClose =>
    match s.mode, s.arr, s.codes with
    | .bfrange, some ds, [hi, lo] =>
      ({ s with arr := none, codes := [] }, rangeEntry lo hi (.array ds.reverse.toArray))
    | _, _, _ => ({ s with arr := none, codes := [] }, none)
  | t =>
    match s.arr with
    | some ds =>
      match dstText? t with
      | some d => ({ s with arr := some (d :: ds) }, none)
      | none => (s, none)
    | none => scanOperand s t

/-- Add an entry to the CMap when under the cap, else set `truncated`. -/
def addEntry (m : CMap) : Option Entry → CMap
  | none => m
  | some (.use n) => { m with usecmap := some n }
  | some e =>
    if m.entries < maxEntries then
      match e with
      | .cs r => { m with codespace := m.codespace ++ [r] }
      | .ch src d => { m with chars := m.chars ++ [(src, d)] }
      | .rg r => { m with ranges := m.ranges ++ [r] }
      | .use n => { m with usecmap := some n }
    else { m with truncated := true }

/-- One parser step. -/
def step (st : PState) (t : Token) : PState :=
  ⟨{ (scan st.s t).1 with prev := some t }, addEntry st.cmap (scan st.s t).2⟩

/-- Sort the `bfchar` entries into the lookup table. -/
def buildTable (chars : List (List UInt8 × String)) : Array (Nat × String) :=
  (chars.map fun (c, s) => (keyOf c, s)).toArray.qsort (fun a b => a.1 < b.1)

/-- Parse a token list. Total (a fold). -/
def parseTokens (ts : List Token) : CMap :=
  let m := (ts.foldl step {}).cmap
  { m with table := buildTable m.chars }

/-- **Entry point.** Parse a (decoded) CMap stream. Never fails. -/
def parse (bytes : ByteArray) : CMap := parseTokens (tokenize bytes)

/-! ### Entry bounds -/

/-- Adding an entry adds at most one, and never passes the cap. -/
theorem addEntry_entries (m : CMap) (e : Option Entry) :
    (addEntry m e).entries ≤ m.entries + 1 ∧
    (m.entries ≤ maxEntries → (addEntry m e).entries ≤ maxEntries) := by
  unfold addEntry
  split
  · omega
  · simp [CMap.entries]
  · split
    · rename_i h
      split <;> simp [CMap.entries] at * <;> omega
    · simp [CMap.entries]

/-- The invariant of the fold: entries bounded by the tokens read and by the cap. -/
def Inv (k : Nat) (st : PState) : Prop := st.cmap.entries ≤ k ∧ st.cmap.entries ≤ maxEntries

/-- The fold preserves `Inv`, one token at a time. -/
theorem foldl_inv (ts : List Token) :
    ∀ (st : PState) (k : Nat), Inv k st → Inv (k + ts.length) (ts.foldl step st) := by
  induction ts with
  | nil => intro st k h; simpa using h
  | cons t ts ih =>
    intro st k h
    have h1 := addEntry_entries st.cmap (scan st.s t).2
    have h0 := h.1
    have := ih (step st t) (k + 1) ⟨by simp only [step]; omega, by simp only [step]; exact h1.2 h.2⟩
    simp only [List.foldl, List.length_cons]
    rwa [show k + (ts.length + 1) = k + 1 + ts.length by omega]

private theorem inv_init : Inv 0 ({} : PState) := ⟨by simp [CMap.entries], by simp [CMap.entries]⟩

/-- **Entries ≤ tokens**: a CMap never holds more entries than tokens were read. -/
theorem parseTokens_entries_le (ts : List Token) : (parseTokens ts).entries ≤ ts.length := by
  have := (foldl_inv ts {} 0 inv_init).1
  simpa [parseTokens, CMap.entries] using this

/-- **Entries ≤ tokens of the input** (hence ≤ `maxTokens`, `tokenize_length_le`). -/
theorem parse_entries_le_tokens (bytes : ByteArray) :
    (parse bytes).entries ≤ (tokenize bytes).length :=
  parseTokens_entries_le _

/-- **Entry cap**: at most `maxEntries` entries. -/
theorem parse_entries_le_max (bytes : ByteArray) : (parse bytes).entries ≤ maxEntries := by
  have := (foldl_inv (tokenize bytes) {} 0 inv_init).2
  simpa [parse, parseTokens, CMap.entries] using this

/-! ## Decoding -/

/-- Whether the first `r.lo.length` bytes of `bs` fall in the codespace range `r`. -/
def CodeRange.matches (r : CodeRange) (bs : List UInt8) : Bool :=
  let n := r.lo.length
  n ≤ bs.length &&
    ((bs.take n).zip (r.lo.zip r.hi)).all fun (b, lo, hi) => lo ≤ b && b ≤ hi

/-- The code length (1–4 when the CMap is sane, always ≥ 1 after `max 1`) at the head of
`bs` (see the module doc). -/
def CMap.codeLen (m : CMap) (bs : List UInt8) : Nat :=
  let exact := [1, 2, 3, 4].find? fun n =>
    m.codespace.any fun r => r.lo.length == n && r.matches bs
  match exact with
  | some n => n
  | none =>
    match m.codespace.map (·.lo.length) |>.min? with
    | some n => n
    | none =>
      match m.chars.head?, m.ranges.head? with
      | some (c, _), _ => c.length
      | none, some r => r.lo.length
      | none, none => 1

/-- Split a string into character codes (§9.7.6.2). -/
def CMap.codes (m : CMap) : List UInt8 → List (List UInt8)
  | [] => []
  | b :: bs =>
    let k := m.codeLen (b :: bs) - 1
    (b :: bs.take k) :: m.codes (bs.drop k)
termination_by l => l.length
decreasing_by simp; omega

/-- **Decoding consumes the input**: the codes concatenate to the input. -/
theorem CMap.codes_flatten (m : CMap) : ∀ bs : List UInt8, (m.codes bs).flatten = bs
  | [] => by simp [CMap.codes]
  | b :: bs => by
    rw [CMap.codes]
    simp only [List.flatten_cons, List.cons_append]
    rw [CMap.codes_flatten m (bs.drop _), List.take_append_drop]
termination_by bs => bs.length
decreasing_by simp; omega

/-- Every code is non-empty. -/
theorem CMap.codes_ne_nil (m : CMap) : ∀ bs : List UInt8, ∀ c ∈ m.codes bs, c ≠ []
  | [] => by simp [CMap.codes]
  | b :: bs => by
    rw [CMap.codes]
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with h | h
    · simp [h]
    · exact CMap.codes_ne_nil m _ c h
termination_by bs => bs.length
decreasing_by simp; omega

/-- The Unicode text of one `bfrange` for code `c` (same length as `lo`), if in range. -/
def BfRange.lookup (r : BfRange) (c : List UInt8) : Option String :=
  if c.length == r.lo.length && beValue r.lo ≤ beValue c && beValue c ≤ beValue r.hi then
    let off := beValue c - beValue r.lo
    match r.dst with
    | .base d => some (ofUtf16 (beBytes d.length (beValue d + off)))
    | .array ds => ds[off]?
  else none

/-- The Unicode text of a code: `bfchar` (binary search), then the first matching `bfrange`. -/
def CMap.lookup (m : CMap) (c : List UInt8) : Option String :=
  let k := keyOf c
  match m.table.binSearch (k, "") (fun a b => a.1 < b.1) with
  | some (_, s) => some s
  | none => m.ranges.findSome? (·.lookup c)

/-- Decode a shown string: its codes, each with its Unicode text when mapped. -/
def CMap.decode (m : CMap) (bs : List UInt8) : List (List UInt8 × Option String) :=
  (m.codes bs).map fun c => (c, m.lookup c)

/-- **Decoding consumes the input** (`decode` form). -/
theorem CMap.decode_flatten (m : CMap) (bs : List UInt8) :
    ((m.decode bs).map Prod.fst).flatten = bs := by
  simp [CMap.decode, List.map_map, Function.comp_def, CMap.codes_flatten]

/-! ## Spot checks -/

section Tests

private def b (s : String) : ByteArray := s.toUTF8

private def sample : CMap := parse (b "/CIDInit /ProcSet findresource begin
12 dict begin
begincmap
/CIDSystemInfo << /Registry (Adobe) /Ordering (UCS) /Supplement 0 >> def
/CMapName /Adobe-Identity-UCS def
/CMapType 2 def
1 begincodespacerange
<0000> <FFFF>
endcodespacerange
3 beginbfchar
<0003> <0020>
<0011> <FB01>
<0012> <D835DC00>
endbfchar
2 beginbfrange
<0024> <0026> <0041>
<0030> <0032> [<0066006C> <0078> /eacute]
endbfrange
endcmap
CMapName currentdict /CMap defineresource pop
end
end")

#guard sample.codespace == [⟨[0, 0], [255, 255]⟩]
#guard sample.chars.length == 3 && sample.ranges.length == 2 && sample.entries == 6
#guard sample.decode [0, 3, 0, 0x24, 0, 0x26] ==
  [([0, 3], some " "), ([0, 0x24], some "A"), ([0, 0x26], some "C")]
#guard sample.lookup [0, 0x11] == some (String.ofList [Char.ofNat 0xFB01])
#guard sample.lookup [0, 0x12] == some (String.ofList [Char.ofNat 0x1D400])
#guard sample.lookup [0, 0x30] == some "fl"
#guard sample.lookup [0, 0x32] == some "é"
#guard sample.lookup [0, 0x33] == none
-- odd trailing byte: a 1-byte partial code, still consumed
#guard sample.codes [0, 3, 7] == [[0, 3], [7]]

/-- Mixed 1- and 2-byte codespace (§9.7.6.2 example shape). -/
private def mixed : CMap := parse (b "2 begincodespacerange <00> <80> <8140> <9FFC> endcodespacerange
1 beginbfchar <8141> <3042> endbfchar 1 beginbfrange <41> <42> <0061> endbfrange")

#guard mixed.codes [0x41, 0x81, 0x41, 0x42] == [[0x41], [0x81, 0x41], [0x42]]
#guard (mixed.decode [0x41, 0x81, 0x41]).map (·.2) ==
  [some "a", some (String.ofList [Char.ofNat 0x3042])]
-- broken input: lexical garbage skipped, entries kept
#guard (parse (b "1 beginbfchar <01> <0041> ) endbfchar 1 beginbfchar <02> <0042> endbfchar")).lookup
  [2] == some "B"
#guard (parse (b "/Foo usecmap")).usecmap == some "Foo"
#guard (parse (b "")).codes [1, 2] == [[1], [2]]
-- carry into the previous byte
#guard (parse (b "1 beginbfrange <00> <02> <00FF> endbfrange")).lookup [1] ==
  some (String.ofList [Char.ofNat 0x100])

end Tests

end SafePdf.Core.Font.CMap
