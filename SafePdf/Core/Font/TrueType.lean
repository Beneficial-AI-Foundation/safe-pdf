import SafePdf.Core.Error
import SafePdf.Core.Limits
import SafePdf.Core.Content.GState
import SafePdf.Core.Font.Encoding
import SafePdf.Core.Font.Outline

/-!
# Embedded TrueType fonts (Plan.md §6 Phase 6, task 6.1; ISO 32000-2 §9.6.6.4, §9.9)

Parses an embedded TrueType font program (`/FontFile2`, already Flate-decoded by the caller)
far enough to give **text extraction and glyph positions** what they need, and validates and
exposes the glyph outlines for Phase 7. References are to the *Apple TrueType Reference
Manual* and the *OpenType specification* (`sfnt` container): table directory, `head`, `hhea`,
`hmtx`, `maxp`, `cmap` (formats 0, 4, 6, 12), `post` (formats 1.0, 2.0), `loca`, `glyf`.

Fonts are untrusted input (Plan.md §6: Duqu came in through font parsing), so this module
follows the core discipline: pure, every byte read through a bounded helper (`u8At`, `u16At`,
`u32At`, `i16At`, all `Option`, with `*_some_lt` theorems), every loop structural on a fuel
bounded by a table size, a count read from the font, or a cap.

## Pipeline (`parse`)

1. **Directory.** `sfnt` version `0x00010000` or `'true'` (`'OTTO'` = CFF and `'ttcf'` =
   collection are `Error.unsupported`); at most `maxTables` records, all of which must lie in
   the input (else the directory is malformed). A record whose `offset + length` exceeds the
   input is **skipped** (listed in `TTFont.skipped`); every table used is sliced out of the
   input with `extract` after `findTable_bounds` has established it lies inside, so no table
   parser can read past `bytes.size` (`tableBytes_size`).
2. **Required:** `head` (`unitsPerEm ≠ 0`, `indexToLocFormat ∈ {0, 1}`, font bbox) and `maxp`
   (`numGlyphs ≥ 1`). Missing or malformed → `Error.malformed`.
3. **Optional** (absent or malformed → empty, recorded in `skipped`):
   * `hhea` + `hmtx`: advance widths of the first `min numberOfHMetrics numGlyphs` glyphs
     (fewer if `hmtx` is short); later glyphs repeat the last advance (`advanceOfGlyph`).
   * `cmap`: at most `maxCmaps` encoding records; subtables of formats 0, 4, 6, 12 are kept
     (their headers validated to fit in the table: format 4 needs its four segment arrays,
     format 6 its glyph array, format 12 its groups); other formats are skipped. Lookups
     are lazy over the stored `cmap` bytes; a lookup result `0` or `≥ numGlyphs` is "no
     glyph". Format 4: `seg4Find` scans `endCode` with fuel `segCount`
     (`seg4Find_lt`); an `idRangeOffset` glyph read is bounds-checked like every read.
   * `post`: format 1.0 (the 258 standard Macintosh names) and 2.0 (indices < 258 into
     `stdMacNames`, others into the Pascal-string list, read with fuel = table size); 2.5 and
     3.0 give no names.
   * `loca` + `glyf`: per glyph, `[loca k, loca (k+1))` must be ordered, inside `glyf` and
     not start before the end of the previous accepted glyph (so the glyph ranges are
     disjoint and validation is linear in the `glyf` size). Simple glyphs are fully decoded
     (end points strictly increasing, flags with repeat counts, delta coordinates) and must
     use every point; composites are decoded into `Component`s. A bad glyph is **rejected**
     (listed in `TTFont.rejected`, never fatal). Composite depth is computed by
     `maxCompositeDepth + 1` rounds of `depthRound`: a composite resolves once all its
     components have; one still unresolved after the rounds is cyclic, deeper than
     `maxCompositeDepth`, or refers to a rejected or out-of-range glyph, and is rejected.

## Character → glyph (§9.6.6.4)

`glyphOfCode code symbolic enc`:
* **symbolic**: `(3,0)` with `code`, `0xF000+code`, `0xF100+code`, `0xF200+code`; then
  `(1,0)` with `code`; then `(3,1)` with `code` (a common misuse).
* **nonsymbolic**: the encoding `enc` (default `StandardEncoding`; task 6.5 passes the font's
  `/Encoding` with `/Differences` applied) names a glyph; its Unicode value (Adobe Glyph
  List, `glyphToUnicode`, one code point) is looked up in a Unicode cmap (`glyphOfUnicode`),
  else its MacRoman code in `(1,0)`, else the name in `post`; failing all three, the raw
  code is tried in `(3,0)` (with the `0xF0xx` offsets) and `(1,0)`, but not in `(3,1)`.

`glyphOfUnicode u` tries `(3,10)`, `(0,6)`, `(0,4)`, `(3,1)`, `(0,3)`, `(0,2)`, `(0,1)`,
`(0,0)`.

## Advances

`advanceOfGlyph gid` (font units) and `advanceText code` = `advance / unitsPerEm` as `Fixed`,
rounded once to the nearest `10⁻⁶` (ties up, `roundDiv`). `/Widths` in the PDF font dictionary
take precedence; this is the fallback (task 6.5).

## Outlines (Phase 7)

`outline gid : Option (Array Contour)` with `Contour = Array Point` (`x y : Int`,
`onCurve : Bool`) in font units. Composites are flattened recursively by `outlineAux`, bounded
by `maxCompositeDepth` (structural fuel), a visited list of the glyphs on the current path
(`outlineAux_visited`: a cycle yields `none`), a call budget `maxOutlineCalls` and a point cap
`maxOutlinePoints`. Component transforms are F2Dot14 (`16384 = 1`), applied as
`x' = a·x + c·y`, `y' = b·x + d·y` rounded with `roundDiv`, then the offset (scaled only with
`SCALED_COMPONENT_OFFSET`); point-matching components align parent point `arg1` with child
point `arg2`. Hinting instructions are skipped (stored lengths only, never executed).

## Not covered

Checksums are not verified (real embedded subsets often have wrong ones). `cmap` formats 2,
8, 10, 13, 14, `post` 2.5, `OS/2`, `name`, `kern`, `vhea`/`vmtx`, TrueType collections and
CFF-flavoured OpenType are out of scope (CFF is a separate task).
-/

namespace SafePdf.Core.Font.TrueType

open SafePdf SafePdf.Core.Content SafePdf.Core.Font

/-! ## Bounded reads (big-endian) -/

/-- The byte at `i`, as a `Nat`. -/
def u8At (b : ByteArray) (i : Nat) : Option Nat := b[i]?.map (·.toNat)

/-- The big-endian `uint16` at `i`, built with `UInt16` arithmetic. -/
def u16At (b : ByteArray) (i : Nat) : Option Nat :=
  if h : i + 1 < b.size then
    some ((b[i]'(by omega)).toUInt16 <<< 8 ||| (b[i + 1]'h).toUInt16).toNat
  else none

/-- The big-endian `uint32` at `i`, built with `UInt32` arithmetic. -/
def u32At (b : ByteArray) (i : Nat) : Option Nat :=
  if h : i + 3 < b.size then
    some (((b[i]'(by omega)).toUInt32 <<< 24 ||| (b[i + 1]'(by omega)).toUInt32 <<< 16 |||
      (b[i + 2]'(by omega)).toUInt32 <<< 8 ||| (b[i + 3]'h).toUInt32).toNat)
  else none

/-- Two's-complement value of a 16-bit unsigned value. -/
def toI16 (v : Nat) : Int := if v < 32768 then (v : Int) else (v : Int) - 65536

/-- Two's-complement value of an 8-bit unsigned value. -/
def toI8 (v : Nat) : Int := if v < 128 then (v : Int) else (v : Int) - 256

/-- The big-endian `int16` (`FWord`, `F2Dot14` raw) at `i`. -/
def i16At (b : ByteArray) (i : Nat) : Option Int := (u16At b i).map toI16

/-- A successful byte read is in bounds. -/
theorem u8At_some_lt {b : ByteArray} {i v : Nat} (h : u8At b i = some v) : i < b.size := by
  unfold u8At at h
  cases hb : b[i]? with
  | none => rw [hb] at h; cases h
  | some x =>
    rcases (getElem?_eq_some_iff.mp hb) with ⟨hi, _⟩
    exact hi

/-- A successful `uint16` read is in bounds: both bytes `i`, `i + 1` exist. -/
theorem u16At_some_lt {b : ByteArray} {i v : Nat} (h : u16At b i = some v) :
    i + 1 < b.size := by
  unfold u16At at h
  split at h
  · assumption
  · cases h

/-- A successful `uint32` read is in bounds: bytes `i … i + 3` exist. -/
theorem u32At_some_lt {b : ByteArray} {i v : Nat} (h : u32At b i = some v) :
    i + 3 < b.size := by
  unfold u32At at h
  split at h
  · assumption
  · cases h

/-- A successful `int16` read is in bounds. -/
theorem i16At_some_lt {b : ByteArray} {i : Nat} {v : Int} (h : i16At b i = some v) :
    i + 1 < b.size := by
  unfold i16At at h
  cases hu : u16At b i with
  | none => rw [hu] at h; cases h
  | some x => exact u16At_some_lt hu

/-- `uint16` values are below `2¹⁶`. -/
theorem u16At_lt {b : ByteArray} {i v : Nat} (h : u16At b i = some v) : v < 65536 := by
  unfold u16At at h
  split at h
  · cases h; exact UInt16.toNat_lt _
  · cases h

/-! ## Caps -/

/-- Maximum number of table directory records. -/
def maxTables : Nat := 256

/-- Maximum number of `cmap` encoding records. -/
def maxCmaps : Nat := 64

/-- Maximum composite glyph nesting depth (as FreeType, pdf.js use similar bounds). -/
def maxCompositeDepth : Nat := 16

/-- Maximum number of glyph visits when flattening one outline. -/
def maxOutlineCalls : Nat := 4096

/-- Maximum number of points in one flattened outline. -/
def maxOutlinePoints : Nat := 65536

/-! ## Table directory -/

/-- A table directory record: 4-byte tag (as a big-endian number), offset and length. -/
structure TableRec where
  /-- The tag, big-endian (`'cmap'` = `0x636D6170`). -/
  tag : Nat
  /-- Offset from the start of the font. -/
  offset : Nat
  /-- Length in bytes. -/
  length : Nat
  deriving Repr, Inhabited, BEq

/-- The numeric value of a 4-character tag. -/
def tagOf (s : String) : Nat := s.toList.foldl (fun a c => a * 256 + c.toNat) 0

/-- The 4-character spelling of a tag (for messages). -/
def tagName (t : Nat) : String :=
  String.ofList ((List.range 4).reverse.map fun k => Char.ofNat (t / 256 ^ k % 256))

/-- Directory record `k` (at `12 + 16·k`). -/
def readRec (b : ByteArray) (k : Nat) : Option TableRec := do
  let base := 12 + 16 * k
  let tag ← u32At b base
  let offset ← u32At b (base + 8)
  let length ← u32At b (base + 12)
  some ⟨tag, offset, length⟩

/-- Whether a record lies inside an input of `size` bytes. -/
def TableRec.inBounds (r : TableRec) (size : Nat) : Bool := r.offset + r.length ≤ size

/-- The first in-bounds record with tag `tag`. -/
def findTable (b : ByteArray) (recs : List TableRec) (tag : Nat) : Option TableRec :=
  recs.find? fun r => r.tag == tag && r.inBounds b.size

/-- **Directory bounds**: a table found by `findTable` lies inside the input. -/
theorem findTable_bounds {b : ByteArray} {recs : List TableRec} {tag : Nat} {r : TableRec}
    (h : findTable b recs tag = some r) : r.offset + r.length ≤ b.size := by
  unfold findTable at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, TableRec.inBounds, decide_eq_true_eq] at hp
  exact hp.2

/-- The bytes of a table found in the directory. -/
def tableBytes (b : ByteArray) (recs : List TableRec) (tag : Nat) : Option ByteArray :=
  (findTable b recs tag).map fun r => b.extract r.offset (r.offset + r.length)

/-- **No read past the input**: a table slice is exactly the record's `length` bytes of the
input (the record lies inside it, `findTable_bounds`). -/
theorem tableBytes_size {b : ByteArray} {recs : List TableRec} {tag : Nat} {t : ByteArray}
    (h : tableBytes b recs tag = some t) :
    ∃ r, findTable b recs tag = some r ∧ t.size = r.length := by
  unfold tableBytes at h
  cases hf : findTable b recs tag with
  | none => rw [hf] at h; cases h
  | some r =>
    rw [hf] at h
    cases h
    refine ⟨r, rfl, ?_⟩
    have := findTable_bounds hf
    rw [ByteArray.size_extract]
    omega

/-! ## `head`, `maxp`, `hhea`/`hmtx` -/

/-- The fields of `head` that matter here. -/
structure Head where
  /-- `unitsPerEm` (nonzero). -/
  unitsPerEm : Nat
  /-- Font bounding box. -/
  xMin : Int
  /-- Font bounding box. -/
  yMin : Int
  /-- Font bounding box. -/
  xMax : Int
  /-- Font bounding box. -/
  yMax : Int
  /-- `indexToLocFormat = 1` (32-bit `loca` offsets). -/
  longLoca : Bool
  deriving Repr, Inhabited

/-- Turn a missing read into a malformed-input error. -/
def need {α : Type} (o : Option α) (msg : String) : Except Error α :=
  match o with
  | some a => .ok a
  | none => .error (.malformed 0 s!"TrueType: {msg}")

/-- Parse `head` (54 bytes). -/
def parseHead (t : ByteArray) : Except Error Head := do
  let upem ← need (u16At t 18) "head: truncated"
  if upem = 0 then throw (.malformed 0 "TrueType: head: unitsPerEm = 0")
  let xMin ← need (i16At t 36) "head: truncated"
  let yMin ← need (i16At t 38) "head: truncated"
  let xMax ← need (i16At t 40) "head: truncated"
  let yMax ← need (i16At t 42) "head: truncated"
  let fmt ← need (i16At t 50) "head: truncated"
  if fmt ≠ 0 ∧ fmt ≠ 1 then throw (.malformed 0 "TrueType: head: bad indexToLocFormat")
  return { unitsPerEm := upem, xMin, yMin, xMax, yMax, longLoca := fmt == 1 }

/-- Advance widths from `hhea.numberOfHMetrics` and `hmtx`: the first
`min numberOfHMetrics numGlyphs` entries that fit in `hmtx`. -/
def parseAdvances (hhea hmtx : ByteArray) (numGlyphs : Nat) : Array Nat :=
  let nh := (u16At hhea 34).getD 0
  let n := min (min nh numGlyphs) (hmtx.size / 4)
  ((List.range n).filterMap fun k => u16At hmtx (4 * k)).toArray

/-! ## `cmap` -/

/-- A supported `cmap` subtable, located at byte `base` of the `cmap` table. -/
inductive Sub where
  /-- Format 0: byte encoding table (256 one-byte glyph ids at `base + 6`). -/
  | f0 (base : Nat)
  /-- Format 4: segment mapping to delta values, `segCount` segments. -/
  | f4 (base segCount : Nat)
  /-- Format 6: trimmed table mapping `[first, first + count)`. -/
  | f6 (base first count : Nat)
  /-- Format 12: segmented coverage, `nGroups` groups. -/
  | f12 (base nGroups : Nat)
  deriving Repr, Inhabited

/-- A `cmap` encoding record with a supported subtable. -/
structure Cmap where
  /-- Platform ID (0 Unicode, 1 Macintosh, 3 Windows). -/
  platform : Nat
  /-- Encoding ID. -/
  encoding : Nat
  /-- The subtable. -/
  sub : Sub
  deriving Repr, Inhabited

/-- Validate the subtable at `base` (its header and arrays must fit in the `cmap` table);
`none` for unsupported formats or a subtable that does not fit. -/
def parseSub (d : ByteArray) (base : Nat) : Option Sub := do
  let fmt ← u16At d base
  if fmt = 0 then
    if base + 262 ≤ d.size then some (.f0 base) else none
  else if fmt = 4 then
    let segX2 ← u16At d (base + 6)
    let seg := segX2 / 2
    if 0 < seg ∧ base + 16 + 8 * seg ≤ d.size then some (.f4 base seg) else none
  else if fmt = 6 then
    let first ← u16At d (base + 6)
    let count ← u16At d (base + 8)
    if base + 10 + 2 * count ≤ d.size then some (.f6 base first count) else none
  else if fmt = 12 then
    let n ← u32At d (base + 12)
    if base + 16 + 12 * n ≤ d.size then some (.f12 base n) else none
  else none

/-- The encoding records of a `cmap` table (at most `maxCmaps`), keeping supported subtables.
Returns the records kept and the number skipped. -/
def parseCmap (d : ByteArray) : List Cmap × Nat :=
  let n := min ((u16At d 2).getD 0) maxCmaps
  let recs := (List.range n).map fun k => do
    let p ← u16At d (4 + 8 * k)
    let e ← u16At d (4 + 8 * k + 2)
    let off ← u32At d (4 + 8 * k + 4)
    let s ← parseSub d off
    some (Cmap.mk p e s)
  (recs.filterMap id, (recs.filter Option.isNone).length)

/-- Format 4 segment search: the first segment `i ≥ i₀` with `endCode[i] ≥ c`, scanning at
most `fuel` segments (called with `fuel = segCount`). -/
def seg4Find (d : ByteArray) (base seg c : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    if i < seg then
      match u16At d (base + 14 + 2 * i) with
      | some e => if c ≤ e then some i else seg4Find d base seg c fuel (i + 1)
      | none => none
    else none

/-- **Format 4 walk bound**: the segment found is a valid segment index (`< segCount`). -/
theorem seg4Find_lt (d : ByteArray) (base seg c : Nat) :
    ∀ (fuel i j : Nat), seg4Find d base seg c fuel i = some j → j < seg := by
  intro fuel
  induction fuel with
  | zero => intro i j h; simp only [seg4Find] at h; cases h
  | succ fuel ih =>
    intro i j h
    simp only [seg4Find] at h
    split at h
    · split at h
      · split at h
        · cases h; assumption
        · exact ih _ _ h
      · cases h
    · cases h

/-- Format 4 lookup (raw result; `0` = missing glyph). -/
def lookup4 (d : ByteArray) (base seg c : Nat) : Option Nat := do
  let i ← seg4Find d base seg c seg 0
  let start ← u16At d (base + 16 + 2 * seg + 2 * i)
  if c < start then none else
  let delta ← u16At d (base + 16 + 4 * seg + 2 * i)
  let roPos := base + 16 + 6 * seg + 2 * i
  let ro ← u16At d roPos
  if ro = 0 then some ((c + delta) % 65536)
  else
    let g ← u16At d (roPos + ro + 2 * (c - start))
    if g = 0 then some 0 else some ((g + delta) % 65536)

/-- Format 12 group search over at most `fuel` groups (called with `fuel = nGroups`). -/
def group12Find (d : ByteArray) (base c : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, k =>
    match u32At d (base + 16 + 12 * k), u32At d (base + 20 + 12 * k),
        u32At d (base + 24 + 12 * k) with
    | some s, some e, some g =>
      if s ≤ c ∧ c ≤ e then some (g + (c - s)) else group12Find d base c fuel (k + 1)
    | _, _, _ => none

/-- Raw lookup of `c` in a subtable of the `cmap` bytes `d`. -/
def Sub.lookup (d : ByteArray) : Sub → Nat → Option Nat
  | .f0 base, c => if c < 256 then u8At d (base + 6 + c) else none
  | .f4 base seg, c => lookup4 d base seg c
  | .f6 base first count, c =>
    if first ≤ c ∧ c < first + count then u16At d (base + 10 + 2 * (c - first)) else none
  | .f12 base n, c => group12Find d base c n 0

/-! ## `post` -/

set_option maxRecDepth 4000 in
/-- The 258 standard Macintosh glyph names (`post` formats 1.0 and 2.0, indices 0–257). -/
def stdMacNames : Array String := #[
  ".notdef", ".null", "nonmarkingreturn", "space", "exclam", "quotedbl", "numbersign",
  "dollar", "percent", "ampersand", "quotesingle", "parenleft", "parenright", "asterisk",
  "plus", "comma", "hyphen", "period", "slash", "zero", "one", "two", "three", "four", "five",
  "six", "seven", "eight", "nine", "colon", "semicolon", "less", "equal", "greater",
  "question", "at", "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O",
  "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z", "bracketleft", "backslash",
  "bracketright", "asciicircum", "underscore", "grave", "a", "b", "c", "d", "e", "f", "g",
  "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y",
  "z", "braceleft", "bar", "braceright", "asciitilde", "Adieresis", "Aring", "Ccedilla",
  "Eacute", "Ntilde", "Odieresis", "Udieresis", "aacute", "agrave", "acircumflex",
  "adieresis", "atilde", "aring", "ccedilla", "eacute", "egrave", "ecircumflex", "edieresis",
  "iacute", "igrave", "icircumflex", "idieresis", "ntilde", "oacute", "ograve", "ocircumflex",
  "odieresis", "otilde", "uacute", "ugrave", "ucircumflex", "udieresis", "dagger", "degree",
  "cent", "sterling", "section", "bullet", "paragraph", "germandbls", "registered",
  "copyright", "trademark", "acute", "dieresis", "notequal", "AE", "Oslash", "infinity",
  "plusminus", "lessequal", "greaterequal", "yen", "mu", "partialdiff", "summation",
  "product", "pi", "integral", "ordfeminine", "ordmasculine", "Omega", "ae", "oslash",
  "questiondown", "exclamdown", "logicalnot", "radical", "florin", "approxequal", "Delta",
  "guillemotleft", "guillemotright", "ellipsis", "nonbreakingspace", "Agrave", "Atilde",
  "Otilde", "OE", "oe", "endash", "emdash", "quotedblleft", "quotedblright", "quoteleft",
  "quoteright", "divide", "lozenge", "ydieresis", "Ydieresis", "fraction", "currency",
  "guilsinglleft", "guilsinglright", "fi", "fl", "daggerdbl", "periodcentered",
  "quotesinglbase", "quotedblbase", "perthousand", "Acircumflex", "Ecircumflex", "Aacute",
  "Edieresis", "Egrave", "Iacute", "Icircumflex", "Idieresis", "Igrave", "Oacute",
  "Ocircumflex", "apple", "Ograve", "Uacute", "Ucircumflex", "Ugrave", "dotlessi",
  "circumflex", "tilde", "macron", "breve", "dotaccent", "ring", "cedilla", "hungarumlaut",
  "ogonek", "caron", "Lslash", "lslash", "Scaron", "scaron", "Zcaron", "zcaron", "brokenbar",
  "Eth", "eth", "Yacute", "yacute", "Thorn", "thorn", "minus", "multiply", "onesuperior",
  "twosuperior", "threesuperior", "onehalf", "onequarter", "threequarters", "franc",
  "Gbreve", "gbreve", "Idotaccent", "Scedilla", "scedilla", "Cacute", "cacute", "Ccaron",
  "ccaron", "dcroat"]

/-- The Pascal strings of a `post` 2.0 table from `pos`, at most `fuel` of them (each takes at
least one byte, so `fuel = table size` reads them all); stops at the end or a truncated one. -/
def pascalStrings (t : ByteArray) : Nat → Nat → Array String → Array String
  | 0, _, acc => acc
  | fuel + 1, pos, acc =>
    match u8At t pos with
    | none => acc
    | some len =>
      if pos + 1 + len ≤ t.size then
        pascalStrings t fuel (pos + 1 + len)
          (acc.push (glyphNameOf (t.extract (pos + 1) (pos + 1 + len)).toList))
      else acc

/-- Glyph names from `post` (one per glyph, `""` when unknown); empty for formats without
names or a malformed table. -/
def parsePost (t : ByteArray) (numGlyphs : Nat) : Array String :=
  match u32At t 0 with
  | some 0x00010000 =>
    ((List.range (min numGlyphs 258)).map fun k => stdMacNames.getD k "").toArray
  | some 0x00020000 =>
    match u16At t 32 with
    | some n =>
      if 34 + 2 * n ≤ t.size then
        let extra := pascalStrings t t.size (34 + 2 * n) #[]
        ((List.range (min n numGlyphs)).map fun k =>
          match u16At t (34 + 2 * k) with
          | some i => if i < 258 then stdMacNames.getD i "" else extra.getD (i - 258) ""
          | none => "").toArray
      else #[]
    | none => #[]
  | _ => #[]

/-! ## `glyf`: simple and composite glyphs -/

/-- An outline point in font units. -/
structure Point where
  /-- x coordinate. -/
  x : Int
  /-- y coordinate. -/
  y : Int
  /-- On-curve point (else a quadratic control point). -/
  onCurve : Bool
  deriving Repr, Inhabited, BEq, DecidableEq

/-- A closed contour. -/
abbrev Contour := Array Point

/-- A component of a composite glyph. -/
structure Component where
  /-- The referenced glyph. -/
  glyph : Nat
  /-- The component flags. -/
  flags : Nat
  /-- First argument: x offset, or parent point number (point matching). -/
  arg1 : Int
  /-- Second argument: y offset, or child point number (point matching). -/
  arg2 : Int
  /-- F2Dot14 transform `[a b c d]` raw (`16384 = 1`): `x' = a·x + c·y`, `y' = b·x + d·y`. -/
  a : Int
  /-- See `a`. -/
  b : Int
  /-- See `a`. -/
  c : Int
  /-- See `a`. -/
  d : Int
  deriving Repr, Inhabited, BEq

/-- The shape of a validated glyph. -/
inductive Shape where
  /-- No outline (e.g. `space`). -/
  | empty
  /-- A simple glyph with its contour and point counts. -/
  | simple (contours points : Nat)
  /-- A composite glyph. -/
  | composite (comps : Array Component)
  deriving Repr, Inhabited

/-- A validated glyph: its bounding box, shape and own `glyf` bytes (for lazy outlines). -/
structure Glyph where
  /-- Bounding box. -/
  xMin : Int
  /-- Bounding box. -/
  yMin : Int
  /-- Bounding box. -/
  xMax : Int
  /-- Bounding box. -/
  yMax : Int
  /-- Shape. -/
  shape : Shape
  /-- The glyph's bytes in `glyf`. -/
  data : ByteArray
  deriving Inhabited

/-- Flag decoding: `rem` more points, at most `fuel` flag records (each covers ≥ 1 point, so
`fuel = numPoints` suffices); a repeat count is cut at `rem`. -/
def decodeFlags (d : ByteArray) : Nat → Nat → Nat → Array UInt8 → Option (Array UInt8 × Nat)
  | 0, pos, rem, acc => if rem = 0 then some (acc, pos) else none
  | fuel + 1, pos, rem, acc =>
    if rem = 0 then some (acc, pos) else
    match d[pos]? with
    | none => none
    | some f =>
      if f &&& 8 != 0 then
        match d[pos + 1]? with
        | none => none
        | some r =>
          let n := min (r.toNat + 1) rem
          decodeFlags d fuel (pos + 2) (rem - n) (acc ++ Array.replicate n f)
      else decodeFlags d fuel (pos + 1) (rem - 1) (acc.push f)

/-- Coordinate decoding for one axis (`short`/`same` are the flag bits: `2`/`16` for x, `4`/`32`
for y), accumulating deltas from `v`. Structural on the flag list. -/
def decodeCoords (d : ByteArray) (short same : UInt8) :
    List UInt8 → Nat → Int → Array Int → Option (Array Int × Nat)
  | [], pos, _, acc => some (acc, pos)
  | f :: fs, pos, v, acc =>
    if f &&& short != 0 then
      match u8At d pos with
      | some b =>
        let v' := if f &&& same != 0 then v + b else v - b
        decodeCoords d short same fs (pos + 1) v' (acc.push v')
      | none => none
    else if f &&& same != 0 then decodeCoords d short same fs pos v (acc.push v)
    else
      match i16At d pos with
      | some dv => decodeCoords d short same fs (pos + 2) (v + dv) (acc.push (v + dv))
      | none => none

/-- The end-point indices of `n` contours (from byte 10), required strictly increasing. -/
def endPoints (d : ByteArray) (n : Nat) : Option (Array Nat) :=
  (List.range n).foldlM (init := #[]) fun acc k => do
    let e ← u16At d (10 + 2 * k)
    match acc.back? with
    | some p => if p < e then some (acc.push e) else none
    | none => some (acc.push e)

/-- Split points into contours at the end-point indices. -/
def splitContours (pts : Array Point) (ends : Array Nat) : Array Contour :=
  (ends.foldl (fun (acc, start) e => (acc.push (pts.extract start (e + 1)), e + 1))
    ((#[] : Array Contour), 0)).1

/-- Decode a simple glyph (`numberOfContours = n ≥ 0`) into contours; also returns the
number of points. Every point must be decoded from bytes inside the glyph. -/
def decodeSimple (d : ByteArray) (n : Nat) : Option (Array Contour × Nat) := do
  let ends ← endPoints d n
  let np := match ends.back? with | some e => e + 1 | none => 0
  let insLen ← u16At d (10 + 2 * n)
  let pos := 12 + 2 * n + insLen
  if d.size < pos then none else
  let (flags, p1) ← decodeFlags d np pos np #[]
  let (xs, p2) ← decodeCoords d 2 16 flags.toList p1 0 #[]
  let (ys, p3) ← decodeCoords d 4 32 flags.toList p2 0 #[]
  if d.size < p3 then none else
  let pts := (List.range np).map fun k =>
    Point.mk (xs.getD k 0) (ys.getD k 0) ((flags.getD k 0) &&& 1 != 0)
  some (splitContours pts.toArray ends, np)

/-- Decode the components of a composite glyph from `pos`, at most `fuel` of them (each takes
≥ 6 bytes, so `fuel = size / 6 + 1` reads all that fit). -/
def decodeComponents (d : ByteArray) : Nat → Nat → Array Component → Option (Array Component)
  | 0, _, _ => none
  | fuel + 1, pos, acc => do
    let flags ← u16At d pos
    let gid ← u16At d (pos + 2)
    let xy := flags &&& 2 != 0
    let ((a1, a2), p) ← if flags &&& 1 != 0 then do
        let x ← u16At d (pos + 4)
        let y ← u16At d (pos + 6)
        pure (if xy then (toI16 x, toI16 y) else ((x : Int), (y : Int)), pos + 8)
      else do
        let x ← u8At d (pos + 4)
        let y ← u8At d (pos + 5)
        pure (if xy then (toI8 x, toI8 y) else ((x : Int), (y : Int)), pos + 6)
    let (a, b, c, dd, p') ← if flags &&& 8 != 0 then do
        let s ← i16At d p
        pure (s, 0, 0, s, p + 2)
      else if flags &&& 0x40 != 0 then do
        let sx ← i16At d p
        let sy ← i16At d (p + 2)
        pure (sx, 0, 0, sy, p + 4)
      else if flags &&& 0x80 != 0 then do
        let a ← i16At d p
        let b ← i16At d (p + 2)
        let c ← i16At d (p + 4)
        let dd ← i16At d (p + 6)
        pure (a, b, c, dd, p + 8)
      else pure (16384, 0, 0, 16384, p)
    let acc := acc.push { glyph := gid, flags, arg1 := a1, arg2 := a2, a, b, c, d := dd }
    if flags &&& 0x20 != 0 then decodeComponents d fuel p' acc else some acc

/-- Validate one glyph's bytes: header, then a full simple-glyph decode or the component list
(component glyph ids must be `< numGlyphs`). -/
def validateGlyph (d : ByteArray) (numGlyphs : Nat) : Except String Glyph := do
  let some nc := i16At d 0 | throw "truncated header"
  let some x0 := i16At d 2 | throw "truncated header"
  let some y0 := i16At d 4 | throw "truncated header"
  let some x1 := i16At d 6 | throw "truncated header"
  let some y1 := i16At d 8 | throw "truncated header"
  if 0 ≤ nc then
    match decodeSimple d nc.toNat with
    | some (_, np) => return ⟨x0, y0, x1, y1, .simple nc.toNat np, d⟩
    | none => throw "bad simple glyph"
  else
    match decodeComponents d (d.size / 6 + 1) 10 #[] with
    | some cs =>
      if cs.all (·.glyph < numGlyphs) then return ⟨x0, y0, x1, y1, .composite cs, d⟩
      else throw "component glyph out of range"
    | none => throw "bad composite glyph"

/-- `loca` entry `k` as a byte offset into `glyf`. -/
def locaAt (loca : ByteArray) (long : Bool) (k : Nat) : Option Nat :=
  if long then u32At loca (4 * k) else (u16At loca (2 * k)).map (2 * ·)

/-- Validate all glyphs in order. `prevEnd` is the end of the last accepted glyph; a glyph
starting before it (overlapping or out of order) is rejected, so the decoded ranges are
disjoint. Returns glyphs (`none` = rejected or missing) and the rejections. -/
def readGlyphs (glyf loca : ByteArray) (long : Bool) (numGlyphs : Nat) :
    Array (Option Glyph) × Array (Nat × String) :=
  let r := (List.range numGlyphs).foldl (fun (gs, rs, prevEnd) k =>
    match locaAt loca long k, locaAt loca long (k + 1) with
    | some s, some e =>
      if e < s then (gs.push none, rs.push (k, "loca out of order"), prevEnd)
      else if glyf.size < e then (gs.push none, rs.push (k, "loca past glyf"), prevEnd)
      else if s = e then (gs.push (some ⟨0, 0, 0, 0, .empty, ByteArray.empty⟩), rs, prevEnd)
      else if s < prevEnd then (gs.push none, rs.push (k, "glyph overlaps previous"), prevEnd)
      else
        match validateGlyph (glyf.extract s e) numGlyphs with
        | .ok g => (gs.push (some g), rs, e)
        | .error msg => (gs.push none, rs.push (k, msg), prevEnd)
    | _, _ => (gs.push none, rs.push (k, "loca truncated"), prevEnd))
    ((#[] : Array (Option Glyph)), (#[] : Array (Nat × String)), 0)
  (r.1, r.2.1)

/-- One round of composite depth resolution: simple/empty glyphs have depth 0; a composite
gets `1 + max` once every component has a depth. -/
def depthRound (glyphs : Array (Option Glyph)) (depth : Array (Option Nat)) :
    Array (Option Nat) :=
  glyphs.map fun g? =>
    match g? with
    | none => none
    | some g =>
      match g.shape with
      | .composite cs =>
        cs.foldl (fun acc c => do
          let m ← acc
          let dc ← (depth[c.glyph]?).join
          some (max m (dc + 1))) (some 1)
      | _ => some 0

/-- Composite depths after `maxCompositeDepth + 1` rounds; `none` = unresolved (cyclic, too
deep, or depending on a rejected glyph). -/
def depths (glyphs : Array (Option Glyph)) : Array (Option Nat) :=
  (List.range (maxCompositeDepth + 1)).foldl (fun dp _ => depthRound glyphs dp)
    (Array.replicate glyphs.size none)

/-- Reject composites whose depth did not resolve. -/
def pruneComposites (glyphs : Array (Option Glyph)) (rejected : Array (Nat × String)) :
    Array (Option Glyph) × Array (Nat × String) :=
  let dp := depths glyphs
  let r := (List.range glyphs.size).foldl (fun (gs, rs) k =>
    match glyphs[k]?.join with
    | some g =>
      match (dp[k]?).join with
      | some _ => (gs.push (some g), rs)
      | none => (gs.push none, rs.push (k, "composite cyclic, too deep or broken"))
    | none => (gs.push none, rs)) ((#[] : Array (Option Glyph)), rejected)
  r

/-! ## The font -/

/-- A parsed TrueType font. -/
structure TTFont where
  /-- `head.unitsPerEm`. -/
  unitsPerEm : Nat
  /-- `unitsPerEm` is nonzero. -/
  upem_pos : 0 < unitsPerEm
  /-- Font bounding box (`head`). -/
  xMin : Int
  /-- Font bounding box. -/
  yMin : Int
  /-- Font bounding box. -/
  xMax : Int
  /-- Font bounding box. -/
  yMax : Int
  /-- `maxp.numGlyphs` (≥ 1). -/
  numGlyphs : Nat
  /-- `hhea.ascender` (0 without `hhea`). -/
  ascender : Int
  /-- `hhea.descender` (0 without `hhea`). -/
  descender : Int
  /-- Advance widths of the first glyphs (`hmtx` long metrics). -/
  advances : Array Nat
  /-- The `cmap` table bytes (subtables are read lazily from here). -/
  cmapData : ByteArray
  /-- Supported `cmap` subtables. -/
  cmaps : Array Cmap
  /-- Glyph names from `post` (`""` = unknown). -/
  names : Array String
  /-- Validated glyphs (`none` = rejected or no `glyf`). -/
  glyphs : Array (Option Glyph)
  /-- Rejected glyphs with the reason. -/
  rejected : Array (Nat × String)
  /-- Tables skipped (out of bounds, malformed, unsupported subtables), with the reason. -/
  skipped : Array String

/-- Advance width of a glyph in font units: `hmtx` entry, or the last one for glyphs past
`numberOfHMetrics`; `none` for `gid ≥ numGlyphs` or without metrics. -/
def TTFont.advanceOfGlyph (f : TTFont) (gid : Nat) : Option Nat :=
  if gid < f.numGlyphs then f.advances[min gid (f.advances.size - 1)]? else none

/-- An advance exists only for glyphs of the font. -/
theorem TTFont.advanceOfGlyph_lt {f : TTFont} {gid v : Nat}
    (h : f.advanceOfGlyph gid = some v) : gid < f.numGlyphs := by
  unfold TTFont.advanceOfGlyph at h
  split at h
  · assumption
  · cases h

/-- Look `c` up in subtable `(p, e)`; a result `0` or `≥ numGlyphs` is no glyph. -/
def TTFont.lookupIn (f : TTFont) (p e c : Nat) : Option Nat :=
  match f.cmaps.find? (fun m => m.platform == p && m.encoding == e) with
  | some m =>
    match m.sub.lookup f.cmapData c with
    | some g => if 0 < g ∧ g < f.numGlyphs then some g else none
    | none => none
  | none => none

/-- First success of a list of lookups `(platform, encoding, code)`. -/
def TTFont.firstOf (f : TTFont) : List (Nat × Nat × Nat) → Option Nat
  | [] => none
  | (p, e, c) :: rest =>
    match f.lookupIn p e c with
    | some g => some g
    | none => f.firstOf rest

/-- A lookup succeeds only with a real glyph: `0 < gid < numGlyphs`. -/
theorem TTFont.lookupIn_lt {f : TTFont} {p e c g : Nat} (h : f.lookupIn p e c = some g) :
    0 < g ∧ g < f.numGlyphs := by
  unfold TTFont.lookupIn at h
  split at h
  · split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h
  · cases h

/-- The glyph of a Unicode scalar value through the Unicode cmaps. -/
def TTFont.glyphOfUnicode (f : TTFont) (u : Nat) : Option Nat :=
  f.firstOf [(3, 10, u), (0, 6, u), (0, 4, u), (3, 1, u), (0, 3, u), (0, 2, u), (0, 1, u),
    (0, 0, u)]

/-- The glyph with a given `post` name. -/
def TTFont.glyphOfName (f : TTFont) (n : String) : Option Nat :=
  if n.isEmpty then none else
  match f.names.findIdx? (· == n) with
  | some g => if 0 < g ∧ g < f.numGlyphs then some g else none
  | none => none

/-- The `post` name of a glyph. -/
def TTFont.glyphName? (f : TTFont) (gid : Nat) : Option String :=
  match f.names[gid]? with
  | some n => if n.isEmpty then none else some n
  | none => none

/-- The single code point of a glyph name, via the Adobe Glyph List. -/
def unicodeOfName (n : GlyphName) : Option Nat :=
  match glyphToUnicode n with
  | some s => match s.toList with
    | [ch] => some ch.toNat
    | _ => none
  | none => none

/-- The raw-code lookups for a symbolic font (§9.6.6.4). -/
def symbolicLookups (c : Nat) : List (Nat × Nat × Nat) :=
  [(3, 0, c), (3, 0, 0xF000 + c), (3, 0, 0xF100 + c), (3, 0, 0xF200 + c), (1, 0, c)]

/-- The glyph of a one-byte character code (ISO 32000-2 §9.6.6.4); `enc` is the simple
font's encoding (task 6.5 builds it from `/Encoding`), used for nonsymbolic fonts. -/
def TTFont.glyphOfCode (f : TTFont) (code : UInt8) (symbolic : Bool)
    (enc : Encoding := standardEncoding) : Option Nat :=
  let c := code.toNat
  if symbolic then f.firstOf (symbolicLookups c ++ [(3, 1, c)])
  else
    let byName := match enc.glyph c with
      | some n =>
        match (unicodeOfName n).bind f.glyphOfUnicode with
        | some g => some g
        | none =>
          match (macRomanEncoding.findIdx? (· == some n)).bind (f.lookupIn 1 0) with
          | some g => some g
          | none => f.glyphOfName n
      | none => none
    match byName with
    | some g => some g
    | none => f.firstOf (symbolicLookups c)

/-- A glyph advance in text space: `units / unitsPerEm`, rounded once to `Fixed`. -/
def TTFont.toText (f : TTFont) (units : Nat) : Fixed :=
  Fixed.clamp (roundDiv ((units : Int) * fixedScale) f.unitsPerEm)

/-- The text-space advance of a character code (fallback for missing `/Widths`). -/
def TTFont.advanceText (f : TTFont) (code : UInt8) (symbolic : Bool)
    (enc : Encoding := standardEncoding) : Option Fixed := do
  let g ← f.glyphOfCode code symbolic enc
  let a ← f.advanceOfGlyph g
  some (f.toText a)

/-- The text-space advance of a glyph id (`advanceOfGlyph` scaled by `unitsPerEm`): the width
fallback of a `/CIDFontType2` font, whose CIDs select glyphs through `/CIDToGIDMap`
(§9.7.4.2, task 6.7c). -/
def TTFont.advanceOfGlyphText (f : TTFont) (gid : Nat) : Option Fixed :=
  (f.advanceOfGlyph gid).map f.toText

/-- The validated glyph `gid`. -/
def TTFont.glyph? (f : TTFont) (gid : Nat) : Option Glyph := (f.glyphs[gid]?).join

/-! ## Outlines -/

/-- Apply a component transform and offset to a point. -/
def Component.apply (cm : Component) (dx dy : Int) (p : Point) : Point :=
  { x := roundDiv (cm.a * p.x + cm.c * p.y) 16384 + dx,
    y := roundDiv (cm.b * p.x + cm.d * p.y) 16384 + dy, onCurve := p.onCurve }

/-- The offset of a component (`ARGS_ARE_XY_VALUES`, optionally scaled), or by point
matching parent point `arg1` against transformed child point `arg2`. -/
def Component.offset (cm : Component) (parent child : Array Point) : Option (Int × Int) :=
  if cm.flags &&& 2 != 0 then
    if cm.flags &&& 0x800 != 0 then
      let q := cm.apply 0 0 ⟨cm.arg1, cm.arg2, true⟩
      some (q.x, q.y)
    else some (cm.arg1, cm.arg2)
  else do
    let pp ← parent[cm.arg1.toNat]?
    let cp ← child[cm.arg2.toNat]?
    let q := cm.apply 0 0 cp
    some (pp.x - q.x, pp.y - q.y)

/-- Total number of points in a list of contours. -/
def numPoints (cs : Array Contour) : Nat := cs.foldl (fun n c => n + c.size) 0

/-- Flatten glyph `gid` into contours: `depth` is structural fuel (`maxCompositeDepth`),
`visited` the glyphs on the current path (a revisit is a cycle: `none`), `budget` the
remaining glyph visits; returns the contours and the budget left. -/
def outlineAux (f : TTFont) : Nat → List Nat → Nat → Nat → Option (Array Contour × Nat)
  | 0, _, _, _ => none
  | depth + 1, visited, budget, gid =>
    if gid ∈ visited then none else
    if budget = 0 then none else
    match f.glyph? gid with
    | none => none
    | some g =>
      match g.shape with
      | .empty => some (#[], budget - 1)
      | .simple n _ =>
        match decodeSimple g.data n with
        | some (cs, _) => some (cs, budget - 1)
        | none => none
      | .composite comps =>
        comps.foldlM (init := ((#[] : Array Contour), budget - 1)) fun (acc, bud) cm => do
          let (child, bud') ← outlineAux f depth (gid :: visited) bud cm.glyph
          let childPts := child.flatMap id
          let (dx, dy) ← cm.offset (acc.flatMap id) childPts
          let placed := child.map (·.map (cm.apply dx dy))
          let out := acc ++ placed
          if maxOutlinePoints < numPoints out then none else some (out, bud')

/-- Depth exhaustion yields no outline. -/
theorem outlineAux_zero (f : TTFont) (v : List Nat) (b g : Nat) :
    outlineAux f 0 v b g = none := rfl

/-- **Cycle safety**: a glyph already on the current composite path yields no outline. -/
theorem outlineAux_visited (f : TTFont) (depth b g : Nat) (v : List Nat) (h : g ∈ v) :
    outlineAux f depth v b g = none := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [outlineAux, h, ↓reduceIte]

/-- The outline of a glyph in font units, composites flattened (Phase 7). -/
def TTFont.outline (f : TTFont) (gid : Nat) : Option (Array Contour) :=
  (outlineAux f maxCompositeDepth [] maxOutlineCalls gid).map (·.1)

/-! ### Outlines in the common type (task 7.3a) -/

/-- A font-unit point as a glyph-space `Content.Point`. -/
def Point.toPt (p : Point) : Content.Point := ⟨Fixed.ofInt p.x, Fixed.ofInt p.y⟩

/-- The midpoint of two font-unit points (exact in `Fixed`: halves of integers). -/
def midPt (p q : Point) : Content.Point :=
  ⟨Fixed.clamp ((p.x + q.x) * fixedScale / 2), Fixed.clamp ((p.y + q.y) * fixedScale / 2)⟩

/-- The segments of one closed quadratic contour (TrueType rules: two consecutive off-curve
points imply the on-curve point midway between them; a contour without on-curve points
starts at the midpoint of its first two points). At most `c.size + 2` segments. -/
def contourSegs (c : Contour) : Array Outline.OSeg :=
  match c[0]? with
  | none => #[]
  | some p0 =>
    -- the start point and the index after it where the walk begins
    let start : Content.Point × Nat :=
      match c.findIdx? (·.onCurve) with
      | some i => ((c.getD i p0).toPt, i + 1)
      | none => (midPt p0 (c.getD 1 p0), 1)
    let n := c.size
    -- walk `n` points cyclically from `start.2`, then close back to the start
    let st := (List.range n).foldl (fun (acc : Array Outline.OSeg × Option Content.Point) k =>
      let p := c.getD ((start.2 + k) % n) p0
      if p.onCurve && k + 1 == n && start.1 == p.toPt then acc
      else
        match p.onCurve, acc.2 with
        | true, none => (acc.1.push (.lineTo p.toPt), none)
        | true, some q => (acc.1.push (.quadTo q p.toPt), none)
        | false, none => (acc.1, some p.toPt)
        | false, some q =>
          let m : Content.Point := ⟨Fixed.clamp ((q.x.raw + p.toPt.x.raw) / 2),
            Fixed.clamp ((q.y.raw + p.toPt.y.raw) / 2)⟩
          (acc.1.push (.quadTo q m), some p.toPt)) (#[Outline.OSeg.moveTo start.1], none)
    let segs := match st.2 with
      | some q => st.1.push (.quadTo q start.1)
      | none => st.1
    segs.push .close

/-- **Glyph outline in the common type** (task 7.3a): the contours of `outline gid` (font
units, composites resolved) as quadratic segments; `none` when the glyph has no outline or
exceeds `Outline.maxOutlineSegs`. -/
def TTFont.glyphOutline (f : TTFont) (gid : Nat) : Option Outline.Outline :=
  (f.outline gid).bind fun cs => Outline.Outline.ofArray (cs.flatMap contourSegs)

/-! ## Parsing -/

/-- Parse an embedded TrueType font program (`/FontFile2` contents, Flate already decoded).
Fails on a malformed directory, a missing or malformed `head`/`maxp`, or an input over
`Limits.maxDecodedStreamBytes`; other problems skip a table or reject a glyph. -/
def parse (limits : Limits) (bytes : ByteArray) : Except Error TTFont := do
  if limits.maxDecodedStreamBytes < bytes.size then throw (.limitExceeded .decodedStreamBytes)
  let ver ← need (u32At bytes 0) "truncated header"
  if ver = 0x4F54544F then throw (.unsupported "OpenType font with CFF outlines ('OTTO')")
  if ver = 0x74746366 then throw (.unsupported "TrueType collection ('ttcf')")
  if ver ≠ 0x00010000 ∧ ver ≠ 0x74727565 then
    throw (.malformed 0 "TrueType: bad sfnt version")
  let n ← need (u16At bytes 4) "truncated header"
  if maxTables < n then throw (.malformed 4 s!"TrueType: more than {maxTables} tables")
  let recs ← (List.range n).mapM fun k => need (readRec bytes k) "truncated table directory"
  let outOfBounds := (recs.filter fun r => !r.inBounds bytes.size).map fun r =>
    s!"{tagName r.tag}: past end of font"
  let tbl (s : String) := tableBytes bytes recs (tagOf s)
  let head ← parseHead (← need (tbl "head") "missing head table")
  let ⟨upem, hupem⟩ : {u : Nat // 0 < u} ←
    if h : head.unitsPerEm = 0 then throw (.malformed 0 "TrueType: head: unitsPerEm = 0")
    else pure ⟨head.unitsPerEm, Nat.pos_of_ne_zero h⟩
  let maxp ← need (tbl "maxp") "missing maxp table"
  let numGlyphs ← need (u16At maxp 4) "maxp: truncated"
  if numGlyphs = 0 then throw (.malformed 0 "TrueType: maxp: no glyphs")
  let hhea := tbl "hhea"
  let (advances, sk1) := match hhea, tbl "hmtx" with
    | some hh, some hm => (parseAdvances hh hm numGlyphs, ([] : List String))
    | _, _ => (#[], ["hhea/hmtx: missing"])
  let cmapData := (tbl "cmap").getD ByteArray.empty
  let (cmaps, nSkip) := parseCmap cmapData
  let sk2 := if (tbl "cmap").isNone then ["cmap: missing"]
    else if nSkip = 0 then [] else [s!"cmap: {nSkip} subtables unsupported or malformed"]
  let names := match tbl "post" with
    | some p => parsePost p numGlyphs
    | none => #[]
  let (glyphs, rejected, sk3) := match tbl "glyf", tbl "loca" with
    | some g, some l =>
      let (gs, rs) := readGlyphs g l head.longLoca numGlyphs
      let (gs', rs') := pruneComposites gs rs
      (gs', rs', ([] : List String))
    | _, _ => ((#[] : Array (Option Glyph)), (#[] : Array (Nat × String)), ["glyf/loca: missing"])
  return {
    unitsPerEm := upem
    upem_pos := hupem
    xMin := head.xMin, yMin := head.yMin, xMax := head.xMax, yMax := head.yMax
    numGlyphs
    ascender := (hhea.bind (i16At · 4)).getD 0
    descender := (hhea.bind (i16At · 6)).getD 0
    advances, cmapData, cmaps := cmaps.toArray, names, glyphs, rejected
    skipped := (outOfBounds ++ sk1 ++ sk2 ++ sk3).toArray }

/-! ## Tests

The fixture is `Tests/fonts/tiny.ttf`, generated by `python3 -I Tests/fonts/gen_truetype.py`
(see its docstring): 5 glyphs `.notdef` (500), `space` (250, empty), `A` (600), `Aring`
(composite of `A` and `A.ss01` scaled 0.5 at (100, 50); advance repeats 600), `A.ss01`
(two contours); cmaps (1,0) f0, (3,0) f6, (3,1) f4, (3,10) f12; `post` 2.0. The malformed
variants `bad-*.ttf` are reproduced below by patching the same bytes. -/

/-- Decodes a hex string (whitespace ignored); test helper. -/
private def fromHex (str : String) : ByteArray :=
  let ds := str.toList.filterMap fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87) else none
  let rec go : List Nat → ByteArray → ByteArray
    | a :: b :: rest, acc => go rest (acc.push (a * 16 + b).toUInt8)
    | _, acc => acc
  go ds ByteArray.empty

/-- `Tests/fonts/tiny.ttf` (888 bytes). -/
private def tinyTtf : ByteArray := fromHex
  "000100000008008000030000636d6170e01007460000008c000001aa676c79663ebf9d0600000238000000746865
  6164617643a1000002ac0000003668686561057a0194000002e400000024686d7478054600960000030800000010
  6c6f636100340061000003180000000c6d617870000600000000032400000020706f7374797a60cb000003440000
  0033000000040001000000000024000300000000012a00030001000001380003000a0000016a0000010600000000
  00000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000
  00000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000
  00000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000
  00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  0000000000000000000000000000000000000000000000000006000e0000f0410002000200040004003200000008
  0004000100040020004100c5ffff00000020004100c5ffffffe1ffc10000000100000000000400000003000c0000
  000000400000000000000004000000200000002000000001000000410000004100000002000000c5000000c50000
  00030001f6000001f60000000004000000010032000001c202bc0003000033211121320190fe7002bc0000010000
  0000025802bc00020000310001012c012c02bcfd4400ffff00000000025802bc0023000200000000000a00046432
  200000020064006401f401f40003000700003721112113353315640190fe7064c8640190fed4c8c8000100000001
  000059da9b995f0f3cf5000b03e80000000000000000000000000000000000000000025802bc0000000800020000
  00000000000100000320ff380000025800000000025800010000000000000000000000000000000301f4003200fa
  000002580000000000640000000d000d001a0027003a000100000005000000000000000000000000000000000000
  00000000000000000002000000000000ff9c00320000000000000000000000000000000000000000000500000003
  00240063010206412e7373303100"

/-- Set byte `i` to `v`; test helper. -/
private def patch (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray := ⟨b.data.setIfInBounds i v⟩

/-- `bad-head.ttf`: `head` offset 904, past the end. -/
private def badHead : ByteArray := patch (patch tinyTtf 54 3) 55 0x88

/-- `bad-loca.ttf`: `loca[3]` and `loca[4]` swapped (checksum bytes differ, unchecked): glyph 2
then extends over glyph 3's bytes (accepted, trailing bytes ignored), glyph 3 is out of order
and glyph 4 overlaps glyph 2's new range; both are rejected. -/
private def badLoca : ByteArray := patch (patch tinyTtf 799 39) 801 26

/-- `bad-cycle.ttf`: glyph 3's second component refers to glyph 3. -/
private def badCycle : ByteArray := patch tinyTtf 641 3

/-- The parsed fixture (or a dummy that fails every check). -/
private def tiny : Option TTFont := (parse Limits.default tinyTtf).toOption

#guard tinyTtf.size == 888
#guard (tiny.map fun f => (f.unitsPerEm, f.numGlyphs, f.advances, f.xMin, f.yMin, f.xMax,
  f.yMax, f.ascender, f.descender)) == some (1000, 5, #[500, 250, 600], 0, 0, 600, 700, 800, -200)
#guard (tiny.map fun f => (f.rejected.size, f.skipped.size, f.cmaps.size)) == some (0, 0, 4)
-- advances, with the "last advance repeats" rule
#guard (tiny.map fun f => (List.range 6).map f.advanceOfGlyph) ==
  some [some 500, some 250, some 600, some 600, some 600, none]
#guard (tiny.bind fun f => f.advanceText 0x41 false).map (·.raw) == some 600000
#guard (tiny.bind fun f => f.advanceText 0x20 false).map (·.raw) == some 250000
#guard (tiny.map fun f => (List.range 6).map fun g => (f.advanceOfGlyphText g).map (·.raw)) ==
  some [some 500000, some 250000, some 600000, some 600000, some 600000, none]
-- cmap: format 12 (3,10), format 4 (3,1) incl. the idRangeOffset segment, format 0, format 6
#guard (tiny.map fun f => [0x20, 0x41, 0xC5, 0x1F600, 0x42].map f.glyphOfUnicode) ==
  some [some 1, some 2, some 3, some 4, none]
#guard (tiny.map fun f => [0x20, 0x41, 0xC5, 0x1F600, 0xFFFF, 0x42].map (f.lookupIn 3 1)) ==
  some [some 1, some 2, some 3, none, none, none]
#guard (tiny.map fun f => [0x20, 0x41, 0x81, 0x80].map (f.lookupIn 1 0)) ==
  some [some 1, some 2, some 3, none]
#guard (tiny.map fun f => [0xF041, 0xF042, 0xF043, 0x41].map (f.lookupIn 3 0)) ==
  some [some 2, some 4, none, none]
-- §9.6.6.4 code → glyph
#guard (tiny.map fun f => [0x41, 0x42, 0x81, 0x20].map (f.glyphOfCode · true)) ==
  some [some 2, some 4, some 3, some 1]
#guard (tiny.map fun f => [0x41, 0x20, 0xC5].map (f.glyphOfCode · false)) ==
  some [some 2, some 1, none]
#guard (tiny.bind fun f => f.glyphOfCode 0xC5 false winAnsiEncoding) == some 3
#guard (tiny.bind fun f => f.glyphOfCode 0x81 false macRomanEncoding) == some 3
-- post 2.0 names
#guard (tiny.map fun f => (List.range 6).map f.glyphName?) ==
  some [some ".notdef", some "space", some "A", some "Aring", some "A.ss01", none]
#guard (tiny.bind fun f => f.glyphOfName "A.ss01") == some 4
-- glyf: shapes, composite components, outlines
#guard (tiny.bind fun f => (f.glyph? 3).map fun g => match g.shape with
  | .composite cs => cs.toList.map fun c => (c.glyph, c.flags, c.arg1, c.arg2, c.a, c.d)
  | _ => []) == some [(2, 0x23, 0, 0, 16384, 16384), (4, 0x0A, 100, 50, 8192, 8192)]
#guard (tiny.bind fun f => (f.glyph? 4).map fun g => match g.shape with
  | .simple c p => (c, p, g.xMin, g.yMin, g.xMax, g.yMax)
  | _ => (0, 0, 0, 0, 0, 0)) == some (2, 8, 100, 100, 500, 500)
#guard (tiny.bind fun f => f.outline 2) ==
  some #[#[⟨0, 0, true⟩, ⟨300, 700, false⟩, ⟨600, 0, true⟩]]
#guard (tiny.bind fun f => f.outline 1) == some #[]
#guard (tiny.bind fun f => (f.outline 0).map numPoints) == some 4
#guard (tiny.bind fun f => (f.outline 3).map fun cs => (cs.size, numPoints cs, cs[1]?.bind (·[0]?),
  cs[2]?.bind (·[2]?))) == some (3, 11, some ⟨150, 100, true⟩, some ⟨300, 250, true⟩)
#guard (tiny.bind fun f => f.outline 5) == none
#guard (tiny.bind fun f => (f.glyphOutline 2).map (·.1)) ==
  some #[.moveTo ⟨Fixed.zero, Fixed.zero⟩, .quadTo ⟨Fixed.ofInt 300, Fixed.ofInt 700⟩
    ⟨Fixed.ofInt 600, Fixed.zero⟩, .close]
#guard (tiny.bind fun f => (f.glyphOutline 3).map (·.bboxUnits)) == some (some (0, 0, 600, 700))
#guard (tiny.bind fun f => (f.glyphOutline 1).map (·.1.size)) == some 0
-- all off-curve: starts at the midpoint, implied on-curve points between controls
#guard contourSegs #[⟨0, 0, false⟩, ⟨100, 0, false⟩, ⟨100, 100, false⟩, ⟨0, 100, false⟩] ==
  #[.moveTo ⟨Fixed.ofInt 50, Fixed.zero⟩, .quadTo ⟨Fixed.ofInt 100, Fixed.zero⟩
      ⟨Fixed.ofInt 100, Fixed.ofInt 50⟩,
    .quadTo ⟨Fixed.ofInt 100, Fixed.ofInt 100⟩ ⟨Fixed.ofInt 50, Fixed.ofInt 100⟩,
    .quadTo ⟨Fixed.zero, Fixed.ofInt 100⟩ ⟨Fixed.zero, Fixed.ofInt 50⟩,
    .quadTo ⟨Fixed.zero, Fixed.zero⟩ ⟨Fixed.ofInt 50, Fixed.zero⟩, .close]

-- the standard Macintosh names agree with `macRomanEncoding` (ASCII and 0x80–0xFF), except
-- 0xCA (`nonbreakingspace` vs PDF's `space`); the 15 Mac-only symbols are unassigned in PDF
#guard stdMacNames.size == 258
#guard ((List.range 95).filter fun k =>
  macRomanEncoding[0x20 + k]?.join != stdMacNames[3 + k]?) == []
#guard ((List.range 128).filter fun k =>
  match macRomanEncoding[0x80 + k]?.join with
  | some n => some n != stdMacNames[98 + k]?
  | none => false) == [0xCA - 0x80]
-- malformed inputs
#guard (parse Limits.default (tinyTtf.extract 0 836)).toOption.map
  (fun f => (f.skipped, f.names.size, f.numGlyphs)) == some (#["post: past end of font"], 0, 5)
#guard (parse Limits.default badHead).toOption.isNone
#guard (parse Limits.default badLoca).toOption.map
  (fun f => (f.rejected, (f.glyph? 4).isSome, (f.outline 2).isSome)) ==
  some (#[(3, "loca out of order"), (4, "glyph overlaps previous")], false, true)
#guard (parse Limits.default badCycle).toOption.map
  (fun f => (f.rejected, f.outline 3, (f.outline 2).isSome)) ==
  some (#[(3, "composite cyclic, too deep or broken")], none, true)
#guard (parse Limits.default (tinyTtf.extract 0 20)).toOption.isNone
#guard (parse Limits.default "not a font at all".toUTF8).toOption.isNone
#guard (match parse Limits.default
    (patch (patch (patch (patch tinyTtf 0 0x4F) 1 0x54) 2 0x54) 3 0x4F) with
  | .error (.unsupported _) => true | _ => false)
#guard (parse { maxDecodedStreamBytes := 100 } tinyTtf).toOption.isNone
-- the cycle check of `outlineAux` holds even without the parse-time pruning
#guard (tiny.map fun f => (outlineAux f 16 [3] 100 3).isNone) == some true
#guard (u16At tinyTtf 4, u32At tinyTtf 0, i16At ⟨#[0xFF, 0x9C]⟩ 0, u16At tinyTtf 887) ==
  (some 8, some 0x00010000, some (-100), none)

end SafePdf.Core.Font.TrueType
