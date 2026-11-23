import SafePdf.Core.Font.Std14
import SafePdf.Core.Content.GState

/-!
# Glyph widths of simple and Type0 fonts (Plan.md §6 Phase 6, task 6.4)

Width resolution for the text interpreter: character code → horizontal advance in text space
units (glyph-space width / 1000, as `Core.Content.Fixed`), per ISO 32000-2 §9.6.2 (simple
fonts: `/FirstChar`, `/LastChar`, `/Widths`, `/MissingWidth` of the `/FontDescriptor`,
standard 14 metrics), §9.7.4.3 (CIDFont `/W` and `/DW`) and §9.7.5.2 (the predefined
`Identity-H` / `Identity-V` CMaps: two-byte big-endian codes, CID = code).

## Design decisions

* **Fonts are untrusted; nothing here fails.** Every bad entry is skipped and the lookup falls
  back; the caller learns where a width came from through `WidthSource` (`unknown` = no
  information, width 0).
* **Indirect objects** inside font dictionaries (`/Widths 12 0 R`, `/FontDescriptor`,
  `/DescendantFonts`, inner `/W` arrays) are resolved by a caller-supplied
  `resolve : PdfObject → PdfObject` (one level, e.g. the document's object lookup; `id` in
  tests). It is applied a bounded number of times: once per dictionary entry read and once per
  array element.
* **Simple fonts** (`SimpleMetrics`): the width of each of the 256 codes is computed once
  (`SimpleMetrics.table`, size 256 by `SimpleMetrics.ofDict_table_size`), so lookups are
  `O(1)`. Rule, in order: (1) `/Widths[code − FirstChar]` when the font has `/Widths`, the
  code is in `FirstChar..LastChar` and the entry is a number; (2) only when the font has no
  `/Widths`: the standard 14 width (`Std14.ofBaseFont` of `/BaseFont`, glyph name from the
  font's encoding); (3) `/MissingWidth` of the font descriptor when present; (4) `0` with
  `WidthSource.unknown`. `/Widths` is truncated to 256 entries. Type 3 fonts are excluded
  (`FontMetrics.ofDict` gives `none`): their widths are in glyph space scaled by
  `/FontMatrix`, not by 1/1000.
* **Exact /1000.** An integer width `w` becomes `Fixed` raw `w · 1000`; a real `m·10⁻ˢ`
  becomes `m·10⁻⁽ˢ⁺³⁾` through `Fixed.ofDecimal` (exact for `s ≤ 3`, rounded half up beyond).
* **CIDFonts** (`CIDMetrics`): `/W` is parsed by `parseW` into `WEntry`s, one per
  `c [w₁ … wₙ]` or `c_first c_last w` group (`parseW_length_le`: never more entries than array
  elements). Because Identity-H/V codes are two bytes, CIDs are `< 65536`; the entries are
  expanded once into a dense 65536-entry table (`buildWTable`, size theorem
  `buildWTable_size`) with the **first** matching entry winning (as pdfium; overlaps are
  undefined in the standard). The expansion visits at most `maxWCells` (2²⁰) cells in total,
  so a hostile `/W` (`0 65535 w` repeated) costs `O(entries + 2²⁰)`; beyond the budget the
  remaining entries are ignored and `CIDMetrics.truncated` is set. Missing CIDs take `/DW`
  (default 1000). Vertical metrics (`/W2`, `/DW2`) are not handled: `Identity-V` gets the same
  horizontal widths and the caller must not use them as vertical advances.
* **Encodings other than Identity-H/V** (embedded or other predefined CMaps) are task 6.5:
  `FontMetrics.ofDict` gives `none` for them. A trailing odd byte of an Identity string is
  dropped (`identityCodes`).

Everything is pure and total.
-/

namespace SafePdf.Core.Font

open SafePdf
open SafePdf.Core.Content (Fixed)

/-- Where a width came from (most to least authoritative). -/
inductive WidthSource where
  /-- The font's `/Widths` array (simple) or `/W` array (CIDFont). -/
  | widths
  /-- The standard 14 AFM metrics (simple font without `/Widths`). -/
  | std14
  /-- `/MissingWidth` of the font descriptor (simple font). -/
  | missingWidth
  /-- `/DW` of the CIDFont, or its default 1000. -/
  | defaultWidth
  /-- No information: the width is 0. -/
  | unknown
  deriving DecidableEq, Repr, Inhabited

/-- A width number in glyph space divided by 1000 (text space for a 1-unit font size):
integers exactly, reals via `Fixed.ofDecimal` with the scale raised by 3. -/
def widthOfNum? : PdfObject → Option Fixed
  | .int w => some (Fixed.clamp (w * 1000))
  | .real d => some (Fixed.ofDecimal ⟨d.mantissa, d.scale + 3⟩)
  | _ => none

/-- An integer entry of a dictionary (after resolving). -/
def getInt? (resolve : PdfObject → PdfObject) (d : Dict) (key : String) : Option Int :=
  match getR resolve d key with
  | some (.int i) => some i
  | _ => none

/-- The font descriptor dictionary of a font, if present. -/
def fontDescriptor? (resolve : PdfObject → PdfObject) (fontDict : Dict) : Option Dict :=
  match getR resolve fontDict "FontDescriptor" with
  | some (.dict fd) => some fd
  | _ => none

/-- The `/BaseFont` name of a font as a string. -/
def baseFontName? (resolve : PdfObject → PdfObject) (fontDict : Dict) : Option String :=
  match getR resolve fontDict "BaseFont" with
  | some (.name n) => some (glyphNameOf n.bytes)
  | _ => none

/-! ## Simple fonts -/

/-- The inputs of the simple-font width rule, read once from the font dictionary. -/
structure SimpleInputs where
  /-- `/FirstChar` (0 when absent or negative). -/
  firstChar : Nat
  /-- `/LastChar`, when present and non-negative. -/
  lastChar : Option Nat
  /-- `/Widths` entries (at most 256), each a number or `none` for a bad entry. -/
  widths : Array (Option Fixed)
  /-- Whether the font has a `/Widths` array. -/
  hasWidths : Bool
  /-- `/MissingWidth` of the font descriptor, when present and a number. -/
  missingWidth : Option Fixed
  /-- The standard 14 font substituting for `/BaseFont`, if recognised. -/
  std14 : Option Std14
  /-- The font's encoding. -/
  encoding : Encoding

/-- The width of one code under the simple-font rule (see the module doc). -/
def SimpleInputs.width (s : SimpleInputs) (code : Nat) : Fixed × WidthSource :=
  let fromWidths : Option Fixed :=
    if s.hasWidths ∧ s.firstChar ≤ code ∧ (s.lastChar.all fun l => code ≤ l) then
      match s.widths[code - s.firstChar]? with
      | some (some w) => some w
      | _ => none
    else none
  match fromWidths with
  | some w => (w, .widths)
  | none =>
    let fromStd : Option Fixed :=
      if s.hasWidths then none
      else
        match s.std14, s.encoding.glyph code with
        | some f, some g => (f.width? g).map fun w => Fixed.clamp ((w : Int) * 1000)
        | _, _ => none
    match fromStd with
    | some w => (w, .std14)
    | none =>
      match s.missingWidth with
      | some w => (w, .missingWidth)
      | none => (Fixed.zero, .unknown)

/-- Precomputed widths of a simple font: one entry per code `0..255`. -/
structure SimpleMetrics where
  /-- Width and source of each code; 256 entries. -/
  table : Array (Fixed × WidthSource)
  /-- The font's encoding (code → glyph name), for text extraction. -/
  encoding : Encoding
  /-- The standard 14 font substituting for `/BaseFont`, if recognised. -/
  std14 : Option Std14
  deriving Inhabited

/-- Read the width inputs of a simple font. `builtin?` is the font program's built-in
encoding when known (see `simpleEncoding`); when absent and the font maps onto Symbol or
ZapfDingbats, nothing better than StandardEncoding is available. -/
def SimpleInputs.ofDict (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) : SimpleInputs :=
  let fd := (fontDescriptor? resolve fontDict).getD []
  let widthsObj := getR resolve fontDict "Widths"
  let ws : List PdfObject :=
    match widthsObj with
    | some (.array xs) => xs.take 256
    | _ => []
  { firstChar := ((getInt? resolve fontDict "FirstChar").getD 0).toNat
    lastChar := (getInt? resolve fontDict "LastChar").bind fun l =>
      if 0 ≤ l then some l.toNat else none
    widths := (ws.map fun x => widthOfNum? (resolve x)).toArray
    hasWidths := match widthsObj with
      | some (.array _) => true
      | _ => false
    missingWidth := (getR resolve fd "MissingWidth").bind widthOfNum?
    std14 := (baseFontName? resolve fontDict).bind Std14.ofBaseFont
    encoding := simpleEncoding resolve fontDict builtin? }

/-- Precompute the widths of a simple font (ISO 32000-2 §9.6.2). -/
def SimpleMetrics.ofDict (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) : SimpleMetrics :=
  let s := SimpleInputs.ofDict resolve fontDict builtin?
  { table := (List.range 256).toArray.map s.width, encoding := s.encoding, std14 := s.std14 }

/-- The width table of a simple font always has 256 entries. -/
theorem SimpleMetrics.ofDict_table_size (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) : (SimpleMetrics.ofDict resolve fontDict builtin?).table.size = 256 := by
  simp [SimpleMetrics.ofDict]

/-- Width of a one-byte code (in range for every byte: `ofDict_table_size`). -/
def SimpleMetrics.width (m : SimpleMetrics) (code : Nat) : Fixed × WidthSource :=
  m.table[code]?.getD (Fixed.zero, .unknown)

/-! ## CIDFonts: `/W` -/

/-- One group of a CIDFont `/W` array (§9.7.4.3). -/
inductive WEntry where
  /-- `c [w₁ … wₙ]`: CIDs `c, c+1, …` get `w₁, w₂, …` (`none` = bad entry, skipped). -/
  | run (first : Nat) (ws : Array (Option Fixed))
  /-- `c_first c_last w`: every CID in the range gets `w`. -/
  | range (first last : Nat) (w : Fixed)
  deriving Inhabited

/-- Parse a `/W` array. Each group consumes at least two elements; malformed elements are
skipped one at a time. Total and linear. -/
def parseW (resolve : PdfObject → PdfObject) : List PdfObject → List WEntry
  | [] => []
  | [_] => []
  | x :: y :: rest =>
    match resolve x, resolve y with
    | .int c, .array ws =>
      if 0 ≤ c then
        .run c.toNat (ws.map fun w => widthOfNum? (resolve w)).toArray :: parseW resolve rest
      else parseW resolve rest
    | .int c, .int c2 =>
      match rest with
      | [] => []
      | z :: rest' =>
        match widthOfNum? (resolve z) with
        | some w =>
          if 0 ≤ c ∧ c ≤ c2 then .range c.toNat c2.toNat w :: parseW resolve rest'
          else parseW resolve rest'
        | none => parseW resolve rest'
    | _, _ => parseW resolve (y :: rest)

/-- `/W` parsing is bounded: never more groups than array elements (in fact at most half). -/
theorem parseW_length_le (resolve : PdfObject → PdfObject) (xs : List PdfObject) :
    (parseW resolve xs).length ≤ xs.length := by
  fun_induction parseW resolve xs <;> simp_all <;> omega

/-- Total number of table cells `buildWTable` may visit: bounds the cost of a hostile `/W`. -/
def maxWCells : Nat := 1 <<< 20

/-- Number of CIDs reachable through Identity-H/V (two-byte codes). -/
def cidCount : Nat := 65536

/-- Set `tbl[cid] := w` unless an earlier entry already set it (first entry wins). -/
def setFirst (tbl : Array (Option Fixed)) (cid : Nat) (w : Fixed) : Array (Option Fixed) :=
  match tbl[cid]? with
  | some none => tbl.setIfInBounds cid (some w)
  | _ => tbl

/-- Fill `n` consecutive cells from `cid` with `w` (first entry wins). -/
def fillConst (tbl : Array (Option Fixed)) (cid : Nat) (w : Fixed) : Nat → Array (Option Fixed)
  | 0 => tbl
  | n + 1 => fillConst (setFirst tbl cid w) (cid + 1) w n

/-- Fill consecutive cells from `cid` with the given widths (bad entries skipped). -/
def fillRun (tbl : Array (Option Fixed)) (cid : Nat) : List (Option Fixed) → Array (Option Fixed)
  | [] => tbl
  | some w :: rest => fillRun (setFirst tbl cid w) (cid + 1) rest
  | none :: rest => fillRun tbl (cid + 1) rest

/-- Number of in-table cells (`< cidCount`) among `n` cells starting at `first`. -/
def cellsInTable (first n : Nat) : Nat := min n (cidCount - first)

/-- Expand `/W` entries into a dense table, with a cell budget; returns the table and whether
the budget ran out (remaining entries ignored). Structural on the entry list. -/
def buildWAux (tbl : Array (Option Fixed)) (budget : Nat) :
    List WEntry → Array (Option Fixed) × Bool
  | [] => (tbl, false)
  | .run first ws :: rest =>
    let n := cellsInTable first ws.size
    if n ≤ budget then buildWAux (fillRun tbl first (ws.toList.take n)) (budget - n) rest
    else (fillRun tbl first (ws.toList.take budget), true)
  | .range first last w :: rest =>
    let n := cellsInTable first (last + 1 - first)
    if n ≤ budget then buildWAux (fillConst tbl first w n) (budget - n) rest
    else (fillConst tbl first w budget, true)

/-- The dense CID → width table of a `/W` array, and whether the cell budget ran out. -/
def buildWTable (entries : List WEntry) : Array (Option Fixed) × Bool :=
  buildWAux (Array.replicate cidCount none) maxWCells entries

/-- `setFirst` keeps the table size. -/
theorem setFirst_size (tbl : Array (Option Fixed)) (cid : Nat) (w : Fixed) :
    (setFirst tbl cid w).size = tbl.size := by
  unfold setFirst; split <;> simp

/-- `fillConst` keeps the table size. -/
theorem fillConst_size (tbl : Array (Option Fixed)) (cid : Nat) (w : Fixed) (n : Nat) :
    (fillConst tbl cid w n).size = tbl.size := by
  induction n generalizing tbl cid with
  | zero => rfl
  | succ n ih => simp [fillConst, ih, setFirst_size]

/-- `fillRun` keeps the table size. -/
theorem fillRun_size (tbl : Array (Option Fixed)) (cid : Nat) (ws : List (Option Fixed)) :
    (fillRun tbl cid ws).size = tbl.size := by
  induction ws generalizing tbl cid with
  | nil => rfl
  | cons w rest ih => cases w <;> simp [fillRun, ih, setFirst_size]

/-- `buildWAux` keeps the table size. -/
theorem buildWAux_size (tbl : Array (Option Fixed)) (budget : Nat) (es : List WEntry) :
    (buildWAux tbl budget es).1.size = tbl.size := by
  induction es generalizing tbl budget with
  | nil => rfl
  | cons e rest ih =>
    cases e <;> simp only [buildWAux] <;> split <;> simp [ih, fillRun_size, fillConst_size]

/-- The CID width table always has one entry per two-byte CID, so the lookup of every
Identity-H/V code is in bounds. -/
theorem buildWTable_size (es : List WEntry) : (buildWTable es).1.size = cidCount := by
  simp [buildWTable, buildWAux_size]

/-- Widths of a CIDFont (§9.7.4.3), for two-byte CIDs. -/
structure CIDMetrics where
  /-- `/DW`, default 1000 (as 1.0 in text space). -/
  dw : Fixed
  /-- Width of each CID `< 65536` from `/W`, `none` when not listed. -/
  table : Array (Option Fixed)
  /-- The `/W` cell budget ran out: some entries were ignored. -/
  truncated : Bool

/-- Read `/W` and `/DW` of a CIDFont dictionary. -/
def CIDMetrics.ofCIDFont (resolve : PdfObject → PdfObject) (cidFont : Dict) : CIDMetrics :=
  let entries :=
    match getR resolve cidFont "W" with
    | some (.array xs) => parseW resolve xs
    | _ => []
  let (table, truncated) := buildWTable entries
  { dw := ((getR resolve cidFont "DW").bind widthOfNum?).getD Fixed.one
    table, truncated }

/-- The width of a CID: `/W` entry, else `/DW`. -/
def CIDMetrics.width (m : CIDMetrics) (cid : Nat) : Fixed × WidthSource :=
  match m.table[cid]? with
  | some (some w) => (w, .widths)
  | _ => (m.dw, .defaultWidth)

/-- Split a string of an Identity-H/V font into two-byte big-endian codes (= CIDs); a
trailing odd byte is dropped. -/
def identityCodes : List UInt8 → List Nat
  | hi :: lo :: rest => (hi.toNat * 256 + lo.toNat) :: identityCodes rest
  | _ => []

/-- Identity codes: one CID per two bytes, each `< 65536`. -/
theorem identityCodes_length : ∀ bs : List UInt8, (identityCodes bs).length = bs.length / 2
  | [] => by simp [identityCodes]
  | [_] => by simp [identityCodes]
  | _ :: _ :: rest => by simp [identityCodes, identityCodes_length rest]; omega

/-! ## Fonts -/

/-- Metrics of a font usable for text layout. -/
inductive FontMetrics where
  /-- A simple font (Type1, MMType1, TrueType): one-byte codes. -/
  | simple (m : SimpleMetrics)
  /-- A Type0 font with an Identity-H (`vertical = false`) or Identity-V CMap. -/
  | cid (m : CIDMetrics) (vertical : Bool)

/-- Whether a Type0 font's `/Encoding` is a predefined identity CMap: `some false` for
`Identity-H`, `some true` for `Identity-V`, `none` otherwise (task 6.5). -/
def identityEncoding? (resolve : PdfObject → PdfObject) (fontDict : Dict) : Option Bool :=
  match getR resolve fontDict "Encoding" with
  | some (.name n) =>
    let s := glyphNameOf n.bytes
    if s == "Identity-H" then some false else if s == "Identity-V" then some true else none
  | _ => none

/-- Build the metrics of a font dictionary (§9.6, §9.7). `none` for Type 3 fonts (widths
scaled by `/FontMatrix`) and for Type0 fonts whose CMap is not Identity-H/V (6.5). A Type0
font without a usable descendant gets `/DW` 1000 for every CID. -/
def FontMetrics.ofDict (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) : Option FontMetrics :=
  let subtype := match getR resolve fontDict "Subtype" with
    | some (.name n) => glyphNameOf n.bytes
    | _ => ""
  if subtype == "Type3" then none
  else if subtype == "Type0" then
    match identityEncoding? resolve fontDict with
    | none => none
    | some vertical =>
      let desc : Dict :=
        match getR resolve fontDict "DescendantFonts" with
        | some (.array (d :: _)) =>
          match resolve d with
          | .dict dd => dd
          | _ => []
        | _ => []
      some (.cid (CIDMetrics.ofCIDFont resolve desc) vertical)
  else some (.simple (SimpleMetrics.ofDict resolve fontDict builtin?))

/-- The character codes of a shown string: bytes for simple fonts, two-byte CIDs for
Identity-H/V. -/
def FontMetrics.codes : FontMetrics → List UInt8 → List Nat
  | .simple _, bs => bs.map (·.toNat)
  | .cid _ _, bs => identityCodes bs

/-- The horizontal advance (glyph width / 1000) of one code, and its source. Total. -/
def FontMetrics.width : FontMetrics → Nat → Fixed × WidthSource
  | .simple m, c => m.width c
  | .cid m _, c => m.width c

/-! ## Spot checks -/

/-- `Fixed` from a raw value, for the checks below. -/
private def fx (r : Int) : Fixed := Fixed.clamp r

private def nm (s : String) : PdfObject := .name (Name.ofString s)

#guard widthOfNum? (.int 278) == some (fx 278000)
#guard widthOfNum? (.real ⟨2785, 1⟩) == some (fx 278500)
#guard widthOfNum? (nm "x") == none

/-- A Helvetica font without `/Widths` (standard 14 metrics). -/
private def helv : Dict :=
  [(Name.ofString "Type", nm "Font"), (Name.ofString "Subtype", nm "Type1"),
   (Name.ofString "BaseFont", nm "Helvetica"), (Name.ofString "Encoding", nm "WinAnsiEncoding")]

#guard (SimpleMetrics.ofDict id helv none).width 0x20 == (fx 278000, .std14)
#guard (SimpleMetrics.ofDict id helv none).width 0x57 == (fx 944000, .std14)
#guard (SimpleMetrics.ofDict id helv none).width 0x80 == (fx 556000, .std14)
#guard (SimpleMetrics.ofDict id helv none).width 0x01 == (Fixed.zero, .unknown)
#guard (SimpleMetrics.ofDict id helv none).width 300 == (Fixed.zero, .unknown)

/-- A subset TrueType font with `/Widths` for codes 32..34 and a `/MissingWidth`. -/
private def tt : Dict :=
  [(Name.ofString "Subtype", nm "TrueType"), (Name.ofString "BaseFont", nm "ABCDEF+Arial"),
   (Name.ofString "FirstChar", .int 32), (Name.ofString "LastChar", .int 34),
   (Name.ofString "Widths", .array [.int 250, nm "bad", .real ⟨5005, 1⟩, .int 9]),
   (Name.ofString "FontDescriptor", .dict [(Name.ofString "MissingWidth", .int 111)])]

#guard (SimpleMetrics.ofDict id tt none).width 32 == (fx 250000, .widths)
#guard (SimpleMetrics.ofDict id tt none).width 33 == (fx 111000, .missingWidth)
#guard (SimpleMetrics.ofDict id tt none).width 34 == (fx 500500, .widths)
#guard (SimpleMetrics.ofDict id tt none).width 35 == (fx 111000, .missingWidth)
#guard (SimpleMetrics.ofDict id tt none).width 65 == (fx 111000, .missingWidth)

/-- A Type0 Identity-H font with `/W` in both forms and `/DW`. -/
private def t0 : Dict :=
  [(Name.ofString "Subtype", nm "Type0"), (Name.ofString "Encoding", nm "Identity-H"),
   (Name.ofString "DescendantFonts", .array [.dict
     [(Name.ofString "Subtype", nm "CIDFontType2"), (Name.ofString "DW", .int 500),
      (Name.ofString "W", .array [.int 1, .array [.int 100, .int 200], nm "junk",
        .int 10, .int 20, .int 300, .int 15, .array [.int 999],
        .int 65535, .array [.int 7, .int 8]])]])]

/-- The metrics of `t0`. -/
private def t0m : FontMetrics := (FontMetrics.ofDict id t0 none).getD (.simple default)

#guard t0m.codes [0x00, 0x01, 0x00, 0x0F, 0xFF] == [1, 15]
#guard t0m.width 1 == (fx 100000, .widths)
#guard t0m.width 2 == (fx 200000, .widths)
#guard t0m.width 3 == (fx 500000, .defaultWidth)
#guard t0m.width 15 == (fx 300000, .widths)
#guard t0m.width 20 == (fx 300000, .widths)
#guard t0m.width 65535 == (fx 7000, .widths)
#guard t0m.width 70000 == (fx 500000, .defaultWidth)
#guard (parseW id [.int 1, .array [], .int 2, .int 3, .int 4, .int (-1), .int 5, .int 6]).length == 2
#guard (FontMetrics.ofDict id [(Name.ofString "Subtype", nm "Type3")] none).isNone
#guard (FontMetrics.ofDict id [(Name.ofString "Subtype", nm "Type0"),
  (Name.ofString "Encoding", nm "UniJIS-UTF16-H")] none).isNone
#guard (match FontMetrics.ofDict id [(Name.ofString "Subtype", nm "Type0"),
  (Name.ofString "Encoding", nm "Identity-V")] none with
  | some m => m.width 5 == (Fixed.one, .defaultWidth)
  | none => false)
-- A hostile `/W` (many full ranges) is cut by the cell budget.
#guard (buildWTable ((List.range 40).map fun _ => .range 0 65535 Fixed.one)).2

end SafePdf.Core.Font
