import SafePdf.Core.Text

/-!
# Substitute fonts for non-embedded fonts (task 7.7)

Plan.md §6 Phase 7 ("Faithfulness: pixel-differential vs MuPDF/pdf.js"), ISO 32000-2 §9.6.2.2
(standard 14 fonts), §9.8.2 (font descriptor flags). Ledger Decisions 2026-11-20 (7.7):
"Substitute fonts are found on the system, not committed".

A font without an embedded program (the standard 14, the "hail mary" font of a `Tf` naming no
font, any other non-embedded simple font) has no outlines. MuPDF paints such text with the
URW base-35 fonts it bundles; the repository ships no font files, so the **Shell** finds the
substitute programs on the system at run time (`SafePdf/Shell/Fonts.lean`: `SAFEPDF_FONT_DIR`,
then Debian's `fonts-urw-base35`, then `fonts-texgyre`) and hands their bytes to the core as
data: a `SubstFonts` table with one program per standard-14 face. Parsing is pure and lazy
(`Thunk`): a face is parsed by the existing Type 1 parser (`Font.Type1.parse`) or, for an
OpenType file, by the CFF parser on its `CFF ` table (`otfCFF?`), the first time a page needs
it, and then shared by every page.

## Choosing the substitute (MuPDF 1.25.1, `source/pdf/pdf-font.c`)

* `cleanName?` is `pdf_clean_font_name`: the `/BaseFont` compared, ignoring spaces, with the
  names of MuPDF's `base_font_names` table (the standard 14 and their Arial, Times New Roman,
  Courier New, Symbol MT aliases). No subset-tag stripping, no prefix matching: exactly
  MuPDF's table.
* **No `/FontDescriptor`** (`pdf_load_builtin_font`, `has_descriptor = 0`): the cleaned name,
  else Times-Roman (this is also the "hail mary" font: no dictionary at all).
* **A descriptor without an embedded program** (`pdf_load_font_descriptor`: `/FontFile`,
  else `/FontFile2`, else `/FontFile3`, embedded when that entry is an indirect reference): a
  cleaned name loads the built-in face; any other name goes to `pdf_load_system_font` →
  `pdf_load_substitute_font` with `mono` = `/Flags` FixedPitch (bit 1), `serif` = Serif
  (bit 2), `italic` = Italic (bit 7) or `Italic`/`Oblique` in the name, `bold` = ForceBold
  (bit 19) or `Bold` in the name (case-sensitive substrings, as `strstr`). MuPDF 1.25.1 does
  not look at `/FontWeight` or `/StemV`, so neither do we.
* Only the second case sets `ft_stretch` (`Choice.stretch`): MuPDF then scales each glyph
  horizontally by `w / realw` (`fz_adjust_ft_glyph_width`: `fz_pre_scale(trm, w/realw, 1)`),
  where `w` is the glyph's entry of the font's width table (`pdf_make_width_table`: the
  maximum of the integer `/Widths` of the codes that select the glyph, else `/MissingWidth`)
  and `realw` the substitute's own advance (×1000), when both are positive. `widthTable`
  reproduces the width table's inputs (`pdf_load_simple_font`: `/FirstChar`, `/LastChar`,
  integer entries via `pdf_array_get_int`, the range reset to `0..0` when out of `0..255`).
  Built-in faces (standard names and aliases, no descriptor) are never stretched.
* CIDFonts (`/Type0`) go to `pdf_load_system_font` with a collection (CJK fonts, or a
  substitute reached through a `to_ttf_cmap`): not substituted here (a gap, unpainted as
  before).

## Bounds

Nothing here loops over the input beyond fixed sizes: `cleanName?` scans a constant table,
`widthTable` at most 256 codes, `otfCFF?` at most `maxOtfTables` directory records; parsing
uses the parsers' own caps (`Limits.maxFontGlyphs`, `maxCFFGlyphs`, `glyphFuel`, …).
-/

namespace SafePdf.Core.Raster.Subst

open SafePdf SafePdf.Core
open SafePdf.Core.Font (Std14 Encoding)

/-! ## 1. Names (MuPDF `base_font_names`, `pdf_clean_font_name`) -/

/-- MuPDF 1.25.1's `base_font_names`: each standard-14 face with the names that select it
(the first is its PostScript name). -/
def baseFontNames : List (Std14 × List String) :=
  [ (.courier, ["Courier", "CourierNew", "CourierNewPSMT"]),
    (.courierBold, ["Courier-Bold", "CourierNew,Bold", "Courier,Bold", "CourierNewPS-BoldMT",
      "CourierNew-Bold"]),
    (.courierOblique, ["Courier-Oblique", "CourierNew,Italic", "Courier,Italic",
      "CourierNewPS-ItalicMT", "CourierNew-Italic"]),
    (.courierBoldOblique, ["Courier-BoldOblique", "CourierNew,BoldItalic", "Courier,BoldItalic",
      "CourierNewPS-BoldItalicMT", "CourierNew-BoldItalic"]),
    (.helvetica, ["Helvetica", "ArialMT", "Arial"]),
    (.helveticaBold, ["Helvetica-Bold", "Arial-BoldMT", "Arial,Bold", "Arial-Bold",
      "Helvetica,Bold"]),
    (.helveticaOblique, ["Helvetica-Oblique", "Arial-ItalicMT", "Arial,Italic", "Arial-Italic",
      "Helvetica,Italic", "Helvetica-Italic"]),
    (.helveticaBoldOblique, ["Helvetica-BoldOblique", "Arial-BoldItalicMT", "Arial,BoldItalic",
      "Arial-BoldItalic", "Helvetica,BoldItalic", "Helvetica-BoldItalic"]),
    (.timesRoman, ["Times-Roman", "TimesNewRomanPSMT", "TimesNewRoman", "TimesNewRomanPS"]),
    (.timesBold, ["Times-Bold", "TimesNewRomanPS-BoldMT", "TimesNewRoman,Bold",
      "TimesNewRomanPS-Bold", "TimesNewRoman-Bold"]),
    (.timesItalic, ["Times-Italic", "TimesNewRomanPS-ItalicMT", "TimesNewRoman,Italic",
      "TimesNewRomanPS-Italic", "TimesNewRoman-Italic"]),
    (.timesBoldItalic, ["Times-BoldItalic", "TimesNewRomanPS-BoldItalicMT",
      "TimesNewRoman,BoldItalic", "TimesNewRomanPS-BoldItalic", "TimesNewRoman-BoldItalic"]),
    (.symbol, ["Symbol", "Symbol,Italic", "Symbol,Bold", "Symbol,BoldItalic", "SymbolMT",
      "SymbolMT,Italic", "SymbolMT,Bold", "SymbolMT,BoldItalic"]),
    (.zapfDingbats, ["ZapfDingbats"]) ]

/-- A name without its spaces (`strcmp_ignore_space` compares these). -/
def noSpaces (s : String) : List Char := s.toList.filter (· ≠ ' ')

/-- **`pdf_clean_font_name`**: the standard-14 face a `/BaseFont` names exactly (spaces
ignored), if any. -/
def cleanName? (name : String) : Option Std14 :=
  let n := noSpaces name
  (baseFontNames.find? fun (_, ns) => ns.any fun s => noSpaces s == n).map (·.1)

/-- Whether `p` occurs in a character list. -/
def infixL (p : List Char) : List Char → Bool
  | [] => p.isEmpty
  | c :: cs => p.isPrefixOf (c :: cs) || infixL p cs

/-- Whether `pat` occurs in `s` (as C `strstr`). -/
def hasInfix (pat s : String) : Bool := infixL pat.toList s.toList

/-- **`pdf_lookup_substitute_font`**: the face for the style bits. -/
def substituteFace (mono serif bold italic : Bool) : Std14 :=
  if mono then
    if bold then (if italic then .courierBoldOblique else .courierBold)
    else (if italic then .courierOblique else .courier)
  else if serif then
    if bold then (if italic then .timesBoldItalic else .timesBold)
    else (if italic then .timesItalic else .timesRoman)
  else
    if bold then (if italic then .helveticaBoldOblique else .helveticaBold)
    else (if italic then .helveticaOblique else .helvetica)

/-- The chosen substitute: the face, and whether glyphs are stretched to the PDF widths. -/
structure Choice where
  /-- The standard-14 face whose program paints the font. -/
  face : Std14
  /-- MuPDF's `ft_stretch` (substitute, not built-in). -/
  stretch : Bool
  deriving DecidableEq, Repr

/-- Bit `k` (0-based) of a flags value. -/
def bit (flags : Int) (k : Nat) : Bool := flags.toNat / 2 ^ k % 2 == 1

/-- **The substitute of a non-embedded simple font** (see the module doc): `basefont` is the
`/BaseFont` (empty when absent), `flags` the descriptor's `/Flags` when the font has a
descriptor. -/
def choose (basefont : String) (flags : Option Int) : Choice :=
  match flags with
  | none => { face := (cleanName? basefont).getD .timesRoman, stretch := false }
  | some fl =>
    match cleanName? basefont with
    | some f => { face := f, stretch := false }
    | none =>
      let bold := hasInfix "Bold" basefont || bit fl 18
      let italic := hasInfix "Italic" basefont || hasInfix "Oblique" basefont || bit fl 6
      { face := substituteFace (bit fl 0) (bit fl 1) bold italic, stretch := true }

/-- Whether a font descriptor has an embedded program, as MuPDF decides it: the first of
`/FontFile`, `/FontFile2`, `/FontFile3` present is an indirect reference. -/
def embedded (desc : Dict) : Bool :=
  let first := (Dict.get? desc (Name.ofString "FontFile")).orElse fun _ =>
    (Dict.get? desc (Name.ofString "FontFile2")).orElse fun _ =>
      Dict.get? desc (Name.ofString "FontFile3")
  match first with
  | some (.ref _ _) => true
  | _ => false

/-- **The substitute for a simple font dictionary**, or `none` when it has an embedded
program (or is not a simple font: `/Type0`, `/Type3`, `/DescendantFonts`, `/CharProcs`). -/
def chooseFor (resolve : PdfObject → PdfObject) (fd : Dict) : Option Choice :=
  let subtype := (Text.nameStr? (Font.getR resolve fd "Subtype")).getD ""
  if subtype == "Type0" || subtype == "Type3" || (Font.getR resolve fd "DescendantFonts").isSome
    || (Font.getR resolve fd "CharProcs").isSome then none
  else
    let base := (Font.baseFontName? resolve fd).getD ""
    match Font.fontDescriptor? resolve fd with
    | none => some (choose base none)
    | some desc =>
      if embedded desc then none
      else some (choose base (some ((Font.getInt? resolve desc "Flags").getD 0)))

/-! ## 2. The PDF width table (`pdf_make_width_table` inputs) -/

/-- Truncation toward zero (C's `(int)` of a real). -/
def truncRat (q : Rat) : Int := if 0 ≤ q then q.floor else q.ceil

/-- `pdf_to_int` of a width entry: integers as they are, reals truncated, anything else 0. -/
def intOf : PdfObject → Int
  | .int i => i
  | .real d => truncRat ((d.mantissa : Rat) / ((10 ^ d.scale : Nat) : Rat))
  | _ => 0

/-- The PDF's horizontal metrics as MuPDF's simple-font loader records them: the
`(code, width)` pairs of `/Widths` (glyph units, integers) and the default width
(`/MissingWidth`, truncated; 0 when absent). `none` without `/Widths` (MuPDF then takes the
substitute's own widths: no stretch). -/
def widthTable (resolve : PdfObject → PdfObject) (fd : Dict) : Option (List (Nat × Int) × Int) :=
  match Font.getR resolve fd "Widths" with
  | some (.array ws) =>
    let first := (Font.getInt? resolve fd "FirstChar").getD 0
    let last := (Font.getInt? resolve fd "LastChar").getD 0
    let (first, last) := if first < 0 || 255 < last || last < first then (0, 0) else (first, last)
    let n := (last - first + 1).toNat
    let codes := (List.range n).map fun i =>
      (first.toNat + i, match ws[i]? with
        | some o => intOf (resolve o)
        | none => 0)
    let dflt := match (Font.fontDescriptor? resolve fd).bind (Font.getR resolve · "MissingWidth") with
      | some o => intOf o
      | none => 0
    some (codes, dflt)
  | _ => none

/-- The width table has at most 256 codes. -/
theorem widthTable_length_le (resolve : PdfObject → PdfObject) (fd : Dict)
    {t : List (Nat × Int) × Int} (h : widthTable resolve fd = some t) : t.1.length ≤ 256 := by
  unfold widthTable at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [List.length_map, List.length_range]
    split <;> simp_all <;> omega
  · simp at h

/-! ## 3. Programs and the table -/

/-- A parsed substitute program. -/
inductive Program where
  /-- A Type 1 font (`.t1`, `.pfb`, `.pfa`). -/
  | type1 (f : Font.Type1.Font1)
  /-- A CFF font (the `CFF ` table of an OpenType file). -/
  | cff (f : Font.CFF.CFFFont)

/-- The built-in encoding of a substitute program (the implicit base of the font's encoding). -/
def Program.builtin : Program → Encoding
  | .type1 f => f.encoding
  | .cff f => Text.cffEncoding f

/-- Most OpenType table directory records read. -/
def maxOtfTables : Nat := 64

/-- The `CFF ` table of an OpenType (`OTTO`) file, if any. -/
def otfCFF? (b : ByteArray) : Option ByteArray := do
  let tag ← Font.TrueType.u32At b 0
  if tag != Font.TrueType.tagOf "OTTO" then none
  let n ← Font.TrueType.u16At b 4
  let recs := (List.range (min n maxOtfTables)).filterMap (Font.TrueType.readRec b)
  let r ← Font.TrueType.findTable b recs (Font.TrueType.tagOf "CFF ")
  some (b.extract r.offset (r.offset + r.length))

/-- Parse a substitute program: an OpenType file through its `CFF ` table, anything else as
a Type 1 font (PFB segments, or clear text followed by `eexec`). `none` when it does not
parse. -/
def Program.parse (limits : Limits) (bytes : ByteArray) : Option Program :=
  match otfCFF? bytes with
  | some tbl =>
    match Font.CFF.parse limits tbl with
    | .ok f => if f.isCID then none else some (.cff f)
    | .error _ => none
  | none =>
    match Font.Type1.parse limits bytes with
    | .ok f => some (.type1 f)
    | .error _ => none

/-- The substitute programs found by the Shell, one per standard-14 face at most, each parsed
on first use (`Thunk`). The empty table (the default) paints nothing, as before task 7.7. -/
structure SubstFonts where
  /-- The faces and their (lazily parsed) programs. -/
  faces : List (Std14 × Thunk (Option Program)) := []

instance : Inhabited SubstFonts := ⟨{}⟩

/-- Build the table from file contents (first entry per face wins). -/
def SubstFonts.ofBytes (limits : Limits) (files : List (Std14 × ByteArray)) : SubstFonts :=
  { faces := files.map fun (f, b) => (f, Thunk.mk fun _ => Program.parse limits b) }

/-- The program of a face, if the Shell found one and it parses. -/
def SubstFonts.get? (t : SubstFonts) (f : Std14) : Option Program :=
  (t.faces.lookup f).bind Thunk.get

/-- Whether the table has no face at all. -/
def SubstFonts.isEmpty (t : SubstFonts) : Bool := t.faces.isEmpty

/-! ## 4. Checks -/

#guard cleanName? "Arial" == some .helvetica
#guard cleanName? "Arial,Bold" == some .helveticaBold
#guard cleanName? "TimesNewRoman" == some .timesRoman
#guard cleanName? "Times New Roman" == some .timesRoman
#guard cleanName? "CourierNew" == some .courier
#guard cleanName? "ABCDEF+Helvetica" == none
#guard cleanName? "Verdana" == none
#guard choose "" none == { face := .timesRoman, stretch := false }
#guard choose "Verdana" none == { face := .timesRoman, stretch := false }
#guard choose "Helvetica-Bold" (some 32) == { face := .helveticaBold, stretch := false }
-- Non-standard names with a descriptor: style from the flags and the name, stretched.
#guard choose "Verdana-Bold" (some 32) == { face := .helveticaBold, stretch := true }
#guard choose "Georgia" (some 34) == { face := .timesRoman, stretch := true }
#guard choose "Consolas" (some 33) == { face := .courier, stretch := true }
#guard choose "Foo" (some (2 + 64 + 262144)) == { face := .timesBoldItalic, stretch := true }
#guard intOf (.real ⟨5565, 1⟩) == 556 && intOf (.real ⟨-5565, 1⟩) == -556
#guard (widthTable id [(Name.ofString "FirstChar", .int 32), (Name.ofString "LastChar", .int 33),
  (Name.ofString "Widths", .array [.int 278, .real ⟨3555, 1⟩])]) == some ([(32, 278), (33, 355)], 0)
#guard (widthTable id [(Name.ofString "FirstChar", .int 32), (Name.ofString "LastChar", .int 300),
  (Name.ofString "Widths", .array [.int 278])]) == some ([(0, 278)], 0)

end SafePdf.Core.Raster.Subst
