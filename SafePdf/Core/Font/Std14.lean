import SafePdf.Core.Font.Encoding

/-!
# Standard 14 fonts: metrics and substitution (Plan.md §6 Phase 6, task 6.4)

Advance widths of the standard 14 Type 1 fonts (ISO 32000-2 §9.6.2.2) for simple fonts that
omit `/Widths` (deprecated but common for the standard 14), and the substitution of common
font names (Arial, Times New Roman, Courier New, subset prefixes, style suffixes) onto them.

## Design decisions

* **Provenance.** The widths are the Adobe Core 14 AFM `WX` values (Helvetica, Times,
  Courier families), transcribed from memory of the AFM files (no AFM was downloaded, per the
  task's rules). Every row was written in one fixed glyph order and checked for alignment
  mechanically. Values are considered reliable for the StandardEncoding glyphs; the `Euro`
  entries (Helvetica 556, Times 500) are **unsure**: the 1997 Core 14 AFMs may not contain
  `Euro` at all; the values are those of later Adobe metrics used by common viewers.
* **Composites.** Accented letters (`Aacute`, `ccedilla`, `Scaron`, …) were not transcribed
  per font: their width is that of the base letter, which holds for every composite of these AFMs
  (`iacute`, `icircumflex`, `idieresis`, `igrave` take the width of `dotlessi`, e.g.
  Helvetica `i` 222 but `iacute` 278). `std14GlyphNames` lists base glyphs first, then the
  58 composites; the generated rows repeat the base width for each composite.
* **Courier** (all four styles) is monospaced: every glyph of the table is 600. The Oblique
  styles of Helvetica share the upright widths.
* **Symbol and ZapfDingbats** metrics (and their built-in encodings) are **not** tabulated:
  `Std14.width?` returns `none` for them, and width resolution reports the fallback. Reported
  as a follow-up task.
* **Substitution** (`Std14.ofBaseFont`): a subset tag `ABCDEF+` (six upper-case letters and
  `+`, §9.9.2) is stripped, spaces are removed, then the family is recognised by prefix
  (`Helvetica`/`Arial` → Helvetica, `TimesNewRoman`/`Times` → Times, `CourierNew`/`Courier`
  → Courier, `Symbol`, `ZapfDingbats`/`Dingbats`) and the style from the rest of the name
  (`Bold` → bold; `Italic` or `Oblique` → italic), so `Arial,Bold`, `Arial-BoldMT`,
  `TimesNewRomanPS-BoldItalicMT` and `Helvetica-Oblique` all resolve. Arial Narrow and other
  condensed variants map onto Helvetica (approximate widths).

Everything is pure and total.
-/

namespace SafePdf.Core.Font

/-- The standard 14 fonts (ISO 32000-2 §9.6.2.2). -/
inductive Std14 where
  /-- Helvetica. -/
  | helvetica
  /-- Helvetica-Bold. -/
  | helveticaBold
  /-- Helvetica-Oblique. -/
  | helveticaOblique
  /-- Helvetica-BoldOblique. -/
  | helveticaBoldOblique
  /-- Times-Roman. -/
  | timesRoman
  /-- Times-Bold. -/
  | timesBold
  /-- Times-Italic. -/
  | timesItalic
  /-- Times-BoldItalic. -/
  | timesBoldItalic
  /-- Courier. -/
  | courier
  /-- Courier-Bold. -/
  | courierBold
  /-- Courier-Oblique. -/
  | courierOblique
  /-- Courier-BoldOblique. -/
  | courierBoldOblique
  /-- Symbol. -/
  | symbol
  /-- ZapfDingbats. -/
  | zapfDingbats
  deriving DecidableEq, Repr, Inhabited

/-! ## Width tables (generated; see the module doc for provenance) -/

/-- Glyph names with standard-14 widths: StandardEncoding and WinAnsi glyphs plus `minus` and `Euro`, then the accented composites. Parallel to every width row. -/
def std14GlyphNames : Array String := #[
  "space", "exclam", "quotedbl", "numbersign", "dollar", "percent", "ampersand", "quoteright", "parenleft", "parenright", "asterisk", "plus",
  "comma", "hyphen", "period", "slash", "zero", "one", "two", "three", "four", "five", "six", "seven",
  "eight", "nine", "colon", "semicolon", "less", "equal", "greater", "question", "at", "A", "B", "C",
  "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O",
  "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z", "bracketleft",
  "backslash", "bracketright", "asciicircum", "underscore", "quoteleft", "a", "b", "c", "d", "e", "f", "g",
  "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s",
  "t", "u", "v", "w", "x", "y", "z", "braceleft", "bar", "braceright", "asciitilde", "exclamdown",
  "cent", "sterling", "fraction", "yen", "florin", "section", "currency", "quotesingle", "quotedblleft", "guillemotleft", "guilsinglleft", "guilsinglright",
  "fi", "fl", "endash", "dagger", "daggerdbl", "periodcentered", "paragraph", "bullet", "quotesinglbase", "quotedblbase", "quotedblright", "guillemotright",
  "ellipsis", "perthousand", "questiondown", "grave", "acute", "circumflex", "tilde", "macron", "breve", "dotaccent", "dieresis", "ring",
  "cedilla", "hungarumlaut", "ogonek", "caron", "emdash", "AE", "ordfeminine", "Lslash", "Oslash", "OE", "ordmasculine", "ae",
  "dotlessi", "lslash", "oslash", "oe", "germandbls", "brokenbar", "copyright", "registered", "logicalnot", "degree", "plusminus", "twosuperior",
  "threesuperior", "onesuperior", "mu", "multiply", "divide", "onequarter", "onehalf", "threequarters", "Eth", "eth", "Thorn", "thorn",
  "trademark", "minus", "Euro", "Aacute", "Acircumflex", "Adieresis", "Agrave", "Aring", "Atilde", "Ccedilla", "Eacute", "Ecircumflex",
  "Edieresis", "Egrave", "Iacute", "Icircumflex", "Idieresis", "Igrave", "Ntilde", "Oacute", "Ocircumflex", "Odieresis", "Ograve", "Otilde",
  "Scaron", "Uacute", "Ucircumflex", "Udieresis", "Ugrave", "Yacute", "Ydieresis", "Zcaron", "aacute", "acircumflex", "adieresis", "agrave",
  "aring", "atilde", "ccedilla", "eacute", "ecircumflex", "edieresis", "egrave", "iacute", "icircumflex", "idieresis", "igrave", "ntilde",
  "oacute", "ocircumflex", "odieresis", "ograve", "otilde", "scaron", "uacute", "ucircumflex", "udieresis", "ugrave", "yacute", "ydieresis",
  "zcaron"]

/-- Helvetica (and Helvetica-Oblique) AFM widths, parallel to `std14GlyphNames`. -/
def helveticaWidths : Array Nat := #[
  278, 278, 355, 556, 556, 889, 667, 222, 333, 333, 389, 584,
  278, 333, 278, 278, 556, 556, 556, 556, 556, 556, 556, 556,
  556, 556, 278, 278, 584, 584, 584, 556, 1015, 667, 667, 722,
  722, 667, 611, 778, 722, 278, 500, 667, 556, 833, 722, 778,
  667, 778, 722, 667, 611, 722, 667, 944, 667, 667, 611, 278,
  278, 278, 469, 556, 222, 556, 556, 500, 556, 556, 278, 556,
  556, 222, 222, 500, 222, 833, 556, 556, 556, 556, 333, 500,
  278, 556, 500, 722, 500, 500, 500, 334, 260, 334, 584, 333,
  556, 556, 167, 556, 556, 556, 556, 191, 333, 556, 333, 333,
  500, 500, 556, 556, 556, 278, 537, 350, 222, 333, 333, 556,
  1000, 1000, 611, 333, 333, 333, 333, 333, 333, 333, 333, 333,
  333, 333, 333, 333, 1000, 1000, 370, 556, 778, 1000, 365, 889,
  278, 222, 611, 944, 611, 260, 737, 737, 584, 400, 584, 333,
  333, 333, 556, 584, 584, 834, 834, 834, 722, 556, 667, 556,
  1000, 584, 556, 667, 667, 667, 667, 667, 667, 722, 667, 667,
  667, 667, 278, 278, 278, 278, 722, 778, 778, 778, 778, 778,
  667, 722, 722, 722, 722, 667, 667, 611, 556, 556, 556, 556,
  556, 556, 500, 556, 556, 556, 556, 278, 278, 278, 278, 556,
  556, 556, 556, 556, 556, 500, 556, 556, 556, 556, 500, 500,
  500]

/-- Helvetica-Bold (and Helvetica-BoldOblique) AFM widths, parallel to `std14GlyphNames`. -/
def helveticaBoldWidths : Array Nat := #[
  278, 333, 474, 556, 556, 889, 722, 278, 333, 333, 389, 584,
  278, 333, 278, 278, 556, 556, 556, 556, 556, 556, 556, 556,
  556, 556, 333, 333, 584, 584, 584, 611, 975, 722, 722, 722,
  722, 667, 611, 778, 722, 278, 556, 722, 611, 833, 722, 778,
  667, 778, 722, 667, 611, 722, 667, 944, 667, 667, 611, 333,
  278, 333, 584, 556, 278, 556, 611, 556, 611, 556, 333, 611,
  611, 278, 278, 556, 278, 889, 611, 611, 611, 611, 389, 556,
  333, 611, 556, 778, 556, 556, 500, 389, 280, 389, 584, 333,
  556, 556, 167, 556, 556, 556, 556, 238, 500, 556, 333, 333,
  611, 611, 556, 556, 556, 278, 556, 350, 278, 500, 500, 556,
  1000, 1000, 611, 333, 333, 333, 333, 333, 333, 333, 333, 333,
  333, 333, 333, 333, 1000, 1000, 370, 611, 778, 1000, 365, 889,
  278, 278, 611, 944, 611, 280, 737, 737, 584, 400, 584, 333,
  333, 333, 611, 584, 584, 834, 834, 834, 722, 611, 667, 611,
  1000, 584, 556, 722, 722, 722, 722, 722, 722, 722, 667, 667,
  667, 667, 278, 278, 278, 278, 722, 778, 778, 778, 778, 778,
  667, 722, 722, 722, 722, 667, 667, 611, 556, 556, 556, 556,
  556, 556, 556, 556, 556, 556, 556, 278, 278, 278, 278, 611,
  611, 611, 611, 611, 611, 556, 611, 611, 611, 611, 556, 556,
  500]

/-- Times-Roman AFM widths, parallel to `std14GlyphNames`. -/
def timesRomanWidths : Array Nat := #[
  250, 333, 408, 500, 500, 833, 778, 333, 333, 333, 500, 564,
  250, 333, 250, 278, 500, 500, 500, 500, 500, 500, 500, 500,
  500, 500, 278, 278, 564, 564, 564, 444, 921, 722, 667, 667,
  722, 611, 556, 722, 722, 333, 389, 722, 611, 889, 722, 722,
  556, 722, 667, 556, 611, 722, 722, 944, 722, 722, 611, 333,
  278, 333, 469, 500, 333, 444, 500, 444, 500, 444, 333, 500,
  500, 278, 278, 500, 278, 778, 500, 500, 500, 500, 333, 389,
  278, 500, 500, 722, 500, 500, 444, 480, 200, 480, 541, 333,
  500, 500, 167, 500, 500, 500, 500, 180, 444, 500, 333, 333,
  556, 556, 500, 500, 500, 250, 453, 350, 333, 444, 444, 500,
  1000, 1000, 444, 333, 333, 333, 333, 333, 333, 333, 333, 333,
  333, 333, 333, 333, 1000, 889, 276, 611, 722, 889, 310, 667,
  278, 278, 500, 722, 500, 200, 760, 760, 564, 400, 564, 300,
  300, 300, 500, 564, 564, 750, 750, 750, 722, 500, 556, 500,
  980, 564, 500, 722, 722, 722, 722, 722, 722, 667, 611, 611,
  611, 611, 333, 333, 333, 333, 722, 722, 722, 722, 722, 722,
  556, 722, 722, 722, 722, 722, 722, 611, 444, 444, 444, 444,
  444, 444, 444, 444, 444, 444, 444, 278, 278, 278, 278, 500,
  500, 500, 500, 500, 500, 389, 500, 500, 500, 500, 500, 500,
  444]

/-- Times-Bold AFM widths, parallel to `std14GlyphNames`. -/
def timesBoldWidths : Array Nat := #[
  250, 333, 555, 500, 500, 1000, 833, 333, 333, 333, 500, 570,
  250, 333, 250, 278, 500, 500, 500, 500, 500, 500, 500, 500,
  500, 500, 333, 333, 570, 570, 570, 500, 930, 722, 667, 722,
  722, 667, 611, 778, 778, 389, 500, 778, 667, 944, 722, 778,
  611, 778, 722, 556, 667, 722, 722, 1000, 722, 722, 667, 333,
  278, 333, 581, 500, 333, 500, 556, 444, 556, 444, 333, 500,
  556, 278, 333, 556, 278, 833, 556, 500, 556, 556, 444, 389,
  333, 556, 500, 722, 500, 500, 444, 394, 220, 394, 520, 333,
  500, 500, 167, 500, 500, 500, 500, 278, 500, 500, 333, 333,
  556, 556, 500, 500, 500, 250, 540, 350, 333, 500, 500, 500,
  1000, 1000, 500, 333, 333, 333, 333, 333, 333, 333, 333, 333,
  333, 333, 333, 333, 1000, 1000, 300, 667, 778, 1000, 330, 722,
  278, 278, 500, 722, 556, 220, 747, 747, 570, 400, 570, 300,
  300, 300, 556, 570, 570, 750, 750, 750, 722, 500, 611, 556,
  1000, 570, 500, 722, 722, 722, 722, 722, 722, 722, 667, 667,
  667, 667, 389, 389, 389, 389, 722, 778, 778, 778, 778, 778,
  556, 722, 722, 722, 722, 722, 722, 667, 500, 500, 500, 500,
  500, 500, 444, 444, 444, 444, 444, 278, 278, 278, 278, 556,
  500, 500, 500, 500, 500, 389, 556, 556, 556, 556, 500, 500,
  444]

/-- Times-Italic AFM widths, parallel to `std14GlyphNames`. -/
def timesItalicWidths : Array Nat := #[
  250, 333, 420, 500, 500, 833, 778, 333, 333, 333, 500, 675,
  250, 333, 250, 278, 500, 500, 500, 500, 500, 500, 500, 500,
  500, 500, 333, 333, 675, 675, 675, 500, 920, 611, 611, 667,
  722, 611, 611, 722, 722, 333, 444, 667, 556, 833, 667, 722,
  611, 722, 611, 500, 556, 722, 611, 833, 611, 556, 556, 389,
  278, 389, 422, 500, 333, 500, 500, 444, 500, 444, 278, 500,
  500, 278, 278, 444, 278, 722, 500, 500, 500, 500, 389, 389,
  278, 500, 444, 667, 444, 444, 389, 400, 275, 400, 541, 389,
  500, 500, 167, 500, 500, 500, 500, 214, 556, 500, 333, 333,
  500, 500, 500, 500, 500, 250, 523, 350, 333, 556, 556, 500,
  889, 1000, 500, 333, 333, 333, 333, 333, 333, 333, 333, 333,
  333, 333, 333, 333, 889, 889, 276, 556, 722, 944, 310, 667,
  278, 278, 500, 667, 500, 275, 760, 760, 675, 400, 675, 300,
  300, 300, 500, 675, 675, 750, 750, 750, 722, 500, 611, 500,
  980, 675, 500, 611, 611, 611, 611, 611, 611, 667, 611, 611,
  611, 611, 333, 333, 333, 333, 667, 722, 722, 722, 722, 722,
  500, 722, 722, 722, 722, 556, 556, 556, 500, 500, 500, 500,
  500, 500, 444, 444, 444, 444, 444, 278, 278, 278, 278, 500,
  500, 500, 500, 500, 500, 389, 500, 500, 500, 500, 444, 444,
  389]

/-- Times-BoldItalic AFM widths, parallel to `std14GlyphNames`. -/
def timesBoldItalicWidths : Array Nat := #[
  250, 389, 555, 500, 500, 833, 778, 333, 333, 333, 500, 570,
  250, 333, 250, 278, 500, 500, 500, 500, 500, 500, 500, 500,
  500, 500, 333, 333, 570, 570, 570, 500, 832, 667, 667, 667,
  722, 667, 667, 722, 778, 389, 500, 667, 611, 889, 722, 722,
  611, 722, 667, 556, 611, 722, 667, 889, 667, 611, 611, 333,
  278, 333, 570, 500, 333, 500, 500, 444, 500, 444, 333, 500,
  556, 278, 278, 500, 278, 778, 556, 500, 500, 500, 389, 389,
  278, 556, 444, 667, 500, 444, 389, 348, 220, 348, 570, 389,
  500, 500, 167, 500, 500, 500, 500, 278, 500, 500, 333, 333,
  556, 556, 500, 500, 500, 250, 500, 350, 333, 500, 500, 500,
  1000, 1000, 500, 333, 333, 333, 333, 333, 333, 333, 333, 333,
  333, 333, 333, 333, 1000, 944, 266, 611, 722, 944, 300, 722,
  278, 278, 500, 722, 500, 220, 747, 747, 606, 400, 570, 300,
  300, 300, 576, 570, 570, 750, 750, 750, 722, 500, 611, 500,
  1000, 606, 500, 667, 667, 667, 667, 667, 667, 667, 667, 667,
  667, 667, 389, 389, 389, 389, 722, 722, 722, 722, 722, 722,
  556, 722, 722, 722, 722, 611, 611, 611, 500, 500, 500, 500,
  500, 500, 444, 444, 444, 444, 444, 278, 278, 278, 278, 556,
  500, 500, 500, 500, 500, 389, 556, 556, 556, 556, 444, 444,
  389]


set_option maxRecDepth 4000 in
/-- Every width row is parallel to `std14GlyphNames`. -/
theorem std14_rows_size :
    std14GlyphNames.size = 229 ∧ helveticaWidths.size = 229 ∧
    helveticaBoldWidths.size = 229 ∧ timesRomanWidths.size = 229 ∧
    timesBoldWidths.size = 229 ∧ timesItalicWidths.size = 229 ∧
    timesBoldItalicWidths.size = 229 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Std14

/-- The PostScript name of a standard font. -/
def postScriptName : Std14 → String
  | helvetica => "Helvetica"
  | helveticaBold => "Helvetica-Bold"
  | helveticaOblique => "Helvetica-Oblique"
  | helveticaBoldOblique => "Helvetica-BoldOblique"
  | timesRoman => "Times-Roman"
  | timesBold => "Times-Bold"
  | timesItalic => "Times-Italic"
  | timesBoldItalic => "Times-BoldItalic"
  | courier => "Courier"
  | courierBold => "Courier-Bold"
  | courierOblique => "Courier-Oblique"
  | courierBoldOblique => "Courier-BoldOblique"
  | symbol => "Symbol"
  | zapfDingbats => "ZapfDingbats"

/-- Whether the font is symbolic (its built-in encoding is not StandardEncoding). -/
def isSymbolic : Std14 → Bool
  | symbol | zapfDingbats => true
  | _ => false

/-- The AFM advance width (glyph space, 1/1000 em) of a glyph, when tabulated. `none` for a
glyph outside `std14GlyphNames` and for Symbol / ZapfDingbats (not tabulated). -/
def width? (f : Std14) (g : GlyphName) : Option Nat :=
  match std14GlyphNames.findIdx? (· == g) with
  | none => none
  | some i =>
    match f with
    | helvetica | helveticaOblique => helveticaWidths[i]?
    | helveticaBold | helveticaBoldOblique => helveticaBoldWidths[i]?
    | timesRoman => timesRomanWidths[i]?
    | timesBold => timesBoldWidths[i]?
    | timesItalic => timesItalicWidths[i]?
    | timesBoldItalic => timesBoldItalicWidths[i]?
    | courier | courierBold | courierOblique | courierBoldOblique => some 600
    | symbol | zapfDingbats => none

end Std14

/-! ## Name substitution -/

/-- Strip a subset tag: six upper-case ASCII letters followed by `+` (ISO 32000-2 §9.9.2). -/
def stripSubsetTag (cs : List Char) : List Char :=
  match cs with
  | a :: b :: c :: d :: e :: f :: '+' :: rest =>
    if [a, b, c, d, e, f].all fun x => 'A' ≤ x ∧ x ≤ 'Z' then rest else cs
  | _ => cs

/-- Whether `pat` occurs as a contiguous sublist of `cs`. -/
def hasInfix (pat : List Char) : List Char → Bool
  | [] => pat.isEmpty
  | c :: rest => pat.isPrefixOf (c :: rest) || hasInfix pat rest

/-- Style of a standard family from the rest of a font name: (bold, italic). -/
def styleOf (rest : List Char) : Bool × Bool :=
  (hasInfix "Bold".toList rest,
    hasInfix "Italic".toList rest || hasInfix "Oblique".toList rest)

/-- Font families recognised by prefix, in the order tried (longest prefixes first). -/
def familyPrefixes : List (String × Nat) :=
  [("ZapfDingbats", 3), ("Dingbats", 3), ("Symbol", 4), ("Helvetica", 0), ("Arial", 0),
   ("TimesNewRoman", 1), ("Times", 1), ("CourierNew", 2), ("Courier", 2)]

/-- The standard font of a family index (`0` Helvetica, `1` Times, `2` Courier, `3`
ZapfDingbats, `4` Symbol) and style. -/
def ofFamily (fam : Nat) (bold italic : Bool) : Std14 :=
  match fam, bold, italic with
  | 0, false, false => .helvetica
  | 0, true, false => .helveticaBold
  | 0, false, true => .helveticaOblique
  | 0, true, true => .helveticaBoldOblique
  | 1, false, false => .timesRoman
  | 1, true, false => .timesBold
  | 1, false, true => .timesItalic
  | 1, true, true => .timesBoldItalic
  | 2, false, false => .courier
  | 2, true, false => .courierBold
  | 2, false, true => .courierOblique
  | 2, true, true => .courierBoldOblique
  | 3, _, _ => .zapfDingbats
  | _, _, _ => .symbol

/-- Map a `/BaseFont` name onto a standard 14 font (see the module doc for the rules);
`none` when the family is not recognised. -/
def Std14.ofBaseFont (name : String) : Option Std14 :=
  let cs := (stripSubsetTag name.toList).filter (· ≠ ' ')
  match familyPrefixes.find? (fun p => p.1.toList.isPrefixOf cs) with
  | none => none
  | some (pfx, fam) =>
    let (bold, italic) := styleOf (cs.drop pfx.length)
    some (ofFamily fam bold italic)

/-! ## Spot checks -/

#guard Std14.helvetica.width? "space" == some 278
#guard Std14.helvetica.width? "a" == some 556
#guard Std14.helvetica.width? "W" == some 944
#guard Std14.helvetica.width? "i" == some 222
#guard Std14.helvetica.width? "iacute" == some 278
#guard Std14.helvetica.width? "at" == some 1015
#guard Std14.helveticaBoldOblique.width? "a" == some 556
#guard Std14.helveticaBold.width? "b" == some 611
#guard Std14.timesRoman.width? "space" == some 250
#guard Std14.timesRoman.width? "a" == some 444
#guard Std14.timesRoman.width? "W" == some 944
#guard Std14.timesRoman.width? "Aacute" == some 722
#guard Std14.timesBold.width? "W" == some 1000
#guard Std14.timesItalic.width? "A" == some 611
#guard Std14.timesBoldItalic.width? "mu" == some 576
#guard Std14.courier.width? "W" == some 600
#guard Std14.courierBoldOblique.width? "eacute" == some 600
#guard Std14.symbol.width? "space" == none
#guard Std14.helvetica.width? "nonexistent" == none
-- Every glyph of StandardEncoding and WinAnsiEncoding has a Helvetica / Times width.
#guard [standardEncoding, winAnsiEncoding, macRomanEncoding, pdfDocEncoding].all fun e =>
  e.all fun g => match g with
    | some n => (Std14.timesBoldItalic.width? n).isSome && (Std14.helvetica.width? n).isSome
    | none => true
#guard Std14.ofBaseFont "Helvetica" == some .helvetica
#guard Std14.ofBaseFont "Times-Roman" == some .timesRoman
#guard Std14.ofBaseFont "Arial" == some .helvetica
#guard Std14.ofBaseFont "ArialMT" == some .helvetica
#guard Std14.ofBaseFont "Arial,Bold" == some .helveticaBold
#guard Std14.ofBaseFont "Arial-BoldItalicMT" == some .helveticaBoldOblique
#guard Std14.ofBaseFont "ABCDEF+Arial-ItalicMT" == some .helveticaOblique
#guard Std14.ofBaseFont "TimesNewRoman" == some .timesRoman
#guard Std14.ofBaseFont "TimesNewRomanPS-BoldItalicMT" == some .timesBoldItalic
#guard Std14.ofBaseFont "Times New Roman,Italic" == some .timesItalic
#guard Std14.ofBaseFont "CourierNew,Bold" == some .courierBold
#guard Std14.ofBaseFont "Courier-Oblique" == some .courierOblique
#guard Std14.ofBaseFont "Symbol" == some .symbol
#guard Std14.ofBaseFont "ZapfDingbats" == some .zapfDingbats
#guard Std14.ofBaseFont "AbCDEF+Arial" == none
#guard Std14.ofBaseFont "Calibri" == none

end SafePdf.Core.Font
