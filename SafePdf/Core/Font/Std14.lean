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
  mechanically. Values are considered reliable for the StandardEncoding glyphs. **`Euro`**
  (task 6.4b): Helvetica and Helvetica-Bold 556, all four Times styles 500, Courier 600. These
  are the `Euro` entries of the Core 14 AFM set as redistributed by the open-source viewers
  (pdf.js `metrics.js`, PDFBox, MuPDF) and agree with the fonts' design (Euro at the figure
  width: Helvetica/Times figures are 556/500). **Verified (6.4c)**: every width of every row
  (the 229 glyphs × 12 text fonts, `Euro` included) equals the `WX` of the Adobe Core14 AFMs as redistributed by Apache PDFBox 3.0.3 (`pdfbox/src/main/resources/org/apache/pdfbox/resources/afm/`); no
  mismatch. (Adobe's 1997 text-font AFMs have no `Euro`; the redistributed files add it as an
  unencoded `C -1` entry with the values above.)
* **Composites.** Accented letters (`Aacute`, `ccedilla`, `Scaron`, …) were not transcribed
  per font: their width is that of the base letter, which holds for every composite of these AFMs
  (`iacute`, `icircumflex`, `idieresis`, `igrave` take the width of `dotlessi`, e.g.
  Helvetica `i` 222 but `iacute` 278). `std14GlyphNames` lists base glyphs first, then the
  58 composites; the generated rows repeat the base width for each composite.
* **Courier** (all four styles) is monospaced: every glyph of the table is 600. The Oblique
  styles of Helvetica share the upright widths.
* **Symbol and ZapfDingbats** (task 6.4b): `symbolWidths` and `zapfDingbatsWidths` are the
  `WX` values of Adobe's `Symbol.afm` (001.008) and `ZapfDingbats.afm` (002.000), indexed by
  **code** of the fonts' built-in encodings (`symbolNames`, `zapfDingbatsNames` in
  `Font.Encoding`); written from memory in 6.4b, verified code by code against the AFMs in
  6.4c (one fix: Symbol `0xF0` is unassigned). Every glyph of these two AFMs is encoded except
  Symbol's `apple` (`C -1`, `WX 790`), so `width?` looks the glyph name up in the built-in
  encoding and special-cases `apple` (`symbolAppleWidth`).
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


/-- Symbol AFM widths by **code** (parallel to `symbolNames`, the built-in encoding; `0` where
unassigned). -/
def symbolWidths : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  250, 333, 713, 500, 549, 833, 778, 439, 333, 333, 500, 549, 250, 549, 250, 278,
  500, 500, 500, 500, 500, 500, 500, 500, 500, 500, 278, 278, 549, 549, 549, 444,
  549, 722, 667, 722, 612, 611, 763, 603, 722, 333, 631, 722, 686, 889, 722, 722,
  768, 741, 556, 592, 611, 690, 439, 768, 645, 795, 611, 333, 863, 333, 658, 500,
  500, 631, 549, 549, 494, 439, 521, 411, 603, 329, 603, 549, 549, 576, 521, 549,
  549, 521, 549, 603, 439, 576, 713, 686, 493, 686, 494, 480, 200, 480, 549, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  750, 620, 247, 549, 167, 713, 500, 753, 753, 753, 753, 1042, 987, 603, 987, 603,
  400, 549, 411, 549, 549, 713, 494, 460, 549, 549, 549, 549, 1000, 603, 1000, 658,
  823, 686, 795, 987, 768, 768, 823, 768, 768, 713, 713, 713, 713, 713, 713, 713,
  768, 713, 790, 790, 890, 823, 549, 250, 713, 603, 603, 1042, 987, 603, 987, 603,
  494, 329, 790, 790, 786, 713, 384, 384, 384, 384, 384, 384, 494, 494, 494, 494,
  0, 329, 274, 686, 686, 686, 384, 384, 384, 384, 384, 384, 494, 494, 494, 0]

/-- Width of Symbol's one unencoded glyph, `apple` (`Symbol.afm`: `C -1 ; WX 790 ; N apple`). It
is reachable only through `/Differences`. -/
def symbolAppleWidth : Nat := 790

/-- ZapfDingbats AFM widths by **code** (parallel to `zapfDingbatsNames`, the built-in
encoding; `0` where unassigned). -/
def zapfDingbatsWidths : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  278, 974, 961, 974, 980, 719, 789, 790, 791, 690, 960, 939, 549, 855, 911, 933,
  911, 945, 974, 755, 846, 762, 761, 571, 677, 763, 760, 759, 754, 494, 552, 537,
  577, 692, 786, 788, 788, 790, 793, 794, 816, 823, 789, 841, 823, 833, 816, 831,
  923, 744, 723, 749, 790, 792, 695, 776, 768, 792, 759, 707, 708, 682, 701, 826,
  815, 789, 789, 707, 687, 696, 689, 786, 787, 713, 791, 785, 791, 873, 761, 762,
  762, 759, 759, 892, 892, 788, 784, 438, 138, 277, 415, 392, 392, 668, 668, 0,
  390, 390, 317, 317, 276, 276, 509, 509, 410, 410, 234, 234, 334, 334, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 732, 544, 544, 910, 667, 760, 760, 776, 595, 694, 626, 788, 788, 788, 788,
  788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788,
  788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788, 788,
  788, 788, 788, 788, 894, 838, 1016, 458, 748, 924, 748, 918, 927, 928, 928, 834,
  873, 828, 924, 924, 917, 930, 931, 463, 883, 836, 836, 867, 867, 696, 696, 874,
  0, 874, 760, 946, 771, 865, 771, 888, 967, 888, 831, 873, 927, 970, 918, 0]

set_option maxRecDepth 4000 in
/-- The Symbol and ZapfDingbats width rows have one entry per code. -/
theorem symbolic_rows_size : symbolWidths.size = 256 ∧ zapfDingbatsWidths.size = 256 := by
  refine ⟨rfl, rfl⟩

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

/-- The width of glyph `g` in a font whose glyphs are exactly those of a 256-entry built-in
encoding `names` (`""` = unassigned), with widths `ws` by code. -/
def widthByCode (names : Array String) (ws : Array Nat) (g : GlyphName) : Option Nat :=
  if g.isEmpty then none
  else
    match names.findIdx? (· == g) with
    | none => none
    | some i => ws[i]?

/-- The AFM advance width (glyph space, 1/1000 em) of a glyph, when tabulated. `none` for a
glyph outside `std14GlyphNames` (Helvetica, Times, Courier) or outside the built-in encoding
(Symbol, ZapfDingbats). -/
def width? (f : Std14) (g : GlyphName) : Option Nat :=
  match f with
  | symbol => if g == "apple" then some symbolAppleWidth else widthByCode symbolNames symbolWidths g
  | zapfDingbats => widthByCode zapfDingbatsNames zapfDingbatsWidths g
  | _ =>
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

/-- Advance (1/1000 em) of the substitute font's `.notdef` glyph, used for a code with no glyph
in a font without `/Widths`. MuPDF 1.25.1 (`pdf_load_simple_font`, `ft_width`) takes the advance
of glyph 0 of the URW substitute; measured with `mutool draw -F stext` it equals the `space`
width of each of the 14 fonts (278 Helvetica and ZapfDingbats, 250 Times and Symbol, 600
Courier). -/
def notdefWidth (f : Std14) : Nat :=
  (f.width? "space").getD 600

end Std14

/-! ## Name substitution -/

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
#guard Std14.zapfDingbats.width? "a4" == some 719
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
-- Euro widths (Core 14 AFMs).
#guard Std14.helvetica.width? "Euro" == some 556
#guard Std14.helveticaBold.width? "Euro" == some 556
#guard Std14.timesRoman.width? "Euro" == some 500
#guard Std14.timesBoldItalic.width? "Euro" == some 500
#guard Std14.courier.width? "Euro" == some 600
-- Symbol and ZapfDingbats.
#guard Std14.symbol.width? "space" == some 250
#guard Std14.symbol.width? "alpha" == some 631
#guard Std14.symbol.width? "Lambda" == some 686
#guard Std14.symbol.width? "minus" == some 549
#guard Std14.symbol.width? "arrowboth" == some 1042
#guard Std14.symbol.width? "Euro" == some 750
#guard Std14.symbol.width? "apple" == some 790
#guard Std14.symbol.width? "A" == none
#guard Std14.symbol.width? "" == none
#guard Std14.zapfDingbats.width? "space" == some 278
#guard Std14.zapfDingbats.width? "a1" == some 974
#guard Std14.zapfDingbats.width? "a20" == some 846
#guard Std14.zapfDingbats.width? "a120" == some 788
#guard Std14.zapfDingbats.width? "a163" == some 1016
#guard Std14.zapfDingbats.width? "a82" == some 138
#guard Std14.zapfDingbats.width? "a191" == some 918
#guard Std14.zapfDingbats.width? "alpha" == none
#guard Std14.symbol.width? "braceex" == some 494
#guard Std14.symbol.width? "angleright" == some 329
#guard Std14.symbol.width? "Upsilon1" == some 620
#guard Std14.zapfDingbats.width? "a89" == some 390
#guard Std14.zapfDingbats.width? "a205" == some 509
#guard Std14.zapfDingbats.width? "a96" == some 334
#guard Std14.zapfDingbats.width? "a101" == some 732
#guard Std14.timesItalic.width? "Euro" == some 500
#guard Std14.timesBold.width? "Euro" == some 500
#guard Std14.helveticaOblique.width? "Euro" == some 556
#guard Std14.helveticaBoldOblique.width? "Euro" == some 556
#guard Std14.courierBoldOblique.width? "Euro" == some 600
-- Every encoded Symbol / ZapfDingbats glyph has a non-zero width, and no unassigned code has one.
#guard (List.range 256).all fun c =>
  (symbolEncoding.glyph c).isSome == (symbolWidths.getD c 0 != 0)
#guard (List.range 256).all fun c =>
  (zapfDingbatsEncoding.glyph c).isSome == (zapfDingbatsWidths.getD c 0 != 0)
#guard Std14.ofBaseFont "Calibri" == none
#guard Std14.helveticaBold.notdefWidth == 278
#guard Std14.timesBoldItalic.notdefWidth == 250
#guard Std14.courierOblique.notdefWidth == 600
#guard Std14.symbol.notdefWidth == 250
#guard Std14.zapfDingbats.notdefWidth == 278

end SafePdf.Core.Font
