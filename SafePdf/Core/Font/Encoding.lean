import SafePdf.Core.Object

/-!
# Simple-font encodings and glyph names (Plan.md §6 Phase 6, task 6.4)

Character encodings of simple fonts (ISO 32000-2 §9.6.5, Annex D) and the glyph-name to
Unicode fallback used by text extraction when a font has no `/ToUnicode` CMap (task 6.5).

## Design decisions

* **Glyph names are `String`s** (`GlyphName`). Lookups go through `Array String` tables with
  `==` search (v4.36 `match` on many `List UInt8` literal patterns is too slow to elaborate).
  A PDF name's bytes become a glyph name byte-for-byte as Latin-1 characters
  (`glyphNameOf`); real glyph names are ASCII, so this is the identity on them, and it is
  injective and total on any other bytes.
* **`Encoding = Array (Option GlyphName)`**, indexed by the one-byte character code; `none` is
  an unassigned code. The four predefined tables have 256 entries (`*_size` theorems), and
  `applyDifferences` preserves the size (`applyDifferences_size`), so every encoding built
  here has 256 entries.
* **Tables (Annex D, Table D.2 / D.3).** `standardEncoding`, `winAnsiEncoding`,
  `macRomanEncoding`, `pdfDocEncoding` are transcribed from Annex D. They were cross-checked
  mechanically while writing this file: WinAnsi against the `cp1252` code page and MacRoman
  against Mac OS Roman, through the glyph-to-Unicode table below (no mismatch apart from the
  documented differences). Notes of Annex D that are applied:
  - WinAnsi: `0xA0` is `space` (non-breaking), `0xAD` is `hyphen` (soft hyphen), and the
    unused codes `0x7F 0x81 0x8D 0x8F 0x90 0x9D` map to `bullet` (Annex D note 4, as pdf.js).
  - MacRoman: `0xCA` is `space`; `0xDB` is `currency` (not the later Apple `Euro`); the 15
    Mac OS Roman glyphs outside the Latin character set (`notequal infinity lessequal
    greaterequal partialdiff summation product pi integral Omega radical approxequal Delta
    lozenge apple`) are **not** in PDF's MacRomanEncoding and stay unassigned.
  - PDFDoc: `0x18`–`0x1F` are the spacing accents, `0x7F`, `0x9F`, `0xAD` are undefined.
  The built-in encodings of Symbol and ZapfDingbats are not tabulated here (reported as a follow-up);
  a caller that knows a font's built-in encoding passes it as `builtin?`.
* **`/Differences`** (§9.6.5.1, Table 112): an integer sets the current code, each following
  name is assigned to the current code which then increments. A code outside `0..255` makes
  the names up to the next integer ignored; any other object is skipped. Total, linear in the
  array, never fails.
* **Base encoding** (Table 112 `BaseEncoding`): an `/Encoding` name selects a predefined
  encoding; a dictionary uses its `/BaseEncoding` name, else the implicit base. The implicit
  base is the font program's built-in encoding when the caller knows it (`builtin?`: an
  embedded program's encoding, or a standard symbolic font's), else `StandardEncoding` (the
  §9.6.5 rule for nonsymbolic fonts; for a symbolic font without a known built-in encoding
  there is nothing better). `MacExpertEncoding` is not tabulated and falls back to the
  implicit base. TrueType-specific rules (§9.6.5.4) belong to task 6.1.
* **Glyph name → Unicode** follows the Adobe Glyph List Specification: drop the suffix from
  the first `.`, split at `_`, map each component through the AGL subset `aglNames` (every
  glyph of the four encodings plus `minus`, `ff`, `ffi`, `ffl`, `nbspace`, `sfthyphen` and the
  15 Mac symbols), else `uniXXXX…` (groups of four hex digits) or `uXXXX`–`uXXXXXX`, else
  nothing. Hex digits are accepted in either case (AGL requires upper case; pdf.js accepts
  both) and surrogates / values above `0x10FFFF` are rejected. `afii*` names are not covered.

Everything is pure and total.
-/

namespace SafePdf.Core.Font

open SafePdf

/-- A glyph name (ISO 32000-2 §9.6.5), e.g. `"Aacute"`, as a `String`. -/
abbrev GlyphName := String

/-- The glyph name spelled by a PDF name's bytes, each byte read as a Latin-1 character. -/
def glyphNameOf (bytes : List UInt8) : GlyphName :=
  String.ofList (bytes.map fun b => Char.ofNat b.toNat)

/-- A simple-font encoding: the glyph name of each one-byte code, `none` when unassigned. -/
abbrev Encoding := Array (Option GlyphName)

/-- Turn a 256-entry name table (`""` = unassigned) into an `Encoding`. -/
def ofNameTable (t : Array String) : Encoding :=
  t.map fun s => if s.isEmpty then none else some s

/-! ## Annex D tables (generated; see the module doc for provenance) -/

/-- Annex D column STD (StandardEncoding) by code; `""` = unassigned. -/
def standardNames : Array String := #[
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "space", "exclam", "quotedbl", "numbersign", "dollar", "percent", "ampersand", "quoteright",
  "parenleft", "parenright", "asterisk", "plus", "comma", "hyphen", "period", "slash",
  "zero", "one", "two", "three", "four", "five", "six", "seven",
  "eight", "nine", "colon", "semicolon", "less", "equal", "greater", "question",
  "at", "A", "B", "C", "D", "E", "F", "G",
  "H", "I", "J", "K", "L", "M", "N", "O",
  "P", "Q", "R", "S", "T", "U", "V", "W",
  "X", "Y", "Z", "bracketleft", "backslash", "bracketright", "asciicircum", "underscore",
  "quoteleft", "a", "b", "c", "d", "e", "f", "g",
  "h", "i", "j", "k", "l", "m", "n", "o",
  "p", "q", "r", "s", "t", "u", "v", "w",
  "x", "y", "z", "braceleft", "bar", "braceright", "asciitilde", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "exclamdown", "cent", "sterling", "fraction", "yen", "florin", "section",
  "currency", "quotesingle", "quotedblleft", "guillemotleft", "guilsinglleft", "guilsinglright", "fi", "fl",
  "", "endash", "dagger", "daggerdbl", "periodcentered", "", "paragraph", "bullet",
  "quotesinglbase", "quotedblbase", "quotedblright", "guillemotright", "ellipsis", "perthousand", "", "questiondown",
  "", "grave", "acute", "circumflex", "tilde", "macron", "breve", "dotaccent",
  "dieresis", "", "ring", "cedilla", "", "hungarumlaut", "ogonek", "caron",
  "emdash", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "AE", "", "ordfeminine", "", "", "", "",
  "Lslash", "Oslash", "OE", "ordmasculine", "", "", "", "",
  "", "ae", "", "", "", "dotlessi", "", "",
  "lslash", "oslash", "oe", "germandbls", "", "", "", ""
  ]

/-- Annex D column WIN (WinAnsiEncoding) by code; `""` = unassigned. -/
def winAnsiNames : Array String := #[
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "space", "exclam", "quotedbl", "numbersign", "dollar", "percent", "ampersand", "quotesingle",
  "parenleft", "parenright", "asterisk", "plus", "comma", "hyphen", "period", "slash",
  "zero", "one", "two", "three", "four", "five", "six", "seven",
  "eight", "nine", "colon", "semicolon", "less", "equal", "greater", "question",
  "at", "A", "B", "C", "D", "E", "F", "G",
  "H", "I", "J", "K", "L", "M", "N", "O",
  "P", "Q", "R", "S", "T", "U", "V", "W",
  "X", "Y", "Z", "bracketleft", "backslash", "bracketright", "asciicircum", "underscore",
  "grave", "a", "b", "c", "d", "e", "f", "g",
  "h", "i", "j", "k", "l", "m", "n", "o",
  "p", "q", "r", "s", "t", "u", "v", "w",
  "x", "y", "z", "braceleft", "bar", "braceright", "asciitilde", "bullet",
  "Euro", "bullet", "quotesinglbase", "florin", "quotedblbase", "ellipsis", "dagger", "daggerdbl",
  "circumflex", "perthousand", "Scaron", "guilsinglleft", "OE", "bullet", "Zcaron", "bullet",
  "bullet", "quoteleft", "quoteright", "quotedblleft", "quotedblright", "bullet", "endash", "emdash",
  "tilde", "trademark", "scaron", "guilsinglright", "oe", "bullet", "zcaron", "Ydieresis",
  "space", "exclamdown", "cent", "sterling", "currency", "yen", "brokenbar", "section",
  "dieresis", "copyright", "ordfeminine", "guillemotleft", "logicalnot", "hyphen", "registered", "macron",
  "degree", "plusminus", "twosuperior", "threesuperior", "acute", "mu", "paragraph", "periodcentered",
  "cedilla", "onesuperior", "ordmasculine", "guillemotright", "onequarter", "onehalf", "threequarters", "questiondown",
  "Agrave", "Aacute", "Acircumflex", "Atilde", "Adieresis", "Aring", "AE", "Ccedilla",
  "Egrave", "Eacute", "Ecircumflex", "Edieresis", "Igrave", "Iacute", "Icircumflex", "Idieresis",
  "Eth", "Ntilde", "Ograve", "Oacute", "Ocircumflex", "Otilde", "Odieresis", "multiply",
  "Oslash", "Ugrave", "Uacute", "Ucircumflex", "Udieresis", "Yacute", "Thorn", "germandbls",
  "agrave", "aacute", "acircumflex", "atilde", "adieresis", "aring", "ae", "ccedilla",
  "egrave", "eacute", "ecircumflex", "edieresis", "igrave", "iacute", "icircumflex", "idieresis",
  "eth", "ntilde", "ograve", "oacute", "ocircumflex", "otilde", "odieresis", "divide",
  "oslash", "ugrave", "uacute", "ucircumflex", "udieresis", "yacute", "thorn", "ydieresis"
  ]

/-- Annex D column MAC (MacRomanEncoding) by code; `""` = unassigned. -/
def macRomanNames : Array String := #[
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "space", "exclam", "quotedbl", "numbersign", "dollar", "percent", "ampersand", "quotesingle",
  "parenleft", "parenright", "asterisk", "plus", "comma", "hyphen", "period", "slash",
  "zero", "one", "two", "three", "four", "five", "six", "seven",
  "eight", "nine", "colon", "semicolon", "less", "equal", "greater", "question",
  "at", "A", "B", "C", "D", "E", "F", "G",
  "H", "I", "J", "K", "L", "M", "N", "O",
  "P", "Q", "R", "S", "T", "U", "V", "W",
  "X", "Y", "Z", "bracketleft", "backslash", "bracketright", "asciicircum", "underscore",
  "grave", "a", "b", "c", "d", "e", "f", "g",
  "h", "i", "j", "k", "l", "m", "n", "o",
  "p", "q", "r", "s", "t", "u", "v", "w",
  "x", "y", "z", "braceleft", "bar", "braceright", "asciitilde", "",
  "Adieresis", "Aring", "Ccedilla", "Eacute", "Ntilde", "Odieresis", "Udieresis", "aacute",
  "agrave", "acircumflex", "adieresis", "atilde", "aring", "ccedilla", "eacute", "egrave",
  "ecircumflex", "edieresis", "iacute", "igrave", "icircumflex", "idieresis", "ntilde", "oacute",
  "ograve", "ocircumflex", "odieresis", "otilde", "uacute", "ugrave", "ucircumflex", "udieresis",
  "dagger", "degree", "cent", "sterling", "section", "bullet", "paragraph", "germandbls",
  "registered", "copyright", "trademark", "acute", "dieresis", "", "AE", "Oslash",
  "", "plusminus", "", "", "yen", "mu", "", "",
  "", "", "", "ordfeminine", "ordmasculine", "", "ae", "oslash",
  "questiondown", "exclamdown", "logicalnot", "", "florin", "", "", "guillemotleft",
  "guillemotright", "ellipsis", "space", "Agrave", "Atilde", "Otilde", "OE", "oe",
  "endash", "emdash", "quotedblleft", "quotedblright", "quoteleft", "quoteright", "divide", "",
  "ydieresis", "Ydieresis", "fraction", "currency", "guilsinglleft", "guilsinglright", "fi", "fl",
  "daggerdbl", "periodcentered", "quotesinglbase", "quotedblbase", "perthousand", "Acircumflex", "Ecircumflex", "Aacute",
  "Edieresis", "Egrave", "Iacute", "Icircumflex", "Idieresis", "Igrave", "Oacute", "Ocircumflex",
  "", "Ograve", "Uacute", "Ucircumflex", "Ugrave", "dotlessi", "circumflex", "tilde",
  "macron", "breve", "dotaccent", "ring", "cedilla", "hungarumlaut", "ogonek", "caron"
  ]

/-- Annex D column PDF (PDFDocEncoding) by code; `""` = unassigned. -/
def pdfDocNames : Array String := #[
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "breve", "caron", "circumflex", "dotaccent", "hungarumlaut", "ogonek", "ring", "tilde",
  "space", "exclam", "quotedbl", "numbersign", "dollar", "percent", "ampersand", "quotesingle",
  "parenleft", "parenright", "asterisk", "plus", "comma", "hyphen", "period", "slash",
  "zero", "one", "two", "three", "four", "five", "six", "seven",
  "eight", "nine", "colon", "semicolon", "less", "equal", "greater", "question",
  "at", "A", "B", "C", "D", "E", "F", "G",
  "H", "I", "J", "K", "L", "M", "N", "O",
  "P", "Q", "R", "S", "T", "U", "V", "W",
  "X", "Y", "Z", "bracketleft", "backslash", "bracketright", "asciicircum", "underscore",
  "grave", "a", "b", "c", "d", "e", "f", "g",
  "h", "i", "j", "k", "l", "m", "n", "o",
  "p", "q", "r", "s", "t", "u", "v", "w",
  "x", "y", "z", "braceleft", "bar", "braceright", "asciitilde", "",
  "bullet", "dagger", "daggerdbl", "ellipsis", "emdash", "endash", "florin", "fraction",
  "guilsinglleft", "guilsinglright", "minus", "perthousand", "quotedblbase", "quotedblleft", "quotedblright", "quoteleft",
  "quoteright", "quotesinglbase", "trademark", "fi", "fl", "Lslash", "OE", "Scaron",
  "Ydieresis", "Zcaron", "dotlessi", "lslash", "oe", "scaron", "zcaron", "",
  "Euro", "exclamdown", "cent", "sterling", "currency", "yen", "brokenbar", "section",
  "dieresis", "copyright", "ordfeminine", "guillemotleft", "logicalnot", "", "registered", "macron",
  "degree", "plusminus", "twosuperior", "threesuperior", "acute", "mu", "paragraph", "periodcentered",
  "cedilla", "onesuperior", "ordmasculine", "guillemotright", "onequarter", "onehalf", "threequarters", "questiondown",
  "Agrave", "Aacute", "Acircumflex", "Atilde", "Adieresis", "Aring", "AE", "Ccedilla",
  "Egrave", "Eacute", "Ecircumflex", "Edieresis", "Igrave", "Iacute", "Icircumflex", "Idieresis",
  "Eth", "Ntilde", "Ograve", "Oacute", "Ocircumflex", "Otilde", "Odieresis", "multiply",
  "Oslash", "Ugrave", "Uacute", "Ucircumflex", "Udieresis", "Yacute", "Thorn", "germandbls",
  "agrave", "aacute", "acircumflex", "atilde", "adieresis", "aring", "ae", "ccedilla",
  "egrave", "eacute", "ecircumflex", "edieresis", "igrave", "iacute", "icircumflex", "idieresis",
  "eth", "ntilde", "ograve", "oacute", "ocircumflex", "otilde", "odieresis", "divide",
  "oslash", "ugrave", "uacute", "ucircumflex", "udieresis", "yacute", "thorn", "ydieresis"
  ]

/-- Glyph names of the Adobe Glyph List subset (sorted), parallel to `aglCodes`. -/
def aglNames : Array String := #[
  "A", "AE", "Aacute", "Acircumflex", "Adieresis", "Agrave", "Aring", "Atilde",
  "B", "C", "Ccedilla", "D", "Delta", "E", "Eacute", "Ecircumflex",
  "Edieresis", "Egrave", "Eth", "Euro", "F", "G", "H", "I",
  "Iacute", "Icircumflex", "Idieresis", "Igrave", "J", "K", "L", "Lslash",
  "M", "N", "Ntilde", "O", "OE", "Oacute", "Ocircumflex", "Odieresis",
  "Ograve", "Omega", "Oslash", "Otilde", "P", "Q", "R", "S",
  "Scaron", "T", "Thorn", "U", "Uacute", "Ucircumflex", "Udieresis", "Ugrave",
  "V", "W", "X", "Y", "Yacute", "Ydieresis", "Z", "Zcaron",
  "a", "aacute", "acircumflex", "acute", "adieresis", "ae", "agrave", "ampersand",
  "approxequal", "aring", "asciicircum", "asciitilde", "asterisk", "at", "atilde", "b",
  "backslash", "bar", "braceleft", "braceright", "bracketleft", "bracketright", "breve", "brokenbar",
  "bullet", "c", "caron", "ccedilla", "cedilla", "cent", "circumflex", "colon",
  "comma", "copyright", "currency", "d", "dagger", "daggerdbl", "degree", "dieresis",
  "divide", "dollar", "dotaccent", "dotlessi", "e", "eacute", "ecircumflex", "edieresis",
  "egrave", "eight", "ellipsis", "emdash", "endash", "equal", "eth", "exclam",
  "exclamdown", "f", "ff", "ffi", "ffl", "fi", "five", "fl",
  "florin", "four", "fraction", "g", "germandbls", "grave", "greater", "greaterequal",
  "guillemotleft", "guillemotright", "guilsinglleft", "guilsinglright", "h", "hungarumlaut", "hyphen", "i",
  "iacute", "icircumflex", "idieresis", "igrave", "infinity", "integral", "j", "k",
  "l", "less", "lessequal", "logicalnot", "lozenge", "lslash", "m", "macron",
  "minus", "mu", "multiply", "n", "nbspace", "nine", "notequal", "ntilde",
  "numbersign", "o", "oacute", "ocircumflex", "odieresis", "oe", "ogonek", "ograve",
  "one", "onehalf", "onequarter", "onesuperior", "ordfeminine", "ordmasculine", "oslash", "otilde",
  "p", "paragraph", "parenleft", "parenright", "partialdiff", "percent", "period", "periodcentered",
  "perthousand", "pi", "plus", "plusminus", "product", "q", "question", "questiondown",
  "quotedbl", "quotedblbase", "quotedblleft", "quotedblright", "quoteleft", "quoteright", "quotesinglbase", "quotesingle",
  "r", "radical", "registered", "ring", "s", "scaron", "section", "semicolon",
  "seven", "sfthyphen", "six", "slash", "space", "sterling", "summation", "t",
  "thorn", "three", "threequarters", "threesuperior", "tilde", "trademark", "two", "twosuperior",
  "u", "uacute", "ucircumflex", "udieresis", "ugrave", "underscore", "v", "w",
  "x", "y", "yacute", "ydieresis", "yen", "z", "zcaron", "zero"]

/-- Unicode code points of `aglNames`, entry by entry (Adobe Glyph List). -/
def aglCodes : Array Nat := #[
  0x0041, 0x00C6, 0x00C1, 0x00C2, 0x00C4, 0x00C0, 0x00C5, 0x00C3,
  0x0042, 0x0043, 0x00C7, 0x0044, 0x2206, 0x0045, 0x00C9, 0x00CA,
  0x00CB, 0x00C8, 0x00D0, 0x20AC, 0x0046, 0x0047, 0x0048, 0x0049,
  0x00CD, 0x00CE, 0x00CF, 0x00CC, 0x004A, 0x004B, 0x004C, 0x0141,
  0x004D, 0x004E, 0x00D1, 0x004F, 0x0152, 0x00D3, 0x00D4, 0x00D6,
  0x00D2, 0x2126, 0x00D8, 0x00D5, 0x0050, 0x0051, 0x0052, 0x0053,
  0x0160, 0x0054, 0x00DE, 0x0055, 0x00DA, 0x00DB, 0x00DC, 0x00D9,
  0x0056, 0x0057, 0x0058, 0x0059, 0x00DD, 0x0178, 0x005A, 0x017D,
  0x0061, 0x00E1, 0x00E2, 0x00B4, 0x00E4, 0x00E6, 0x00E0, 0x0026,
  0x2248, 0x00E5, 0x005E, 0x007E, 0x002A, 0x0040, 0x00E3, 0x0062,
  0x005C, 0x007C, 0x007B, 0x007D, 0x005B, 0x005D, 0x02D8, 0x00A6,
  0x2022, 0x0063, 0x02C7, 0x00E7, 0x00B8, 0x00A2, 0x02C6, 0x003A,
  0x002C, 0x00A9, 0x00A4, 0x0064, 0x2020, 0x2021, 0x00B0, 0x00A8,
  0x00F7, 0x0024, 0x02D9, 0x0131, 0x0065, 0x00E9, 0x00EA, 0x00EB,
  0x00E8, 0x0038, 0x2026, 0x2014, 0x2013, 0x003D, 0x00F0, 0x0021,
  0x00A1, 0x0066, 0xFB00, 0xFB03, 0xFB04, 0xFB01, 0x0035, 0xFB02,
  0x0192, 0x0034, 0x2044, 0x0067, 0x00DF, 0x0060, 0x003E, 0x2265,
  0x00AB, 0x00BB, 0x2039, 0x203A, 0x0068, 0x02DD, 0x002D, 0x0069,
  0x00ED, 0x00EE, 0x00EF, 0x00EC, 0x221E, 0x222B, 0x006A, 0x006B,
  0x006C, 0x003C, 0x2264, 0x00AC, 0x25CA, 0x0142, 0x006D, 0x00AF,
  0x2212, 0x00B5, 0x00D7, 0x006E, 0x00A0, 0x0039, 0x2260, 0x00F1,
  0x0023, 0x006F, 0x00F3, 0x00F4, 0x00F6, 0x0153, 0x02DB, 0x00F2,
  0x0031, 0x00BD, 0x00BC, 0x00B9, 0x00AA, 0x00BA, 0x00F8, 0x00F5,
  0x0070, 0x00B6, 0x0028, 0x0029, 0x2202, 0x0025, 0x002E, 0x00B7,
  0x2030, 0x03C0, 0x002B, 0x00B1, 0x220F, 0x0071, 0x003F, 0x00BF,
  0x0022, 0x201E, 0x201C, 0x201D, 0x2018, 0x2019, 0x201A, 0x0027,
  0x0072, 0x221A, 0x00AE, 0x02DA, 0x0073, 0x0161, 0x00A7, 0x003B,
  0x0037, 0x00AD, 0x0036, 0x002F, 0x0020, 0x00A3, 0x2211, 0x0074,
  0x00FE, 0x0033, 0x00BE, 0x00B3, 0x02DC, 0x2122, 0x0032, 0x00B2,
  0x0075, 0x00FA, 0x00FB, 0x00FC, 0x00F9, 0x005F, 0x0076, 0x0077,
  0x0078, 0x0079, 0x00FD, 0x00FF, 0x00A5, 0x007A, 0x017E, 0x0030]

/-- `StandardEncoding` (Annex D, column STD). -/
def standardEncoding : Encoding := ofNameTable standardNames

/-- `WinAnsiEncoding` (Annex D, column WIN, with the Annex D notes applied). -/
def winAnsiEncoding : Encoding := ofNameTable winAnsiNames

/-- `MacRomanEncoding` (Annex D, column MAC). -/
def macRomanEncoding : Encoding := ofNameTable macRomanNames

/-- `PDFDocEncoding` (Annex D, column PDF, Table D.3). -/
def pdfDocEncoding : Encoding := ofNameTable pdfDocNames

set_option maxRecDepth 4000 in
/-- `StandardEncoding` has 256 entries. -/
theorem standardEncoding_size : standardEncoding.size = 256 := by
  rw [standardEncoding, ofNameTable, Array.size_map]; rfl

set_option maxRecDepth 4000 in
/-- `WinAnsiEncoding` has 256 entries. -/
theorem winAnsiEncoding_size : winAnsiEncoding.size = 256 := by
  rw [winAnsiEncoding, ofNameTable, Array.size_map]; rfl

set_option maxRecDepth 4000 in
/-- `MacRomanEncoding` has 256 entries. -/
theorem macRomanEncoding_size : macRomanEncoding.size = 256 := by
  rw [macRomanEncoding, ofNameTable, Array.size_map]; rfl

set_option maxRecDepth 4000 in
/-- `PDFDocEncoding` has 256 entries. -/
theorem pdfDocEncoding_size : pdfDocEncoding.size = 256 := by
  rw [pdfDocEncoding, ofNameTable, Array.size_map]; rfl

namespace Encoding

/-- The glyph name of a one-byte code (`none` when unassigned or out of range). -/
def glyph (e : Encoding) (code : Nat) : Option GlyphName :=
  match e[code]? with
  | some g => g
  | none => none

end Encoding

/-- A predefined encoding selected by name (Table 112): `StandardEncoding`,
`WinAnsiEncoding`, `MacRomanEncoding`, `PDFDocEncoding`. Others (`MacExpertEncoding`,
unknown names) give `none`. -/
def namedEncoding? (n : Name) : Option Encoding :=
  let s := glyphNameOf n.bytes
  if s == "WinAnsiEncoding" then some winAnsiEncoding
  else if s == "MacRomanEncoding" then some macRomanEncoding
  else if s == "StandardEncoding" then some standardEncoding
  else if s == "PDFDocEncoding" then some pdfDocEncoding
  else none

/-! ## `/Differences` -/

/-- Apply `/Differences` entries with current code `cur` (`none` after an out-of-range
integer: names are ignored until the next integer). Structural on the list. -/
def applyDiffsAux : Encoding → Option Nat → List PdfObject → Encoding
  | e, _, [] => e
  | e, _, .int n :: rest =>
    applyDiffsAux e (if 0 ≤ n ∧ n < 256 then some n.toNat else none) rest
  | e, some c, .name nm :: rest =>
    applyDiffsAux (e.setIfInBounds c (some (glyphNameOf nm.bytes))) (some (c + 1)) rest
  | e, none, .name _ :: rest => applyDiffsAux e none rest
  | e, cur, _ :: rest => applyDiffsAux e cur rest

/-- Apply a `/Differences` array `[code /name /name … code /name …]` to `base`
(ISO 32000-2 §9.6.5.1, Table 112). Bad entries are skipped. -/
def applyDifferences (base : Encoding) (diffs : List PdfObject) : Encoding :=
  applyDiffsAux base none diffs

/-- `applyDiffsAux` never changes the number of codes. -/
theorem applyDiffsAux_size (e : Encoding) (cur : Option Nat) (diffs : List PdfObject) :
    (applyDiffsAux e cur diffs).size = e.size := by
  induction diffs generalizing e cur with
  | nil => simp [applyDiffsAux]
  | cons x rest ih =>
    cases x <;> cases cur <;> simp [applyDiffsAux, ih]

/-- `applyDifferences` preserves the size of the base encoding (256 for every base here). -/
theorem applyDifferences_size (base : Encoding) (diffs : List PdfObject) :
    (applyDifferences base diffs).size = base.size :=
  applyDiffsAux_size base none diffs

/-! ## The encoding of a simple font -/

/-- Read a dictionary entry, resolving one level of indirection with `resolve`. -/
def getR (resolve : PdfObject → PdfObject) (d : Dict) (key : String) : Option PdfObject :=
  (Dict.get? d (Name.ofString key)).map resolve

/-- The `/Flags` of the font's `/FontDescriptor` (Table 121), `0` when absent or bad. -/
def fontFlags (resolve : PdfObject → PdfObject) (fontDict : Dict) : Nat :=
  match getR resolve fontDict "FontDescriptor" with
  | some (.dict fd) =>
    match getR resolve fd "Flags" with
    | some (.int f) => f.toNat
    | _ => 0
  | _ => 0

/-- Whether the font descriptor marks the font symbolic (`/Flags` bit 3, Table 122). The
encoding rules below only depend on it through `builtin?` (see the module doc). -/
def isSymbolic (resolve : PdfObject → PdfObject) (fontDict : Dict) : Bool :=
  (fontFlags resolve fontDict / 4) % 2 == 1

/-- The encoding of a simple font (ISO 32000-2 §9.6.5, Table 112). `builtin?` is the font
program's built-in encoding when known (embedded program, or a standard symbolic font);
otherwise the implicit base is `StandardEncoding`. Never fails: a bad `/Encoding` entry
leaves the implicit base. -/
def simpleEncoding (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) : Encoding :=
  let implicit := builtin?.getD standardEncoding
  match getR resolve fontDict "Encoding" with
  | some (.name n) => (namedEncoding? n).getD implicit
  | some (.dict ed) =>
    let base :=
      match getR resolve ed "BaseEncoding" with
      | some (.name n) => (namedEncoding? n).getD implicit
      | _ => implicit
    match getR resolve ed "Differences" with
    | some (.array diffs) => applyDifferences base diffs
    | _ => base
  | _ => implicit

/-- A simple font's encoding has the size of its base: 256 entries whenever `builtin?` has
256 entries (or is absent). -/
theorem simpleEncoding_size (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) (h : ∀ b, builtin? = some b → b.size = 256) :
    (simpleEncoding resolve fontDict builtin?).size = 256 := by
  have hi : (builtin?.getD standardEncoding).size = 256 := by
    cases hb : builtin? with
    | none => simp [standardEncoding_size]
    | some b => simpa using h b hb
  have hn : ∀ n, ((namedEncoding? n).getD (builtin?.getD standardEncoding)).size = 256 := by
    intro n
    unfold namedEncoding?
    dsimp only
    split
    · exact winAnsiEncoding_size
    · split
      · exact macRomanEncoding_size
      · split
        · exact standardEncoding_size
        · split
          · exact pdfDocEncoding_size
          · exact hi
  unfold simpleEncoding
  simp only
  split
  · exact hn _
  · rename_i ed _
    have hb : (match getR resolve ed "BaseEncoding" with
        | some (.name n) => (namedEncoding? n).getD (builtin?.getD standardEncoding)
        | _ => builtin?.getD standardEncoding).size = 256 := by
      split
      · exact hn _
      · exact hi
    split
    · rw [applyDifferences_size]; exact hb
    · exact hb
  · exact hi

/-! ## Glyph name → Unicode (Adobe Glyph List specification) -/

/-- The AGL code point of a glyph name in the subset `aglNames`. -/
def aglLookup (g : GlyphName) : Option Nat :=
  match aglNames.findIdx? (· == g) with
  | some i => aglCodes[i]?
  | none => none

/-- Value of one hexadecimal digit (either case). -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Parse hexadecimal digits (accumulator form); `none` on a non-hex character. -/
def parseHexAux : Nat → List Char → Option Nat
  | acc, [] => some acc
  | acc, c :: rest =>
    match hexDigit c with
    | some v => parseHexAux (acc * 16 + v) rest
    | none => none

/-- Whether `n` is a Unicode scalar value (not a surrogate, at most `0x10FFFF`). -/
def isScalar (n : Nat) : Bool := n ≤ 0x10FFFF && !(0xD800 ≤ n && n ≤ 0xDFFF)

/-- `uni` suffix: one or more groups of exactly four hex digits, each a scalar value. -/
def uniGroups : List Char → Option (List Char)
  | [] => some []
  | a :: b :: c :: d :: rest =>
    match parseHexAux 0 [a, b, c, d] with
    | some v =>
      if isScalar v then (uniGroups rest).map (Char.ofNat v :: ·) else none
    | none => none
  | _ => none

/-- Map one `_`-separated component of a glyph name (AGL specification, step 3). -/
def componentToUnicode (comp : List Char) : List Char :=
  match aglLookup (String.ofList comp) with
  | some u => [Char.ofNat u]
  | none =>
    match comp with
    | 'u' :: 'n' :: 'i' :: rest@(_ :: _) => (uniGroups rest).getD []
    | 'u' :: rest =>
      if 4 ≤ rest.length ∧ rest.length ≤ 6 then
        match parseHexAux 0 rest with
        | some v => if isScalar v then [Char.ofNat v] else []
        | none => []
      else []
    | _ => []

/-- The Unicode text of a glyph name per the Adobe Glyph List specification (suffix after
`.` dropped, `_` ligature components concatenated); `none` when nothing maps. The fallback for
text extraction without `/ToUnicode` (task 6.5). -/
def glyphToUnicode (g : GlyphName) : Option String :=
  let base := g.toList.takeWhile (· ≠ '.')
  let out := (base.splitOn '_').flatMap componentToUnicode
  if out.isEmpty then none else some (String.ofList out)

/-! ## Spot checks -/

#guard standardEncoding.size == 256 && winAnsiEncoding.size == 256
#guard winAnsiEncoding.glyph 0x80 == some "Euro"
#guard winAnsiEncoding.glyph 0x91 == some "quoteleft"
#guard winAnsiEncoding.glyph 0x27 == some "quotesingle"
#guard winAnsiEncoding.glyph 0xE9 == some "eacute"
#guard winAnsiEncoding.glyph 0x81 == some "bullet"
#guard standardEncoding.glyph 0x27 == some "quoteright"
#guard standardEncoding.glyph 0x60 == some "quoteleft"
#guard standardEncoding.glyph 0xA4 == some "fraction"
#guard standardEncoding.glyph 0xFB == some "germandbls"
#guard standardEncoding.glyph 0x80 == none
#guard (standardEncoding.filterMap id).size == 149
#guard macRomanEncoding.glyph 0xDB == some "currency"
#guard macRomanEncoding.glyph 0x80 == some "Adieresis"
#guard macRomanEncoding.glyph 0xAD == none
#guard macRomanEncoding.glyph 0xFF == some "caron"
#guard pdfDocEncoding.glyph 0x18 == some "breve"
#guard pdfDocEncoding.glyph 0xA0 == some "Euro"
#guard pdfDocEncoding.glyph 0xAD == none
#guard (pdfDocEncoding.filterMap id).size == 229
#guard (applyDifferences standardEncoding
    [.int 39, .name (Name.ofString "quotesingle"), .name (Name.ofString "x"),
     .int 300, .name (Name.ofString "ignored"), .real ⟨1, 0⟩,
     .int 255, .name (Name.ofString "a"), .name (Name.ofString "b")]).glyph 39
  == some "quotesingle"
#guard (applyDifferences standardEncoding [.int 39, .name (Name.ofString "q"),
    .name (Name.ofString "x")]).glyph 40 == some "x"
#guard (applyDifferences standardEncoding [.int 255, .name (Name.ofString "a"),
    .name (Name.ofString "b")]).size == 256
#guard (simpleEncoding id [(Name.ofString "Encoding", .name (Name.ofString "WinAnsiEncoding"))]
    none).glyph 0x80 == some "Euro"
#guard (simpleEncoding id [(Name.ofString "Encoding", .dict
    [(Name.ofString "BaseEncoding", .name (Name.ofString "MacRomanEncoding")),
     (Name.ofString "Differences", .array [.int 65, .name (Name.ofString "Euro")])])]
    none).glyph 0x41 == some "Euro"
#guard (simpleEncoding id [(Name.ofString "Encoding", .dict
    [(Name.ofString "Differences", .array [.int 1, .name (Name.ofString "g1")])])]
    none).glyph 0x27 == some "quoteright"
#guard (simpleEncoding id [] none).glyph 0x41 == some "A"
#guard glyphToUnicode "A" == some "A"
#guard glyphToUnicode "Euro" == some "€"
#guard glyphToUnicode "quoteright" == some "’"
#guard glyphToUnicode "fi" == some "ﬁ"
#guard glyphToUnicode "uni20AC" == some "€"
#guard glyphToUnicode "uni00410042" == some "AB"
#guard glyphToUnicode "uniD800" == none
#guard glyphToUnicode "u1F600" == some (String.ofList [Char.ofNat 0x1F600])
#guard glyphToUnicode "f_f_i" == some "ffi"
#guard glyphToUnicode "a.sc" == some "a"
#guard glyphToUnicode ".notdef" == none
#guard glyphToUnicode "g123" == none
#guard glyphToUnicode "uni" == none
#guard isSymbolic id [(Name.ofString "FontDescriptor", .dict [(Name.ofString "Flags", .int 4)])]
#guard !isSymbolic id [(Name.ofString "FontDescriptor", .dict [(Name.ofString "Flags", .int 32)])]
-- Every glyph of the four encodings has an AGL code point.
#guard [standardEncoding, winAnsiEncoding, macRomanEncoding, pdfDocEncoding].all fun e =>
  e.all fun g => match g with | some n => (aglLookup n).isSome | none => true

end SafePdf.Core.Font
