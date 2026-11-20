import SafePdf.Core.Object
import SafePdf.Core.Font.GlyphList

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
* **Symbol and ZapfDingbats (Annex D.5, D.6).** `symbolEncoding` (189 codes) and
  `zapfDingbatsEncoding` (202 codes) are the built-in encodings of the two standard symbolic
  fonts: the `C` entries of Adobe's `Symbol.afm` (001.008, which encodes `Euro` at `0xA0`) and
  `ZapfDingbats.afm` (002.000), which Annex D reproduces. Written from memory in 6.4b and
  verified in 6.4c, code by code, against the Adobe Core14 AFMs as redistributed by Apache PDFBox 3.0.3 (`pdfbox/src/main/resources/org/apache/pdfbox/resources/afm/`); the one mismatch (`apple` at `0xF0`: the
  AFM lists `apple` unencoded, `C -1`, as do pdf.js and PDFBox) was fixed. The glyph-name →
  Unicode tables below were verified against Adobe's `glyphlist.txt` and `zapfdingbats.txt`
  (github.com/adobe-type-tools/agl-aglfn @ 4036a9c) with no mismatch. Counts and spot checks
  are `#guard`s below. They are the implicit base of a font
  whose `/BaseFont` names one of them (`symbolicBuiltin?`, same prefixes as
  `Std14.ofBaseFont`, subset tag stripped) when the caller has no program encoding.
* **`/Differences`** (§9.6.5.1, Table 112): an integer sets the current code, each following
  name is assigned to the current code which then increments. A code outside `0..255` makes
  the names up to the next integer ignored; any other object is skipped. Total, linear in the
  array, never fails.
* **Base encoding** (Table 112 `BaseEncoding`): an `/Encoding` name selects a predefined
  encoding; a dictionary uses its `/BaseEncoding` name, else the implicit base. The implicit
  base is the font program's built-in encoding when the caller knows it (`builtin?`: an
  embedded program's encoding), else a standard symbolic font's built-in encoding by
  `/BaseFont` (`implicitBase`), else `StandardEncoding` (the
  §9.6.5 rule for nonsymbolic fonts; for a symbolic font without a known built-in encoding
  there is nothing better). `MacExpertEncoding` is not tabulated and falls back to the
  implicit base. TrueType-specific rules (§9.6.5.4) belong to task 6.1.
* **Glyph name → Unicode** follows the Adobe Glyph List Specification: drop the suffix from
  the first `.`, split at `_`, map each component through the AGL subset `aglNames` (every
  glyph of the four encodings plus `minus`, `ff`, `ffi`, `ffl`, `nbspace`, `sfthyphen` and the
  15 Mac symbols) and `aglSymbolNames` (the other Symbol glyphs: Greek, math, arrows, the
  Corporate Use extension pieces), else `uniXXXX…` (groups of four hex digits) or
  `uXXXX`–`uXXXXXX`, else nothing. For a ZapfDingbats font (`glyphToUnicodeIn true`) the
  ITC Zapf Dingbats Glyph List (`dingbatNames`, `a1`…`a206`) is tried first; `glyphToUnicode`
  is the variant for any other font. Hex digits are accepted in either case (AGL requires upper case; pdf.js accepts
  both) and surrogates / values above `0x10FFFF` are rejected.
* **Full glyph list (task 6.7b).** A component that the subset does not know is looked up in
  `aglTable`, the whole AGL 2.0 (4281 names: `afii*`, `dotlessj`, small caps, …) plus the 271
  TeX font names of lcdf-typetools' `texglyphlist.txt` (CMSY `negationslash`, `angbracketleft`,
  CMTT `visiblespace`, AMS relations, …), data in `GlyphList.lean`, parsed once and searched by
  bisection (`bsearch`). After `uni`/`u` names, a non-ZapfDingbats component `aNN` (two to five
  decimal digits, `32..0xFFFF`) maps to `U+NN` as in MuPDF (`aDecimal`: Ghostscript's names for
  dvips bitmap glyphs). `gNN`, `cidNN`, `index…` and other generated names map to nothing.

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

/-- Built-in encoding of the standard **Symbol** font by code (ISO 32000-2 Annex D.5, Adobe
`Symbol.afm` 001.008); `""` = unassigned. 189 codes: `0x20`–`0x7E` and `0xA0`–`0xFE` except
`0xF0` (the AFM's unencoded `apple` glyph has no code). -/
def symbolNames : Array String := #[
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "space", "exclam", "universal", "numbersign", "existential", "percent", "ampersand", "suchthat",
  "parenleft", "parenright", "asteriskmath", "plus", "comma", "minus", "period", "slash",
  "zero", "one", "two", "three", "four", "five", "six", "seven",
  "eight", "nine", "colon", "semicolon", "less", "equal", "greater", "question",
  "congruent", "Alpha", "Beta", "Chi", "Delta", "Epsilon", "Phi", "Gamma",
  "Eta", "Iota", "theta1", "Kappa", "Lambda", "Mu", "Nu", "Omicron",
  "Pi", "Theta", "Rho", "Sigma", "Tau", "Upsilon", "sigma1", "Omega",
  "Xi", "Psi", "Zeta", "bracketleft", "therefore", "bracketright", "perpendicular", "underscore",
  "radicalex", "alpha", "beta", "chi", "delta", "epsilon", "phi", "gamma",
  "eta", "iota", "phi1", "kappa", "lambda", "mu", "nu", "omicron",
  "pi", "theta", "rho", "sigma", "tau", "upsilon", "omega1", "omega",
  "xi", "psi", "zeta", "braceleft", "bar", "braceright", "similar", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "Euro", "Upsilon1", "minute", "lessequal", "fraction", "infinity", "florin", "club",
  "diamond", "heart", "spade", "arrowboth", "arrowleft", "arrowup", "arrowright", "arrowdown",
  "degree", "plusminus", "second", "greaterequal", "multiply", "proportional", "partialdiff", "bullet",
  "divide", "notequal", "equivalence", "approxequal", "ellipsis", "arrowvertex", "arrowhorizex", "carriagereturn",
  "aleph", "Ifraktur", "Rfraktur", "weierstrass", "circlemultiply", "circleplus", "emptyset", "intersection",
  "union", "propersuperset", "reflexsuperset", "notsubset", "propersubset", "reflexsubset", "element", "notelement",
  "angle", "gradient", "registerserif", "copyrightserif", "trademarkserif", "product", "radical", "dotmath",
  "logicalnot", "logicaland", "logicalor", "arrowdblboth", "arrowdblleft", "arrowdblup", "arrowdblright", "arrowdbldown",
  "lozenge", "angleleft", "registersans", "copyrightsans", "trademarksans", "summation", "parenlefttp", "parenleftex",
  "parenleftbt", "bracketlefttp", "bracketleftex", "bracketleftbt", "bracelefttp", "braceleftmid", "braceleftbt", "braceex",
  "", "angleright", "integral", "integraltp", "integralex", "integralbt", "parenrighttp", "parenrightex",
  "parenrightbt", "bracketrighttp", "bracketrightex", "bracketrightbt", "bracerighttp", "bracerightmid", "bracerightbt", ""
  ]

/-- Built-in encoding of the standard **ZapfDingbats** font by code (ISO 32000-2 Annex D.6,
Adobe `ZapfDingbats.afm` 002.000); `""` = unassigned. 202 codes: `0x20`–`0x7E`, `0x80`–`0x8D`
and `0xA1`–`0xFE` except `0xF0`. -/
def zapfDingbatsNames : Array String := #[
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "space", "a1", "a2", "a202", "a3", "a4", "a5", "a119",
  "a118", "a117", "a11", "a12", "a13", "a14", "a15", "a16",
  "a105", "a17", "a18", "a19", "a20", "a21", "a22", "a23",
  "a24", "a25", "a26", "a27", "a28", "a6", "a7", "a8",
  "a9", "a10", "a29", "a30", "a31", "a32", "a33", "a34",
  "a35", "a36", "a37", "a38", "a39", "a40", "a41", "a42",
  "a43", "a44", "a45", "a46", "a47", "a48", "a49", "a50",
  "a51", "a52", "a53", "a54", "a55", "a56", "a57", "a58",
  "a59", "a60", "a61", "a62", "a63", "a64", "a65", "a66",
  "a67", "a68", "a69", "a70", "a71", "a72", "a73", "a74",
  "a203", "a75", "a204", "a76", "a77", "a78", "a79", "a81",
  "a82", "a83", "a84", "a97", "a98", "a99", "a100", "",
  "a89", "a90", "a93", "a94", "a91", "a92", "a205", "a85",
  "a206", "a86", "a87", "a88", "a95", "a96", "", "",
  "", "", "", "", "", "", "", "",
  "", "", "", "", "", "", "", "",
  "", "a101", "a102", "a103", "a104", "a106", "a107", "a108",
  "a112", "a111", "a110", "a109", "a120", "a121", "a122", "a123",
  "a124", "a125", "a126", "a127", "a128", "a129", "a130", "a131",
  "a132", "a133", "a134", "a135", "a136", "a137", "a138", "a139",
  "a140", "a141", "a142", "a143", "a144", "a145", "a146", "a147",
  "a148", "a149", "a150", "a151", "a152", "a153", "a154", "a155",
  "a156", "a157", "a158", "a159", "a160", "a161", "a163", "a164",
  "a196", "a165", "a192", "a166", "a167", "a168", "a169", "a170",
  "a171", "a172", "a173", "a162", "a174", "a175", "a176", "a177",
  "a178", "a179", "a193", "a180", "a199", "a181", "a200", "a182",
  "", "a201", "a183", "a184", "a197", "a185", "a194", "a198",
  "a186", "a195", "a187", "a188", "a189", "a190", "a191", ""
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

/-- Glyph names of the Symbol font (Annex D.5) missing from `aglNames`, parallel to
`aglSymbolCodes`. Code points are those of the Adobe Glyph List; the AGL itself maps the
Symbol-only extension pieces and serif/sans variants (`parenlefttp`, `registerserif`, `apple`,
…) to the Corporate Use area `U+F6D9`–`U+F8FF`, and so does this table. -/
def aglSymbolNames : Array String := #[
  "universal", "existential", "suchthat", "asteriskmath", "congruent", "Alpha", "Beta", "Chi",
  "Epsilon", "Phi", "Gamma", "Eta", "Iota", "theta1", "Kappa", "Lambda",
  "Mu", "Nu", "Omicron", "Pi", "Theta", "Rho", "Sigma", "Tau",
  "Upsilon", "sigma1", "Xi", "Psi", "Zeta", "therefore", "perpendicular", "radicalex",
  "alpha", "beta", "chi", "delta", "epsilon", "phi", "gamma", "eta",
  "iota", "phi1", "kappa", "lambda", "nu", "omicron", "theta", "rho",
  "sigma", "tau", "upsilon", "omega1", "omega", "xi", "psi", "zeta",
  "similar", "Upsilon1", "minute", "club", "diamond", "heart", "spade", "arrowboth",
  "arrowleft", "arrowup", "arrowright", "arrowdown", "second", "proportional", "equivalence", "arrowvertex",
  "arrowhorizex", "carriagereturn", "aleph", "Ifraktur", "Rfraktur", "weierstrass", "circlemultiply", "circleplus",
  "emptyset", "intersection", "union", "propersuperset", "reflexsuperset", "notsubset", "propersubset", "reflexsubset",
  "element", "notelement", "angle", "gradient", "registerserif", "copyrightserif", "trademarkserif", "dotmath",
  "logicaland", "logicalor", "arrowdblboth", "arrowdblleft", "arrowdblup", "arrowdblright", "arrowdbldown", "angleleft",
  "registersans", "copyrightsans", "trademarksans", "parenlefttp", "parenleftex", "parenleftbt", "bracketlefttp", "bracketleftex",
  "bracketleftbt", "bracelefttp", "braceleftmid", "braceleftbt", "braceex", "apple", "angleright", "integraltp",
  "integralex", "integralbt", "parenrighttp", "parenrightex", "parenrightbt", "bracketrighttp", "bracketrightex", "bracketrightbt",
  "bracerighttp", "bracerightmid", "bracerightbt"]

/-- Unicode code points of `aglSymbolNames`, entry by entry (Adobe Glyph List). -/
def aglSymbolCodes : Array Nat := #[
  0x2200, 0x2203, 0x220B, 0x2217, 0x2245, 0x0391, 0x0392, 0x03A7,
  0x0395, 0x03A6, 0x0393, 0x0397, 0x0399, 0x03D1, 0x039A, 0x039B,
  0x039C, 0x039D, 0x039F, 0x03A0, 0x0398, 0x03A1, 0x03A3, 0x03A4,
  0x03A5, 0x03C2, 0x039E, 0x03A8, 0x0396, 0x2234, 0x22A5, 0xF8E5,
  0x03B1, 0x03B2, 0x03C7, 0x03B4, 0x03B5, 0x03C6, 0x03B3, 0x03B7,
  0x03B9, 0x03D5, 0x03BA, 0x03BB, 0x03BD, 0x03BF, 0x03B8, 0x03C1,
  0x03C3, 0x03C4, 0x03C5, 0x03D6, 0x03C9, 0x03BE, 0x03C8, 0x03B6,
  0x223C, 0x03D2, 0x2032, 0x2663, 0x2666, 0x2665, 0x2660, 0x2194,
  0x2190, 0x2191, 0x2192, 0x2193, 0x2033, 0x221D, 0x2261, 0xF8E6,
  0xF8E7, 0x21B5, 0x2135, 0x2111, 0x211C, 0x2118, 0x2297, 0x2295,
  0x2205, 0x2229, 0x222A, 0x2283, 0x2287, 0x2284, 0x2282, 0x2286,
  0x2208, 0x2209, 0x2220, 0x2207, 0xF6DA, 0xF6D9, 0xF6DB, 0x22C5,
  0x2227, 0x2228, 0x21D4, 0x21D0, 0x21D1, 0x21D2, 0x21D3, 0x2329,
  0xF8E8, 0xF8E9, 0xF8EA, 0xF8EB, 0xF8EC, 0xF8ED, 0xF8EE, 0xF8EF,
  0xF8F0, 0xF8F1, 0xF8F2, 0xF8F3, 0xF8F4, 0xF8FF, 0x232A, 0x2320,
  0xF8F5, 0x2321, 0xF8F6, 0xF8F7, 0xF8F8, 0xF8F9, 0xF8FA, 0xF8FB,
  0xF8FC, 0xF8FD, 0xF8FE]

/-- Glyph names of the ZapfDingbats font (`a1`…`a206`), parallel to `dingbatCodes`. Used only
for a font known to be ZapfDingbats (AGL specification: the ITC Zapf Dingbats Glyph List
applies to that font alone; other fonts may name glyphs `a12` for unrelated shapes). -/
def dingbatNames : Array String := #[
  "a1", "a2", "a202", "a3", "a4", "a5", "a119", "a118", "a117", "a11",
  "a12", "a13", "a14", "a15", "a16", "a105", "a17", "a18", "a19", "a20",
  "a21", "a22", "a23", "a24", "a25", "a26", "a27", "a28", "a6", "a7",
  "a8", "a9", "a10", "a29", "a30", "a31", "a32", "a33", "a34", "a35",
  "a36", "a37", "a38", "a39", "a40", "a41", "a42", "a43", "a44", "a45",
  "a46", "a47", "a48", "a49", "a50", "a51", "a52", "a53", "a54", "a55",
  "a56", "a57", "a58", "a59", "a60", "a61", "a62", "a63", "a64", "a65",
  "a66", "a67", "a68", "a69", "a70", "a71", "a72", "a73", "a74", "a203",
  "a75", "a204", "a76", "a77", "a78", "a79", "a81", "a82", "a83", "a84",
  "a97", "a98", "a99", "a100", "a89", "a90", "a93", "a94", "a91", "a92",
  "a205", "a85", "a206", "a86", "a87", "a88", "a95", "a96", "a101", "a102",
  "a103", "a104", "a106", "a107", "a108", "a112", "a111", "a110", "a109", "a120",
  "a121", "a122", "a123", "a124", "a125", "a126", "a127", "a128", "a129", "a130",
  "a131", "a132", "a133", "a134", "a135", "a136", "a137", "a138", "a139", "a140",
  "a141", "a142", "a143", "a144", "a145", "a146", "a147", "a148", "a149", "a150",
  "a151", "a152", "a153", "a154", "a155", "a156", "a157", "a158", "a159", "a160",
  "a161", "a163", "a164", "a196", "a165", "a192", "a166", "a167", "a168", "a169",
  "a170", "a171", "a172", "a173", "a162", "a174", "a175", "a176", "a177", "a178",
  "a179", "a193", "a180", "a199", "a181", "a200", "a182", "a201", "a183", "a184",
  "a197", "a185", "a194", "a198", "a186", "a195", "a187", "a188", "a189", "a190",
  "a191"]

/-- Unicode code points of `dingbatNames` (Adobe's ITC Zapf Dingbats Glyph List): the
Dingbats block `U+2701`–`U+27BE` by position, except the glyphs Unicode encodes elsewhere
(`☎ ☛ ☞ ★ ● ■ ▲ ▼ ◆ ◗`, the suits `U+2660`–`U+2666`, `①`–`⑩`, `→ ↔ ↕`) and the ornamental
brackets `0x80`–`0x8D` at `U+2768`–`U+2775`. -/
def dingbatCodes : Array Nat := #[
0x2701, 0x2702, 0x2703, 0x2704, 0x260E, 0x2706, 0x2707, 0x2708, 0x2709, 0x261B,
  0x261E, 0x270C, 0x270D, 0x270E, 0x270F, 0x2710, 0x2711, 0x2712, 0x2713, 0x2714,
  0x2715, 0x2716, 0x2717, 0x2718, 0x2719, 0x271A, 0x271B, 0x271C, 0x271D, 0x271E,
  0x271F, 0x2720, 0x2721, 0x2722, 0x2723, 0x2724, 0x2725, 0x2726, 0x2727, 0x2605,
  0x2729, 0x272A, 0x272B, 0x272C, 0x272D, 0x272E, 0x272F, 0x2730, 0x2731, 0x2732,
  0x2733, 0x2734, 0x2735, 0x2736, 0x2737, 0x2738, 0x2739, 0x273A, 0x273B, 0x273C,
  0x273D, 0x273E, 0x273F, 0x2740, 0x2741, 0x2742, 0x2743, 0x2744, 0x2745, 0x2746,
  0x2747, 0x2748, 0x2749, 0x274A, 0x274B, 0x25CF, 0x274D, 0x25A0, 0x274F, 0x2750,
  0x2751, 0x2752, 0x25B2, 0x25BC, 0x25C6, 0x2756, 0x25D7, 0x2758, 0x2759, 0x275A,
  0x275B, 0x275C, 0x275D, 0x275E, 0x2768, 0x2769, 0x276A, 0x276B, 0x276C, 0x276D,
  0x276E, 0x276F, 0x2770, 0x2771, 0x2772, 0x2773, 0x2774, 0x2775, 0x2761, 0x2762,
  0x2763, 0x2764, 0x2765, 0x2766, 0x2767, 0x2663, 0x2666, 0x2665, 0x2660, 0x2460,
  0x2461, 0x2462, 0x2463, 0x2464, 0x2465, 0x2466, 0x2467, 0x2468, 0x2469, 0x2776,
  0x2777, 0x2778, 0x2779, 0x277A, 0x277B, 0x277C, 0x277D, 0x277E, 0x277F, 0x2780,
  0x2781, 0x2782, 0x2783, 0x2784, 0x2785, 0x2786, 0x2787, 0x2788, 0x2789, 0x278A,
  0x278B, 0x278C, 0x278D, 0x278E, 0x278F, 0x2790, 0x2791, 0x2792, 0x2793, 0x2794,
  0x2192, 0x2194, 0x2195, 0x2798, 0x2799, 0x279A, 0x279B, 0x279C, 0x279D, 0x279E,
  0x279F, 0x27A0, 0x27A1, 0x27A2, 0x27A3, 0x27A4, 0x27A5, 0x27A6, 0x27A7, 0x27A8,
  0x27A9, 0x27AA, 0x27AB, 0x27AC, 0x27AD, 0x27AE, 0x27AF, 0x27B1, 0x27B2, 0x27B3,
  0x27B4, 0x27B5, 0x27B6, 0x27B7, 0x27B8, 0x27B9, 0x27BA, 0x27BB, 0x27BC, 0x27BD,
  0x27BE]

/-- `StandardEncoding` (Annex D, column STD). -/
def standardEncoding : Encoding := ofNameTable standardNames

/-- `WinAnsiEncoding` (Annex D, column WIN, with the Annex D notes applied). -/
def winAnsiEncoding : Encoding := ofNameTable winAnsiNames

/-- `MacRomanEncoding` (Annex D, column MAC). -/
def macRomanEncoding : Encoding := ofNameTable macRomanNames

/-- `PDFDocEncoding` (Annex D, column PDF, Table D.3). -/
def pdfDocEncoding : Encoding := ofNameTable pdfDocNames

/-- The built-in encoding of the standard Symbol font (Annex D.5). -/
def symbolEncoding : Encoding := ofNameTable symbolNames

/-- The built-in encoding of the standard ZapfDingbats font (Annex D.6). -/
def zapfDingbatsEncoding : Encoding := ofNameTable zapfDingbatsNames

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

set_option maxRecDepth 4000 in
/-- The Symbol built-in encoding has 256 entries. -/
theorem symbolEncoding_size : symbolEncoding.size = 256 := by
  rw [symbolEncoding, ofNameTable, Array.size_map]; rfl

set_option maxRecDepth 4000 in
/-- The ZapfDingbats built-in encoding has 256 entries. -/
theorem zapfDingbatsEncoding_size : zapfDingbatsEncoding.size = 256 := by
  rw [zapfDingbatsEncoding, ofNameTable, Array.size_map]; rfl

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

/-- Strip a subset tag: six upper-case ASCII letters followed by `+` (ISO 32000-2 §9.9.2). -/
def stripSubsetTag (cs : List Char) : List Char :=
  match cs with
  | a :: b :: c :: d :: e :: f :: '+' :: rest =>
    if [a, b, c, d, e, f].all fun x => 'A' ≤ x ∧ x ≤ 'Z' then rest else cs
  | _ => cs

/-- The built-in encoding of a standard symbolic font named by `/BaseFont` (Annex D.5, D.6):
after stripping a subset tag and spaces, a name starting with `Symbol` gives
`symbolEncoding`, one starting with `ZapfDingbats` or `Dingbats` gives `zapfDingbatsEncoding`
(the same family prefixes as `Std14.ofBaseFont`); any other name gives `none`. -/
def symbolicBuiltin? (baseFont : String) : Option Encoding :=
  let cs := (stripSubsetTag baseFont.toList).filter (· ≠ ' ')
  if "Symbol".toList.isPrefixOf cs then some symbolEncoding
  else if "ZapfDingbats".toList.isPrefixOf cs || "Dingbats".toList.isPrefixOf cs then
    some zapfDingbatsEncoding
  else none

/-- `symbolicBuiltin?` gives a 256-entry encoding. -/
theorem symbolicBuiltin?_size (baseFont : String) (b : Encoding)
    (h : symbolicBuiltin? baseFont = some b) : b.size = 256 := by
  unfold symbolicBuiltin? at h
  dsimp only at h
  split at h
  · cases h; exact symbolEncoding_size
  · split at h
    · cases h; exact zapfDingbatsEncoding_size
    · cases h

/-- The `/BaseFont` of a font dictionary as a string (`""` when absent or not a name). -/
def baseFontOf (resolve : PdfObject → PdfObject) (fontDict : Dict) : String :=
  match getR resolve fontDict "BaseFont" with
  | some (.name n) => glyphNameOf n.bytes
  | _ => ""

/-- The implicit base encoding of a simple font: the program's built-in encoding `builtin?`
when the caller knows it (an embedded program), else the built-in encoding of a standard
symbolic font named by `/BaseFont` (Symbol, ZapfDingbats: `symbolicBuiltin?`), else
`StandardEncoding`. -/
def implicitBase (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) : Encoding :=
  match builtin? with
  | some b => b
  | none => (symbolicBuiltin? (baseFontOf resolve fontDict)).getD standardEncoding

/-- The implicit base has 256 entries whenever `builtin?` has (or is absent). -/
theorem implicitBase_size (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) (h : ∀ b, builtin? = some b → b.size = 256) :
    (implicitBase resolve fontDict builtin?).size = 256 := by
  unfold implicitBase
  cases hb : builtin? with
  | some b => exact h b hb
  | none =>
    cases hs : symbolicBuiltin? (baseFontOf resolve fontDict) with
    | none => simpa using standardEncoding_size
    | some e => simpa using symbolicBuiltin?_size _ e hs

/-- The encoding of a simple font (ISO 32000-2 §9.6.5, Table 112). The implicit base is
`implicitBase`: `builtin?` (the embedded program's built-in encoding) when known, else the
built-in encoding of a non-embedded standard symbolic font (Symbol, ZapfDingbats), else
`StandardEncoding`. Never fails: a bad `/Encoding` entry leaves the implicit base. -/
def simpleEncoding (resolve : PdfObject → PdfObject) (fontDict : Dict)
    (builtin? : Option Encoding) : Encoding :=
  let implicit := implicitBase resolve fontDict builtin?
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
  have hi : (implicitBase resolve fontDict builtin?).size = 256 :=
    implicitBase_size resolve fontDict builtin? h
  have hn : ∀ n, ((namedEncoding? n).getD (implicitBase resolve fontDict builtin?)).size = 256 := by
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
        | some (.name n) => (namedEncoding? n).getD (implicitBase resolve fontDict builtin?)
        | _ => implicitBase resolve fontDict builtin?).size = 256 := by
      split
      · exact hn _
      · exact hi
    split
    · rw [applyDifferences_size]; exact hb
    · exact hb
  · exact hi

/-! ## Glyph name → Unicode (Adobe Glyph List specification) -/

/-- The code point of `g` in a name table and its parallel code table. -/
def tableLookup (names : Array String) (codes : Array Nat) (g : GlyphName) : Option Nat :=
  match names.findIdx? (· == g) with
  | some i => codes[i]?
  | none => none

/-- The AGL code point of a glyph name in the subset `aglNames` or `aglSymbolNames`. -/
def aglLookup (g : GlyphName) : Option Nat :=
  (tableLookup aglNames aglCodes g).or (tableLookup aglSymbolNames aglSymbolCodes g)

/-- The code point of a ZapfDingbats glyph name (`a1`…`a206`, `dingbatNames`). -/
def dingbatLookup (g : GlyphName) : Option Nat := tableLookup dingbatNames dingbatCodes g

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

/-! ### The full glyph list (`GlyphList.lean`, task 6.7b) -/

/-- One line `name;HEX[ HEX…]` of `aglData`: the name and its Unicode sequence (every group
exactly four to six hex digits and a scalar value), else `none`. -/
def parseAglLine (l : String) : Option (String × List Char) :=
  match l.splitOn ";" with
  | [n, v] =>
    let groups := v.splitOn " "
    let cps := groups.filterMap fun g =>
      if 4 ≤ g.length ∧ g.length ≤ 6 then
        (parseHexAux 0 g.toList).bind fun x => if isScalar x then some (Char.ofNat x) else none
      else none
    if cps.length == groups.length && !n.isEmpty then some (n, cps) else none
  | _ => none

/-- The full glyph list, parsed once (a closed constant): the AGL 2.0 plus the TeX names of
`texglyphlist.txt`, sorted by name (`aglTable_sorted`). -/
def aglTable : Array (String × List Char) :=
  ((aglData.splitOn "\n").filterMap parseAglLine).toArray

/-- Binary search for `k` in the name-sorted table `t` between `lo` (inclusive) and `hi`
(exclusive); terminates on `hi - lo`. -/
def bsearch (t : Array (String × List Char)) (k : String) (lo hi : Nat) : Option (List Char) :=
  if _h : lo < hi then
    let mid := (lo + hi) / 2
    match t[mid]? with
    | some (n, v) =>
      if k < n then bsearch t k lo mid
      else if n < k then bsearch t k (mid + 1) hi
      else some v
    | none => none
  else none
termination_by hi - lo

/-- The Unicode sequence of a glyph name in the full glyph list (`aglTable`). -/
def aglFullLookup (g : GlyphName) : Option (List Char) := bsearch aglTable g 0 aglTable.size

/-- MuPDF's `aNN` names (decimal, as `fz_unicode_from_glyph_name`): `a` followed by two to five
decimal digits whose value `v` is in `32..0xFFFF` and a scalar value maps to `U+v` (Type 3 fonts
of dvips through Ghostscript name glyphs by their code; MuPDF also maps `1..31`, to control
characters, which extraction would turn into spaces). Not used for ZapfDingbats fonts, whose
`a1`…`a206` are their own glyph names. -/
def aDecimal : List Char → Option Char
  | 'a' :: ds@(_ :: _ :: _) =>
    if ds.length ≤ 5 ∧ ds.all Char.isDigit then
      let v := ds.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0
      if 32 ≤ v ∧ v ≤ 0xFFFF ∧ isScalar v then some (Char.ofNat v) else none
    else none
  | _ => none

/-- Map one `_`-separated component of a glyph name (AGL specification, step 3); with
`dingbats` (the font is ZapfDingbats) the ITC Zapf Dingbats Glyph List is tried first. Then the
hand-checked AGL subset (`aglLookup`), the full glyph list with the TeX names
(`aglFullLookup`), `uniXXXX…`, `uXXXX`–`uXXXXXX`, and (not for ZapfDingbats) MuPDF's decimal
`aNN` (`aDecimal`). -/
def componentToUnicode (dingbats : Bool) (comp : List Char) : List Char :=
  let name := String.ofList comp
  match (if dingbats then dingbatLookup name else none).or (aglLookup name) with
  | some u => [Char.ofNat u]
  | none =>
    match aglFullLookup name with
    | some cs => cs
    | none =>
      match comp with
      | 'u' :: 'n' :: 'i' :: rest@(_ :: _) => (uniGroups rest).getD []
      | 'u' :: rest =>
        if 4 ≤ rest.length ∧ rest.length ≤ 6 then
          match parseHexAux 0 rest with
          | some v => if isScalar v then [Char.ofNat v] else []
          | none => []
        else []
      | _ => if dingbats then [] else (aDecimal comp).toList

/-- The Unicode text of a glyph name per the Adobe Glyph List specification, for a font that
is ZapfDingbats (`dingbats = true`: `a1`…`a206` map through the ITC Zapf Dingbats Glyph
List, as the AGL specification prescribes for that font only) or not. -/
def glyphToUnicodeIn (dingbats : Bool) (g : GlyphName) : Option String :=
  let base := g.toList.takeWhile (· ≠ '.')
  let out := (base.splitOn '_').flatMap (componentToUnicode dingbats)
  if out.isEmpty then none else some (String.ofList out)

/-- The Unicode text of a glyph name per the Adobe Glyph List specification (suffix after
`.` dropped, `_` ligature components concatenated); `none` when nothing maps. The fallback for
text extraction without `/ToUnicode` (task 6.5). -/
def glyphToUnicode (g : GlyphName) : Option String :=
  glyphToUnicodeIn false g

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
#guard [standardEncoding, winAnsiEncoding, macRomanEncoding, pdfDocEncoding,
    symbolEncoding].all fun e =>
  e.all fun g => match g with | some n => (aglLookup n).isSome | none => true
-- Every ZapfDingbats glyph has a code point through the dingbats list.
#guard zapfDingbatsEncoding.all fun g => match g with
  | some n => (glyphToUnicodeIn true n).isSome | none => true
-- Symbol (Annex D.5): 189 encoded glyphs; ZapfDingbats (Annex D.6): 202.
#guard (symbolEncoding.filterMap id).size == 189
#guard (zapfDingbatsEncoding.filterMap id).size == 202
#guard aglSymbolNames.size == aglSymbolCodes.size && dingbatNames.size == dingbatCodes.size
#guard dingbatNames.size == 201
#guard symbolEncoding.glyph 0x2D == some "minus"
#guard symbolEncoding.glyph 0x4C == some "Lambda"
#guard symbolEncoding.glyph 0x61 == some "alpha"
#guard symbolEncoding.glyph 0x6D == some "mu"
#guard symbolEncoding.glyph 0xA0 == some "Euro"
#guard symbolEncoding.glyph 0xD5 == some "product"
#guard symbolEncoding.glyph 0xF0 == none
#guard symbolEncoding.glyph 0xEF == some "braceex"
#guard symbolEncoding.glyph 0xF1 == some "angleright"
#guard symbolEncoding.glyph 0x7E == some "similar"
#guard symbolEncoding.glyph 0xA1 == some "Upsilon1"
#guard symbolEncoding.glyph 0xFE == some "bracerightbt"
#guard symbolEncoding.glyph 0xFF == none
#guard symbolEncoding.glyph 0x9F == none
#guard symbolEncoding.glyph 0x7F == none
#guard zapfDingbatsEncoding.glyph 0x34 == some "a20"
#guard zapfDingbatsEncoding.glyph 0x6C == some "a71"
#guard zapfDingbatsEncoding.glyph 0x80 == some "a89"
#guard zapfDingbatsEncoding.glyph 0x81 == some "a90"
#guard zapfDingbatsEncoding.glyph 0x84 == some "a91"
#guard zapfDingbatsEncoding.glyph 0x86 == some "a205"
#guard zapfDingbatsEncoding.glyph 0x88 == some "a206"
#guard zapfDingbatsEncoding.glyph 0x8D == some "a96"
#guard zapfDingbatsEncoding.glyph 0x8E == none
#guard zapfDingbatsEncoding.glyph 0x7F == none
#guard zapfDingbatsEncoding.glyph 0xA0 == none
#guard zapfDingbatsEncoding.glyph 0xA1 == some "a101"
#guard zapfDingbatsEncoding.glyph 0xFE == some "a191"
#guard zapfDingbatsEncoding.glyph 0xF0 == none
#guard glyphToUnicode "minus" == some "−"
#guard glyphToUnicode "Lambda" == some "Λ"
#guard glyphToUnicode "alpha" == some "α"
#guard glyphToUnicode "summation" == some "∑"
#guard glyphToUnicode "arrowright" == some "→"
-- `aNN` names map only for ZapfDingbats.
#guard glyphToUnicode "a20" == none
#guard glyphToUnicodeIn true "a20" == some "✔"
#guard glyphToUnicodeIn true "a71" == some "●"
#guard glyphToUnicodeIn true "a35" == some "★"
#guard glyphToUnicodeIn true "a120" == some "①"
#guard glyphToUnicodeIn true "a1" == some "✁"
-- The ornamental brackets 0x80–0x8D map to U+2768–U+2775 (Adobe `zapfdingbats.txt`).
#guard (List.range 14).all fun i =>
  ((zapfDingbatsEncoding.glyph (0x80 + i)).bind (glyphToUnicodeIn true)) ==
    some (String.ofList [Char.ofNat (0x2768 + i)])
#guard glyphToUnicodeIn true "a89" == some "❨"
#guard glyphToUnicodeIn true "a96" == some "❵"
#guard glyphToUnicodeIn true "a191" == some "➾"
#guard glyphToUnicodeIn true "a160" == some "➔"
#guard glyphToUnicodeIn true "a161" == some "→"
#guard glyphToUnicodeIn true "a163" == some "↔"
#guard glyphToUnicode "apple" == some (String.ofList [Char.ofNat 0xF8FF])
#guard glyphToUnicodeIn true "space" == some " "
-- The full glyph list (task 6.7b): parsed completely, sorted, and consistent with the subset.
#guard aglTable.size == 4552 && (aglData.splitOn "\n").length == 4552
#guard (List.range (aglTable.size - 1)).all fun i =>
  match aglTable[i]?, aglTable[i + 1]? with
  | some a, some b => decide (a.1 < b.1)
  | _, _ => false
#guard (aglNames.zip aglCodes).all fun (n, c) => aglFullLookup n == some [Char.ofNat c]
#guard (aglSymbolNames.zip aglSymbolCodes).all fun (n, c) => aglFullLookup n == some [Char.ofNat c]
#guard glyphToUnicode "dotlessj" == some (String.ofList [Char.ofNat 0xF6BE])
#guard glyphToUnicode "afii10017" == some "А"
#guard glyphToUnicode "Ng" == some "Ŋ"
#guard glyphToUnicode "zukatakana" == some "ズ"
-- TeX names (texglyphlist): CMSY, CMEX, CMTT, AMS.
#guard glyphToUnicode "negationslash" == some (String.ofList [Char.ofNat 0x0338])
#guard glyphToUnicode "angbracketleft" == some "⟨"
#guard glyphToUnicode "visiblespace" == some "␣"
#guard glyphToUnicode "turnstileleft" == some "⊢"
#guard glyphToUnicode "minusplus" == some "∓"
#guard glyphToUnicode "circledot" == some "⊙"
#guard glyphToUnicode "owner" == some "∋"
#guard glyphToUnicode "SS" == some "SS"
#guard glyphToUnicode "Digamma" == some (String.ofList [Char.ofNat 0x1D7CB])
#guard glyphToUnicode "altselector" == none
#guard glyphToUnicode "negationslash.alt" == some (String.ofList [Char.ofNat 0x0338])
-- MuPDF's decimal `aNN` names, not for ZapfDingbats.
#guard glyphToUnicode "a66" == some "B"
#guard glyphToUnicode "a8364" == some "€"
#guard glyphToUnicode "a1" == none
#guard glyphToUnicode "a65536" == none
#guard glyphToUnicode "a66x" == none
#guard glyphToUnicode "a0" == none
#guard glyphToUnicode "a12" == none
#guard glyphToUnicodeIn true "a250" == none
#guard glyphToUnicode "g66" == none
-- A non-embedded Symbol / ZapfDingbats font without `/Encoding` uses its built-in encoding.
#guard (simpleEncoding id [(Name.ofString "BaseFont", .name (Name.ofString "Symbol"))]
    none).glyph 0x61 == some "alpha"
#guard (simpleEncoding id [(Name.ofString "BaseFont", .name (Name.ofString "ABCDEF+SymbolMT"))]
    none).glyph 0x2D == some "minus"
#guard (simpleEncoding id [(Name.ofString "BaseFont", .name (Name.ofString "ZapfDingbats"))]
    none).glyph 0x34 == some "a20"
#guard (simpleEncoding id [(Name.ofString "BaseFont", .name (Name.ofString "Symbol")),
    (Name.ofString "Encoding", .name (Name.ofString "WinAnsiEncoding"))] none).glyph 0x61 ==
  some "a"
#guard (simpleEncoding id [(Name.ofString "BaseFont", .name (Name.ofString "Symbol"))]
    (some standardEncoding)).glyph 0x61 == some "a"
#guard (simpleEncoding id [(Name.ofString "BaseFont", .name (Name.ofString "Helvetica"))]
    none).glyph 0x61 == some "a"

end SafePdf.Core.Font
