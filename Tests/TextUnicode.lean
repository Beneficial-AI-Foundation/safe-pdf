import SafePdf

/-!
# Unicode mapping of simple fonts without a complete ToUnicode (task 6.7b)

Plan.md §6 Phase 6 (text extraction, fallback via encoding and glyph names; exit M6). Hand-built
PDFs, each checked against the page text and per-glyph texts that MuPDF 1.25
(`mutool draw -F txt`) produces for the same file (the reproducers were also run through it):

* an embedded **Type 1 program with a TeX built-in encoding** (`ff` at 11, `negationslash`
  at 54, `exclamdown` at 60, `endash`/`emdash` at 123/124, the CMEX-only `parenleftbig` at 33),
  built here (`texFont`: clear text + eexec section, `/lenIV -1` so the charstrings are plain),
  with `/Widths`, without `/Encoding` and without `/ToUnicode`: the built-in encoding is read;
  with a **partial** ToUnicode (only `A`): the program is still read for the other codes;
* TeX, Symbol and AGL glyph names through `/Differences` on a non-embedded font;
* **Type 3** glyphs: AGL names, MuPDF's decimal `aNN`, `uniXXXX`, unknown names at ASCII codes
  (that ASCII character) and above 126 (U+FFFD); the same unknown names in a Type 1 font give
  U+FFFD (no ASCII guess outside Type 3).
-/

namespace SafePdf.Tests.TextUnicode

open SafePdf.Core
open SafePdf.Core.Text

/-- A PDF whose objects `1 …` are the given bodies. -/
def mkPdf (objs : List String) : ByteArray := Id.run do
  let mut body := "%PDF-1.4\n"
  let mut offs : List Nat := []
  let mut i := 1
  for o in objs do
    offs := offs ++ [body.utf8ByteSize]
    body := body ++ s!"{i} 0 obj\n{o}\nendobj\n"
    i := i + 1
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  let x := body.utf8ByteSize
  let rows := String.join (offs.map row)
  (body ++ s!"xref\n0 {objs.length + 1}\n0000000000 65535 f \n" ++ rows ++
    s!"trailer\n<< /Size {objs.length + 1} /Root 1 0 R >>\nstartxref\n{x}\n%%EOF\n").toUTF8

/-- A stream object body. -/
def strmObj (d data : String) : String :=
  s!"<< {d} /Length {data.utf8ByteSize} >>\nstream\n{data}\nendstream"

/-- Lower-case hex of a byte array, with the ASCIIHex end marker. -/
def hex (b : ByteArray) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (b.toList.flatMap fun x => [digit (x.toNat / 16), digit (x.toNat % 16)]) ++ ">"

/-- One page showing `c` with font `/F1` = object 5 (`font`); further objects from 6 on. -/
def doc (font c : String) (extra : List String) : ByteArray := mkPdf ([
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
  "<< /Type /Page /Parent 2 0 R /Resources << /Font << /F1 5 0 R >> >> /Contents 4 0 R >>",
  strmObj "" c,
  font] ++ extra)

/-! ## A Type 1 program with a TeX built-in encoding -/

/-- The glyphs of `texFont` (every charstring is `0 500 hsbw endchar`). -/
def texGlyphs : List String :=
  [".notdef", "A", "ff", "negationslash", "exclamdown", "endash", "emdash", "parenleftbig"]

/-- Clear text of `texFont`: an explicit built-in encoding as in CMR10/CMSY10/CMEX10. -/
def texClear : String :=
  "%!PS-AdobeFont-1.0: SafePdfTeX 001.000\n11 dict begin\n/FontName /SafePdfTeX def\n" ++
  "/PaintType 0 def\n/FontType 1 def\n/FontMatrix [0.001 0 0 0.001 0 0] readonly def\n" ++
  "/Encoding 256 array\n0 1 255 {1 index exch /.notdef put} for\n" ++
  "dup 11 /ff put\ndup 33 /parenleftbig put\ndup 54 /negationslash put\n" ++
  "dup 60 /exclamdown put\ndup 65 /A put\ndup 123 /endash put\ndup 124 /emdash put\n" ++
  "readonly def\n/FontBBox {0 0 1000 1000} readonly def\ncurrentdict end\n" ++
  "currentfile eexec\n"

/-- The private part (plaintext): `/lenIV -1`, so charstrings are not encrypted. -/
def texPrivate : ByteArray :=
  let cs : ByteArray := ⟨#[139, 248, 136, 13, 14]⟩
  let head := "dup /Private 8 dict dup begin\n/RD{string currentfile exch readstring pop}" ++
    "executeonly def\n/ND{noaccess def}executeonly def\n/NP{noaccess put}executeonly def\n" ++
    "/lenIV -1 def\n/Subrs 0 array\n2 index /CharStrings 8 dict dup begin\n"
  let glyphs := texGlyphs.foldl (fun (acc : ByteArray) g =>
    acc ++ s!"/{g} 5 RD ".toUTF8 ++ cs ++ " ND\n".toUTF8) ByteArray.empty
  head.toUTF8 ++ glyphs ++
    "end\nend\nreadonly put\nnoaccess put\ndup /FontName get exch definefont pop\nmark currentfile closefile\n".toUTF8

/-- The eexec section of `texFont`. -/
def texCipher : ByteArray :=
  Font.Type1.encrypt Font.Type1.eexecKey ⟨#[1, 2, 3, 4]⟩ texPrivate

/-- The font program as embedded in `/FontFile`. -/
def texFont : ByteArray := texClear.toUTF8 ++ texCipher

/-- An embedded `texFont` with `/Widths` (codes 0–127, 500 each) and the extra font dictionary
entries `extra`; 6 descriptor, 7 program, then `more`. -/
def texDoc (extra c : String) (more : List String := []) : ByteArray :=
  doc ("<< /Type /Font /Subtype /Type1 /BaseFont /SafePdfTeX /FirstChar 0 /LastChar 127 " ++
      "/Widths [" ++ " ".intercalate (List.replicate 128 "500") ++ "] " ++
      "/FontDescriptor 6 0 R " ++ extra ++ " >>") c
    ([ "<< /Type /FontDescriptor /FontName /SafePdfTeX /Flags 4 /FontBBox [0 0 1000 1000] " ++
        "/ItalicAngle 0 /Ascent 1000 /Descent 0 /CapHeight 1000 /StemV 80 /FontFile 7 0 R >>",
      strmObj (s!"/Filter /ASCIIHexDecode /Length1 {texClear.utf8ByteSize} " ++
        s!"/Length2 {texCipher.size} /Length3 0") (hex texFont) ] ++ more)

/-- A ToUnicode CMap mapping only code 65 (`A`). -/
def partialTU : String :=
  strmObj "" ("1 begincodespacerange <00> <FF> endcodespacerange\n" ++
    "1 beginbfchar <41> <0041> endbfchar")

/-- A ToUnicode CMap mapping every code with a non-zero width (0–127) to `X`. -/
def fullTU : String :=
  strmObj "" ("1 begincodespacerange <00> <FF> endcodespacerange\n" ++
    "1 beginbfrange <00> <7F> [" ++ " ".intercalate (List.replicate 128 "<0058>") ++
    "] endbfrange")

/-! ## Names through `/Differences` -/

/-- A Type 3 font with `/Differences` (`diffs`) starting at code `start`; one charproc. -/
def type3Doc (start : Nat) (names : List String) (c : String) : ByteArray :=
  let procs := " ".intercalate (names.map fun n => s!"/{n} 6 0 R")
  doc ("<< /Type /Font /Subtype /Type3 /FontBBox [0 0 1000 1000] " ++
      "/FontMatrix [0.001 0 0 0.001 0 0] /CharProcs << " ++ procs ++ " >> " ++
      s!"/Encoding << /Type /Encoding /Differences [{start} " ++
      " ".intercalate (names.map ("/" ++ ·)) ++ "] >> /FirstChar 0 /LastChar 255 /Widths [" ++
      " ".intercalate (List.replicate 256 "600") ++ "] /Resources << >> >>") c
    [strmObj "" "600 0 d0 0 0 500 500 re f"]

/-- A non-embedded Type 1 font `/Foo` with `/Differences` from `start`. -/
def type1Doc (start : Nat) (names : List String) (c : String) : ByteArray :=
  doc ("<< /Type /Font /Subtype /Type1 /BaseFont /Foo /FirstChar 0 /LastChar 255 /Widths [" ++
      " ".intercalate (List.replicate 256 "500") ++ s!"] /Encoding << /Differences [{start} " ++
      " ".intercalate (names.map ("/" ++ ·)) ++ "] >> >>") c []

/-- Show each code of `codes` (hex) on its own line, 20 units apart. -/
def lines (codes : List String) : String :=
  "BT /F1 10 Tf 72 700 Td " ++ " ".intercalate (codes.map fun c => s!"<{c}> Tj 0 -20 Td") ++
    " ET"

/-- Extract page 1: glyph texts, page text, font descriptions. -/
def extract (b : ByteArray) : Option (List String × String × List String) :=
  match Doc.openDoc {} b with
  | .ok d =>
    match d.pages.toList with
    | p :: _ =>
      match (extractDocPage {} d p (Filter.Budget.init {})).1 with
      | .ok t => some (t.glyphs.map (·.text), t.text, t.fonts.map (·.2.desc))
      | .error _ => none
    | [] => none
  | .error _ => none

/-- U+FFFD. -/
def r : String := replacementStr

/-- A string of one code point. -/
def u (n : Nat) : String := String.ofList [Char.ofNat n]

/-- The cases: label, PDF, expected glyph texts, whether the font program must be read. -/
def cases : List (String × ByteArray × List String × Bool) :=
  [ -- MuPDF: "ﬀ ≠-slash ¡ – — A" with U+FFFD for parenleftbig (its glyph has no Unicode)
    ("Type1 built-in TeX encoding, /Widths, no /Encoding, no ToUnicode",
      texDoc "" (lines ["0b", "36", "3c", "7b", "7c", "41", "21"]),
      ["ff", u 0x0338, "¡", "–", "—", "A", r], true),
    ("Type1 built-in encoding behind a partial ToUnicode",
      texDoc "/ToUnicode 8 0 R" (lines ["41", "7b", "0b"]) [partialTU],
      ["A", "–", "ff"], true),
    ("Type1 with a complete ToUnicode: the program is not needed",
      texDoc "/ToUnicode 8 0 R" (lines ["41", "7b"]) [fullTU],
      ["X", "X"], false),
    -- Differences replace the built-in names; an unassigned code is `.notdef`
    ("Type1 /Differences over the built-in encoding",
      texDoc "/Encoding << /Differences [123 /minus] >>" (lines ["7b", "7c", "42"]),
      ["−", "—", r], true),
    ("TeX and Symbol names on a non-embedded font",
      type1Doc 161 ["minus", "dagger", "Lambda", "negationslash", "angbracketleft",
        "turnstileleft", "visiblespace", "dotlessj", "afii10017", "periodcentered"]
        (lines ["a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8", "a9", "aa"]),
      ["−", "†", "Λ", u 0x0338, "⟨", "⊢", "␣", u 0xF6BE, "А", "·"], false),
    -- Type 1: unknown names are U+FFFD even at ASCII codes (MuPDF does the same)
    ("Type1 unknown names", type1Doc 66 ["g66", "suppress"] (lines ["42", "43"]), [r, r], false),
    -- Type 3: unknown names at ASCII codes read as ASCII; above 126 U+FFFD; `aNN` decimal
    ("Type3 names", type3Doc 66 ["g66", "foo", "uni0047"] (lines ["42", "43", "44"]),
      ["B", "C", "G"], false),
    ("Type3 names above 126", type3Doc 200
        ["eacute", "a201", "g202", "Cdd", "index204", "a66", "f_i", "uni00E9"]
        (lines ["c8", "c9", "ca", "cb", "cc", "cd", "ce", "cf"]),
      ["é", "É", r, r, r, "B", "fi", "é"], false) ]

/-- Run the cases; the number of failures. -/
def run : IO Nat := do
  let mut bad := 0
  for (label, pdf, texts, wantProg) in cases do
    match extract pdf with
    | some (gs, _, descs) =>
      let hasProg := descs.any fun d => (d.splitOn "FontFile").length > 1
      if gs != texts || hasProg != wantProg then
        IO.println s!"  FAIL {label}: got {gs} {descs}, expected {texts} (program read: {wantProg})"
        bad := bad + 1
    | none =>
      IO.println s!"  FAIL {label}: extraction failed"
      bad := bad + 1
  -- the built-in encoding as parsed from the program itself
  match Font.Type1.parse {} texFont (some texClear.utf8ByteSize) (some texCipher.size) with
  | .ok f =>
    if f.encoding[123]? != some (some "endash") || f.encoding[33]? != some (some "parenleftbig") ||
        f.glyphs.size != texGlyphs.length then
      IO.println s!"  FAIL texFont: encoding / glyphs not as built"
      bad := bad + 1
  | .error _ =>
    IO.println "  FAIL texFont: does not parse"
    bad := bad + 1
  return bad

end SafePdf.Tests.TextUnicode
