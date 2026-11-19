import SafePdf

/-!
# Font identity across resource frames (task 6.7a)

Plan.md §6 Phase 6 (text extraction, exit M6), §3 C3/C6. Hand-built PDFs in which a form
XObject and the page both select `/F1` but mean different font objects (different `/Widths`
and different `/ToUnicode`), plus a form with a direct font dictionary under the same name,
a font selected before a form that has its own `/F1`, and an ExtGState `/Font`. Each text run
must take the metrics (glyph positions, i.e. the interpreter's `Config.advance`) and the Unicode
map of its own font object (`Core.Text.extractDocPage`).
-/

namespace SafePdf.Tests.FontIdentity

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

/-- Page content `c`. Objects: 5 page font (Helvetica, WinAnsi: `AB` → "AB", widths 667),
6 form with its own `/F1` = object 7, 7 the form's font (`/Widths [1000 1000]`, ToUnicode
`A → Q`, `B → R`), 8 its ToUnicode, 9 a form whose `/F1` is a direct Courier dictionary
(width 600), 10 a form with its own `/F1` (object 7) that shows text without `Tf`. -/
def doc (c : String) : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
  "<< /Type /Page /Parent 2 0 R /Resources << /Font << /F1 5 0 R >> " ++
    "/XObject << /Fm 6 0 R /Fd 9 0 R /Fi 10 0 R >> " ++
    "/ExtGState << /GS1 << /Font [7 0 R 10] >> >> >> /Contents 4 0 R >>",
  strmObj "" c,
  "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>",
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 612 792] /Resources << /Font << /F1 7 0 R >> >>"
    "BT /F1 10 Tf 72 600 Td (A) Tj (B) Tj ET",
  "<< /Type /Font /Subtype /Type1 /BaseFont /Custom /FirstChar 65 /LastChar 66 " ++
    "/Widths [1000 1000] /ToUnicode 8 0 R >>",
  strmObj "" ("1 begincodespacerange <00> <FF> endcodespacerange\n" ++
    "2 beginbfchar <41> <0051> <42> <0052> endbfchar"),
  strmObj ("/Type /XObject /Subtype /Form /BBox [0 0 612 792] /Resources << /Font << /F1 " ++
      "<< /Type /Font /Subtype /Type1 /BaseFont /Courier >> >> >>")
    "BT /F1 10 Tf 72 500 Td (A) Tj (B) Tj ET",
  strmObj "/Type /XObject /Subtype /Form /BBox [0 0 612 792] /Resources << /Font << /F1 7 0 R >> >>"
    "BT 72 400 Td (AB) Tj ET"]

/-- Extract page 1: glyphs as `(text, x·1000)`, and the page text. -/
def extract (b : ByteArray) : Option (List (String × Int) × String) :=
  match Doc.openDoc {} b with
  | .ok d =>
    match d.pages.toList with
    | p :: _ =>
      match (extractDocPage {} d p (Filter.Budget.init {})).1 with
      | .ok t => some (t.glyphs.map (fun g => (g.text, g.x.raw / 1000)), t.text)
      | .error _ => none
    | [] => none
  | .error _ => none

/-- The cases: label, content, expected glyphs, expected text. -/
def cases : List (String × String × List (String × Int) × String) :=
  [ ("page /F1", "BT /F1 10 Tf 72 700 Td (A) Tj (B) Tj ET",
      [("A", 72000), ("B", 78670)], "AB"),
    ("form /F1 (own object)", "/Fm Do",
      [("Q", 72000), ("R", 82000)], "QR"),
    ("page then form", "BT /F1 10 Tf 72 700 Td (A) Tj (B) Tj ET /Fm Do",
      [("A", 72000), ("B", 78670), ("Q", 72000), ("R", 82000)], "AB\n\nQR"),
    ("form then page", "/Fm Do BT /F1 10 Tf 72 700 Td (A) Tj (B) Tj ET",
      [("Q", 72000), ("R", 82000), ("A", 72000), ("B", 78670)], "QR\n\nAB"),
    ("form /F1 (direct dictionary)", "/Fd Do",
      [("A", 72000), ("B", 78000)], "AB"),
    ("font selected before the form", "/F1 10 Tf /Fi Do",
      [("A", 72000), ("B", 78670)], "AB"),
    ("ExtGState /Font", "BT /GS1 gs 72 700 Td (A) Tj (B) Tj ET",
      [("Q", 72000), ("R", 82000)], "QR") ]

/-- Run the cases; the number of failures. -/
def run : IO Nat := do
  let mut bad := 0
  for (label, c, glyphs, text) in cases do
    match extract (doc c) with
    | some (gs, t) =>
      if gs != glyphs || t != text then
        IO.println s!"  FAIL {label}: got {gs} {repr t}, expected {glyphs} {repr text}"
        bad := bad + 1
    | none =>
      IO.println s!"  FAIL {label}: extraction failed"
      bad := bad + 1
  return bad

end SafePdf.Tests.FontIdentity
