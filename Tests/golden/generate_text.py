"""Generator of the golden inputs of the `text` inspector view (task 6.6).

Usage:
  python3 -I Tests/golden/generate_text.py Tests/golden/text     write the input PDFs

Stdlib only, deterministic (no compression). The generated PDFs are the test inputs of
`Tests/TextView.lean` (kept outside the golden directory: every file there is an input):

* latin.pdf    one page, Helvetica (WinAnsiEncoding) and Times-Roman (StandardEncoding):
               Td/T*/TL lines, a TJ word gap and kerning, a paragraph gap (blank line),
               words shown right to left on one line, an overprinted duplicate (fake bold,
               dropped), invisible text (Tr 3, kept), Tc/Tw spacing, WinAnsi bytes
               (e acute, en dash, ligature-free text), a scaled Tm.
* unicode.pdf  three pages. Page 1: a Type0 font (Identity-H, CIDFontType2, /W widths)
               with a /ToUnicode CMap (bfchar and bfrange; a U+FB01 ligature that the
               extraction decomposes to "fi", a CJK character, accented Latin) and one
               unmapped code (U+FFFD). Page 2: text rotated by 90 degrees (Tm 0 1 -1 0) and
               a line upside down (180 degrees). Page 3: /Contents is a FlateDecode stream
               with corrupt data (the page reports its decode error, empty text).
"""

import os
import sys


def pdf(objs):
    """objs: list of bodies (bytes) for objects 1..n; trailer /Root 1 0 R."""
    out = b"%PDF-1.7\n"
    offs = []
    for i, body in enumerate(objs, 1):
        offs.append(len(out))
        out += b"%d 0 obj\n" % i + body + b"\nendobj\n"
    x = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for o in offs:
        out += b"%010d 00000 n \n" % o
    out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, x)
    return out


def stream(data, extra=b""):
    return b"<< /Length %d%s >>\nstream\n" % (len(data), extra) + data + b"\nendstream"


LATIN = (
    b"BT /F1 12 Tf 14 TL 72 720 Td (First line of text.) Tj\n"
    b"T* [(Word) -400 (gap) 30 (and) -20 (kerning)] TJ\n"
    b"0 -40 Td (After a paragraph gap.) Tj ET\n"
    b"BT /F1 12 Tf 200 600 Td (right) Tj -60 0 Td (Left) Tj ET\n"
    b"BT /F1 12 Tf 72 580 Td (Bold) Tj 0.3 0 Td (Bold) Tj ET\n"
    b"BT /F1 12 Tf 3 Tr 72 560 Td (invisible OCR layer) Tj 0 Tr ET\n"
    b"BT /F1 10 Tf 1 Tc 3 Tw 72 540 Td (spaced out words) Tj 0 Tc 0 Tw ET\n"
    b"BT /F1 12 Tf 72 520 Td (caf\\351 \\226 na\\357ve) Tj ET\n"
    b"BT /F2 1 Tf 18 0 0 18 72 480 Tm (Times via Tm, \\256) Tj ET\n"
)


def latin():
    return pdf([
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
        b"<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Resources << /Font << "
        b"/F1 << /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >> "
        b"/F2 << /Type /Font /Subtype /Type1 /BaseFont /Times-Roman >> >> >> >>",
        stream(LATIN),
    ])


TOUNICODE = b"""/CIDInit /ProcSet findresource begin
12 dict begin
begincmap
/CIDSystemInfo << /Registry (Adobe) /Ordering (UCS) /Supplement 0 >> def
/CMapName /Adobe-Identity-UCS def
/CMapType 2 def
1 begincodespacerange
<0000> <FFFF>
endcodespacerange
5 beginbfchar
<0001> <0048>
<0002> <00E9>
<0003> <FB01>
<0004> <4E2D>
<0006> <0020>
endbfchar
1 beginbfrange
<0010> <0019> <0030>
endbfrange
endcmap
CMapName currentdict /CMap defineresource pop
end
end
"""

# Codes: H e-acute fi-ligature CJK space digits 0..3, then an unmapped code 0005.
UNI_PAGE1 = (
    b"BT /T0 14 Tf 72 700 Td <0001000200030004> Tj\n"
    b"0 -20 Td <00100011001200130006> Tj <0005> Tj ET\n"
)

UNI_PAGE2 = (
    b"BT /F1 12 Tf 0 1 -1 0 300 100 Tm (Rotated ninety) Tj ET\n"
    b"BT /F1 12 Tf 0 1 -1 0 300 300 Tm (same line) Tj ET\n"
    b"BT /F1 12 Tf -1 0 0 -1 400 700 Tm (Upside down) Tj ET\n"
)


def unicode_():
    return pdf([
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R 8 0 R 10 0 R] /Count 3 /MediaBox [0 0 612 792] >>",
        b"<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Resources << /Font << /T0 5 0 R >> >> >>",
        stream(UNI_PAGE1),
        b"<< /Type /Font /Subtype /Type0 /BaseFont /TestCID /Encoding /Identity-H "
        b"/DescendantFonts [6 0 R] /ToUnicode 7 0 R >>",
        b"<< /Type /Font /Subtype /CIDFontType2 /BaseFont /TestCID "
        b"/CIDSystemInfo << /Registry (Adobe) /Ordering (Identity) /Supplement 0 >> "
        b"/DW 1000 /W [1 [722 556 556 1000 400 278] 16 25 556] >>",
        stream(TOUNICODE),
        b"<< /Type /Page /Parent 2 0 R /Contents 9 0 R /Resources << /Font << "
        b"/F1 << /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >> "
        b">> >> >>",
        stream(UNI_PAGE2),
        b"<< /Type /Page /Parent 2 0 R /Contents 11 0 R >>",
        stream(b"this is not zlib data", b" /Filter /FlateDecode"),
    ])


def main(argv):
    if len(argv) != 2:
        print(__doc__)
        return 2
    out = argv[1]
    os.makedirs(out, exist_ok=True)
    for name, data in (("latin.pdf", latin()), ("unicode.pdf", unicode_())):
        with open(os.path.join(out, name), "wb") as fh:
            fh.write(data)
        print("wrote %s (%d bytes)" % (os.path.join(out, name), len(data)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
