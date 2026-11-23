"""Generator and checker for the golden inputs of the `ops` and `svg` inspector views (task 5.4).

Usage:
  python3 -I Tests/golden/generate_svg.py Tests/golden/svg          write the input PDFs
  python3 -I Tests/golden/generate_svg.py --check Tests/golden/svg  parse every SVG section
                                                                    of the .expected files
                                                                    (and any *.svg given) as XML

Stdlib only, deterministic (no compression). The generated PDFs are the test inputs:

* shapes.pdf  two pages. Page 1: filled and stroked rectangles in gray/RGB/CMYK, even-odd
              fill, q/Q nesting, cm (scale, translate, rotate-ish skew), a curve, line
              caps/joins/miter limit/dashes, zero width, W n clip and a nested W* clip,
              fill-and-stroke b, an unknown operator outside and inside BX/EX, a
              malformed operand, unbalanced Q, a sh and a Do placeholder. /Contents is an
              array of two streams split between two operators. Page 2: /Rotate 90 with a
              CropBox, one stroked rectangle under a non-uniform cm.
* text.pdf    one page of text: Tf, Td, TL, T*, Tj, TJ with adjustments, ' and ", Tr modes
              (fill, stroke, invisible), Tc/Tw/Tz/Ts, Latin-1 and XML-special bytes
              (& < > "), an inline image (BI/ID/EI), text shown without a font (warned).
"""

import os
import sys
import xml.etree.ElementTree as ET


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


SHAPES_1A = b"""% part 1
0.5 g 10 10 100 50 re f
1 0 0 RG 4 w 1 J 1 j 120 10 80 50 re S
0 0 1 0 k 0 1 0 0.5 K 220 10 60 60 re 260 30 60 60 re f*
q 2 0 0 2 300 100 cm 0 0 1 rg 0 0 20 10 re f
  0.5 w [3 1] 0 d 0 J 2 j 0 0 m 20 0 l 20 10 l S
Q
q 1 0.5 0 1 50 150 cm 0.2 0.4 0.6 RG 2 w 0 0 m 30 40 60 -40 90 0 c S Q
0 w 0 G 10 300 m 200 300 l S
"""

SHAPES_1B = b"""% part 2 (separate stream)
q 0 0 300 300 re W n
  1 0 0 rg 50 50 400 400 re f
  q 100 100 100 100 re W* n 0 1 0 rg 0 0 600 600 re f Q
  0.5 0.5 0 rg 0 0 1 RG 3 w 150 150 50 50 re b
Q
0.1 M 400 400 m 450 450 l 500 400 l S
1 2 frobnicate BX 3 zork EX
/x w Q
/Sh0 sh /Im1 Do
"""

SHAPES_2 = b"q 2 0 0 1 10 10 cm 0 0 1 RG 3 w 0 0 50 50 re S Q\n"

TEXT = (
    b"BT (no font yet) Tj ET\n"
    b"BT /F1 12 Tf 72 700 Td (Hello, world) Tj\n"
    b"14 TL T* [(Kern) -250 (ed) 120 (text)] TJ\n"
    b"(Next line via quote) '\n"
    b"2 1 (Word & char spacing) \"\n"
    b"1 0 0 RG 1 Tr (Stroked <text>) Tj 3 Tr (invisible \"quoted\") Tj 0 Tr\n"
    b"1 Tc 2 Tw 80 Tz 3 Ts (Latin-1: caf\\351 \\251) Tj ET\n"
    b"BT 0 0 1 rg /F2 24 Tf 1 0 0 1 300 500 Tm (Big) Tj ET\n"
    b"q 50 0 0 20 72 600 cm BI /W 2 /H 2 /CS /G /BPC 8 ID \x00\x80\xff\x40 EI Q\n"
)


def shapes():
    return pdf([
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R 6 0 R] /Count 2 /MediaBox [0 0 612 792] >>",
        b"<< /Type /Page /Parent 2 0 R /Contents [4 0 R 5 0 R] >>",
        stream(SHAPES_1A),
        stream(SHAPES_1B),
        b"<< /Type /Page /Parent 2 0 R /Rotate 90 /CropBox [5 5 205.5 105] /Contents 7 0 R >>",
        stream(SHAPES_2),
    ])


def text():
    return pdf([
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
        b"<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Resources << /Font << "
        b"/F1 << /Type /Font /Subtype /Type1 /BaseFont /Helvetica >> "
        b"/F2 << /Type /Font /Subtype /Type1 /BaseFont /Times-Roman >> >> >> >>",
        stream(TEXT),
    ])


def svg_sections(text_):
    """Yield (title, svg text) for each `--- svg page N` section of an .expected file."""
    title, buf = None, []
    for line in text_.split("\n"):
        if line.startswith("--- "):
            if title is not None:
                yield title, "\n".join(buf)
            title, buf = (line, []) if line.startswith("--- svg") else (None, [])
        elif title is not None:
            buf.append(line)
    if title is not None:
        yield title, "\n".join(buf)


def check(paths):
    n, bad = 0, 0
    files = []
    for p in paths:
        if os.path.isdir(p):
            files += [os.path.join(p, f) for f in sorted(os.listdir(p))
                      if f.endswith(".expected") or f.endswith(".svg")]
        else:
            files.append(p)
    for f in files:
        with open(f, "rb") as fh:
            data = fh.read()
        if f.endswith(".svg"):
            items = [(f, data)]
        else:
            items = [(f + " " + t, s.encode("utf-8"))
                     for t, s in svg_sections(data.decode("utf-8"))]
        for label, body in items:
            n += 1
            try:
                root = ET.fromstring(body)
                if root.tag != "{http://www.w3.org/2000/svg}svg":
                    raise ValueError("root element is %s" % root.tag)
            except Exception as e:  # report and continue
                bad += 1
                print("NOT WELL-FORMED: %s: %s" % (label, e))
    print("checked %d SVG document(s), %d not well-formed" % (n, bad))
    return 1 if bad or n == 0 else 0


def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "--check":
        sys.exit(check(sys.argv[2:]))
    d = sys.argv[1]
    for name, data in (("shapes.pdf", shapes()), ("text.pdf", text())):
        with open(os.path.join(d, name), "wb") as f:
            f.write(data)


if __name__ == "__main__":
    main()
