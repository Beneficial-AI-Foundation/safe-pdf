"""Generate the substitute-font fixture of task 7.7 (Tests/RasterSubst.lean, docs/raster.md).

    python3 -I Tests/fixtures-subst/gen_subst.py [OUT]     # default Tests/fixtures-subst/subst.pdf

One 400 x 320 pt page, uncompressed, no font embedded. One line of 20 pt text per font,
baselines 280, 240, 200, 160, 120, 80, 40 (pdf y):

  F1  /Type1 /Helvetica, no descriptor, no /Widths (standard-14 AFM widths)
  F2  /Type1 /Helvetica-Bold, /WinAnsiEncoding, no descriptor
  F3  /Type1 /Times-Roman, no descriptor
  F4  /Type1 /Courier, no descriptor
  F5  /TrueType /Arial (MuPDF alias of Helvetica), descriptor /Flags 32, /Widths (Helvetica)
  F6  /TrueType /Verdana (not a standard name), descriptor /Flags 32, /Widths all 600:
      MuPDF's substitute Helvetica, each glyph stretched to 600 units
  F7  /Type1 /Garamond-Bold, descriptor /Flags 34 (serif): substitute Times-Bold, /Widths
      all 500 (stretched)

Deterministic; stdlib only.
"""
import os
import sys

TEXT = "Hamburgefonstiv 0123"

# Helvetica AFM widths of the characters used.
HELV = {" ": 278, "H": 722, "a": 556, "m": 833, "b": 556, "u": 556, "r": 333,
        "g": 556, "e": 556, "f": 278, "o": 556, "n": 556, "s": 500, "t": 278,
        "i": 222, "v": 500, "0": 556, "1": 556, "2": 556, "3": 556}


def widths(fn):
    return "[" + " ".join(str(fn(chr(c))) for c in range(32, 123)) + "]"


def build():
    objs = []

    def add(s):
        objs.append(s)
        return len(objs)

    cat = add("<< /Type /Catalog /Pages 2 0 R >>")
    assert cat == 1
    add(None)  # pages, filled below
    fonts = {}
    fonts["F1"] = add("<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>")
    fonts["F2"] = add("<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold "
                      "/Encoding /WinAnsiEncoding >>")
    fonts["F3"] = add("<< /Type /Font /Subtype /Type1 /BaseFont /Times-Roman >>")
    fonts["F4"] = add("<< /Type /Font /Subtype /Type1 /BaseFont /Courier >>")
    d5 = add("<< /Type /FontDescriptor /FontName /Arial /Flags 32 "
             "/FontBBox [-665 -325 2000 1040] /ItalicAngle 0 /Ascent 905 /Descent -212 "
             "/CapHeight 716 /StemV 80 >>")
    fonts["F5"] = add("<< /Type /Font /Subtype /TrueType /BaseFont /Arial "
                      "/Encoding /WinAnsiEncoding /FirstChar 32 /LastChar 122 "
                      f"/Widths {widths(lambda c: HELV.get(c, 556))} /FontDescriptor {d5} 0 R >>")
    d6 = add("<< /Type /FontDescriptor /FontName /Verdana /Flags 32 "
             "/FontBBox [-50 -207 1447 1000] /ItalicAngle 0 /Ascent 1005 /Descent -209 "
             "/CapHeight 727 /StemV 87 >>")
    fonts["F6"] = add("<< /Type /Font /Subtype /TrueType /BaseFont /Verdana "
                      "/Encoding /WinAnsiEncoding /FirstChar 32 /LastChar 122 "
                      f"/Widths {widths(lambda c: 600)} /FontDescriptor {d6} 0 R >>")
    d7 = add("<< /Type /FontDescriptor /FontName /Garamond-Bold /Flags 34 "
             "/FontBBox [-100 -250 1100 950] /ItalicAngle 0 /Ascent 900 /Descent -250 "
             "/CapHeight 650 /StemV 120 >>")
    fonts["F7"] = add("<< /Type /Font /Subtype /Type1 /BaseFont /Garamond-Bold "
                      "/Encoding /WinAnsiEncoding /FirstChar 32 /LastChar 122 "
                      f"/Widths {widths(lambda c: 500)} /FontDescriptor {d7} 0 R >>")
    lines = []
    for k, name in enumerate(["F1", "F2", "F3", "F4", "F5", "F6", "F7"]):
        y = 280 - 40 * k
        lines.append(f"BT /{name} 20 Tf 20 {y} Td ({TEXT}) Tj ET")
    content = "\n".join(lines) + "\n"
    cont = add(f"<< /Length {len(content)} >>\nstream\n{content}endstream")
    fres = " ".join(f"/{n} {o} 0 R" for n, o in fonts.items())
    page = add(f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 400 320] "
               f"/Resources << /Font << {fres} >> >> /Contents {cont} 0 R >>")
    objs[1] = f"<< /Type /Pages /Kids [{page} 0 R] /Count 1 >>"

    out = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
    offs = []
    for i, o in enumerate(objs):
        offs.append(len(out))
        out += f"{i + 1} 0 obj\n{o}\nendobj\n".encode("latin-1")
    xref = len(out)
    out += f"xref\n0 {len(objs) + 1}\n0000000000 65535 f \n".encode()
    for o in offs:
        out += f"{o:010d} 00000 n \n".encode()
    out += (f"trailer\n<< /Size {len(objs) + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n"
            .encode())
    return bytes(out)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "subst.pdf")
    with open(out, "wb") as f:
        f.write(build())
    print(out)


if __name__ == "__main__":
    main()
