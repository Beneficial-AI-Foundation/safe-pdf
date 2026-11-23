"""Generate Tests/golden/text/enc-*.pdf (task 6.12).

  python3 -I gen_enc.py REPO_ROOT

enc-plain.pdf: one page, unencrypted, built here (stdlib only, deterministic):
  /F1  Helvetica (Type 1, standard 14), /Encoding dict with /Differences [65 /Aring]
  /F2  Type0 Identity-H, CIDFontType2 with /W and /FontFile2 = tiny.ttf, /ToUnicode CMap as a FlateDecode stream
  /F3  TrueType with /FontFile2 = Tests/fonts/tiny.ttf (FlateDecode), no /Widths
       (widths come from the program's hmtx: A 600, space 250)
  /X1  form XObject with its own /Resources (/F1 = Times-Bold)
  /F9  not a resource: MuPDF's substitute Times-Roman
  /Info /Title is a string (encrypted in the encrypted variants).
enc-rc4-40.pdf, enc-rc4-128.pdf, enc-aes-128.pdf, enc-aes-256.pdf: the same file encrypted
by qpdf (empty user password) with --static-id --static-aes-iv (deterministic).
"""
import os
import subprocess
import sys
import zlib


def pdf(objs, info):
    out = b"%PDF-1.7\n"
    offs = []
    for i, body in enumerate(objs, 1):
        offs.append(len(out))
        out += b"%d 0 obj\n" % i + body + b"\nendobj\n"
    x = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for o in offs:
        out += b"%010d 00000 n \n" % o
    out += (b"trailer\n<< /Size %d /Root 1 0 R /Info %d 0 R >>\nstartxref\n%d\n%%%%EOF\n"
            % (len(objs) + 1, info, x))
    return out


def stream(data, extra=b""):
    return b"<< /Length %d%s >>\nstream\n" % (len(data), extra) + data + b"\nendstream"


def flate(data, extra=b""):
    return stream(zlib.compress(data, 9), b" /Filter /FlateDecode" + extra)


CONTENT = (
    b"BT /F1 12 Tf 72 720 Td (Hello A world) Tj ET\n"
    b"BT /F2 12 Tf 72 700 Td <000100020003> Tj ET\n"
    b"BT /F3 12 Tf 72 680 Td (A A) Tj ET\n"
    b"BT /F9 12 Tf 72 660 Td (Missing font's text) Tj ET\n"
    b"q 1 0 0 1 72 640 cm /X1 Do Q\n"
)

FORM = b"BT /F1 12 Tf 0 0 Td (Form text) Tj ET"

TOUNICODE = (
    b"/CIDInit /ProcSet findresource begin 12 dict begin begincmap\n"
    b"/CMapName /Test def /CMapType 2 def\n"
    b"1 begincodespacerange <0000> <FFFF> endcodespacerange\n"
    b"3 beginbfchar <0001> <03A9> <0002> <00B5> <0003> <20AC> endbfchar\n"
    b"endcmap CMapName currentdict /CMap defineresource pop end end\n"
)


def main(root):
    ttf = open(os.path.join(root, "Tests/fonts/tiny.ttf"), "rb").read()
    objs = [
        b"<< /Type /Catalog /Pages 2 0 R >>",                                   # 1
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",   # 2
        b"<< /Type /Page /Parent 2 0 R /Resources << /Font << /F1 5 0 R /F2 6 0 R"
        b" /F3 9 0 R >> /XObject << /X1 11 0 R >> >> /Contents 4 0 R >>",       # 3
        flate(CONTENT),                                                          # 4
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica"
        b" /Encoding << /Type /Encoding /Differences [65 /Aring] >> >>",         # 5
        b"<< /Type /Font /Subtype /Type0 /BaseFont /TestCID /Encoding /Identity-H"
        b" /DescendantFonts [7 0 R] /ToUnicode 8 0 R >>",                        # 6
        b"<< /Type /Font /Subtype /CIDFontType2 /BaseFont /TestCID"
        b" /CIDSystemInfo << /Registry (Adobe) /Ordering (Identity) /Supplement 0 >>"
        b" /W [1 [700 550 600]] /DW 1000 /FontDescriptor 15 0 R >>",                                   # 7
        flate(TOUNICODE),                                                        # 8
        b"<< /Type /Font /Subtype /TrueType /BaseFont /Tiny /FirstChar 32 /LastChar 65"
        b" /FontDescriptor 10 0 R >>",                                          # 9
        b"<< /Type /FontDescriptor /FontName /Tiny /Flags 32 /FontBBox [0 0 600 700]"
        b" /ItalicAngle 0 /Ascent 700 /Descent 0 /CapHeight 700 /StemV 80"
        b" /FontFile2 12 0 R >>",                                               # 10
        stream(FORM, b" /Type /XObject /Subtype /Form /BBox [0 0 300 50]"
               b" /Resources << /Font << /F1 13 0 R >> >>"),                     # 11
        flate(ttf, b" /Length1 %d" % len(ttf)),                                 # 12
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Times-Bold >>",             # 13
        b"<< /Title (Encrypted text \\(6.12\\)) /Producer (gen_enc.py) >>",       # 14
        b"<< /Type /FontDescriptor /FontName /TestCID /Flags 4 /FontBBox [0 0 600 700]"
        b" /ItalicAngle 0 /Ascent 700 /Descent 0 /CapHeight 700 /StemV 80"
        b" /FontFile2 12 0 R >>",                                               # 15
    ]
    d = os.path.join(root, "Tests/golden/text")
    plain = os.path.join(d, "enc-plain.pdf")
    with open(plain, "wb") as f:
        f.write(pdf(objs, 14))
    variants = {
        "enc-rc4-40.pdf": ["40", "--"],
        "enc-rc4-128.pdf": ["128", "--use-aes=n", "--"],
        "enc-aes-128.pdf": ["128", "--use-aes=y", "--"],
        "enc-aes-256.pdf": ["256", "--"],
    }
    for name, args in variants.items():
        subprocess.run(["qpdf", "--static-id", "--static-aes-iv", "--allow-weak-crypto",
                        "--object-streams=disable", "--stream-data=preserve",
                        "--encrypt", "", "owner"] + args + [plain, os.path.join(d, name)],
                       check=True)


if __name__ == "__main__":
    main(sys.argv[1])
