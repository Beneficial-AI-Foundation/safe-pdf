#!/usr/bin/env python3
"""Fixture for the annotation-dictionary builder (task 9.5b, Tests/WriteAnnots.lean).

  text.pdf   2 pages, 300 x 200, classic xref with /ID. Page 1: black Helvetica text
             "Highlight me please" at (40, 120), size 18, a black 16 x 16 square at
             (190, 116) (vector ink: our renderer paints non-embedded fonts only with a
             system substitute), and a second line at (40, 60);
             page 2: one line of text and an existing /Square annotation (so the writer
             keeps an old /Annots entry first).

Stdlib only, deterministic. Usage:
    python3 -I Tests/fixtures-write/annots/generate.py           # write the PDF
    python3 -I Tests/fixtures-write/annots/generate.py --check   # verify the file on disk
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HEADER = b"%PDF-1.7\n%\xe2\xe3\xcf\xd3\n"
ID = b"[<0123456789ABCDEF0123456789ABCDEF> <0123456789ABCDEF0123456789ABCDEF>]"

PAGE1 = (b"BT /F1 18 Tf 0 g 40 120 Td (Highlight me please) Tj ET\n"
         b"0 g 190 116 16 16 re f\n"
         b"BT /F1 12 Tf 0 g 40 60 Td (A second line of text for a note.) Tj ET\n")
PAGE2 = b"BT /F1 14 Tf 0 g 30 150 Td (Page two text) Tj ET\n"


def stream_obj(num, body, data):
    return (b"%d 0 obj\n<< %s /Length %d >>\nstream\n" % (num, body, len(data))
            + data + b"\nendstream\nendobj\n")


def plain_obj(num, body):
    return b"%d 0 obj\n%s\nendobj\n" % (num, body)


def text_pdf():
    res = b"/Resources << /Font << /F1 7 0 R >> >>"
    objs = [
        plain_obj(1, b"<< /Type /Catalog /Pages 2 0 R >>"),
        plain_obj(2, b"<< /Type /Pages /Kids [ 3 0 R 5 0 R ] /Count 2 >>"),
        plain_obj(3, b"<< /Type /Page /Parent 2 0 R /MediaBox [ 0 0 300 200 ] "
                     b"/Contents 4 0 R " + res + b" >>"),
        stream_obj(4, b"", PAGE1),
        plain_obj(5, b"<< /Type /Page /Parent 2 0 R /MediaBox [ 0 0 300 200 ] "
                     b"/Contents 6 0 R " + res + b" /Annots [ 8 0 R ] >>"),
        stream_obj(6, b"", PAGE2),
        plain_obj(7, b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica "
                     b"/Encoding /WinAnsiEncoding >>"),
        plain_obj(8, b"<< /Type /Annot /Subtype /Square /Rect [ 200 20 260 80 ] "
                     b"/C [ 0 0 1 ] >>"),
    ]
    out = bytearray(HEADER)
    offs = []
    for b in objs:
        offs.append(len(out))
        out += b
    xref = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f\r\n" % (len(objs) + 1)
    for o in offs:
        out += b"%010d 00000 n\r\n" % o
    out += (b"trailer\n<< /Size %d /Root 1 0 R /ID %s >>\nstartxref\n%d\n%%%%EOF\n"
            % (len(objs) + 1, ID, xref))
    return bytes(out)


FILES = {"text.pdf": text_pdf}


def main():
    check = "--check" in sys.argv[1:]
    bad = 0
    for name, gen in FILES.items():
        path = os.path.join(HERE, name)
        data = gen()
        if check:
            try:
                with open(path, "rb") as f:
                    same = f.read() == data
            except OSError:
                same = False
            if not same:
                print("stale: " + name)
                bad += 1
        else:
            with open(path, "wb") as f:
                f.write(data)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
