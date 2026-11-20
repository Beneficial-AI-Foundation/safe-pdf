"""Write a small two-page text PDF for the bib-lean annotation test (task 10.2).

    python3 -I Tests/biblean/annots-pdf.py OUT.pdf [--rotate 90] [--crop X0 Y0 X1 Y1]

Helvetica 12 pt (standard 14, WinAnsiEncoding); page 1 shows `Hello safe world` with its
baseline at (100, 700) in user space, page 2 `Second page` at (100, 500). `--rotate` sets the
pages' `/Rotate`, `--crop` their `/CropBox` (the MediaBox stays [0 0 612 792]), so the test
can check that the annotation rectangles stay in user space whatever the display transform.
Standard library only; the xref offsets are exact.
"""

import argparse
import sys

PAGES = [(100, 700, "Hello safe world"), (100, 500, "Second page")]


def build(rotate: int, crop) -> bytes:
    n = len(PAGES)
    kids = " ".join(f"{4 + 2 * i} 0 R" for i in range(n))
    objs = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        f"<< /Type /Pages /Kids [{kids}] /Count {n} >>".encode(),
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>",
    ]
    extra = ""
    if rotate:
        extra += f" /Rotate {rotate}"
    if crop:
        extra += " /CropBox [%s]" % " ".join(str(v) for v in crop)
    for i, (x, y, text) in enumerate(PAGES):
        c = f"BT /F1 12 Tf {x} {y} Td ({text}) Tj ET\n".encode("latin-1")
        objs.append(f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792]{extra} "
                    f"/Contents {5 + 2 * i} 0 R /Resources << /Font << /F1 3 0 R >> >> >>".encode())
        objs.append(b"<< /Length %d >>\nstream\n" % len(c) + c + b"endstream")
    out = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
    offsets = []
    for i, body in enumerate(objs, start=1):
        offsets.append(len(out))
        out += b"%d 0 obj\n" % i + body + b"\nendobj\n"
    xref = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for off in offsets:
        out += b"%010d 00000 n \n" % off
    out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, xref)
    return bytes(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--rotate", type=int, default=0)
    ap.add_argument("--crop", type=int, nargs=4)
    a = ap.parse_args()
    with open(a.out, "wb") as f:
        f.write(build(a.rotate, a.crop))
    return 0


if __name__ == "__main__":
    sys.exit(main())
