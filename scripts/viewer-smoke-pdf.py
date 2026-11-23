"""Write a small two-page PDF for the viewer smoke test (task 8.2a).

    python3 -I scripts/viewer-smoke-pdf.py OUT.pdf

Page 1 (US Letter) has a dark blue filled rectangle and a red stroked frame; page 2 (A5,
landscape via /Rotate 90) has a green disc-like polygon. Only vector paths: no fonts, so the
output does not depend on font support. Standard library only; the xref offsets are exact.
"""

import sys


def build() -> bytes:
    page1 = b"0.1 0.2 0.6 rg 72 400 468 300 re f\n1 0 0 RG 6 w 40 40 532 712 re S\n"
    page2 = (b"0 0.6 0.2 rg 210 300 m 300 390 l 390 300 l 300 210 l h f\n"
             b"0 0 0 RG 2 w 50 50 m 370 545 l S\n")
    objs = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R 5 0 R] /Count 2 >>",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R /Resources << >> >>",
        b"<< /Length %d >>\nstream\n" % len(page1) + page1 + b"endstream",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 420 595] /Rotate 90 /Contents 6 0 R /Resources << >> >>",
        b"<< /Length %d >>\nstream\n" % len(page2) + page2 + b"endstream",
    ]
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
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    with open(sys.argv[1], "wb") as f:
        f.write(build())
    return 0


if __name__ == "__main__":
    sys.exit(main())
