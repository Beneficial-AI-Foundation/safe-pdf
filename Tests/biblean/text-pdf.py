"""Write a small three-page text PDF for the bib-lean text test (task 10.3).

    python3 -I Tests/biblean/text-pdf.py OUT.pdf

Helvetica (a standard-14 font, WinAnsiEncoding), one text line per `Tj`:

* page 1: a title, the arXiv stamp `arXiv:2101.01234v2 [cs.LG] 5 Jan 2021` and
  `doi:10.1234/safe-pdf.5678.` (the final full stop is sentence punctuation, not DOI);
* page 2: `See also https://doi.org/10.5555/Second-Paper.2, and arXiv:2101.01234.` (a
  second DOI; the same arXiv id without its version, deduplicated);
* page 3: `Reference 10.9999/not-detected` (beyond the two pages scanned for identifiers).

Standard library only; the xref offsets are exact.
"""

import sys

PAGES = [
    ["A Small Paper About Safe PDFs", "arXiv:2101.01234v2 [cs.LG] 5 Jan 2021",
     "doi:10.1234/safe-pdf.5678."],
    ["See also https://doi.org/10.5555/Second-Paper.2, and arXiv:2101.01234."],
    ["Reference 10.9999/not-detected"],
]


def esc(s: str) -> bytes:
    return s.replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)").encode("latin-1")


def content(lines) -> bytes:
    out = b"BT /F1 12 Tf 72 720 Td 16 TL\n"
    for i, line in enumerate(lines):
        out += (b"T* " if i else b"") + b"(" + esc(line) + b") Tj\n"
    return out + b"ET\n"


def build() -> bytes:
    n = len(PAGES)
    # 1 catalog, 2 pages, 3 font, then (page, contents) pairs.
    kids = " ".join(f"{4 + 2 * i} 0 R" for i in range(n))
    objs = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        f"<< /Type /Pages /Kids [{kids}] /Count {n} >>".encode(),
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>",
    ]
    for i, lines in enumerate(PAGES):
        c = content(lines)
        objs.append(f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents {5 + 2 * i} 0 R "
                    f"/Resources << /Font << /F1 3 0 R >> >> >>".encode())
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
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    with open(sys.argv[1], "wb") as f:
        f.write(build())
    return 0


if __name__ == "__main__":
    sys.exit(main())
