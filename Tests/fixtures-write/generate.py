#!/usr/bin/env python3
"""Fixtures for the incremental-update writer (task 9.5a, Tests/WriteIncremental.lean).

Small PDFs covering the cross-reference shapes the writer must extend (ISO 32000-2 §7.5):

  classic.pdf          2 pages, classic xref; page 1 without /Annots, page 2 with a direct
                       /Annots [ 7 0 R ] (a /Square), an /Info and an /ID.
  annots-indirect.pdf  classic xref; both pages share ONE indirect /Annots array object
                       (8 0 R): the writer must rewrite page 1 only, never the shared array.
  annots-null.pdf      classic xref; page 1 has /Annots null.
  updated.pdf          classic.pdf plus one incremental update (two revisions, /Prev).
  xrefstream.pdf       xref stream (FlateDecode + PNG Up predictor), pages and catalog inside
                       an object stream (FlateDecode).
  hybrid.pdf           classic table whose trailer has /XRefStm pointing at an xref stream
                       that lists object 6 (in an object stream) (§7.5.8.4).
  page-gen.pdf         classic xref; page 1 has generation 2.
  broken-xref.pdf      classic.pdf with `startxref` pointing at byte 1: opens only through the
                       repair path, so the writer must refuse it (rule W1).
  linearized.pdf       classic.pdf linearized by qpdf (`--linearize --static-id`; written
                       and checked only when qpdf is installed, else skipped).

Stdlib only, deterministic. Usage:
    python3 -I Tests/fixtures-write/generate.py           # write the PDFs
    python3 -I Tests/fixtures-write/generate.py --check   # verify the files on disk
"""
import os
import shutil
import subprocess
import sys
import tempfile
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
HEADER = b"%PDF-1.7\n%\xe2\xe3\xcf\xd3\n"

CONTENT = b"0 0 1 rg 20 20 100 100 re f\n"
ID = b"[<00112233445566778899AABBCCDDEEFF> <00112233445566778899AABBCCDDEEFF>]"


def stream_obj(num, gen, dict_body, data):
    return (b"%d %d obj\n<< %s /Length %d >>\nstream\n" % (num, gen, dict_body, len(data))
            + data + b"\nendstream\nendobj\n")


def plain_obj(num, gen, body):
    return b"%d %d obj\n%s\nendobj\n" % (num, gen, body)


def classic_file(objs, trailer_extra, base=HEADER, prev=None, size=None):
    """objs: list of (num, gen, bytes of the whole object). Writes one classic section."""
    out = bytearray(base)
    offs = {}
    for num, gen, b in objs:
        offs[num] = (len(out), gen)
        out += b
    xref = len(out)
    nums = sorted(offs)
    size = size if size is not None else max(nums) + 1
    out += b"xref\n"
    if prev is None:
        out += b"0 1\n0000000000 65535 f\r\n"
    # one subsection per run
    runs = []
    for n in nums:
        if runs and runs[-1][-1] + 1 == n:
            runs[-1].append(n)
        else:
            runs.append([n])
    for r in runs:
        out += b"%d %d\n" % (r[0], len(r))
        for n in r:
            off, gen = offs[n]
            out += b"%010d %05d n\r\n" % (off, gen)
    tr = b"/Size %d %s" % (size, trailer_extra)
    if prev is not None:
        tr += b" /Prev %d" % prev
    out += b"trailer\n<< " + tr + b" >>\nstartxref\n%d\n%%%%EOF\n" % xref
    return bytes(out)


def base_objs(page1_extra=b"", page2_extra=b"/Annots [ 7 0 R ]", page1_gen=0):
    return [
        (1, 0, plain_obj(1, 0, b"<< /Type /Catalog /Pages 2 0 R >>")),
        (2, 0, plain_obj(2, 0, b"<< /Type /Pages /Kids [ 3 %d R 5 0 R ] /Count 2 >>" % page1_gen)),
        (3, page1_gen, plain_obj(3, page1_gen,
            b"<< /Type /Page /Parent 2 0 R /MediaBox [ 0 0 200 200 ] /Contents 4 0 R %s >>"
            % page1_extra)),
        (4, 0, stream_obj(4, 0, b"", CONTENT)),
        (5, 0, plain_obj(5, 0,
            b"<< /Type /Page /Parent 2 0 R /MediaBox [ 0 0 200 200 ] /Contents 4 0 R %s >>"
            % page2_extra)),
        (6, 0, plain_obj(6, 0, b"<< /Title (Write fixture) >>")),
        (7, 0, plain_obj(7, 0,
            b"<< /Type /Annot /Subtype /Square /Rect [ 10 10 50 50 ] /C [ 1 0 0 ] >>")),
    ]


def classic():
    return classic_file(base_objs(), b"/Root 1 0 R /Info 6 0 R /ID " + ID)


def annots_indirect():
    objs = base_objs(b"/Annots 8 0 R", b"/Annots 8 0 R")
    objs.append((8, 0, plain_obj(8, 0, b"[ 7 0 R ]")))
    return classic_file(objs, b"/Root 1 0 R")


def annots_null():
    return classic_file(base_objs(b"/Annots null"), b"/Root 1 0 R")


def page_gen():
    return classic_file(base_objs(page1_gen=2), b"/Root 1 0 R")


def updated():
    first = classic()
    prev = int(first.rsplit(b"startxref\n", 1)[1].split(b"\n")[0])
    upd = [(6, 0, plain_obj(6, 0, b"<< /Title (Updated once) >>"))]
    return classic_file(upd, b"/Root 1 0 R /Info 6 0 R /ID " + ID, base=first, prev=prev, size=8)


def png_up(rows, width):
    """PNG Up predictor (type 2) on fixed-width rows."""
    out = bytearray()
    prev = bytes(width)
    for r in rows:
        out.append(2)
        out += bytes((r[i] - prev[i]) & 0xFF for i in range(width))
        prev = r
    return bytes(out)


def objstm(members):
    """members: list of (num, bytes). Returns (N, First, data)."""
    header = bytearray()
    body = bytearray()
    for num, b in members:
        header += b"%d %d " % (num, len(body))
        body += b + b"\n"
    return len(members), len(header), bytes(header) + bytes(body)


def xrefstream():
    out = bytearray(HEADER)
    offs = {}
    n, first, data = objstm([
        (1, b"<< /Type /Catalog /Pages 2 0 R >>"),
        (2, b"<< /Type /Pages /Kids [ 3 0 R 5 0 R ] /Count 2 >>"),
        (3, b"<< /Type /Page /Parent 2 0 R /MediaBox [ 0 0 200 200 ] /Contents 4 0 R >>"),
        (5, b"<< /Type /Page /Parent 2 0 R /MediaBox [ 0 0 200 200 ] /Contents 4 0 R "
            b"/Annots [ 7 0 R ] >>"),
        (7, b"<< /Type /Annot /Subtype /Square /Rect [ 10 10 50 50 ] /C [ 1 0 0 ] >>"),
    ])
    offs[4] = len(out)
    out += stream_obj(4, 0, b"", CONTENT)
    offs[8] = len(out)
    comp = zlib.compress(data, 9)
    out += stream_obj(8, 0, b"/Type /ObjStm /N %d /First %d /Filter /FlateDecode" % (n, first), comp)
    xoff = len(out)
    size = 10
    rows = []
    idx_in_stm = {1: 0, 2: 1, 3: 2, 5: 3, 7: 4}
    for num in range(size):
        if num == 0:
            rows.append(bytes([0, 0, 0, 0, 0xFF, 0xFF]))
        elif num in idx_in_stm:
            rows.append(bytes([2, 0, 0, 8, 0, idx_in_stm[num]]))
        elif num == 4:
            rows.append(bytes([1]) + offs[4].to_bytes(3, "big") + bytes([0, 0]))
        elif num == 8:
            rows.append(bytes([1]) + offs[8].to_bytes(3, "big") + bytes([0, 0]))
        elif num == 9:
            rows.append(bytes([1]) + xoff.to_bytes(3, "big") + bytes([0, 0]))
        else:
            rows.append(bytes([0, 0, 0, 0, 0, 0]))
    raw = zlib.compress(png_up(rows, 6), 9)
    out += stream_obj(9, 0, b"/Type /XRef /Size %d /W [ 1 3 2 ] /Root 1 0 R /ID %s "
                      b"/Filter /FlateDecode /DecodeParms << /Predictor 12 /Columns 6 >>"
                      % (size, ID), raw)
    out += b"startxref\n%d\n%%%%EOF\n" % xoff
    return bytes(out)


def hybrid():
    """Classic table (objects 1-5, 7, 8) + /XRefStm stream listing 6 (in object stream 8)."""
    out = bytearray(HEADER)
    offs = {}
    objs = base_objs()
    for num, gen, b in objs:
        if num == 6:
            continue
        offs[num] = len(out)
        out += b
    n, first, data = objstm([(6, b"<< /Title (Hybrid info) >>")])
    offs[8] = len(out)
    out += stream_obj(8, 0, b"/Type /ObjStm /N %d /First %d" % (n, first), data)
    # the xref stream: entries for 6 (compressed in 8) and itself (9)
    soff = len(out)
    rows = bytes([2, 0, 0, 8, 0, 0]) + bytes([1]) + soff.to_bytes(3, "big") + bytes([0, 0])
    out += stream_obj(9, 0, b"/Type /XRef /Size 10 /W [ 1 3 2 ] /Index [ 6 1 9 1 ]", rows)
    xref = len(out)
    out += b"xref\n0 6\n0000000000 65535 f\r\n"
    for num in range(1, 6):
        out += b"%010d %05d n\r\n" % (offs[num], 0)
    out += b"7 2\n"
    for num in (7, 8):
        out += b"%010d %05d n\r\n" % (offs[num], 0)
    out += (b"trailer\n<< /Size 10 /Root 1 0 R /Info 6 0 R /XRefStm %d >>\nstartxref\n%d\n%%%%EOF\n"
            % (soff, xref))
    return bytes(out)


def broken_xref():
    b = classic()
    head, tail = b.rsplit(b"startxref\n", 1)
    return head + b"startxref\n1\n%%EOF\n"


def linearized():
    """`qpdf --linearize --static-id` of classic.pdf, or None without qpdf."""
    if shutil.which("qpdf") is None:
        return None
    with tempfile.TemporaryDirectory() as d:
        src = os.path.join(d, "in.pdf")
        dst = os.path.join(d, "out.pdf")
        with open(src, "wb") as f:
            f.write(classic())
        subprocess.run(["qpdf", "--linearize", "--static-id", src, dst], check=True)
        with open(dst, "rb") as f:
            return f.read()


FILES = {
    "classic.pdf": classic,
    "annots-indirect.pdf": annots_indirect,
    "annots-null.pdf": annots_null,
    "updated.pdf": updated,
    "xrefstream.pdf": xrefstream,
    "hybrid.pdf": hybrid,
    "page-gen.pdf": page_gen,
    "broken-xref.pdf": broken_xref,
    "linearized.pdf": linearized,
}


def main():
    check = "--check" in sys.argv[1:]
    bad = 0
    for name, fn in FILES.items():
        data = fn()
        if data is None:
            print(f"skip {name} (qpdf not installed)")
            continue
        path = os.path.join(HERE, name)
        if check:
            with open(path, "rb") as f:
                if f.read() != data:
                    print(f"MISMATCH {name}")
                    bad += 1
        else:
            with open(path, "wb") as f:
                f.write(data)
            print(f"wrote {name} ({len(data)} bytes)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
