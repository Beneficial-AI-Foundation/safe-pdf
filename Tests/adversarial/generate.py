#!/usr/bin/env python3
"""Generate the adversarial seed PDFs (Bogk & Schoepl style malicious structure).

Stdlib only, deterministic (no timestamps, no randomness).
Usage (from anywhere):
    python3 -I Tests/adversarial/generate.py           # write the PDFs
    python3 -I Tests/adversarial/generate.py --check   # re-read them and verify offsets

WARNING: the generated files are designed to hang or crash naive PDF readers.
Do not open them in a viewer.
"""
import os
import re
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HEADER = b"%PDF-1.7\n%\xe2\xe3\xcf\xd3\n"
DEEP = 100_000


def stream_obj(n, dict_inner, data, length=None):
    ln = str(len(data)) if length is None else length
    return (b"%d 0 obj\n<< %s /Length %s >>\nstream\n" % (n, dict_inner.encode(), ln.encode())
            + data + b"\nendstream\nendobj\n")


def plain_obj(n, body):
    return b"%d 0 obj\n%s\nendobj\n" % (n, body.encode() if isinstance(body, str) else body)


class Pdf:
    def __init__(self):
        self.buf = bytearray(HEADER)
        self.offs = {}

    def add(self, n, raw):
        self.offs[n] = len(self.buf)
        self.buf += raw

    def xref_table(self, size, prev=None):
        """Classic xref + trailer covering objects 0..size-1 (missing = free).
        Returns (xref_offset, position_of_prev_digits_or_None)."""
        off = len(self.buf)
        self.buf += b"xref\n0 %d\n" % size
        for i in range(size):
            if i == 0 or i not in self.offs:
                self.buf += b"0000000000 65535 f \n"
            else:
                self.buf += b"%010d 00000 n \n" % self.offs[i]
        self.buf += b"trailer\n<< /Size %d /Root 1 0 R" % size
        pos = None
        if prev is not None:
            self.buf += b" /Prev "
            pos = len(self.buf)
            self.buf += b"%010d" % prev
        self.buf += b" >>\n"
        return off, pos

    def xref_stream(self, num, size, types, root=1):
        """Uncompressed (no /Filter) xref stream object `num`, W [1 4 2].
        types: {objnum: (1, offset, 0) | (2, container, index)}; the stream itself is added."""
        off = len(self.buf)
        types = dict(types)
        types[num] = (1, off, 0)
        data = b""
        for i in range(size):
            t = (0, 0, 65535) if i == 0 or i not in types else types[i]
            data += struct.pack(">BIH", *t)
        d = "/Type /XRef /Size %d /W [1 4 2] /Root %d 0 R" % (size, root)
        self.add(num, stream_obj(num, d, data))
        return off

    def patch(self, pos, value):
        self.buf[pos:pos + 10] = b"%010d" % value

    def finish(self, startxref):
        self.buf += b"startxref\n%d\n%%%%EOF\n" % startxref
        return bytes(self.buf)


def basic_objs(p, pages_kids="[3 0 R]", extra_catalog="", content=b"BT /F1 24 Tf 72 700 Td (Hello) Tj ET",
               page_extra="", resources="<< /Font << /F1 5 0 R >> >>", content_obj=None):
    p.add(1, plain_obj(1, "<< /Type /Catalog /Pages 2 0 R %s>>" % extra_catalog))
    p.add(2, plain_obj(2, "<< /Type /Pages /Kids %s /Count 1 >>" % pages_kids))
    p.add(3, plain_obj(3, "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R "
                          "/Resources %s %s>>" % (resources, page_extra)))
    p.add(4, content_obj if content_obj is not None else stream_obj(4, "", content))
    p.add(5, plain_obj(5, "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>"))


def minimal_valid():
    p = Pdf()
    basic_objs(p)
    x, _ = p.xref_table(6)
    return p.finish(x)


def xref_prev_cycle():
    # Section B (earlier) /Prev -> A; section A (last, startxref) /Prev -> B.
    p = Pdf()
    basic_objs(p)
    b, bpos = p.xref_table(6, prev=0)
    # incremental update between the two sections
    p.add(5, plain_obj(5, "<< /Type /Font /Subtype /Type1 /BaseFont /Courier >>"))
    a, apos = p.xref_table(6, prev=b)
    p.patch(bpos, a)
    return p.finish(a)


def xref_prev_self():
    p = Pdf()
    basic_objs(p)
    # Prev must equal this section's own offset, known before writing it.
    off = len(p.buf)
    x, pos = p.xref_table(6, prev=off)
    assert x == off
    return p.finish(x)


def length_self_ref():
    p = Pdf()
    basic_objs(p, content_obj=stream_obj(4, "", b"BT /F1 24 Tf 72 700 Td (Hello) Tj ET", length="4 0 R"))
    x, _ = p.xref_table(6)
    return p.finish(x)


def length_mutual():
    # Stream A (obj 4): /Length 6 0 R.  Obj 6 lives in ObjStm 5, whose own /Length is 4 0 R
    # (stream A's length).  Resolving A's length needs ObjStm 5, whose decoding needs A's length.
    p = Pdf()
    p.add(1, plain_obj(1, "<< /Type /Catalog /Pages 2 0 R >>"))
    p.add(2, plain_obj(2, "<< /Type /Pages /Kids [3 0 R] /Count 1 >>"))
    p.add(3, plain_obj(3, "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R "
                          "/Resources << >> >>"))
    p.add(4, stream_obj(4, "", b"0 0 m 10 10 l S", length="6 0 R"))
    hdr = b"6 0 "
    p.add(5, stream_obj(5, "/Type /ObjStm /N 1 /First %d" % len(hdr), hdr + b"15", length="4 0 R"))
    types = {i: (1, p.offs[i], 0) for i in (1, 2, 3, 4, 5)}
    types[6] = (2, 5, 0)
    x = p.xref_stream(7, 8, types)
    return p.finish(x)


def pages_kids_cycle():
    p = Pdf()
    basic_objs(p, pages_kids="[3 0 R 2 0 R]")  # second kid is the root /Pages node itself
    x, _ = p.xref_table(6)
    return p.finish(x)


def xobject_recursive():
    p = Pdf()
    form = stream_obj(6, "/Type /XObject /Subtype /Form /BBox [0 0 100 100] "
                         "/Resources << /XObject << /Fm1 6 0 R >> >>", b"/Fm1 Do")
    basic_objs(p, content=b"/Fm1 Do", resources="<< /XObject << /Fm1 6 0 R >> >>")
    p.add(6, form)
    x, _ = p.xref_table(7)
    return p.finish(x)


def xobject_mutual():
    # Fm1 (6) draws Fm2 (7), which draws Fm1: mutual recursion through two forms.
    p = Pdf()
    basic_objs(p, content=b"/Fm1 Do", resources="<< /XObject << /Fm1 6 0 R >> >>")
    p.add(6, stream_obj(6, "/Type /XObject /Subtype /Form /BBox [0 0 100 100] "
                           "/Resources << /XObject << /Fm2 7 0 R >> >>", b"0 0 10 10 re f /Fm2 Do"))
    p.add(7, stream_obj(7, "/Type /XObject /Subtype /Form /BBox [0 0 100 100] "
                           "/Resources << /XObject << /Fm1 6 0 R >> >>", b"5 5 10 10 re f /Fm1 Do"))
    x, _ = p.xref_table(8)
    return p.finish(x)


FANOUT_DEPTH = 8
FANOUT_WIDTH = 16


def xobject_fanout():
    # "Billion laughs" through forms: form k (k = 0..7, objects 6..13) invokes form k+1
    # FANOUT_WIDTH times; the last form fills a rectangle. No cycle and only 8 levels (below
    # the nesting fuel), but 16^8 ≈ 4.3e9 form expansions: only a global operator budget
    # (Limits.maxOpsPerPage) stops it.
    p = Pdf()
    basic_objs(p, content=b"/F0 Do", resources="<< /XObject << /F0 6 0 R >> >>")
    for k in range(FANOUT_DEPTH):
        n = 6 + k
        if k + 1 < FANOUT_DEPTH:
            data = b" ".join([b"/F Do"] * FANOUT_WIDTH)
            res = "/Resources << /XObject << /F %d 0 R >> >>" % (n + 1)
        else:
            data = b"0 0 1 1 re f"
            res = ""
        p.add(n, stream_obj(n, "/Type /XObject /Subtype /Form /BBox [0 0 1 1] %s" % res, data))
    x, _ = p.xref_table(6 + FANOUT_DEPTH)
    return p.finish(x)


def objstm_self_container():
    # Xref stream says object 5 is object 0 of object stream 5 (itself).
    # Object 5 is referenced by the page (/Rotate 5 0 R) so a resolver must follow it.
    p = Pdf()
    p.add(1, plain_obj(1, "<< /Type /Catalog /Pages 2 0 R >>"))
    p.add(2, plain_obj(2, "<< /Type /Pages /Kids [3 0 R] /Count 1 >>"))
    p.add(3, plain_obj(3, "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Rotate 5 0 R "
                          "/Resources << >> >>"))
    types = {i: (1, p.offs[i], 0) for i in (1, 2, 3)}
    types[5] = (2, 5, 0)
    x = p.xref_stream(4, 6, types)
    return p.finish(x)


def deep_nesting():
    p = Pdf()
    deep = b"[" * DEEP + b"]" * DEEP
    p.add(1, plain_obj(1, "<< /Type /Catalog /Pages 2 0 R /Deep 6 0 R >>"))
    p.add(2, plain_obj(2, "<< /Type /Pages /Kids [3 0 R] /Count 1 >>"))
    p.add(3, plain_obj(3, "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Resources << >> >>"))
    p.add(6, plain_obj(6, deep))
    x, _ = p.xref_table(7)
    return p.finish(x)


def objstm(n, members, count=None):
    """Uncompressed object stream `n` holding `members` [(num, direct object)]; `count`
    overrides /N (default: the number of members)."""
    pairs, body = [], b""
    for num, obj in members:
        pairs.append(b"%d %d" % (num, len(body)))
        body += obj.encode() + b"\n"
    hdr = b" ".join(pairs) + b"\n"
    cnt = len(members) if count is None else count
    return stream_obj(n, "/Type /ObjStm /N %d /First %d" % (cnt, len(hdr)), hdr + body)


PAGES2 = "<< /Type /Pages /Kids [3 0 R] /Count 1 >>"
PAGE3 = "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Resources << >> >>"


def repair_only(*objs):
    """A catalog (object 1, classic) and `objs` [(num, raw)], with NO cross-reference data
    and no trailer: only the repair path (task 12.7e, rule R6) can open it."""
    p = Pdf()
    p.add(1, plain_obj(1, "<< /Type /Catalog /Pages 2 0 R >>"))
    for n, raw in objs:
        p.add(n, raw)
    p.buf += b"%%EOF\n"
    return bytes(p.buf)


def objstm_n_overflow():
    # /N claims 1000 members but the header holds 2 pairs: the strict header check rejects
    # the container, R6 adds nothing (objects 2 and 3 stay undefined).
    return repair_only((4, objstm(4, [(2, PAGES2), (3, PAGE3)], count=1000)))


def objstm_dup_claim():
    # Containers 4 and 6 both list object 3 (different page sizes); the newest (6) wins.
    page_b = "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 100] /Resources << >> >>"
    return repair_only((4, objstm(4, [(2, PAGES2), (3, PAGE3)])),
                       (6, objstm(6, [(3, page_b)])))


def objstm_nested():
    # Container 4 lists object 6, which is itself a (classic) container, and object 5, an
    # object-stream dictionary that exists only inside 4 (a compressed "container"), and
    # holds the full text of a third container (object 7) inside a string member. R6 keeps 6
    # in use with its own members (3), gives 5 a compressed entry, never reads 5 or 7 as
    # containers, and 7 is no scan hit (the scan jumps over container 4).
    inner7 = objstm(7, [(2, "<< /Type /Pages /Kids [] /Count 0 >>")]).decode("latin-1")
    return repair_only(
        (4, objstm(4, [(6, "<< >>"), (5, "<< /Type /ObjStm /N 1 /First 4 >>"), (2, PAGES2),
                       (8, "(" + inner7.replace("(", "").replace(")", "") + ")")])),
        (6, objstm(6, [(3, PAGE3)])))


def objstm_huge_n():
    # /N at limits.maxObjects (8388607) with a 2-pair header: the header parse stops at the
    # end of the header data; /N above it: limitExceeded before any decode. Neither adds.
    return repair_only((4, objstm(4, [(2, PAGES2), (3, PAGE3)], count=8388607)),
                       (6, objstm(6, [(9, "1")], count=99999999)))


# Files with no cross-reference data (repair path only): `--check` verifies that instead.
REPAIR_ONLY = {"objstm-n-overflow.pdf", "objstm-dup-claim.pdf", "objstm-nested.pdf",
               "objstm-huge-n.pdf"}


FILES = {
    "minimal-valid.pdf": minimal_valid,
    "xref-prev-cycle.pdf": xref_prev_cycle,
    "xref-prev-self.pdf": xref_prev_self,
    "length-self-ref.pdf": length_self_ref,
    "length-mutual.pdf": length_mutual,
    "pages-kids-cycle.pdf": pages_kids_cycle,
    "xobject-recursive.pdf": xobject_recursive,
    "xobject-mutual.pdf": xobject_mutual,
    "xobject-fanout.pdf": xobject_fanout,
    "objstm-self-container.pdf": objstm_self_container,
    "deep-nesting.pdf": deep_nesting,
    "objstm-n-overflow.pdf": objstm_n_overflow,
    "objstm-dup-claim.pdf": objstm_dup_claim,
    "objstm-nested.pdf": objstm_nested,
    "objstm-huge-n.pdf": objstm_huge_n,
}


def generate():
    for name, fn in FILES.items():
        data = fn()
        with open(os.path.join(HERE, name), "wb") as f:
            f.write(data)
        print("wrote %-28s %7d bytes" % (name, len(data)))


def check_one(name, data):
    """Verify startxref and every in-use xref offset (following /Prev with a visited set)."""
    errs = []
    m = list(re.finditer(rb"startxref\n(\d+)\n%%EOF\n$", data))
    if not m:
        return ["no trailing startxref"]
    off = int(m[0].group(1))
    seen = set()
    sections = 0
    while off is not None and off not in seen:
        seen.add(off)
        sections += 1
        prev = None
        if data[off:off + 5] == b"xref\n":
            mm = re.compile(rb"xref\n0 (\d+)\n").match(data, off)
            if not mm:
                errs.append("bad xref header at %d" % off)
                break
            size = int(mm.group(1))
            pos = mm.end()
            for i in range(size):
                line = data[pos:pos + 20]
                pos += 20
                if len(line) != 20 or line[-2:] != b" \n":
                    errs.append("entry %d malformed" % i)
                    continue
                o, g, t = int(line[:10]), int(line[11:16]), line[17:18]
                if t == b"n" and not data[o:].startswith(b"%d %d obj\n" % (i, g)):
                    errs.append("entry %d offset %d does not point at '%d %d obj'" % (i, o, i, g))
            tm = re.compile(rb"trailer\n<<(.*?)>>\n", re.S).match(data, pos)
            if not tm:
                errs.append("no trailer after xref at %d" % off)
                break
            pm = re.search(rb"/Prev (\d+)", tm.group(1))
            prev = int(pm.group(1)) if pm else None
        else:
            hm = re.compile(rb"(\d+) 0 obj\n<< (.*?) >>\nstream\n", re.S).match(data, off)
            if not hm or b"/Type /XRef" not in hm.group(2):
                errs.append("startxref/Prev %d points at neither 'xref' nor an xref stream" % off)
                break
            d = hm.group(2)
            size = int(re.search(rb"/Size (\d+)", d).group(1))
            w = [int(x) for x in re.search(rb"/W \[(\d+) (\d+) (\d+)\]", d).groups()]
            ln = int(re.search(rb"/Length (\d+)", d).group(1))
            body = data[hm.end():hm.end() + ln]
            if data[hm.end() + ln:hm.end() + ln + 10] != b"\nendstream":
                errs.append("xref stream /Length wrong")
            rl = sum(w)
            if rl * size != ln:
                errs.append("xref stream length %d != %d entries * %d" % (ln, size, rl))
            for i in range(size):
                t, a, b = struct.unpack(">BIH", body[i * rl:(i + 1) * rl])
                if t == 1 and not data[a:].startswith(b"%d %d obj\n" % (i, b)):
                    errs.append("entry %d offset %d does not point at '%d %d obj'" % (i, a, i, b))
                if t == 2 and name != "objstm-self-container.pdf" and name != "length-mutual.pdf":
                    errs.append("unexpected type-2 entry %d" % i)
            pm = re.search(rb"/Prev (\d+)", d)
            prev = int(pm.group(1)) if pm else None
        off = prev
    if off is not None and off in seen:
        # Expected for the cyclic files; stopped by the visited set.
        pass
    return errs


def check():
    bad = 0
    for name in FILES:
        path = os.path.join(HERE, name)
        with open(path, "rb") as f:
            data = f.read()
        if data != FILES[name]():
            print("FAIL %s: file differs from generator output" % name)
            bad += 1
            continue
        if name in REPAIR_ONLY:
            errs = [] if (b"startxref" not in data and b"xref\n" not in data
                          and b"trailer" not in data) else ["has cross-reference data"]
        else:
            errs = check_one(name, data)
        if errs:
            bad += 1
            print("FAIL %s: %s" % (name, "; ".join(errs)))
        else:
            print("ok   %s" % name)
    return 1 if bad else 0


if __name__ == "__main__":
    if "--check" in sys.argv[1:]:
        sys.exit(check())
    generate()
