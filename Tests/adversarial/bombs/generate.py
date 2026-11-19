#!/usr/bin/env python3
"""Generate the M3 decompression-bomb corpus (task 3.6a; Plan.md section 6 Phase 3, S3).

Stdlib only (zlib, struct, hashlib), deterministic (no timestamps, no randomness).
Usage (from anywhere):
    python3 -I Tests/adversarial/bombs/generate.py           # write the files + MANIFEST
    python3 -I Tests/adversarial/bombs/generate.py --check   # regenerate in memory and
                                                             # compare byte-for-byte (exit 1
                                                             # on any mismatch)

For every raw stream `NAME` the generator writes
  * NAME.bin  - the encoded stream data,
  * NAME.dict - its stream dictionary as PDF text (`<< /Filter ... >>`, no /Length),
  * NAME.pdf  - a one-page PDF whose page /Contents (object 4) is that stream.
Bombs that only make sense inside the file structure (object stream, xref stream) exist as
PDFs only. `MANIFEST` lists `sha256  size  name` for every file.

The byte-exact output depends on the zlib library Python links against (`--check` reports
the zlib version on a mismatch). The Lean suite only needs the files as committed.

WARNING: these files decompress to gigabytes. Do not open them in a PDF viewer.
"""
import hashlib
import os
import struct
import sys
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
HEADER = b"%PDF-1.7\n%\xe2\xe3\xcf\xd3\n"
KiB = 1 << 10
MiB = 1 << 20
GiB = 1 << 30
SMALL = 1 * MiB          # the suite's small test limit (Tests/Bombs.lean `smallLimit`)
DEFAULT = 256 * MiB      # Limits.default.maxDecodedStreamBytes

_cache = {}


def zfill(n, fill=b"\x00", prefix=b""):
    """zlib (level 9) of `prefix` followed by `n` copies of the 1-byte `fill`, streamed."""
    key = ("zfill", n, fill, prefix)
    if key not in _cache:
        co = zlib.compressobj(9)
        out = [co.compress(prefix)]
        chunk = fill * MiB
        left = n
        while left > 0:
            k = min(left, MiB)
            out.append(co.compress(chunk[:k]))
            left -= k
        out.append(co.flush())
        _cache[key] = b"".join(out)
    return _cache[key]


def zrep(unit, count):
    """zlib (level 9) of `unit * count`, streamed."""
    key = ("zrep", unit, count)
    if key not in _cache:
        co = zlib.compressobj(9)
        per = max(1, MiB // len(unit))
        chunk = unit * per
        out = []
        left = count
        while left > 0:
            k = min(left, per)
            out.append(co.compress(chunk if k == per else unit * k))
            left -= k
        out.append(co.flush())
        _cache[key] = b"".join(out)
    return _cache[key]


def z(data):
    return zlib.compress(data, 9)


def a85(data):
    """ASCII85 encode with `z` for zero groups, terminated by `~>`."""
    out = bytearray()
    for i in range(0, len(data), 4):
        g = data[i:i + 4]
        n = len(g)
        g = g + b"\x00" * (4 - n)
        v = struct.unpack(">I", g)[0]
        if v == 0 and n == 4:
            out += b"z"
            continue
        digs = []
        for _ in range(5):
            digs.append(v % 85)
            v //= 85
        out += bytes(33 + d for d in reversed(digs))[:n + 1]
    return bytes(out) + b"~>"


def ahx(data):
    return data.hex().upper().encode() + b">"


# ---------------------------------------------------------------- LZW

def lzw_width(nxt):
    """Code width with /EarlyChange 1 (Core/Filter/LZW.lean `codeWidth true`)."""
    n = nxt + 1
    return 9 if n < 512 else 10 if n < 1024 else 11 if n < 2048 else 12


class BitWriter:
    def __init__(self):
        self.acc = 0
        self.nbits = 0
        self.out = bytearray()

    def put(self, code, w):
        self.acc = (self.acc << w) | code
        self.nbits += w
        while self.nbits >= 8:
            self.nbits -= 8
            self.out.append((self.acc >> self.nbits) & 0xFF)
        self.acc &= (1 << self.nbits) - 1

    def bytes(self):
        if self.nbits:
            return bytes(self.out) + bytes([(self.acc << (8 - self.nbits)) & 0xFF])
        return bytes(self.out)


def lzw_kwkwk(cycles, repeats):
    """`cycles` times: CLEAR, literal 0, then the KwKwK codes 258..4095 (code c emits c-256
    zero bytes, 7.37 MB per cycle from ~5.7 KB). Then `repeats` times the code 4095 on the
    full table (3839 bytes per 12-bit code), then EOD. Returns (data, decoded size)."""
    bw = BitWriter()
    size = 0
    nxt = 258
    for _ in range(cycles):
        bw.put(256, lzw_width(nxt))
        nxt = 258
        bw.put(0, lzw_width(nxt))
        size += 1
        for c in range(258, 4096):
            bw.put(c, lzw_width(nxt))
            size += c - 256
            nxt += 1
    for _ in range(repeats):
        bw.put(4095, lzw_width(nxt))
        size += 3839
    bw.put(257, lzw_width(nxt))
    return bw.bytes(), size


# ---------------------------------------------------------------- PDFs

def stream_obj(n, dict_inner, data):
    return (b"%d 0 obj\n<< %s /Length %d >>\nstream\n" % (n, dict_inner.encode(), len(data))
            + data + b"\nendstream\nendobj\n")


def plain_obj(n, body):
    return b"%d 0 obj\n%s\nendobj\n" % (n, body.encode())


class Pdf:
    def __init__(self):
        self.buf = bytearray(HEADER)
        self.offs = {}

    def add(self, n, raw):
        self.offs[n] = len(self.buf)
        self.buf += raw

    def xref_table(self, size):
        off = len(self.buf)
        self.buf += b"xref\n0 %d\n" % size
        for i in range(size):
            if i == 0 or i not in self.offs:
                self.buf += b"0000000000 65535 f \n"
            else:
                self.buf += b"%010d 00000 n \n" % self.offs[i]
        self.buf += b"trailer\n<< /Size %d /Root 1 0 R >>\n" % size
        return off

    def xref_stream(self, num, size, types, filt="", data=None):
        """xref stream object `num`, W [1 4 2]. With `data` given, it is used as the
        (already encoded) stream data and `filt` as extra dictionary entries."""
        off = len(self.buf)
        types = dict(types)
        types[num] = (1, off, 0)
        if data is None:
            data = b""
            for i in range(size):
                t = (0, 0, 65535) if i == 0 or i not in types else types[i]
                data += struct.pack(">BIH", *t)
        d = "/Type /XRef /Size %d /W [1 4 2] /Root 1 0 R%s" % (size, filt)
        self.add(num, stream_obj(num, d, data))
        return off

    def finish(self, startxref):
        self.buf += b"startxref\n%d\n%%%%EOF\n" % startxref
        return bytes(self.buf)


CATALOG = "<< /Type /Catalog /Pages 2 0 R >>"
PAGES = "<< /Type /Pages /Kids [3 0 R] /Count 1 >>"
PAGE = "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R >>"


def content_pdf(dict_inner, data):
    """One page whose /Contents is stream object 4 with the given dictionary entries."""
    p = Pdf()
    p.add(1, plain_obj(1, CATALOG))
    p.add(2, plain_obj(2, PAGES))
    p.add(3, plain_obj(3, PAGE))
    p.add(4, stream_obj(4, dict_inner, data))
    return p.finish(p.xref_table(5))


def objstm_pdf(root_inside):
    """Object stream 4 (/FlateDecode) inflating to 320 MiB: header `N 0 ` then `null`, then
    spaces. `root_inside`: the catalog (object 1) is compressed in it; else object 6 (a
    harmless extra object referenced from nowhere) is. Uncompressed xref stream 5."""
    num = 1 if root_inside else 6
    head = b"%d 0 " % num
    first = len(head)
    data = zfill(320 * MiB, b" ", head + b"null")
    p = Pdf()
    if not root_inside:
        p.add(1, plain_obj(1, CATALOG))
    p.add(2, plain_obj(2, "<< /Type /Pages /Kids [] /Count 0 >>"))
    p.add(4, stream_obj(4, "/Type /ObjStm /N 1 /First %d /Filter /FlateDecode" % first, data))
    types = {n: (1, o, 0) for n, o in p.offs.items()}
    types[num] = (2, 4, 0)
    off = p.xref_stream(5, 7, types)
    return p.finish(off)


def objstm_two_pdf():
    """Two object streams, 4 and 5 (/FlateDecode), each inflating to 768 KiB plus its header:
    object 6 lives in 4, object 7 in 5. Each fits the 1 MiB per-stream limit; together (1.5 MiB)
    they exceed a 1 MiB document budget (task 4.5). The catalog is plain; uncompressed xref
    stream 8."""
    p = Pdf()
    p.add(1, plain_obj(1, CATALOG))
    p.add(2, plain_obj(2, "<< /Type /Pages /Kids [] /Count 0 >>"))
    for cont, num in ((4, 6), (5, 7)):
        head = b"%d 0 " % num
        data = zfill(768 * KiB, b" ", head + b"null")
        p.add(cont, stream_obj(cont, "/Type /ObjStm /N 1 /First %d /Filter /FlateDecode"
                               % len(head), data))
    types = {n: (1, o, 0) for n, o in p.offs.items()}
    types[6] = (2, 4, 0)
    types[7] = (2, 5, 0)
    off = p.xref_stream(8, 9, types)
    return p.finish(off)


def xref_bomb_pdf():
    """The only xref section is an xref stream (/FlateDecode) inflating to 320 MiB of zeros
    (its /Size 5 and /W [1 4 2] call for 35 bytes). Objects 1-3 are plain and sound."""
    p = Pdf()
    p.add(1, plain_obj(1, CATALOG))
    p.add(2, plain_obj(2, "<< /Type /Pages /Kids [] /Count 0 >>"))
    p.add(3, plain_obj(3, "null"))
    off = p.xref_stream(4, 5, {}, " /Filter /FlateDecode", zfill(320 * MiB))
    return p.finish(off)


# ---------------------------------------------------------------- the corpus

PNG = "<< /Predictor 12 /Columns 1 >>"


def raw_streams():
    """(name, dictionary text, encoded data, decoded size of the full chain or None when a
    stage before the last already exceeds every limit)."""
    out = []
    f1g = zfill(GiB)
    out.append(("flate-1g", "/Filter /FlateDecode", f1g, GiB))
    out.append(("flate-nested", "/Filter [/FlateDecode /FlateDecode]", z(f1g), GiB))
    out.append(("flate-nested-3", "/Filter [/FlateDecode /FlateDecode /FlateDecode]",
                z(z(f1g)), GiB))
    lz, lzsize = lzw_kwkwk(40, 0)
    out.append(("lzw-kwkwk", "/Filter /LZWDecode", lz, lzsize))
    lz, lzsize = lzw_kwkwk(1, 80000)
    out.append(("lzw-full-table", "/Filter /LZWDecode", lz, lzsize))
    rl = zrep(b"\x81\x00", 5 * MiB // 2)  # 2.5 Mi runs of 128 bytes: 5 MiB -> 320 MiB
    out.append(("runlength", "/Filter [/FlateDecode /RunLengthDecode]", rl, 320 * MiB))
    za = zfill(80 * MiB, b"z")  # 80 Mi `z` -> 320 MiB of zeros
    out.append(("ascii85-z", "/Filter [/FlateDecode /ASCII85Decode]", za, 320 * MiB))
    # 8-deep chain: AHx A85 Fl Fl Fl Fl Fl RL; 9-deep adds one more Fl
    inner = zrep(b"\x81\x00", 5 * MiB // 2)
    for _ in range(4):
        inner = z(inner)
    out.append(("chain-8", "/Filter [/AHx /A85 /Fl /Fl /Fl /Fl /Fl /RL]",
                ahx(a85(inner)), 320 * MiB))
    out.append(("chain-9", "/Filter [/AHx /A85 /Fl /Fl /Fl /Fl /Fl /Fl /RL]",
                ahx(a85(z(inner))), 320 * MiB))
    # predictor: the PNG predictor sits on the inner Flate of 1 GiB of zeros (rows of
    # tag 0 + 1 byte); it cannot amplify, the inner Flate hits the limit first
    out.append(("predictor", "/Filter [/FlateDecode /FlateDecode] /DecodeParms [null %s]" % PNG,
                z(f1g), GiB // 2))
    # controls around the small test limit and the default limit
    out.append(("control-flate-1m", "/Filter /FlateDecode", zfill(SMALL), SMALL))
    out.append(("control-flate-1m-plus1", "/Filter /FlateDecode", zfill(SMALL + 1), SMALL + 1))
    out.append(("control-rl-1m", "/Filter /RunLengthDecode", b"\x81\x00" * (SMALL // 128) + b"\x80",
                SMALL))
    out.append(("control-rl-1m-plus1", "/Filter /RunLengthDecode",
                b"\x81\x00" * (SMALL // 128) + b"\x00\x00\x80", SMALL + 1))
    out.append(("control-predictor-1m", "/Filter /FlateDecode /DecodeParms %s" % PNG,
                zfill(SMALL), SMALL // 2))
    out.append(("control-flate-256m", "/Filter /FlateDecode", zfill(DEFAULT), DEFAULT))
    out.append(("control-flate-256m-plus1", "/Filter /FlateDecode", zfill(DEFAULT + 1),
                DEFAULT + 1))
    return out


# the default-limit controls exist as raw streams only (keeps the corpus under ~5 MB)
NO_PDF = {"control-flate-256m", "control-flate-256m-plus1"}


def generate():
    """{file name: bytes} for the whole corpus, MANIFEST included."""
    files = {}
    for name, dct, data, _ in raw_streams():
        files[name + ".bin"] = data
        files[name + ".dict"] = ("<< %s >>\n" % dct).encode()
        if name not in NO_PDF:
            files[name + ".pdf"] = content_pdf(dct, data)
    files["objstm-bomb.pdf"] = objstm_pdf(False)
    files["objstm-bomb-root.pdf"] = objstm_pdf(True)
    files["objstm-two.pdf"] = objstm_two_pdf()
    files["xref-bomb.pdf"] = xref_bomb_pdf()
    lines = []
    for n in sorted(files):
        lines.append("%s  %d  %s\n" % (hashlib.sha256(files[n]).hexdigest(), len(files[n]), n))
    files["MANIFEST"] = "".join(lines).encode()
    return files


def main():
    files = generate()
    if "--check" in sys.argv[1:]:
        bad = 0
        on_disk = set(os.listdir(HERE)) - {"generate.py", "README.md", "__pycache__"}
        for n in sorted(files):
            path = os.path.join(HERE, n)
            try:
                with open(path, "rb") as f:
                    cur = f.read()
            except OSError:
                print("missing: %s" % n)
                bad += 1
                continue
            if cur != files[n]:
                print("differs: %s" % n)
                bad += 1
        for n in sorted(on_disk - set(files)):
            print("unexpected file: %s" % n)
            bad += 1
        if bad:
            print("%d problem(s); zlib %s (runtime %s)" % (bad, zlib.ZLIB_VERSION,
                                                           zlib.ZLIB_RUNTIME_VERSION))
            sys.exit(1)
        print("ok: %d files match" % len(files))
        return
    for n, data in files.items():
        with open(os.path.join(HERE, n), "wb") as f:
            f.write(data)
    total = sum(len(d) for d in files.values())
    print("wrote %d files, %d bytes" % (len(files), total))


if __name__ == "__main__":
    main()
