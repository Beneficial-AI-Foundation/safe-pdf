"""TrueType collection fixtures for task 9.r7 (Tests/RasterSubst.lean, docs/raster.md).

macOS ships Helvetica, Times and Courier as TrueType collections (`ttcf`). We cannot commit
Apple's (or any third-party) fonts, so the tests use fonts made here:

    python3 -I Tests/fixtures-subst/make_ttc.py synthetic [DIR]
        # writes DIR/mini.ttc and DIR/mini.ttf (default DIR: Tests/fixtures-subst)

  mini.ttc  four TrueType faces with PostScript names (name ID 6) Helvetica,
            Helvetica-Bold (Macintosh Roman name record), Times-Roman, Times-Bold;
            face i draws every printable ASCII character (0x21-0x7E) as one filled box
            100 * (i + 1) units wide and 700 high (so a test can tell the faces apart by
            ink), space is empty; cmap (3,1) format 6, post 3.0, unitsPerEm 1000.
  mini.ttf  one face of the same kind, PostScript name "CourierNewPSMT", box 250 wide.

    python3 -I Tests/fixtures-subst/make_ttc.py merge OUT A.ttf B.ttf ...
        # a collection of existing TrueType fonts (tables copied, offsets rewritten)

The suite uses `merge` at run time on DejaVu Sans / DejaVu Sans Bold when python3 and the
fonts are installed (nothing of them is committed). Deterministic; stdlib only.
"""
import os
import struct
import sys


def pad4(b):
    return b + b"\0" * (-len(b) % 4)


def write_collection(faces):
    """faces: list of (sfnt_version, {tag: bytes}). Returns the collection bytes."""
    n = len(faces)
    header_len = 12 + 4 * n
    dir_lens = [12 + 16 * len(t) for _, t in faces]
    # offset tables first, then all table data
    dir_offs = []
    off = header_len
    for d in dir_lens:
        dir_offs.append(off)
        off += d
    data = b""
    dirs = []
    for (ver, tables), _ in zip(faces, dir_offs):
        tags = sorted(tables)
        recs = b""
        for tag in tags:
            t = tables[tag]
            recs += struct.pack(">4sIII", tag.encode("latin-1"), 0, off + len(data), len(t))
            data += pad4(t)
        nt = len(tags)
        es = max(k for k in range(16) if (1 << k) <= nt) if nt else 0
        dirs.append(struct.pack(">IHHHH", ver, nt, 16 * (1 << es), es, 16 * nt - 16 * (1 << es))
                    + recs)
    head = b"ttcf" + struct.pack(">HHI", 1, 0, n) + b"".join(struct.pack(">I", o) for o in dir_offs)
    return head + b"".join(dirs) + data


def write_single(ver, tables):
    tags = sorted(tables)
    nt = len(tags)
    off = 12 + 16 * nt
    recs = b""
    data = b""
    for tag in tags:
        t = tables[tag]
        recs += struct.pack(">4sIII", tag.encode("latin-1"), 0, off + len(data), len(t))
        data += pad4(t)
    es = max(k for k in range(16) if (1 << k) <= nt)
    return struct.pack(">IHHHH", ver, nt, 16 * (1 << es), es, 16 * nt - 16 * (1 << es)) + recs + data


def read_sfnt(b):
    ver, nt = struct.unpack(">IH", b[:6])
    tables = {}
    for k in range(nt):
        tag, _, off, ln = struct.unpack(">4sIII", b[12 + 16 * k: 28 + 16 * k])
        tables[tag.decode("latin-1")] = b[off:off + ln]
    return ver, tables


def name_table(ps, mac):
    if mac:
        s = ps.encode("latin-1")
        rec = struct.pack(">HHHHHH", 1, 0, 0, 6, len(s), 0)
    else:
        s = ps.encode("utf-16-be")
        rec = struct.pack(">HHHHHH", 3, 1, 0x409, 6, len(s), 0)
    return struct.pack(">HHH", 0, 1, 6 + 12) + rec + s


def box_font(ps, width, mac_name=False):
    """A TrueType font: .notdef and space empty, every 0x21-0x7E the same box glyph."""
    x0, x1, top = 50, 50 + width, 700
    flags = bytes([1, 1, 1, 1])
    xs = struct.pack(">hhhh", x0, 0, x1 - x0, 0)
    ys = struct.pack(">hhhh", 0, top, 0, -top)
    glyph = struct.pack(">hhhhh", 1, x0, 0, x1, top) + struct.pack(">HH", 3, 0) + flags + xs + ys
    glyph = glyph + b"\0" * (len(glyph) % 2)
    glyf = glyph
    loca = struct.pack(">HHHH", 0, 0, 0, len(glyph) // 2)
    adv = width + 100
    head = struct.pack(">IIIIHHqqhhhhHHhhh", 0x00010000, 0x00010000, 0, 0x5F0F3CF5, 0, 1000,
                       0, 0, 0, 0, x1, top, 0, 8, 2, 0, 0)
    hhea = struct.pack(">IhhhHhhhhhhhhhhhH", 0x00010000, 800, -200, 0, adv, 0, 0, x1, 1, 0, 0,
                       0, 0, 0, 0, 0, 3)
    hmtx = struct.pack(">HhHhHh", 500, 0, adv, 0, adv, 0)
    maxp = struct.pack(">IH", 0x00005000, 3)
    # cmap (3,1) format 6 (trimmed table): 0x20 -> 1, 0x21..0x7E -> 2
    gids = [1] + [2] * (0x7E - 0x20)
    sub = struct.pack(">HHHHH", 6, 10 + 2 * len(gids), 0, 0x20, len(gids))
    sub += b"".join(struct.pack(">H", g) for g in gids)
    cmap = struct.pack(">HHHHI", 0, 1, 3, 1, 12) + sub
    post = struct.pack(">IIhhIIIII", 0x00030000, 0, -100, 50, 0, 0, 0, 0, 0)
    return 0x00010000, {"head": head, "hhea": hhea, "hmtx": hmtx, "maxp": maxp, "cmap": cmap,
                        "loca": loca, "glyf": glyf, "post": post,
                        "name": name_table(ps, mac_name)}


def synthetic(out_dir):
    faces = [box_font("Helvetica", 100), box_font("Helvetica-Bold", 200, mac_name=True),
             box_font("Times-Roman", 300), box_font("Times-Bold", 400)]
    with open(os.path.join(out_dir, "mini.ttc"), "wb") as f:
        f.write(write_collection(faces))
    with open(os.path.join(out_dir, "mini.ttf"), "wb") as f:
        f.write(write_single(*box_font("CourierNewPSMT", 250)))


def merge(out, paths):
    faces = []
    for p in paths:
        with open(p, "rb") as f:
            faces.append(read_sfnt(f.read()))
    with open(out, "wb") as f:
        f.write(write_collection(faces))


def main(argv):
    if len(argv) >= 1 and argv[0] == "synthetic":
        synthetic(argv[1] if len(argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
        return 0
    if len(argv) >= 3 and argv[0] == "merge":
        merge(argv[1], argv[2:])
        return 0
    sys.stderr.write(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
