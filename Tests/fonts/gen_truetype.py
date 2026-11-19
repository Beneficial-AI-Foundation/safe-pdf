#!/usr/bin/env python3
"""Generate a tiny hand-built TrueType font for the `SafePdf.Core.Font.TrueType` tests (task 6.1).

Standard library only; deterministic. Run with

  python3 -I Tests/fonts/gen_truetype.py [OUTDIR]     write the fixtures (default: this directory)
  python3 -I Tests/fonts/gen_truetype.py --check      regenerate in memory, compare with the files
  python3 -I Tests/fonts/gen_truetype.py --hex        print tiny.ttf as hex (for the Lean literal)

The font (Apple TrueType Reference Manual / OpenType spec, `sfnt` version 0x00010000) has
8 tables: cmap glyf head hhea hmtx loca maxp post; unitsPerEm 1000, short `loca`, and 5 glyphs:

  gid  post name  advance  outline
  0    .notdef    500      simple: one rectangle, 4 on-curve points
  1    space      250      empty (no glyf data)
  2    A          600      simple: triangle, middle point off-curve
  3    Aring      600*     composite: A at (0,0) (word args) + gid 4 at (100,50) scaled 0.5
  4    A.ss01     600*     simple: two squares (2 contours, 8 points)

  * numberOfHMetrics = 3, so gids 3 and 4 repeat the last advance (600).

cmap subtables (sorted by platform, encoding):
  (1,0)  format 0:  0x20->1, 0x41->2, 0x81->3 (MacRoman Aring)
  (3,0)  format 6:  firstCode 0xF041: 0xF041->2, 0xF042->4 (symbolic, F000 range)
  (3,1)  format 4:  U+0020->1, U+0041->2 (idDelta), U+00C5->3 (idRangeOffset), 0xFFFF end
  (3,10) format 12: U+0020->1, U+0041->2, U+00C5->3, U+1F600->4

post format 2.0: standard Mac indices for .notdef(0) space(3) A(36) Aring(99), and one
custom Pascal-string name `A.ss01` (index 258).

Malformed variants (same font, one defect each), written next to tiny.ttf:
  bad-trunc.ttf   cut after the 'maxp' table data: 'post' lies past the end (table skipped)
  bad-head.ttf    'head' table offset points past the end of the file (font rejected)
  bad-loca.ttf    loca[3] and loca[4] swapped: glyph 3 out of order and glyph 4 overlapping
                  glyph 2's extended range (both rejected, glyphs 0-2 kept)
  bad-cycle.ttf   composite glyph 3's second component refers to glyph 3 (cycle: rejected)
"""
import os
import struct
import sys

UPEM = 1000
NUM_GLYPHS = 5

# Glyph outlines: list of contours, each a list of (x, y, on_curve).
NOTDEF = [[(50, 0, True), (450, 0, True), (450, 700, True), (50, 700, True)]]
GLYPH_A = [[(0, 0, True), (300, 700, False), (600, 0, True)]]
SS01 = [[(100, 100, True), (500, 100, True), (500, 500, True), (100, 500, True)],
        [(200, 200, True), (200, 400, True), (400, 400, True), (400, 200, True)]]

ADVANCES = [500, 250, 600]           # numberOfHMetrics = 3
LSBS = [50, 0, 0, 0, 100]            # left side bearings of all 5 glyphs


def bbox(contours):
    xs = [p[0] for c in contours for p in c]
    ys = [p[1] for c in contours for p in c]
    return min(xs), min(ys), max(xs), max(ys)


def simple_glyph(contours):
    """Encode a simple glyph (glyf table, numberOfContours >= 0), compressing flags."""
    xmin, ymin, xmax, ymax = bbox(contours)
    out = struct.pack(">hhhhh", len(contours), xmin, ymin, xmax, ymax)
    end = -1
    for c in contours:
        end += len(c)
        out += struct.pack(">H", end)
    out += struct.pack(">H", 0)                 # instructionLength
    pts = [p for c in contours for p in c]
    flags, xs, ys = [], b"", b""
    px = py = 0
    for (x, y, on) in pts:
        f = 1 if on else 0
        dx, dy = x - px, y - py
        px, py = x, y
        if dx == 0:
            f |= 0x10
        elif -255 <= dx <= 255:
            f |= 0x02 | (0x10 if dx > 0 else 0)
            xs += bytes([abs(dx)])
        else:
            xs += struct.pack(">h", dx)
        if dy == 0:
            f |= 0x20
        elif -255 <= dy <= 255:
            f |= 0x04 | (0x20 if dy > 0 else 0)
            ys += bytes([abs(dy)])
        else:
            ys += struct.pack(">h", dy)
        flags.append(f)
    # compress runs of equal flags with the REPEAT bit (0x08)
    fb = b""
    i = 0
    while i < len(flags):
        j = i
        while j + 1 < len(flags) and flags[j + 1] == flags[i] and j - i < 255:
            j += 1
        if j > i:
            fb += bytes([flags[i] | 0x08, j - i])
        else:
            fb += bytes([flags[i]])
        i = j + 1
    return out + fb + xs + ys


def composite_glyph(second_gid):
    """Aring: A at (0,0) with word args; `second_gid` at (100,50), byte args, scale 0.5."""
    a = bbox(GLYPH_A)
    s = bbox([[(100 + x // 2, 50 + y // 2, o) for (x, y, o) in c] for c in SS01])
    out = struct.pack(">hhhhh", -1, min(a[0], s[0]), min(a[1], s[1]),
                      max(a[2], s[2]), max(a[3], s[3]))
    # ARG_1_AND_2_ARE_WORDS | ARGS_ARE_XY_VALUES | MORE_COMPONENTS
    out += struct.pack(">HHhh", 0x0001 | 0x0002 | 0x0020, 2, 0, 0)
    # ARGS_ARE_XY_VALUES | WE_HAVE_A_SCALE, byte args, F2Dot14 0.5 = 0x2000
    out += struct.pack(">HHbbH", 0x0002 | 0x0008, second_gid, 100, 50, 0x2000)
    return out


def pad2(b):
    return b + b"\0" * (len(b) % 2)


def build_glyf(cycle=False):
    glyphs = [simple_glyph(NOTDEF), b"", simple_glyph(GLYPH_A),
              composite_glyph(3 if cycle else 4), simple_glyph(SS01)]
    glyf, offs = b"", []
    for g in glyphs:
        offs.append(len(glyf))
        glyf += pad2(g)
    offs.append(len(glyf))
    return glyf, offs


def cmap_table():
    # format 0, (1,0)
    arr = [0] * 256
    arr[0x20], arr[0x41], arr[0x81] = 1, 2, 3
    f0 = struct.pack(">HHH", 0, 262, 0) + bytes(arr)
    # format 6, (3,0)
    f6 = struct.pack(">HHHHHHH", 6, 14, 0, 0xF041, 2, 2, 4)
    # format 4, (3,1)
    seg = 4
    ends = [0x20, 0x41, 0xC5, 0xFFFF]
    starts = [0x20, 0x41, 0xC5, 0xFFFF]
    deltas = [(1 - 0x20) & 0xFFFF, (2 - 0x41) & 0xFFFF, 0, 1]
    ros = [0, 0, 4, 0]                 # idRangeOffset[2] -> glyphIdArray[0]
    gia = [3]
    body = struct.pack(">HHHH", seg * 2, 4, 1, 4)    # segCountX2 searchRange entrySel rangeShift
    body += struct.pack(">4H", *ends) + struct.pack(">H", 0)
    body += struct.pack(">4H", *starts) + struct.pack(">4H", *deltas)
    body += struct.pack(">4H", *ros) + struct.pack(">1H", *gia)
    f4 = struct.pack(">HHH", 4, 6 + len(body), 0) + body
    # format 12, (3,10)
    groups = [(0x20, 0x20, 1), (0x41, 0x41, 2), (0xC5, 0xC5, 3), (0x1F600, 0x1F600, 4)]
    gb = b"".join(struct.pack(">III", *g) for g in groups)
    f12 = struct.pack(">HHIII", 12, 0, 16 + len(gb), 0, len(groups)) + gb
    subs = [((1, 0), f0), ((3, 0), f6), ((3, 1), f4), ((3, 10), f12)]
    head = struct.pack(">HH", 0, len(subs))
    off = 4 + 8 * len(subs)
    recs, data = b"", b""
    for (p, e), s in subs:
        recs += struct.pack(">HHI", p, e, off + len(data))
        data += pad2(s)
    return head + recs + data


def head_table(loc_format=0):
    a, n = bbox(GLYPH_A), bbox(NOTDEF)
    return struct.pack(">IIIIHHqqhhhhHHhhh",
                       0x00010000, 0x00010000, 0, 0x5F0F3CF5, 0x000B, UPEM, 0, 0,
                       min(a[0], n[0]), min(a[1], n[1]), max(a[2], n[2]), max(a[3], n[3]),
                       0, 8, 2, loc_format, 0)


def hhea_table():
    return struct.pack(">IhhhHhhhhhhhhhhhH", 0x00010000, 800, -200, 0, 600, 0, 0, 600,
                       1, 0, 0, 0, 0, 0, 0, 0, len(ADVANCES))


def hmtx_table():
    out = b""
    for i, adv in enumerate(ADVANCES):
        out += struct.pack(">Hh", adv, LSBS[i])
    for lsb in LSBS[len(ADVANCES):]:
        out += struct.pack(">h", lsb)
    return out


def maxp_table():
    return struct.pack(">IH", 0x00010000, NUM_GLYPHS) + struct.pack(">13H", *([0] * 13))


def post_table():
    out = struct.pack(">IIhhIIIII", 0x00020000, 0, -100, 50, 0, 0, 0, 0, 0)
    out += struct.pack(">H", NUM_GLYPHS)
    out += struct.pack(">5H", 0, 3, 36, 99, 258)
    out += bytes([6]) + b"A.ss01"
    return out


def checksum(b):
    b = b + b"\0" * ((4 - len(b) % 4) % 4)
    return sum(struct.unpack(">%dI" % (len(b) // 4), b)) & 0xFFFFFFFF


def build(loca_swap=False, cycle=False):
    glyf, offs = build_glyf(cycle)
    if loca_swap:
        offs[3], offs[4] = offs[4], offs[3]
    loca = b"".join(struct.pack(">H", o // 2) for o in offs)
    tables = {
        b"cmap": cmap_table(), b"glyf": glyf, b"head": head_table(), b"hhea": hhea_table(),
        b"hmtx": hmtx_table(), b"loca": loca, b"maxp": maxp_table(), b"post": post_table(),
    }
    tags = sorted(tables)
    n = len(tags)
    off = 12 + 16 * n
    dir_ = struct.pack(">IHHHH", 0x00010000, n, 128, 3, n * 16 - 128)
    data = b""
    for t in tags:
        tb = tables[t]
        dir_ += t + struct.pack(">III", checksum(tb), off + len(data), len(tb))
        data += tb + b"\0" * ((4 - len(tb) % 4) % 4)
    font = bytearray(dir_ + data)
    # head.checkSumAdjustment = 0xB1B0AFBA - checksum(whole font)
    hoff = off + sum(len(tables[t]) + (4 - len(tables[t]) % 4) % 4
                     for t in tags[:tags.index(b"head")])
    struct.pack_into(">I", font, hoff + 8, (0xB1B0AFBA - checksum(bytes(font))) & 0xFFFFFFFF)
    return bytes(font), {t: o for t, o in table_offsets(bytes(font)).items()}


def table_offsets(font):
    n = struct.unpack_from(">H", font, 4)[0]
    res = {}
    for k in range(n):
        tag, _, o, ln = struct.unpack_from(">4sIII", font, 12 + 16 * k)
        res[tag] = (o, ln, 12 + 16 * k)
    return res


def fixtures():
    tiny, offs = build()
    out = {"tiny.ttf": tiny}
    o, ln, _ = offs[b"maxp"]
    out["bad-trunc.ttf"] = tiny[:o + ln]
    bad = bytearray(tiny)
    struct.pack_into(">I", bad, offs[b"head"][2] + 8, len(tiny) + 16)
    out["bad-head.ttf"] = bytes(bad)
    out["bad-loca.ttf"] = build(loca_swap=True)[0]
    out["bad-cycle.ttf"] = build(cycle=True)[0]
    return out


def main(argv):
    here = os.path.dirname(os.path.abspath(__file__))
    fx = fixtures()
    if "--hex" in argv:
        print(fx["tiny.ttf"].hex())
        for name in sorted(fx):
            print(name, len(fx[name]))
        offs = table_offsets(fx["tiny.ttf"])
        for t in sorted(offs):
            print(t.decode(), "offset", offs[t][0], "length", offs[t][1], "record", offs[t][2])
        return 0
    if "--check" in argv:
        bad = [n for n in sorted(fx)
               if not os.path.exists(os.path.join(here, n))
               or open(os.path.join(here, n), "rb").read() != fx[n]]
        if bad:
            print("gen_truetype: out of date:", " ".join(bad))
            return 1
        print("gen_truetype: %d fixtures up to date" % len(fx))
        return 0
    outdir = argv[1] if len(argv) > 1 else here
    for name, b in sorted(fx.items()):
        with open(os.path.join(outdir, name), "wb") as f:
            f.write(b)
        print(name, len(b))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
