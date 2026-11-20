#!/usr/bin/env python3
"""Deterministic generator of the tiny CFF fixtures (task 6.2), standard library only.

Writes, next to this script:

* ``tiny.cff`` -- a name-keyed CFF (``/FontFile3 /Subtype /Type1C``) "SafePdfTinyCFF":
  7 glyphs ``.notdef space A B C foo bad`` (charset format 0, two custom strings), a custom
  encoding (format 0 + one supplement), a Private DICT with ``defaultWidthX 500``,
  ``nominalWidthX 600``, a real ``BlueScale`` and one local subroutine, one global subroutine.
  Widths: .notdef 500 (default), space 250, A 650 (stems + hintmask), B 700 (width pushed by a
  local subr, path by a global subr), C 610 (endchar accent form, base 65 accent 66),
  foo 600.5 (16.16 operand, ``div``), bad rejected (reserved operator 0).
  Codes: 32 space, 65 A, 66 B, 67 C, 102 foo, 120 bad, supplement 97 -> A.
  FontMatrix ``[1E-3 0 0 0.001 0 0]`` (two real-number forms).

* ``tiny-cid.cff`` -- a CID-keyed CFF (``/CIDFontType0C``) "SafePdfTinyCID", ROS
  Adobe-Identity-0, 4 glyphs with CIDs 0 1 100 101 (charset format 2), two Font DICTs
  (FDSelect format 3: GIDs 0-1 -> FD 0, 2-3 -> FD 1). Top FontMatrix ``[1 0 0 1 0 0]``,
  FD 0 ``[0.001 ...]`` (default 1000, nominal 0), FD 1 ``[0.0005 ...]`` (default 2000,
  nominal 1000, one local subr ending in ``endchar``).
  Widths: GID 0 1000, GID 1 500, GID 2 1000, GID 3 1200 (endchar inside the local subr);
  text-space advances 1, 0.5, 0.5, 0.6.

Run: ``python3 -I Tests/fonts/gen_cff.py`` (prints the files' sizes and hex).
"""

import os
import struct

HERE = os.path.dirname(os.path.abspath(__file__))


def index(items):
    """An INDEX (TN #5176 section 5) with offSize 2 (or empty)."""
    if not items:
        return b"\x00\x00"
    out = struct.pack(">HB", len(items), 2)
    off = 1
    offs = [off]
    for it in items:
        off += len(it)
        offs.append(off)
    out += b"".join(struct.pack(">H", o) for o in offs)
    return out + b"".join(items)


def num(v):
    """A DICT integer operand; large values use the fixed 5-byte form (stable sizes)."""
    if -107 <= v <= 107:
        return bytes([v + 139])
    return b"\x1d" + struct.pack(">i", v)


def num5(v):
    """A DICT integer operand in the 5-byte form."""
    return b"\x1d" + struct.pack(">i", v)


def real(nibbles):
    """A DICT real operand from a nibble string such as '1c3' (end nibble f appended)."""
    s = nibbles + "f"
    if len(s) % 2:
        s += "f"
    return b"\x1e" + bytes.fromhex(s)


def op(*codes):
    return bytes(codes)


def cs_num(v):
    """A Type 2 charstring integer operand."""
    if -107 <= v <= 107:
        return bytes([v + 139])
    if 108 <= v <= 1131:
        v -= 108
        return bytes([(v >> 8) + 247, v & 255])
    if -1131 <= v <= -108:
        v = -v - 108
        return bytes([(v >> 8) + 251, v & 255])
    return b"\x1c" + struct.pack(">h", v)


def cs(*parts):
    out = b""
    for p in parts:
        out += cs_num(p) if isinstance(p, int) else p
    return out


ENDCHAR = b"\x0e"
RMOVETO = b"\x15"
HMOVETO = b"\x16"
RLINETO = b"\x05"
HSTEM = b"\x01"
HINTMASK = b"\x13"
CALLSUBR = b"\x0a"
CALLGSUBR = b"\x1d"
RETURN = b"\x0b"
DIV = b"\x0c\x0c"


def build(name, strings, top_fn, gsubrs, tail_fn):
    """Lay out header, Name, Top DICT, String, Global Subr INDEXes, then the tail blocks.
    `top_fn(offsets)` builds the Top DICT from the offsets of the tail blocks;
    `tail_fn()` returns the list of tail blocks. Top DICT size is offset-independent."""
    header = bytes([1, 0, 4, 2])
    tail = tail_fn()
    dummy = top_fn([0] * len(tail))
    pre = header + index([name]) + index([dummy]) + index(strings) + index(gsubrs)
    offs = []
    pos = len(pre)
    for blk in tail:
        offs.append(pos)
        pos += len(blk)
    top = top_fn(offs)
    assert len(top) == len(dummy)
    return header + index([name]) + index([top]) + index(strings) + index(gsubrs) + b"".join(tail)


def tiny():
    strings = [b"foo", b"bad"]
    # global subr 0: path, return
    gsubrs = [cs(0, 100, RLINETO, RETURN)]
    # local subr 0: push the width operand and dx dy, return
    lsubrs = [cs(100, 10, 20, RETURN)]
    charstrings = [
        cs(0, 0, RMOVETO, ENDCHAR),                              # .notdef: default 500
        cs(-350, ENDCHAR),                                       # space: 600-350 = 250
        cs(50, 10, 20, 30, 40, HSTEM, 1, 2, HINTMASK) + b"\xc0"  # A: width 50 -> 650,
        + cs(5, 5, RMOVETO, ENDCHAR),                            #   2 stems + 1 vstem: 1 byte
        cs(-107, CALLSUBR, RMOVETO, -107, CALLGSUBR, ENDCHAR),   # B: 600+100 = 700
        cs(10, 0, 0, 65, 66, ENDCHAR),                           # C: 610, accent form
        b"\xff\x00\x00\x80\x00" + cs(50, 2) + DIV + HMOVETO + ENDCHAR,  # foo: 600.5
        cs(1, 2) + b"\x00" + ENDCHAR,                            # bad: reserved operator 0
    ]
    # charset format 0: space A B C foo bad
    charset = bytes([0]) + b"".join(struct.pack(">H", s) for s in [1, 34, 35, 36, 391, 392])
    # encoding format 0 with supplement: 6 codes for GIDs 1..6, supplement 97 -> SID 34 (A)
    encoding = bytes([0x80, 6, 32, 65, 66, 67, 102, 120, 1, 97]) + struct.pack(">H", 34)
    priv_core = num(500) + op(20) + num(600) + op(21) + real("0a039625") + op(12, 9)
    priv_len = len(priv_core) + 6  # + Subrs operand (5 bytes) + operator
    private = priv_core + num5(priv_len) + op(19)
    assert len(private) == priv_len
    subrs = index(lsubrs)
    cstrings = index(charstrings)

    def top_fn(o):
        return (num(391) + op(0)  # version: a string SID (ignored)
                + real("1c3") + num(0) + num(0) + real("a001") + num(0) + num(0) + op(12, 7)
                + num(-10) + num(-200) + num(1000) + num(900) + op(5)
                + num5(o[0]) + op(15) + num5(o[1]) + op(16) + num5(o[2]) + op(17)
                + num5(len(private)) + num5(o[3]) + op(18))

    return build(b"SafePdfTinyCFF", strings, top_fn, gsubrs,
                 lambda: [charset, encoding, cstrings, private + subrs])


def tiny_cid():
    strings = [b"Adobe", b"Identity"]
    charstrings = [
        cs(0, 0, RMOVETO, ENDCHAR),        # GID 0, FD 0: default 1000
        cs(500, ENDCHAR),                  # GID 1, FD 0: 0 + 500
        cs(0, 0, 0, RMOVETO, ENDCHAR),     # GID 2, FD 1: 1000 + 0
        cs(-107, CALLSUBR),                # GID 3, FD 1: subr does 200 endchar -> 1200
    ]
    lsubrs1 = [cs(200, ENDCHAR)]
    # charset format 2: ranges (1, nLeft 0), (100, nLeft 1)
    charset = bytes([2]) + struct.pack(">HH", 1, 0) + struct.pack(">HH", 100, 1)
    # FDSelect format 3: (0 -> 0), (2 -> 1), sentinel 4
    fdselect = bytes([3]) + struct.pack(">H", 2) + struct.pack(">HB", 0, 0) \
        + struct.pack(">HB", 2, 1) + struct.pack(">H", 4)
    priv0 = num(1000) + op(20) + num(0) + op(21)
    priv1_core = num(2000) + op(20) + num(1000) + op(21)
    priv1_len = len(priv1_core) + 6
    priv1 = priv1_core + num5(priv1_len) + op(19)
    subrs1 = index(lsubrs1)
    cstrings = index(charstrings)

    def fd_dicts(p0, p1):
        fd0 = real("a001") + num(0) + num(0) + real("a001") + num(0) + num(0) + op(12, 7) \
            + num5(len(priv0)) + num5(p0) + op(18)
        fd1 = real("a0005") + num(0) + num(0) + real("a0005") + num(0) + num(0) + op(12, 7) \
            + num5(len(priv1)) + num5(p1) + op(18)
        return index([fd0, fd1])

    def tail():
        # FDArray size does not depend on the Private offsets (5-byte ints); fix up below.
        return [charset, fdselect, cstrings, fd_dicts(0, 0), priv0, priv1 + subrs1]

    def top_fn(o):
        return (num(391) + num(392) + num(0) + op(12, 30)
                + num(1) + num(0) + num(0) + num(1) + num(0) + num(0) + op(12, 7)
                + num5(o[0]) + op(15) + num5(o[2]) + op(17)
                + num5(o[3]) + op(12, 36) + num5(o[1]) + op(12, 37))

    data = build(b"SafePdfTinyCID", strings, top_fn, [], tail)
    # Patch the FDArray with the real Private offsets.
    blocks = tail()
    start = len(data) - sum(len(b) for b in blocks)
    pos = start
    offs = []
    for blk in blocks:
        offs.append(pos)
        pos += len(blk)
    fda = fd_dicts(offs[4], offs[5])
    assert len(fda) == len(blocks[3])
    return data[:offs[3]] + fda + data[offs[3] + len(fda):]


def main():
    for fname, data in (("tiny.cff", tiny()), ("tiny-cid.cff", tiny_cid())):
        with open(os.path.join(HERE, fname), "wb") as f:
            f.write(data)
        print(fname, len(data))
        print(data.hex())


if __name__ == "__main__":
    main()
