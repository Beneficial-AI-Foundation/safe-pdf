#!/usr/bin/env python3
"""Generate the C4 fixtures of task 12.7h: RC4-40 encrypted files with an object stream.

    python3 -I scripts/gen-enc-objstm.py            # print both files as Lean byte literals
    python3 -I scripts/gen-enc-objstm.py --pdf DIR  # also write them as DIR/<name>.pdf

Stdlib only (hashlib for MD5); RC4 is a small pure-Python implementation written here,
independent of `SafePdf.Core.Crypt`. Deterministic: no timestamps, no randomness.

Standard security handler, ISO 32000-2 §7.6.4: /V 1 /R 2 (RC4, 40-bit key), empty user
password, owner password "owner", /P -4, /ID = two copies of the bytes 20..2F.
Algorithm 2 (file key), 3 (/O), 4 (/U, R2), 1 (object keys: MD5(key ‖ num[3] ‖ gen[2]),
first n + 5 = 10 bytes).

encObjStm (`encObjStmBytes` in `SafePdf/Spec/RepairAgreeEncComp.lean`):
  1 catalog, classic: /Type /Catalog /Pages 2 0 R /Lang (en-US)      (string encrypted)
  2 page tree node, in object stream 6 at index 0                     (not encrypted itself)
  3 page, in object stream 6 at index 1, with /Kind (member)          (not encrypted itself)
  4 content stream, classic, direct /Length                           (data encrypted)
  5 the encryption dictionary, classic                                (never encrypted)
  6 the object stream, classic, unfiltered                            (data encrypted as a whole)
  7 the cross-reference stream (/W [1 2 2], no filter, never encrypted), the only trailer:
    /Root 1 0 R /Encrypt 5 0 R /ID [...]; no `trailer` keyword.
  Strictly: 2 → compressed 6 0, 3 → compressed 6 1, every other object in use, 0 free.

encOrphan (`encOrphanBytes`): the same objects, but the cross-reference stream marks 2 and 3
free (an orphan object stream). Strictly 2 and 3 are `null`; repair rule R6 (after
`withCrypt`) gives them back, so the repair path differs: H7 of `HypEnc` is necessary.
"""
import hashlib
import os
import sys

PAD = bytes([
    0x28, 0xBF, 0x4E, 0x5E, 0x4E, 0x75, 0x8A, 0x41, 0x64, 0x00, 0x4E, 0x56, 0xFF, 0xFA, 0x01, 0x08,
    0x2E, 0x2E, 0x00, 0xB6, 0xD0, 0x68, 0x3E, 0x80, 0x2F, 0x0C, 0xA9, 0xFE, 0x64, 0x53, 0x69, 0x7A])

ID0 = bytes(range(0x20, 0x30))
P = -4
CONTENT = b"BT /F1 24 Tf 72 700 Td (Hello) Tj ET"


def rc4(key, data):
    s = list(range(256))
    j = 0
    for i in range(256):
        j = (j + s[i] + key[i % len(key)]) % 256
        s[i], s[j] = s[j], s[i]
    out = bytearray()
    i = j = 0
    for b in data:
        i = (i + 1) % 256
        j = (j + s[i]) % 256
        s[i], s[j] = s[j], s[i]
        out.append(b ^ s[(s[i] + s[j]) % 256])
    return bytes(out)


def pad(pw):
    return (pw + PAD)[:32]


def owner_entry():
    key = hashlib.md5(pad(b"owner")).digest()[:5]
    return rc4(key, pad(b""))


def file_key(o):
    h = hashlib.md5()
    h.update(pad(b""))
    h.update(o)
    h.update((P & 0xFFFFFFFF).to_bytes(4, "little"))
    h.update(ID0)
    return h.digest()[:5]


def obj_key(key, num, gen):
    k = hashlib.md5(key + num.to_bytes(3, "little") + gen.to_bytes(2, "little")).digest()
    return k[:len(key) + 5]


def hexs(b):
    return b"<" + b.hex().upper().encode() + b">"


def build(orphan):
    o = owner_entry()
    key = file_key(o)
    u = rc4(key, PAD)
    enc = lambda num, data: rc4(obj_key(key, num, 0), data)

    m2 = b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>"
    m3 = (b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R "
          b"/Kind (member) >>")
    hdr = b"2 0 3 %d " % (len(m2) + 1)
    osdata = hdr + m2 + b" " + m3
    osenc = enc(6, osdata)
    content = enc(4, CONTENT)

    objs = {
        1: b"<< /Type /Catalog /Pages 2 0 R /Lang " + hexs(enc(1, b"en-US")) + b" >>",
        4: b"<< /Length %d >>\nstream\n" % len(content) + content + b"\nendstream",
        5: (b"<< /Filter /Standard /V 1 /R 2 /Length 40 /P %d /O " % P) + hexs(o) +
           b" /U " + hexs(u) + b" >>",
        6: (b"<< /Type /ObjStm /N 2 /First %d /Length %d >>\nstream\n" % (len(hdr), len(osenc)))
           + osenc + b"\nendstream",
    }
    out = bytearray(b"%PDF-1.5\n%\xe2\xe3\xcf\xd3\n")
    offs = {}
    for n in (1, 4, 5, 6):
        offs[n] = len(out)
        out += b"%d 0 obj\n" % n + objs[n] + b"\nendobj\n"
    offs[7] = len(out)

    def row(t, a, b):
        return bytes([t]) + a.to_bytes(2, "big") + b.to_bytes(2, "big")

    rows = row(0, 0, 65535) + row(1, offs[1], 0)
    rows += row(0, 0, 1) * 2 if orphan else row(2, 6, 0) + row(2, 6, 1)
    rows += row(1, offs[4], 0) + row(1, offs[5], 0) + row(1, offs[6], 0) + row(1, offs[7], 0)
    xd = (b"<< /Type /XRef /Size 8 /W [1 2 2] /Root 1 0 R /Encrypt 5 0 R /ID [" +
          hexs(ID0) + b" " + hexs(ID0) + b"] /Length %d >>\nstream\n" % len(rows))
    out += b"7 0 obj\n" + xd + rows + b"\nendstream\nendobj\n"
    out += b"startxref\n%d\n%%%%EOF\n" % offs[7]
    return bytes(out)


def lean_literal(b):
    nums = [str(x) for x in b]
    lines, cur = [], ""
    for s in nums:
        piece = s + ", "
        if len(cur) + len(piece) > 94:
            lines.append(cur.rstrip())
            cur = ""
        cur += piece
    lines.append(cur.rstrip().rstrip(","))
    return "⟨#[\n" + "\n  ".join(lines) + "]⟩"


def main():
    files = {"encObjStm": build(False), "encOrphan": build(True)}
    outdir = None
    if len(sys.argv) == 3 and sys.argv[1] == "--pdf":
        outdir = sys.argv[2]
    for name, b in files.items():
        print("-- %s: %d bytes, SHA-256 %s" % (name, len(b), hashlib.sha256(b).hexdigest()))
        print(lean_literal(b))
        if outdir:
            with open(os.path.join(outdir, name + ".pdf"), "wb") as f:
                f.write(b)


if __name__ == "__main__":
    main()
