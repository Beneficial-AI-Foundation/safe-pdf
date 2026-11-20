#!/usr/bin/env python3
"""Generate the glyph-name table `aglData` of `SafePdf/Core/Font/Encoding.lean` (task 6.7b).

Standard library only; run with
  python3 -I Tests/fonts/gen_agl.py GLYPHLIST TEXGLYPHLIST > table.txt
and paste the output over the `aglData` literal.

Inputs (download into a fresh directory, check the SHA-256):
  GLYPHLIST     Adobe Glyph List 2.0, glyphlist.txt,
                https://raw.githubusercontent.com/adobe-type-tools/agl-aglfn/4036a9c/glyphlist.txt
                sha256 a3b2f61ced9f3644cc0d4ecde5c59df34ca286c689d9484a43a710a81c466789
  TEXGLYPHLIST  lcdf-typetools texglyphlist.txt 2.95 (extensions for TeX fonts),
                https://raw.githubusercontent.com/kohler/lcdf-typetools/91137fb4ceb4e0c08ba0b1c33b0d86c781090821/texglyphlist.txt
                sha256 4b11bf2dcd65b004ee2023c5392339aaf89429bef0d3ace13b7b098d108cd991

Output: one `name;HEX[ HEX…]` line per glyph name, sorted by code point order of the name
(Lean's `String` order), every AGL entry, then (merged) every texglyphlist name the AGL does
not define, with its FIRST alternative (the field before the first comma); entries whose value
is not a sequence of Unicode scalar values (texglyphlist's surrogate placeholders such as
`altselector;D802`) are dropped. Each line is a Lean string-gap line.
"""
import hashlib
import sys

SHA = {
    "agl": "a3b2f61ced9f3644cc0d4ecde5c59df34ca286c689d9484a43a710a81c466789",
    "tex": "4b11bf2dcd65b004ee2023c5392339aaf89429bef0d3ace13b7b098d108cd991",
}


def read(path, kind):
    data = open(path, "rb").read()
    h = hashlib.sha256(data).hexdigest()
    if h != SHA[kind]:
        sys.exit("%s: sha256 %s, expected %s" % (path, h, SHA[kind]))
    out = []
    for line in data.decode("ascii").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        name, val = line.split(";")
        out.append((name, val.split(",")[0]))
    return out


def scalar_seq(val):
    cps = [int(x, 16) for x in val.split()]
    return all(c <= 0x10FFFF and not (0xD800 <= c <= 0xDFFF) for c in cps) and cps


def main():
    agl = read(sys.argv[1], "agl")
    tex = read(sys.argv[2], "tex")
    table = {}
    for name, val in agl:
        if name in table:
            sys.exit("duplicate AGL name " + name)
        table[name] = val
    for name, val in tex:
        if name not in table and scalar_seq(val):
            table[name] = val
    for name in sorted(table):
        print('  %s;%s\\n\\' % (name, table[name]))


if __name__ == "__main__":
    main()
