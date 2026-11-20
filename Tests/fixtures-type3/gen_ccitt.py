"""Generate the CCITT fax fixture of task 7.8 (Tests/RasterType3Fax.lean).

    python3 -I Tests/fixtures-type3/gen_ccitt.py [OUT]    # default Tests/fixtures-type3/ccitt.pdf

The construct found in arXiv 0704.0001 (dvips + Ghostscript 9.22): a Type 3 font whose glyph
procedures are `d1` + an inline stencil mask `BI /IM true ... /F /CCF /DP << /K -1 /Columns w >>
ID ... EI`. Without a CCITT decoder each glyph was drawn as a solid box.

One 300 x 220 pt page, uncompressed. Type 3 font F1 (FontMatrix 0.01, one glyph unit = 1 pt at
100 pt), four glyphs, each an inline CCITT image mask of a different flavour:

  code 0x30 '0'  ring 40 x 40, Group 4 (/K -1), /D [1 0] (fax-white pixels paint, the
                 Ghostscript convention), filters [/AHx /CCF] with /DP [null << ... >>]
  code 0x31 '1'  diagonal bar 36 x 40, Group 4, default /Decode (fax-black paints)
  code 0x32 '2'  3-px checkerboard 30 x 30, Group 3 1-D (/K 0), /EncodedByteAlign true,
                 /BlackIs1 true, /D [1 0], filters [/AHx /CCF]
  code 0x33 '3'  letter E 32 x 40, Group 3 mixed (/K 2, 2-D rows tagged), /EndOfLine true,
                 filters [/AHx /CCF]

Text: "0123" at 100 pt (baseline y 150) and at 50 pt (baseline y 95, downscaled glyphs).
Image XObject /Im1 (DeviceGray, 1 bit, 160 x 40, Group 4 with runs > 64 px so make-up codes
occur, filters [/FlateDecode /CCITTFaxDecode], /DecodeParms [null << /K -1 /Columns 7 0 R >>]
with an indirect /Columns) drawn at 20 10 240 x 60.

The encoder follows ITU-T T.4/T.6 (code tables of T.4 Tables 2 and 3, mode codes of Table 4).
Deterministic; stdlib only.
"""
import os
import sys
import zlib

WHITE = {0: '00110101', 1: '000111', 2: '0111', 3: '1000', 4: '1011', 5: '1100', 6: '1110',
         7: '1111', 8: '10011', 9: '10100', 10: '00111', 11: '01000', 12: '001000',
         13: '000011', 14: '110100', 15: '110101', 16: '101010', 17: '101011', 18: '0100111',
         19: '0001100', 20: '0001000', 21: '0010111', 22: '0000011', 23: '0000100',
         24: '0101000', 25: '0101011', 26: '0010011', 27: '0100100', 28: '0011000',
         29: '00000010', 30: '00000011', 31: '00011010', 32: '00011011', 33: '00010010',
         34: '00010011', 35: '00010100', 36: '00010101', 37: '00010110', 38: '00010111',
         39: '00101000', 40: '00101001', 41: '00101010', 42: '00101011', 43: '00101100',
         44: '00101101', 45: '00000100', 46: '00000101', 47: '00001010', 48: '00001011',
         49: '01010010', 50: '01010011', 51: '01010100', 52: '01010101', 53: '00100100',
         54: '00100101', 55: '01011000', 56: '01011001', 57: '01011010', 58: '01011011',
         59: '01001010', 60: '01001011', 61: '00110010', 62: '00110011', 63: '00110100',
         64: '11011', 128: '10010', 192: '010111', 256: '0110111', 320: '00110110',
         384: '00110111', 448: '01100100', 512: '01100101', 576: '01101000',
         640: '01100111', 704: '011001100', 768: '011001101', 832: '011010010',
         896: '011010011', 960: '011010100', 1024: '011010101', 1088: '011010110',
         1152: '011010111', 1216: '011011000', 1280: '011011001', 1344: '011011010',
         1408: '011011011', 1472: '010011000', 1536: '010011001', 1600: '010011010',
         1664: '011000', 1728: '010011011'}
BLACK = {0: '0000110111', 1: '010', 2: '11', 3: '10', 4: '011', 5: '0011', 6: '0010',
         7: '00011', 8: '000101', 9: '000100', 10: '0000100', 11: '0000101', 12: '0000111',
         13: '00000100', 14: '00000111', 15: '000011000', 16: '0000010111',
         17: '0000011000', 18: '0000001000', 19: '00001100111', 20: '00001101000',
         21: '00001101100', 22: '00000110111', 23: '00000101000', 24: '00000010111',
         25: '00000011000', 26: '000011001010', 27: '000011001011', 28: '000011001100',
         29: '000011001101', 30: '000001101000', 31: '000001101001', 32: '000001101010',
         33: '000001101011', 34: '000011010010', 35: '000011010011', 36: '000011010100',
         37: '000011010101', 38: '000011010110', 39: '000011010111', 40: '000001101100',
         41: '000001101101', 42: '000011011010', 43: '000011011011', 44: '000001010100',
         45: '000001010101', 46: '000001010110', 47: '000001010111', 48: '000001100100',
         49: '000001100101', 50: '000001010010', 51: '000001010011', 52: '000000100100',
         53: '000000110111', 54: '000000111000', 55: '000000100111', 56: '000000101000',
         57: '000001011000', 58: '000001011001', 59: '000000101011', 60: '000000101100',
         61: '000001011010', 62: '000001100110', 63: '000001100111', 64: '0000001111',
         128: '000011001000', 192: '000011001001', 256: '000001011011', 320: '000000110011',
         384: '000000110100', 448: '000000110101', 512: '0000001101100',
         576: '0000001101101', 640: '0000001001010', 704: '0000001001011',
         768: '0000001001100', 832: '0000001001101', 896: '0000001110010',
         960: '0000001110011', 1024: '0000001110100', 1088: '0000001110101',
         1152: '0000001110110', 1216: '0000001110111', 1280: '0000001010010',
         1344: '0000001010011', 1408: '0000001010100', 1472: '0000001010101',
         1536: '0000001011010', 1600: '0000001011011', 1664: '0000001100100',
         1728: '0000001100101'}
EOL = '000000000001'
P, H = '0001', '001'
V = {0: '1', 1: '011', 2: '000011', 3: '0000011', -1: '010', -2: '000010', -3: '0000010'}


def run_code(n, black):
    t = BLACK if black else WHITE
    out = ''
    while n >= 1728:
        out += t[1728]
        n -= 1728
    if n >= 64:
        out += t[n // 64 * 64]
        n %= 64
    return out + t[n]


def changes(row):
    """Changing elements (positions whose colour differs from the previous; -1 is white)."""
    prev, out = 0, []
    for i, v in enumerate(row):
        if v != prev:
            out.append(i)
        prev = v
    return out


def color_at(row, i):
    return row[i] if 0 <= i < len(row) else 0


def encode_1d(row):
    w, bits, x, black = len(row), '', 0, 0
    while x < w:
        e = x
        while e < w and row[e] == black:
            e += 1
        bits += run_code(e - x, black)
        x, black = e, 1 - black
    if black == 1:  # a row ending in black: a white run of 0 is not needed (row is complete)
        pass
    return bits


def encode_2d(row, ref):
    """T.4 §4.2.1.3 two-dimensional coding of `row` against `ref` (lists of 0/1, 1 = black)."""
    w = len(row)
    cr, rr = changes(row), changes(ref)
    a0, color, bits = -1, 0, ''

    def nxt(lst, after):
        for p in lst:
            if p > after:
                return p
        return w

    while a0 < w:
        start = a0 if a0 >= 0 else -1
        a1 = nxt(cr, start) if a0 >= 0 else (cr[0] if cr else w)
        # b1: first changing element on ref right of a0 with colour opposite to a0's colour
        b1 = w
        for p in rr:
            if (p > a0 or (a0 < 0 and p >= 0)) and color_at(ref, p) != color:
                b1 = p
                break
        b2 = nxt(rr, b1)
        if b2 < a1:
            bits += P
            a0 = b2
        elif abs(a1 - b1) <= 3:
            bits += V[a1 - b1]
            a0, color = a1, 1 - color
        else:
            a2 = nxt(cr, a1)
            bits += H + run_code(a1 - max(a0, 0), color) + run_code(a2 - a1, 1 - color)
            a0 = a2
    return bits


def pack(bits):
    bits += '0' * (-len(bits) % 8)
    return bytes(int(bits[i:i + 8], 2) for i in range(0, len(bits), 8))


def g4(rows):
    ref, bits = [0] * len(rows[0]), ''
    for r in rows:
        bits += encode_2d(r, ref)
        ref = r
    return pack(bits + EOL + EOL)


def g3_1d_aligned(rows):
    bits = ''
    for r in rows:
        bits += '0' * (-len(bits) % 8)
        bits += encode_1d(r)
    return pack(bits + EOL * 6)


def g3_mixed_eol(rows, k):
    bits, ref = '', [0] * len(rows[0])
    for i, r in enumerate(rows):
        if i % k == 0:
            bits += EOL + '1' + encode_1d(r)
        else:
            bits += EOL + '0' + encode_2d(r, ref)
        ref = r
    return pack(bits + (EOL + '1') * 6)


def bitmap(w, h, f):
    return [[1 if f(x, y) else 0 for x in range(w)] for y in range(h)]


def invert(rows):
    return [[1 - v for v in r] for r in rows]


RING = bitmap(40, 40, lambda x, y: 144 <= (x - 19.5) ** 2 + (y - 19.5) ** 2 <= 380)
DIAG = bitmap(36, 40, lambda x, y: abs(x - (y * 0.8 + 2)) < 4 or y < 5)
CHECK = bitmap(30, 30, lambda x, y: (x // 3 + y // 3) % 2 == 0)
LETTER_E = bitmap(32, 40, lambda x, y: x < 8 or y < 7 or y >= 33 or (17 <= y < 23 and x < 26))
WIDE = bitmap(160, 40, lambda x, y: (x < 70 and y % 10 < 5) or (90 <= x < 157 and y >= 20)
              or x == 80)


def hexdata(b):
    return b.hex().upper().encode() + b'>'


def glyph(w, h, dict_entries, data):
    head = (f'{w + 5} 0 0 0 {w} {h} d1\n'
            f'q {w} 0 0 {h} 0 0 cm\n'
            f'BI /IM true /W {w} /H {h} /BPC 1 {dict_entries} ID\n').encode()
    return head + data + b'\nEI Q\n'


def build():
    g = {}
    # Ghostscript style: ink = fax white, /D [1 0]
    g['g0'] = glyph(40, 40, '/D [1 0] /F [/AHx /CCF] /DP [null << /K -1 /Columns 40 >>]',
                    hexdata(g4(invert(RING))))
    raw1 = g4(DIAG)
    assert b' EI' not in raw1 and b'\nEI' not in raw1 and b'\rEI' not in raw1
    g['g1'] = glyph(36, 40, '/F /CCF /DP << /K -1 /Columns 36 >>', raw1)
    g['g2'] = glyph(30, 30, '/D [1 0] /F [/AHx /CCF] /DP [null << /K 0 /Columns 30 '
                    '/EncodedByteAlign true /BlackIs1 true >>]', hexdata(g3_1d_aligned(CHECK)))
    g['g3'] = glyph(32, 40, '/F [/AHx /CCF] /DP [null << /K 2 /Columns 32 /EndOfLine true >>]',
                    hexdata(g3_mixed_eol(LETTER_E, 2)))

    objs = []

    def add(b):
        objs.append(b)
        return len(objs)

    def stream(d, data):
        return f'<< {d} /Length {len(data)} >>\nstream\n'.encode() + data + b'\nendstream'

    add(b'<< /Type /Catalog /Pages 2 0 R >>')
    add(b'<< /Type /Pages /Kids [3 0 R] /Count 1 >>')
    add(b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 300 220] /Contents 4 0 R '
        b'/Resources << /Font << /F1 5 0 R >> /XObject << /Im1 6 0 R >> >> >>')
    content = (b'BT /F1 100 Tf 20 150 Td (0123) Tj ET\n'
               b'BT /F1 50 Tf 20 95 Td (0123) Tj ET\n'
               b'q 240 0 0 60 20 10 cm /Im1 Do Q\n')
    add(stream('', content))
    procs = ' '.join(f'/{n} {8 + i} 0 R' for i, n in enumerate(sorted(g)))
    add(('<< /Type /Font /Subtype /Type3 /FontBBox [0 0 45 40] '
         '/FontMatrix [0.01 0 0 0.01 0 0] '
         f'/CharProcs << {procs} >> '
         '/Encoding << /Type /Encoding /Differences [48 /g0 /g1 /g2 /g3] >> '
         '/FirstChar 48 /LastChar 51 /Widths [45 41 35 37] /Resources << >> >>').encode())
    fax = g4(WIDE)
    add(stream('/Type /XObject /Subtype /Image /Width 160 /Height 40 /ColorSpace /DeviceGray '
               '/BitsPerComponent 1 /Filter [/FlateDecode /CCITTFaxDecode] '
               '/DecodeParms [null << /K -1 /Columns 7 0 R >>]', zlib.compress(fax, 9)))
    add(b'160')
    for n in sorted(g):
        add(stream('', g[n]))

    out = b'%PDF-1.4\n%\xe2\xe3\xcf\xd3\n'
    offs = []
    for i, o in enumerate(objs, 1):
        offs.append(len(out))
        out += f'{i} 0 obj\n'.encode() + o + b'\nendobj\n'
    xref = len(out)
    out += f'xref\n0 {len(objs) + 1}\n0000000000 65535 f \n'.encode()
    for off in offs:
        out += f'{off:010d} 00000 n \n'.encode()
    out += f'trailer\n<< /Size {len(objs) + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n'.encode()
    return out


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, 'ccitt.pdf')
    with open(out, 'wb') as f:
        f.write(build())


if __name__ == '__main__':
    main()
