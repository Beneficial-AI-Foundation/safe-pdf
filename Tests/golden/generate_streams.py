"""Generator for the golden inputs of the `streams` inspector view (task 3.7).

Usage: python3 -I Tests/golden/generate_streams.py Tests/golden/streams
Stdlib only. Note: zlib output can differ between zlib versions, so regenerated
files may not be byte-identical to the committed ones; the committed PDFs are the
test inputs, this script documents how they were built."""

import zlib, sys, os


def pdf(objs):
    out = b"%PDF-1.7\n"
    offs = []
    for i, body in enumerate(objs, 1):
        offs.append(len(out))
        out += b"%d 0 obj\n" % i + body + b"\nendobj\n"
    x = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for o in offs:
        out += b"%010d 00000 n \n" % o
    out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, x)
    return out


def stream(d, data):
    return b"<< " + d + b" /Length %d >>\nstream\n" % len(data) + data + b"\nendstream"


cat = b"<< /Type /Catalog /Pages 2 0 R >>"
pages = b"<< /Type /Pages /Kids [] /Count 0 >>"
content = b"BT /F1 12 Tf 72 720 Td (Hello, streams) Tj ET\n"
fl = zlib.compress(content)
d = sys.argv[1]
ahx = fl.hex().encode() + b">"
open(os.path.join(d, "flate.pdf"), "wb").write(pdf([cat, pages,
    stream(b"/Filter /FlateDecode", fl),
    stream(b"/Filter [/ASCIIHexDecode /FlateDecode]", ahx),
    stream(b"", b"plain data")]))
jpg = bytes.fromhex("ffd8ffe000104a46494600010100000100010000ffd9")
img = b"/Type /XObject /Subtype /Image /Width 1 /Height 1 /BitsPerComponent 8 /ColorSpace /DeviceGray "
open(os.path.join(d, "image.pdf"), "wb").write(pdf([cat, pages,
    stream(img + b"/Filter /DCTDecode", jpg),
    stream(img + b"/Filter [/AHx /DCT]", jpg.hex().encode() + b">")]))
pred = bytes([0, 1, 2, 3, 0, 4, 5, 6])
open(os.path.join(d, "indirect.pdf"), "wb").write(pdf([cat, pages,
    stream(b"/Filter 4 0 R", fl),
    b"/FlateDecode",
    stream(b"/Filter /FlateDecode /DecodeParms 6 0 R", zlib.compress(pred)),
    b"<< /Predictor 12 /Columns 3 >>",
    stream(b"/Filter /FlateDecode", b"not zlib at all"),
    stream(b"/Filter /BogusDecode", b"xyz")]))
