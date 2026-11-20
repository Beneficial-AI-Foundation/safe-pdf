import sys, os
out = sys.argv[1]


def pdf(path, content, res):
    objs = []
    objs.append(b"<< /Type /Catalog /Pages 2 0 R >>")
    objs.append(b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>")
    objs.append(b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 200] /Contents 4 0 R /Resources "
                + res.encode() + b" >>")
    c = content.encode()
    objs.append(b"<< /Length %d >>\nstream\n" % len(c) + c + b"\nendstream")
    data = b"%PDF-1.7\n"
    offs = []
    for i, o in enumerate(objs):
        offs.append(len(data))
        data += b"%d 0 obj\n" % (i + 1) + o + b"\nendobj\n"
    x = len(data)
    data += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    for o in offs:
        data += b"%010d 00000 n \n" % o
    data += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, x)
    open(os.path.join(out, path), "wb").write(data)


body = ("/K gs 1 0 0 rg 0 0 1 RG 16 w 40 40 120 120 re b "
        "0 1 0 rg 0 0 0 RG 6 w 60 100 m 140 100 l 100 60 l h B")
cases = {
    "ko_ca05": "<< /CA 0.5 >>",
    "ko_ca05_mul": "<< /CA 0.5 /ca 0.7 /BM /Multiply >>",
    "ko_ca1_mul": "<< /BM /Multiply >>",
    "ko_ca1": "<< /CA 1 >>",
    "ko_ca0": "<< /CA 0 >>",
}
for n, g in cases.items():
    pdf(n + ".pdf", "0.9 0.9 0.5 rg 0 0 200 200 re f " + body,
        "<< /ExtGState << /K " + g + " >> >>")
