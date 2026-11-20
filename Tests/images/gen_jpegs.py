#!/usr/bin/env python3
"""Generate the baseline-JPEG fixtures of the DCT decoder (task 7.6a).

    python3 -I Tests/images/gen_jpegs.py [OUTDIR]      (default: Tests/images)

Stdlib only; needs libjpeg-turbo's `cjpeg` and `djpeg` (Debian: libjpeg-turbo-progs) and
skips cleanly when they are missing.  For every fixture NAME it writes

* NAME.jpg  - the JPEG (small synthetic images with odd sizes);
* NAME.ref  - the reference decode: `djpeg -dct int` (libjpeg-turbo's defaults, i.e.
              the settings MuPDF uses: islow IDCT, fancy upsampling), as raw interleaved
              samples preceded by one header line "W H NC\\n".

The four-component fixtures (CMYK and YCCK with an Adobe APP14 marker; cjpeg cannot write
them) are assembled from four grayscale JPEGs: their tables go to slots 0-3, their entropy
data become four non-interleaved scans.  Their reference is computed here from the djpeg
decodes of the four planes (full-size grayscale decoding is exact) with libjpeg's integer
YCC->RGB tables (jdcolor.c); CMYK samples are not inverted (MuPDF, filter-dct.c).

The synthetic source images are deterministic (gradients, edges, a disc, LCG noise).
"""
import os
import shutil
import subprocess
import sys
import tempfile


def lcg(seed):
    x = seed
    while True:
        x = (1103515245 * x + 12345) & 0x7FFFFFFF
        yield x >> 16


def synth(w, h, nc, seed):
    """Interleaved 8-bit samples of a w x h image with nc components."""
    rnd = lcg(seed)
    out = bytearray()
    cx, cy, r2 = w * 0.6, h * 0.4, (min(w, h) * 0.3) ** 2
    for y in range(h):
        for x in range(w):
            inside = (x - cx) ** 2 + (y - cy) ** 2 < r2
            for c in range(nc):
                v = (x * 255 // max(1, w - 1)) if c % 3 == 0 else \
                    (y * 255 // max(1, h - 1)) if c % 3 == 1 else ((x + y) * 4) % 256
                if inside:
                    v = 255 - v
                if (x // 5 + y // 7 + c) % 4 == 0:
                    v = (v + 96) % 256
                v = max(0, min(255, v + (next(rnd) % 21) - 10))
                out.append(v)
    return bytes(out)


def pnm(w, h, nc, data):
    magic = b"P5" if nc == 1 else b"P6"
    return magic + b"\n%d %d\n255\n" % (w, h) + data


def read_pnm(b):
    """(w, h, nc, samples) of a binary P5/P6 file with maxval 255."""
    parts = []
    i = 0
    while len(parts) < 4:
        while b[i:i + 1].isspace():
            i += 1
        if b[i:i + 1] == b"#":
            while b[i:i + 1] != b"\n":
                i += 1
            continue
        j = i
        while not b[j:j + 1].isspace():
            j += 1
        parts.append(b[i:j])
        i = j
    i += 1
    w, h = int(parts[1]), int(parts[2])
    nc = 1 if parts[0] == b"P5" else 3
    return w, h, nc, b[i:i + w * h * nc]


def run(args, data):
    return subprocess.run(args, input=data, stdout=subprocess.PIPE, check=True).stdout


def cjpeg(w, h, nc, data, opts):
    return run(["cjpeg"] + opts, pnm(w, h, nc, data))


def djpeg(jpg):
    return read_pnm(run(["djpeg", "-dct", "int", "-pnm"], jpg))


def segments(jpg):
    """Marker segments of a JPEG up to its first SOS: list of (marker, body), and the
    entropy-coded data of its (single) scan with its SOS body."""
    assert jpg[:2] == b"\xff\xd8"
    i, segs = 2, []
    while True:
        assert jpg[i] == 0xFF
        m = jpg[i + 1]
        n = jpg[i + 2] * 256 + jpg[i + 3]
        body = jpg[i + 4:i + 2 + n]
        i += 2 + n
        if m == 0xDA:
            end = jpg.rindex(b"\xff\xd9")
            return segs, body, jpg[i:end]
        segs.append((m, body))


def seg(m, body):
    return bytes([0xFF, m, (len(body) + 2) >> 8, (len(body) + 2) & 255]) + body


def four_component(w, h, planes, transform):
    """A 4-component baseline JPEG with an Adobe marker (transform 0: CMYK, 2: YCCK),
    one non-interleaved scan per component, built from four grayscale JPEGs."""
    out = bytearray(b"\xff\xd8")
    adobe = b"Adobe" + bytes([0, 100, 0, 0, 0, 0, transform])
    out += seg(0xEE, adobe)
    scans = []
    for k, p in enumerate(planes):
        jpg = cjpeg(w, h, 1, p, ["-grayscale", "-quality", "85"])
        segs, sos, data = segments(jpg)
        for m, body in segs:
            if m == 0xDB:  # DQT: renumber table 0 -> k
                assert body[0] == 0
                out += seg(0xDB, bytes([k]) + body[1:])
            elif m == 0xC4:  # DHT: renumber, tables 0x00 / 0x10 -> 0x0k / 0x1k
                j, nb = 0, bytearray()
                while j < len(body):
                    tc = body[j] >> 4
                    cnt = sum(body[j + 1:j + 17])
                    nb += bytes([(tc << 4) | k]) + body[j + 1:j + 17 + cnt]
                    j += 17 + cnt
                out += seg(0xC4, bytes(nb))
        scans.append(seg(0xDA, bytes([1, k + 1, (k << 4) | k, 0, 63, 0])) + data)
    sof = bytes([8, h >> 8, h & 255, w >> 8, w & 255, 4])
    for k in range(4):
        sof += bytes([k + 1, 0x11, k])
    out += seg(0xC1, sof)
    for s in scans:
        out += s
    out += b"\xff\xd9"
    return bytes(out)


def ycc_rgb(y, cb, cr):
    """libjpeg-turbo ycc_rgb_convert (jdcolor.c, SCALEBITS 16)."""
    def fix(x):
        return int(x * 65536 + 0.5)
    r = y + ((fix(1.40200) * (cr - 128) + 32768) >> 16)
    g = y + ((-fix(0.34414) * (cb - 128) + 32768 - fix(0.71414) * (cr - 128)) >> 16)
    b = y + ((fix(1.77200) * (cb - 128) + 32768) >> 16)
    return [max(0, min(255, v)) for v in (r, g, b)]


def main():
    outdir = sys.argv[1] if len(sys.argv) > 1 else os.path.join("Tests", "images")
    if not (shutil.which("cjpeg") and shutil.which("djpeg")):
        print("gen_jpegs: cjpeg/djpeg missing (libjpeg-turbo-progs); skipped")
        return 0
    os.makedirs(outdir, exist_ok=True)
    fixtures = []
    # (name, w, h, nc, cjpeg options)
    simple = [
        ("gray", 33, 27, 1, ["-grayscale", "-quality", "80"]),
        ("s444", 41, 23, 3, ["-sample", "1x1", "-quality", "80"]),
        ("s422", 37, 29, 3, ["-sample", "2x1", "-quality", "80"]),
        ("s420", 45, 31, 3, ["-sample", "2x2", "-quality", "75"]),
        ("s440", 30, 35, 3, ["-sample", "1x2", "-quality", "80"]),
        ("s411", 50, 17, 3, ["-sample", "4x1", "-quality", "80"]),
        ("narrow", 3, 20, 3, ["-sample", "2x2", "-quality", "90"]),
        ("rst", 47, 33, 3, ["-sample", "2x2", "-restart", "2B", "-quality", "70"]),
        ("rgb", 26, 19, 3, ["-rgb", "-quality", "85"]),
        ("q100", 24, 16, 3, ["-sample", "2x2", "-quality", "100"]),
    ]
    for name, w, h, nc, opts in simple:
        jpg = cjpeg(w, h, nc, synth(w, h, nc, len(name)), opts)
        fixtures.append((name, jpg, djpeg(jpg)))
    # Multi-scan (non-interleaved) sequential file.
    with tempfile.TemporaryDirectory() as tmp:
        sp = os.path.join(tmp, "scans.txt")
        with open(sp, "w") as f:
            f.write("0;\n1;\n2;\n")
        w, h = 29, 21
        jpg = cjpeg(w, h, 3, synth(w, h, 3, 7), ["-sample", "2x2", "-scans", sp])
        fixtures.append(("scans", jpg, djpeg(jpg)))
    # Four components with an Adobe marker.
    w, h = 19, 13
    for name, transform, seed in (("cmyk", 0, 11), ("ycck", 2, 12)):
        src = [synth(w, h, 1, seed + k) for k in range(4)]
        jpg = four_component(w, h, src, transform)
        planes = [djpeg(cjpeg(w, h, 1, p, ["-grayscale", "-quality", "85"]))[3] for p in src]
        ref = bytearray()
        for i in range(w * h):
            c = [p[i] for p in planes]
            if transform == 2:
                ref += bytes([255 - v for v in ycc_rgb(c[0], c[1], c[2])] + [c[3]])
            else:
                ref += bytes(c)
        fixtures.append((name, jpg, (w, h, 4, bytes(ref))))
    total = 0
    for name, jpg, (w, h, nc, data) in fixtures:
        with open(os.path.join(outdir, name + ".jpg"), "wb") as f:
            f.write(jpg)
        with open(os.path.join(outdir, name + ".ref"), "wb") as f:
            f.write(b"%d %d %d\n" % (w, h, nc) + data)
        total += len(jpg) + len(data)
    print("gen_jpegs: %d fixtures, %d bytes" % (len(fixtures), total))
    return 0


if __name__ == "__main__":
    sys.exit(main())
