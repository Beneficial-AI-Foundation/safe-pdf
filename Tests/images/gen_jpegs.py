#!/usr/bin/env python3
"""Generate the JPEG fixtures of the DCT decoder (tasks 7.6a baseline, 7.6b progressive).

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

Progressive fixtures (7.6b, names starting with "p") come from `cjpeg -progressive`
(libjpeg's standard scripts: spectral selection plus successive approximation of DC and AC),
custom `-scans` scripts (refinement-heavy: up to three AC refinement passes, interleaved DC
refinements, single-coefficient bands), restart intervals, odd sizes, quality 100, a smooth
image (long end-of-band runs), and `jpegtran -progressive` of the CMYK fixture (a lossless
transcode, so its reference is the CMYK one).

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


def smooth(w, h, nc):
    """A smooth image (few nonzero AC coefficients: long end-of-band runs)."""
    out = bytearray()
    for y in range(h):
        for x in range(w):
            for c in range(nc):
                v = (x * (2 + c) + y * (3 - c)) // 2 + (40 if (x // 24 + y // 24) % 2 else 0)
                out.append(max(0, min(255, v)))
    return bytes(out)


# Refinement-heavy progressive scan scripts (cjpeg -scans syntax).
SCRIPT_COLOR = """0,1,2: 0-0, 0, 2;
0: 1-5, 0, 3;
2: 1-63, 0, 2;
1: 1-63, 0, 1;
0: 6-63, 0, 3;
0,1,2: 0-0, 2, 1;
0: 1-63, 3, 2;
0,1,2: 0-0, 1, 0;
0: 1-63, 2, 1;
2: 1-63, 2, 1;
1: 1-63, 1, 0;
0: 1-63, 1, 0;
2: 1-63, 1, 0;
"""

SCRIPT_GRAY = """0: 0-0, 0, 3;
0: 1-1, 0, 2;
0: 2-2, 0, 2;
0: 3-9, 0, 2;
0: 10-63, 0, 2;
0: 0-0, 3, 2;
0: 0-0, 2, 1;
0: 1-63, 2, 1;
0: 0-0, 1, 0;
0: 1-63, 1, 0;
"""


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


def djpeg(jpg, strict=True):
    """djpeg's decode; `strict=False` for truncated input (djpeg warns, exit status 2)."""
    if strict:
        return read_pnm(run(["djpeg", "-dct", "int", "-pnm"], jpg))
    r = subprocess.run(["djpeg", "-dct", "int", "-pnm"], input=jpg, stdout=subprocess.PIPE,
                       stderr=subprocess.DEVNULL)
    return read_pnm(r.stdout)


def marker_segments(jpg):
    """(start, end, marker) of every marker segment before the first SOS."""
    i, out = 2, []
    while jpg[i + 1] != 0xDA:
        n = jpg[i + 2] * 256 + jpg[i + 3]
        out.append((i, i + 2 + n, jpg[i + 1]))
        i += 2 + n
    return out


def strip_dht(jpg):
    """The JPEG without its DHT segments (it must use the standard tables)."""
    out = jpg
    for a, e, m in reversed(marker_segments(jpg)):
        if m == 0xC4:
            out = out[:a] + out[e:]
    return out


def first_scans(jpg, n):
    """A progressive JPEG cut after its first `n` scans, with an EOI (only DC known: libjpeg
    interpolates the DC values and the low AC coefficients)."""
    pos, k = 2, 0
    while True:
        i = jpg.index(b"\xff\xda", pos)
        if k == n:
            return jpg[:i] + b"\xff\xd9"
        k += 1
        pos = i + 2


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
    # Progressive (7.6b).
    prog = [
        ("pgray", 33, 27, 1, ["-grayscale", "-quality", "80", "-progressive"]),
        ("p444", 41, 23, 3, ["-sample", "1x1", "-quality", "80", "-progressive"]),
        ("p422", 37, 29, 3, ["-sample", "2x1", "-quality", "80", "-progressive"]),
        ("p420", 45, 31, 3, ["-sample", "2x2", "-quality", "75", "-progressive"]),
        ("pnarrow", 3, 20, 3, ["-sample", "2x2", "-quality", "90", "-progressive"]),
        ("prst", 47, 33, 3, ["-sample", "2x2", "-restart", "3B", "-quality", "70", "-progressive"]),
        ("pq100", 24, 16, 3, ["-sample", "2x2", "-quality", "100", "-progressive"]),
    ]
    for name, w, h, nc, opts in prog:
        jpg = cjpeg(w, h, nc, synth(w, h, nc, len(name) + 100), opts)
        fixtures.append((name, jpg, djpeg(jpg)))
    with tempfile.TemporaryDirectory() as tmp:
        for name, w, h, nc, script, extra in (
                ("pscans", 43, 37, 3, SCRIPT_COLOR, ["-sample", "2x2", "-quality", "85"]),
                ("pscanrst", 35, 26, 3, SCRIPT_COLOR, ["-sample", "2x1", "-quality", "90", "-restart", "2B"]),
                ("pscangray", 29, 31, 1, SCRIPT_GRAY, ["-grayscale", "-quality", "95"])):
            sp = os.path.join(tmp, name + ".txt")
            with open(sp, "w") as f:
                f.write(script)
            jpg = cjpeg(w, h, nc, synth(w, h, nc, len(name) + 200), extra + ["-scans", sp])
            fixtures.append((name, jpg, djpeg(jpg)))
    w, h = 96, 72
    jpg = cjpeg(w, h, 3, smooth(w, h, 3), ["-sample", "2x2", "-quality", "60", "-progressive"])
    fixtures.append(("psmooth", jpg, djpeg(jpg)))
    # 7.6c: no DHT (standard tables, motion-JPEG style) and truncated files.
    byname = {n: j for n, j, _ in fixtures}
    for name, src in (("nodht", "s420"), ("nodhtgray", "gray")):
        jpg = strip_dht(byname[src])
        fixtures.append((name, jpg, djpeg(jpg)))
    for name, src, frac in (
            ("ts420", "s420", 0.6), ("trst", "rst", 0.5), ("tgray", "gray", 0.7),
            ("tp420", "p420", 0.3), ("tp420b", "p420", 0.5), ("tp444", "p444", 0.7),
            ("tpgray", "pgray", 0.5), ("tprst", "prst", 0.3), ("tpscans", "pscans", 0.5),
            ("tpscanrst", "pscanrst", 0.7), ("tpscangray", "pscangray", 0.3),
            ("tpsmooth", "psmooth", 0.7), ("tpnarrow", "pnarrow", 0.5)):
        jpg = byname[src]
        jpg = jpg[:int(len(jpg) * frac)]
        fixtures.append((name, jpg, djpeg(jpg, strict=False)))
    for name, src, nscans in (("dcp420", "p420", 1), ("dcpgray", "pgray", 1)):
        jpg = first_scans(byname[src], nscans)
        fixtures.append((name, jpg, djpeg(jpg)))
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
        if name == "cmyk" and shutil.which("jpegtran"):
            pj = run(["jpegtran", "-progressive"], jpg)
            fixtures.append(("pcmyk", pj, (w, h, 4, bytes(ref))))
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
