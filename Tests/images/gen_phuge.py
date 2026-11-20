#!/usr/bin/env python3
"""Generate `phuge.jpg`, the "huge progressive JPEG" fixture of suite `raster-dct-scale`
(task 8.6): a 2048 x 1536 4:2:0 progressive JPEG (`cjpeg -progressive -quality 75 -sample
2x2`) of large flat tiles and a disc, so it compresses to about 27 KB while its full-size
coefficients (3.1 M) and planes (4.7 MB) are large against a tight decoded-bytes limit.

    python3 -I Tests/images/gen_phuge.py [OUTDIR]      (default: Tests/images)

Stdlib only; needs libjpeg-turbo's `cjpeg` (Debian: libjpeg-turbo-progs) and skips cleanly
when it is missing.
"""
import os
import shutil
import subprocess
import sys

W, H = 2048, 1536


def ppm():
    """The source image as binary PPM: 128-pixel tiles (red by column, green by row) and a
    disc of radius 400 (blue 200 inside, 40 outside)."""
    out = bytearray(b"P6\n%d %d\n255\n" % (W, H))
    for y in range(H):
        for x in range(W):
            inside = (x - 1200) ** 2 + (y - 700) ** 2 < 400 ** 2
            out += bytes(((x // 128) * 16 % 256, (y // 128) * 20 % 256, 200 if inside else 40))
    return bytes(out)


def main():
    outdir = sys.argv[1] if len(sys.argv) > 1 else os.path.join("Tests", "images")
    if not shutil.which("cjpeg"):
        print("gen_phuge: cjpeg missing (libjpeg-turbo-progs); skipped")
        return 0
    jpg = subprocess.run(["cjpeg", "-progressive", "-quality", "75", "-sample", "2x2"],
                         input=ppm(), stdout=subprocess.PIPE, check=True).stdout
    with open(os.path.join(outdir, "phuge.jpg"), "wb") as f:
        f.write(jpg)
    print("gen_phuge: phuge.jpg, %d bytes" % len(jpg))
    return 0


if __name__ == "__main__":
    sys.exit(main())
