#!/usr/bin/env python3
"""Pixel differential comparator: our rendered pages vs MuPDF's `mutool draw`
(comparator `pixels` in run.py).

Plan.md section 6 Phase 7 ("Faithfulness: pixel-differential vs MuPDF/pdf.js
(perceptual diff)"), exit M7: ">= 95% of corpus pages within perceptual
threshold; median page < 100 ms compiled"; task 7.4.  Stdlib only (python3 -I).
Reports by default; `--min-within P` gates (run.py and offline).

Live mode is driven by run.py (`--comparator pixels [--dpi D]`).  Offline:
    python3 -I Tests/differential/pixels.py --a IMG --b IMG [--tol T] [--tau PCT]
    python3 -I Tests/differential/pixels.py --selftest
IMG is a binary PNM (P5 / P6, maxval 255) or an 8-bit PNG (gray, gray+alpha,
RGB, RGBA; non-interlaced; filters 0-4), decoded with zlib.

Our side: `SAFEPDF_RASTER_DIR=DIR SAFEPDF_DPI=D inspect --json --view raster FILE`
writes DIR/page-N.ppm and prints one JSON object per page
    {"page","width","height","dpi","ms","nanos","status","error","file"}
then {"summary": {...}} (or {"summary": {"path","open","error"}} when the
document does not open).  `nanos` is the compiled wall-clock render time of
the page (decode + display list + raster; file writing excluded).
Reference side: `mutool draw -s t -r D -c rgb -F pnm -o DIR/ref-%d.pnm FILE`;
the `-s t` lines `page FILE N Tms` give MuPDF's per-page time (integer ms,
load + run + draw of the page).  Both sides render the CropBox with the
page's /Rotate applied, on opaque white.

Metric (per page).  A pixel DIFFERS when, in some RGB channel, its value in
one image lies outside [min - T, max + T] of the 3x3 neighbourhood of the
same position in the other image (checked both ways, T = TOL = 32 of 255).
The page metric is the percentage of differing pixels; the page is WITHIN
the perceptual threshold when that percentage is <= TAU = 1.0.
Justification:
* the 3x3 neighbourhood range absorbs what a reader does not see: anti-
  aliasing differences on edges (an edge pixel's coverage lies between its
  neighbours' values in both renderers), sub-pixel and 1-px placement
  differences of glyphs and strokes, and different rounding of the page
  size; T = 32 (12.5%) absorbs smooth colour differences (gradient
  quantisation, image resampling filters, colour conversion rounding);
* what remains are real content differences: missing or extra glyphs,
  wrong fills, colours, images, clips, offsets of 2 px or more;
* TAU = 1% of the page area: one missing word of 12 pt text at 72 dpi is
  ~0.05%, a missing text line ~0.3%, a missing text page 3-10%, a missing
  picture or wrong background tens of percent.  So a page within 1% looks
  the same at a glance; a page above it has a visible block-level defect.
Pixel-exact identity is reported too (`identical`).  The metric is a
symmetric, shift-tolerant variant of the fuzzy image compare used by
browser reference tests; it is cheap in pure Python because identical rows
and identical pixels are skipped before any neighbourhood is examined.

Size mismatch.  The page sizes differ when the two sides round the scaled
CropBox differently (MuPDF: fz_round_rect of the transformed box; ours:
ceil of width x zoom).  Both images are padded with white to the larger
size (top-left aligned); a difference of more than 1 px in a dimension is
counted in `size_mismatch` and noted on the page.

Stats per file (summed by run.py): pages (= pages compared), within,
identical, size_mismatch, ours_failed (pages our renderer reported as
errors, counted as not within), ref_missing (pages MuPDF did not render),
page_count_mismatch.  Corpus-wide page times and the worst pages come from
the module lists OURS_MS / REF_MS / PAGES.

Status per file: agree (unless --min-within P is given and fewer than P% of
its pages are within), disagree, known (the core does not open the
document), error (inspector crash / timeout / bad output), skipped (mutool
missing, producing no page, or timing out -- e.g.
Tests/adversarial/xobject-fanout.pdf, where mutool runs for minutes).
"""
import argparse
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import zlib

TIMEOUT = 600
TOL = 32           # channel tolerance beyond the 3x3 neighbourhood range (of 255)
TAU = 1.0          # percent of differing pixels for a page to be "within"
DPI = 72           # set from run.py --dpi
WORST_KEEP = 50
HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURES = os.path.join(HERE, "fixtures")

# Filled by check_file (live mode) for run.py's corpus report.
OURS_MS = []       # our per-page render times (ms, compiled)
REF_MS = []        # MuPDF per-page times (ms, as printed by -s t)
PAGES = []         # (pct, file, page, note) for every compared page


class Skip(Exception):
    pass


class Bad(Exception):
    pass


# ---- image files ----------------------------------------------------------------------
class Image:
    """8-bit RGB image: w, h, bytes (3 per pixel, rows top to bottom)."""

    def __init__(self, w, h, rgb):
        if len(rgb) != 3 * w * h:
            raise Bad("image buffer %d bytes, want %d" % (len(rgb), 3 * w * h))
        self.w, self.h, self.rgb = w, h, bytes(rgb)

    def row(self, y):
        return self.rgb[3 * self.w * y:3 * self.w * (y + 1)]


def _pnm_tokens(data, n):
    """The first n header tokens of a PNM and the offset after the single whitespace
    byte that ends the last one (comments skipped)."""
    toks, i = [], 2
    while len(toks) < n:
        while i < len(data) and data[i:i + 1] in b" \t\r\n":
            i += 1
        if data[i:i + 1] == b"#":
            while i < len(data) and data[i:i + 1] not in b"\r\n":
                i += 1
            continue
        j = i
        while j < len(data) and data[j:j + 1] not in b" \t\r\n#":
            j += 1
        if j == i:
            raise Bad("truncated PNM header")
        toks.append(int(data[i:j]))
        i = j
    return toks, i + 1


def read_pnm(data):
    magic = data[:2]
    if magic not in (b"P5", b"P6"):
        raise Bad("not a binary PNM (P5/P6): %r" % magic)
    (w, h, mx), off = _pnm_tokens(data, 3)
    if mx != 255:
        raise Bad("PNM maxval %d (only 255 supported)" % mx)
    ch = 3 if magic == b"P6" else 1
    px = data[off:off + ch * w * h]
    if len(px) != ch * w * h:
        raise Bad("truncated PNM data")
    if ch == 1:
        px = bytes(v for g in px for v in (g, g, g))
    return Image(w, h, px)


def _paeth(a, b, c):
    p = a + b - c
    pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
    if pa <= pb and pa <= pc:
        return a
    return b if pb <= pc else c


def read_png(data):
    if data[:8] != b"\x89PNG\r\n\x1a\n":
        raise Bad("not a PNG")
    i, idat, hdr = 8, [], None
    while i + 8 <= len(data):
        n, typ = struct.unpack(">I4s", data[i:i + 8])
        body = data[i + 8:i + 8 + n]
        crc = struct.unpack(">I", data[i + 8 + n:i + 12 + n])[0]
        if zlib.crc32(typ + body) & 0xFFFFFFFF != crc:
            raise Bad("PNG chunk %r: bad CRC" % typ)
        if typ == b"IHDR":
            hdr = struct.unpack(">IIBBBBB", body)
        elif typ == b"IDAT":
            idat.append(body)
        elif typ == b"IEND":
            break
        i += 12 + n
    if hdr is None:
        raise Bad("PNG without IHDR")
    w, h, depth, ctype, _, _, interlace = hdr
    chans = {0: 1, 2: 3, 4: 2, 6: 4}.get(ctype)
    if depth != 8 or chans is None or interlace:
        raise Bad("PNG depth %d colour type %d interlace %d unsupported" % (depth, ctype,
                                                                          interlace))
    raw = zlib.decompress(b"".join(idat))
    stride = chans * w
    if len(raw) != (stride + 1) * h:
        raise Bad("PNG data %d bytes, want %d" % (len(raw), (stride + 1) * h))
    prev = bytearray(stride)
    out = bytearray()
    for y in range(h):
        f = raw[y * (stride + 1)]
        cur = bytearray(raw[y * (stride + 1) + 1:(y + 1) * (stride + 1)])
        if f == 1:
            for x in range(chans, stride):
                cur[x] = (cur[x] + cur[x - chans]) & 255
        elif f == 2:
            for x in range(stride):
                cur[x] = (cur[x] + prev[x]) & 255
        elif f == 3:
            for x in range(stride):
                left = cur[x - chans] if x >= chans else 0
                cur[x] = (cur[x] + ((left + prev[x]) >> 1)) & 255
        elif f == 4:
            for x in range(stride):
                left = cur[x - chans] if x >= chans else 0
                ul = prev[x - chans] if x >= chans else 0
                cur[x] = (cur[x] + _paeth(left, prev[x], ul)) & 255
        elif f != 0:
            raise Bad("PNG filter %d" % f)
        out += cur
        prev = cur
    if chans == 3:
        return Image(w, h, out)
    rgb = bytearray()
    for p in range(w * h):
        px = out[chans * p:chans * p + chans]
        if chans in (1, 2):
            c = (px[0],) * 3
            a = px[1] if chans == 2 else 255
        else:
            c, a = px[:3], px[3]
        # Composite onto white.
        rgb += bytes((v * a + 255 * (255 - a) + 127) // 255 for v in c)
    return Image(w, h, rgb)


def read_image(path):
    with open(path, "rb") as fh:
        data = fh.read()
    return read_png(data) if data[:4] == b"\x89PNG" else read_pnm(data)


def pad(img, w, h):
    """img padded with white to w x h (top-left aligned; cropped if larger)."""
    if img.w == w and img.h == h:
        return img
    rows = []
    for y in range(h):
        r = img.row(y)[:3 * w] if y < img.h else b""
        rows.append(r + b"\xff" * (3 * w - len(r)))
    return Image(w, h, b"".join(rows))


# ---- metric ---------------------------------------------------------------------------
def _outside(src, other, w, h, x, y, tol):
    """Does pixel (x, y) of `src` leave the 3x3 neighbourhood range (+- tol) of `other`
    in some channel?"""
    o = 3 * (w * y + x)
    x0, x1, y0, y1 = max(0, x - 1), min(w - 1, x + 1), max(0, y - 1), min(h - 1, y + 1)
    for c in range(3):
        v = src[o + c]
        lo, hi = 255, 0
        for yy in range(y0, y1 + 1):
            base = 3 * w * yy + c
            for xx in range(x0, x1 + 1):
                u = other[base + 3 * xx]
                if u < lo:
                    lo = u
                if u > hi:
                    hi = u
        if v < lo - tol or v > hi + tol:
            return True
    return False


def compare_images(a, b, tol=TOL):
    """-> {"w","h","diff","pct","identical","size_note"} for images a (ours) and b (ref)."""
    note = None
    if (a.w, a.h) != (b.w, b.h):
        note = "size %dx%d vs %dx%d" % (a.w, a.h, b.w, b.h)
    w, h = max(a.w, b.w), max(a.h, b.h)
    big = abs(a.w - b.w) > 1 or abs(a.h - b.h) > 1
    a, b = pad(a, w, h), pad(b, w, h)
    A, B = a.rgb, b.rgb
    diff = 0
    differs = False
    for y in range(h):
        s, e = 3 * w * y, 3 * w * (y + 1)
        if A[s:e] == B[s:e]:
            continue
        differs = True
        ra, rb = A[s:e], B[s:e]
        for x in range(w):
            k = 3 * x
            if ra[k:k + 3] == rb[k:k + 3]:
                continue
            if _outside(A, B, w, h, x, y, tol) or _outside(B, A, w, h, x, y, tol):
                diff += 1
    total = w * h
    return {"w": w, "h": h, "diff": diff, "pct": 100.0 * diff / total if total else 0.0,
            "identical": not differs, "size_note": note, "size_mismatch": big}


# ---- live mode (run.py) ---------------------------------------------------------------
def run_ours(inspect, path, outdir, dpi):
    """-> ({page: record}, summary) from the raster view; images in outdir."""
    if not os.path.exists(inspect):
        raise Skip("inspector not built")
    env = dict(os.environ, SAFEPDF_RASTER_DIR=outdir, SAFEPDF_DPI=str(dpi))
    env.pop("SAFEPDF_PAGE", None)
    env.pop("SAFEPDF_RASTER_FORMAT", None)
    p = subprocess.run([inspect, "--view", "raster", "--json", path], capture_output=True,
                       timeout=TIMEOUT, env=env)
    out = p.stdout.decode("utf-8", "replace")
    if out.lstrip()[:1] != "{":
        if "unknown view" in (out + p.stderr.decode("utf-8", "replace")).lower():
            raise Skip("view not implemented")
        raise Bad("inspect exited %d without JSON: %s" % (
            p.returncode, p.stderr.decode("utf-8", "replace").strip()[:200]))
    return load_ours(out)


def load_ours(text):
    pages, summary = {}, None
    for ln, line in enumerate(text.split("\n"), 1):
        if not line.strip():
            continue
        try:
            rec = json.loads(line)
        except ValueError as e:
            raise Bad("ours line %d: not JSON: %s" % (ln, e))
        if "summary" in rec:
            summary = rec["summary"]
        elif "page" in rec:
            pages[int(rec["page"])] = rec
        else:
            raise Bad("ours line %d: neither a page nor the summary" % ln)
    if summary is None:
        raise Bad("ours: no summary line")
    return pages, summary


_TIME = re.compile(r"^page .* (\d+) (\d+)ms", re.M)


def run_ref(path, outdir, dpi):
    """-> ({page: image path}, {page: ms}, notes) from mutool draw."""
    pat = os.path.join(outdir, "ref-%d.pnm")
    t0 = time.monotonic()
    try:
        p = subprocess.run(["mutool", "draw", "-s", "t", "-r", str(dpi), "-c", "rgb", "-F", "pnm",
                            "-o", pat, path], capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        raise Skip("mutool draw timed out after %d s" % TIMEOUT)
    wall = time.monotonic() - t0
    files = {}
    for f in os.listdir(outdir):
        m = re.fullmatch(r"ref-(\d+)\.pnm", f)
        if m and os.path.getsize(os.path.join(outdir, f)) > 0:
            files[int(m.group(1))] = os.path.join(outdir, f)
    if not files:
        err = [ln.strip() for ln in p.stderr.decode("utf-8", "replace").split("\n")
               if ln.strip() and "ICC support" not in ln]
        raise Skip("mutool draw produced no page (exit %d)%s" % (
            p.returncode, (": " + err[0][:100]) if err else ""))
    text = p.stdout.decode("utf-8", "replace") + p.stderr.decode("utf-8", "replace")
    times = {int(m.group(1)): int(m.group(2)) for m in _TIME.finditer(text)}
    notes = [] if p.returncode == 0 else ["mutool-exit-%d" % p.returncode]
    if not times and files:
        # No -s t lines: average wall time per page (includes process start-up).
        times = {k: 1000.0 * wall / len(files) for k in files}
        notes.append("ref-time-wall")
    return files, times, notes


def compare_dirs(ours, summary, ref_files, ref_times, name, min_within=None, tol=TOL,
                 tau=TAU, notes=()):
    """Per-page comparison report of one file."""
    failed = "error" in summary and "pages" not in summary
    rows = []
    n = max(list(ours) + list(ref_files) + [0])
    for pg in range(1, n + 1):
        o = ours.get(pg)
        r = ref_files.get(pg)
        row = {"page": pg, "ours_ms": None, "ref_ms": ref_times.get(pg), "pct": None,
               "within": False, "identical": False, "note": None, "size_mismatch": False}
        if o is not None:
            row["ours_ms"] = o.get("nanos", 0) / 1e6
        if o is None or o.get("status") != "ok" or not o.get("file"):
            row["note"] = "ours failed: %s" % (o.get("error") if o else "no page")
            row["ours_failed"] = True
        elif r is None:
            row["note"] = "mupdf did not render the page"
            row["ref_missing"] = True
        else:
            c = compare_images(read_image(o["file"]), read_image(r), tol)
            row.update(pct=c["pct"], within=c["pct"] <= tau, identical=c["identical"],
                       note=c["size_note"], size_mismatch=c["size_mismatch"], diff=c["diff"],
                       size=[c["w"], c["h"]])
        rows.append(row)
    within = sum(1 for r in rows if r["within"])
    rep = {"file": name, "pages": len(rows), "pages_ours": len(ours),
           "pages_ref": len(ref_files), "within": within,
           "identical": sum(1 for r in rows if r["identical"]),
           "size_mismatch": sum(1 for r in rows if r["size_mismatch"]),
           "ours_failed_pages": sum(1 for r in rows if r.get("ours_failed")),
           "ref_missing": sum(1 for r in rows if r.get("ref_missing")),
           "doc_failed": summary.get("error") if failed else None,
           "pct_within": 100.0 * within / len(rows) if rows else 100.0,
           "notes": list(notes), "rows": rows}
    if failed:
        rep["status"] = "known"
    elif min_within is not None and rows and rep["pct_within"] < min_within:
        rep["status"] = "disagree"
    else:
        rep["status"] = "agree"
    return rep


def format_report(rep):
    pcts = [r["pct"] for r in rep["rows"] if r["pct"] is not None]
    s = "pages %d, within %d (%.1f%%), identical %d; worst %.3f%% differing; pages ours %d ref %d" % (
        rep["pages"], rep["within"], rep["pct_within"], rep["identical"],
        max(pcts) if pcts else 0.0, rep["pages_ours"], rep["pages_ref"])
    if rep["ours_failed_pages"]:
        s += "; ours-failed %d" % rep["ours_failed_pages"]
    if rep["ref_missing"]:
        s += "; ref-missing %d" % rep["ref_missing"]
    if rep["size_mismatch"]:
        s += "; size-mismatch %d" % rep["size_mismatch"]
    if rep["notes"]:
        s += " [" + ", ".join(rep["notes"]) + "]"
    if rep["doc_failed"]:
        s += " ours-failed: %s" % rep["doc_failed"]
    return s


def stats_of(rep):
    return {"pages": rep["pages"], "within": rep["within"], "identical": rep["identical"],
            "size_mismatch": rep["size_mismatch"], "ours_failed": rep["ours_failed_pages"],
            "ref_missing": rep["ref_missing"],
            "page_count_mismatch": int(rep["pages_ours"] != rep["pages_ref"]),
            "doc_failed_pages": rep["pages"] if rep["doc_failed"] else 0,
            "compared": rep["pages"]}


def check_file(inspect, path, min_within=None, dpi=None):
    """(status, detail, stats) for run.py; records OURS_MS / REF_MS / PAGES."""
    if shutil.which("mutool") is None:
        raise Skip("tool missing: mutool")
    dpi = dpi or DPI
    d = tempfile.mkdtemp(prefix="safepdf-pixels-")
    try:
        od, rd = os.path.join(d, "ours"), os.path.join(d, "ref")
        os.mkdir(od)
        os.mkdir(rd)
        try:
            ours, summary = run_ours(inspect, path, od, dpi)
            ref_files, ref_times, notes = run_ref(path, rd, dpi)
            rep = compare_dirs(ours, summary, ref_files, ref_times, path, min_within,
                               notes=notes)
        except Bad as e:
            return "error", str(e), {}
        except subprocess.TimeoutExpired as e:
            return "error", "timeout: %s" % e, {}
    finally:
        shutil.rmtree(d, True)
    for r in rep["rows"]:
        if r["ours_ms"] is not None and not r.get("ours_failed"):
            OURS_MS.append(r["ours_ms"])
        if r["ref_ms"] is not None:
            REF_MS.append(float(r["ref_ms"]))
        PAGES.append((r["pct"] if r["pct"] is not None else 100.0, path, r["page"],
                      r["note"] or "", r["ours_ms"]))
    return rep["status"], format_report(rep), stats_of(rep)


def quantile(xs, q):
    s = sorted(xs)
    if not s:
        return None
    k = min(len(s) - 1, max(0, -(-int(q * len(s) * 1000) // 1000) - 1))
    return s[k]


def _f(x):
    return "-" if x is None else "%.3f" % x


def summary_lines(stats, min_within=None, tag="pixels"):
    """Corpus report for run.py: (lines, report dict, failed)."""
    head = "%-8s" % tag
    if not stats.get("pages", 0):
        return ["%s no page compared" % head], {"pct_within": None}, False
    pct = 100.0 * stats["within"] / stats["pages"]
    opened = stats["pages"] - stats.get("doc_failed_pages", 0)
    pct_open = 100.0 * stats["within"] / opened if opened else None
    om, op, ox = quantile(OURS_MS, 0.5), quantile(OURS_MS, 0.95), max(OURS_MS or [0])
    rm, rp = quantile(REF_MS, 0.5), quantile(REF_MS, 0.95)
    lines = ["%s corpus: %d page(s), %.2f%% within (<= %g%% pixels differing, tol %d, 3x3), "
             "%d identical, %d ours-failed, %d ref-missing, %d size-mismatch" % (
                 head, stats["pages"], pct, TAU, TOL, stats.get("identical", 0),
                 stats.get("ours_failed", 0), stats.get("ref_missing", 0),
                 stats.get("size_mismatch", 0)),
             "%s of the %d page(s) of documents we open: %s%% within (%d page(s) belong to "
             "documents the core refuses to open)" % (
                 head, opened, _f(pct_open), stats.get("doc_failed_pages", 0)),
             "%s page time ours (compiled render) median %s p95 %s max %s ms; mupdf median %s "
             "p95 %s ms (%d dpi)" % (head, _f(om), _f(op), _f(ox), _f(rm), _f(rp), DPI)]
    worst = sorted(PAGES, key=lambda t: -t[0])
    worst = [t for t in worst if t[0] > 0][:15]
    if worst:
        lines.append("%s worst pages:" % head)
        lines += ["  %8.3f%% %s p%d %s" % (t[0], t[1], t[2], t[3]) for t in worst]
    rep = {"tolerance": {"channel": TOL, "neighbourhood": "3x3", "tau_pct": TAU}, "dpi": DPI,
           "pct_within": pct, "pct_within_opened": pct_open, "pages_opened": opened,
           "min_within": min_within, "pages": stats["pages"],
           "ours_ms": {"median": om, "p95": op, "max": ox},
           "ref_ms": {"median": rm, "p95": rp},
           "worst": [{"pct": t[0], "file": t[1], "page": t[2], "note": t[3], "ours_ms": t[4]}
                     for t in sorted(PAGES, key=lambda t: -t[0])[:WORST_KEEP]]}
    fail = min_within is not None and pct < min_within
    if fail:
        lines.append("FAIL --min-within %.4f: corpus %.4f%% of pages within threshold" % (
            min_within, pct))
    return lines, rep, fail


# ---- self test ------------------------------------------------------------------------
def _fx(name):
    return os.path.join(FIXTURES, name)


def selftest():
    bad = []

    def want(cond, msg):
        if not cond:
            bad.append(msg)
            print("FAIL " + msg)

    # Decoders: our PNG writer (stored DEFLATE, filter 0) and our PPM of the same page.
    ours_ppm = read_image(_fx("pixels_shapes2.ours.ppm"))
    ours_png = read_image(_fx("pixels_shapes2.ours.png"))
    want((ours_ppm.w, ours_ppm.h) == (100, 201), "ppm size %dx%d" % (ours_ppm.w, ours_ppm.h))
    want(ours_png.rgb == ours_ppm.rgb, "png and ppm of our page decode to the same pixels")
    # PNG filters 1-4 and RGBA / gray: round-trip through a hand-built PNG.
    w, h = 5, 5
    px = bytes((x * 40 + y * 7 + c * 3) & 255 for y in range(h) for x in range(w) for c in range(4))
    raw = bytearray()
    for y in range(h):
        f = y  # filters 0..4, one per row
        row = px[20 * y:20 * (y + 1)]
        prev = px[20 * (y - 1):20 * y] if y else bytes(20)
        enc = bytearray()
        for x in range(20):
            left = row[x - 4] if x >= 4 else 0
            ul = prev[x - 4] if x >= 4 else 0
            pred = [0, left, prev[x], (left + prev[x]) >> 1, _paeth(left, prev[x], ul)][f]
            enc.append((row[x] - pred) & 255)
        raw += bytes([f]) + enc

    def chunk(t, b):
        return struct.pack(">I", len(b)) + t + b + struct.pack(">I", zlib.crc32(t + b) & 0xFFFFFFFF)
    png = (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0)) +
           chunk(b"IDAT", zlib.compress(bytes(raw))) + chunk(b"IEND", b""))
    img = read_png(png)
    exp = bytes((px[4 * p + c] * px[4 * p + 3] + 255 * (255 - px[4 * p + 3]) + 127) // 255
                for p in range(w * h) for c in range(3))
    want(img.rgb == exp, "png filters 0-4 + RGBA compositing")
    want(read_pnm(b"P5\n# c\n2 1\n255\n\x00\xff").rgb == b"\x00\x00\x00\xff\xff\xff", "P5")
    # Metric: identity; 1-px shift within; AA edge within; missing block outside.
    c = compare_images(ours_ppm, ours_ppm)
    want(c["identical"] and c["diff"] == 0, "identity")
    sh = Image(ours_ppm.w, ours_ppm.h, b"".join(
        b"\xff\xff\xff" + ours_ppm.row(y)[:-3] for y in range(ours_ppm.h)))
    c = compare_images(ours_ppm, sh)
    want(c["diff"] == 0 and not c["identical"], "1-px shift absorbed (diff %d)" % c["diff"])
    sh2 = Image(ours_ppm.w, ours_ppm.h, b"".join(
        b"\xff\xff\xff" * 3 + ours_ppm.row(y)[:-9] for y in range(ours_ppm.h)))
    c = compare_images(ours_ppm, sh2)
    want(c["diff"] > 0, "3-px shift detected (diff %d)" % c["diff"])
    # Real pair: our page vs MuPDF's page (shapes.pdf p2: filled + stroked shapes).
    ref = read_image(_fx("pixels_shapes2.ref.pnm"))
    c = compare_images(ours_ppm, ref)
    print("shapes p2 ours vs mupdf: %d differing px (%.3f%%), identical %s" % (
        c["diff"], c["pct"], c["identical"]))
    want(c["pct"] <= TAU, "shapes p2 within threshold")
    # Hand-edited reference: a 20x20 block painted black (an extra / missing shape).
    rows = [bytearray(ref.row(y)) for y in range(ref.h)]
    for y in range(150, 170):
        rows[y][3 * 40:3 * 60] = b"\x00" * 60
    edited = Image(ref.w, ref.h, b"".join(bytes(r) for r in rows))
    c = compare_images(ours_ppm, edited)
    want(c["pct"] > TAU and c["diff"] >= 18 * 18, "edited block outside (%d px)" % c["diff"])
    # Size mismatch: padded, noted; > 1 px counted.
    c = compare_images(ours_ppm, Image(ref.w, ref.h - 1, ref.rgb[:3 * ref.w * (ref.h - 1)]))
    want(c["size_note"] is not None and not c["size_mismatch"], "1-px size difference noted")
    # Report plumbing: our JSON fixture + the two images.
    ours, summary = load_ours(open(_fx("pixels_shapes.ours.jsonl"), encoding="utf-8").read()
                              .replace("@FIXTURES@", FIXTURES))
    rep = compare_dirs(ours, summary, {2: _fx("pixels_shapes2.ref.pnm")}, {2: 1}, "shapes",
                       min_within=100.0)
    print("report:     %s: %s" % (rep["status"], format_report(rep)))
    want(rep["pages"] == 2 and rep["within"] == 1 and rep["ref_missing"] == 1
         and rep["status"] == "disagree", "report: page 1 ref missing, page 2 within")
    print("selftest: %s" % ("ok" if not bad else "%d failure(s)" % len(bad)))
    return 1 if bad else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description="Compare rendered pages (perceptual pixel diff)")
    ap.add_argument("--a", help="image A (ours): PNM or PNG")
    ap.add_argument("--b", help="image B (reference): PNM or PNG")
    ap.add_argument("--tol", type=int, default=TOL, help="channel tolerance (default %d)" % TOL)
    ap.add_argument("--tau", type=float, default=TAU,
                    help="max percent of differing pixels for 'within' (default %g)" % TAU)
    ap.add_argument("--json", metavar="OUT")
    ap.add_argument("--selftest", action="store_true", help="check against the fixtures")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    if not (a.a and a.b):
        ap.error("--a and --b are required (or --selftest)")
    try:
        c = compare_images(read_image(a.a), read_image(a.b), a.tol)
    except (Bad, OSError) as e:
        print("error: %s" % e)
        return 2
    within = c["pct"] <= a.tau
    print("%s: %d of %d px differ (%.4f%%), identical %s%s" % (
        "within" if within else "outside", c["diff"], c["w"] * c["h"], c["pct"], c["identical"],
        "; " + c["size_note"] if c["size_note"] else ""))
    if a.json:
        with open(a.json, "w") as fh:
            json.dump(dict(c, within=within, tol=a.tol, tau=a.tau), fh, indent=1)
    return 0 if within else 1


if __name__ == "__main__":
    sys.exit(main())
