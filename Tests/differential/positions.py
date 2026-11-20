#!/usr/bin/env python3
"""Glyph-position differential comparator: our per-glyph origins vs MuPDF's
`mutool draw -F stext` character origins (comparator `positions` in run.py).

Plan.md section 7 item 1; Phase 6 exit M6, clause "all glyph positions within
tolerance"; task 6.10.  Stdlib only (python3 -I).  Reports by default; the
M6 threshold is evaluated from the report (`--min-within` gates when wanted).

Live mode is driven by run.py (`--comparator positions`).  Offline mode:
    python3 -I Tests/differential/positions.py --ours OURS.jsonl --ref REF.stext.xml
                    [--ctm CTM.jsonl] [--min-within PCT] [--json OUT]
    python3 -I Tests/differential/positions.py --selftest

Our side: `SAFEPDF_TEXT_GLYPHS=1 inspect --view text --json FILE`; per page
    {"page": N, ..., "error": null|msg, "glyphList": [[item, seq, x, y, width, size, text], ...]}
then {"summary": {...}}.  (x, y) is the glyph ORIGIN on the baseline in PDF default
user space of the page (unrotated; CropBox not subtracted), `size` the page-space
font size, `text` the glyph's Unicode text (several code points for a ligature).

Reference side: `mutool draw -q -F stext -o - FILE` (MuPDF 1.25.1 format checked):
    <page id="pageN" width=W height=H> <block> <line dir=..> <font name size=S>
    <char quad="x0 y0 ... x3 y3" x=X y=Y bidi color alpha flags=F c="C"/>
(X, Y) is the character origin (pen position on the baseline, the same point as our
(x, y)) in MuPDF DEVICE space at 72 dpi: y grows downwards, the page's /Rotate and
its CropBox origin are applied.  `flags & 4` (FZ_STEXT_SYNTHETIC) marks a space MuPDF
invented for a gap; those are dropped.  The XML is scanned with regular expressions
(not ElementTree): MuPDF may emit character references that are not legal XML 1.0
(e.g. `&#x1;`), and html.unescape decodes them.

Device -> user conversion.  MuPDF maps user space to device space with the page
transform ctm = [a b c d e f] (X = a x + c y + e, Y = b x + d y + f); we invert it:
    x = ( d (X - e) - c (Y - f)) / det,   y = (-b (X - e) + a (Y - f)) / det,
    det = a d - b c.
ctm comes from MuPDF itself: `mutool run` with a small script printing
`page.getTransform()` per page (checked on 1.25.1 against /Rotate 0/90/180/270 with an
offset CropBox: e.g. CropBox [30 40 500 760] /Rotate 90 -> [0 1 1 0 -40 -30]).  When
the script cannot run (mutool built without JavaScript, or a page that fails to load),
ctm is rebuilt from our own `inspect --view pages --json` boxes with MuPDF's
`pdf_page_transform_box` rule: rotate snapped to a multiple of 90,
ctm = scale(1, -1) . rotate(-rotate), then translated so that the transformed
CropBox starts at (0, 0) (UserUnit ignored) -- the file gets the note `ctm-ours`.
Offline, a missing --ctm means [1 0 0 -1 0 H] (H = the stext page height: no
rotation, CropBox at the origin).

Character streams.  Each side becomes, per page, a sequence of characters in
content (our glyphList) / stext (MuPDF) order.  Each glyph's / char's text goes
through text.py's `normalize` (NFKC, drop soft hyphen / zero-width / controls,
fold dashes and quotes) and whitespace is removed, so word spaces never take part
(MuPDF synthesizes some, we never do).  A glyph whose normalized text has k > 1
code points (a ligature "fi", or NFKC expanding U+FB01) yields k characters; the
first carries the glyph origin, the others are TAILS.  MuPDF places ligature tails
at origin + advance; our dump has no baseline direction, so tails are aligned
(counted as matched) but never measured.

Matching.  Per page (pages paired by number) the two character strings are aligned
with difflib.SequenceMatcher (autojunk off); characters in its matching blocks are
the matched pairs, everything else is unmatched on its side (different extraction,
reordered text, missing page).  The alignment is order-preserving: when the
two sides order blocks differently, only one ordering's characters match (e.g. a
20 000-char page with its halves swapped matches ~40%); such pages show up as
unmatched counts, never as distance errors.  Cost: ~4 s for a 20 000-char page.  A matched pair is MEASURED when neither side is a
tail and the character is not U+FFFD (two unmapped glyphs "agree" by accident);
its distance is the Euclidean distance of the two origins in pt (user space).

Tolerance.  A measured pair is WITHIN when
    dist <= max(TOL_ABS, TOL_REL * size),   TOL_ABS = 1 pt, TOL_REL = 0.1,
size = the smaller of our page-space font size and MuPDF's <font size> (the
non-zero one when one is 0).  The two sizes agree for ordinary fonts; for Type 3
fonts they differ by design (ours: |Tfs| x type3SizeScale x scale, an em estimated
from the widths; MuPDF: |Tfs| x scale, FontMatrix ignored), so `size_mismatch`
counts are expected there, and the smaller size keeps the tolerance conservative.
MuPDF's size is the expansion sqrt|det| of the text rendering matrix, ours the
vertical scale max(|c|, |d|): they also differ under Tz != 100 or an anisotropic
CTM (Tests/golden/svg/text.pdf: 80 Tz, ours 12 vs MuPDF 10.73), which is again a
size_mismatch but not a position error.  Rationale: 1 pt is
about a pixel at 100 dpi, far above both sides' arithmetic noise (our Fixed is
10^-6; MuPDF floats ~10^-4), and 10% of the em is far below the smallest real
glyph advance (~0.25 em for i/l/space), so a pair within tolerance is on the
right glyph slot and errors that a reader would notice (wrong widths accumulating
along a line, wrong Tc/Tw/Tz/TJ, wrong text matrix or CTM, wrong page transform)
are not.  Proposed M6 reading of "all glyph positions within tolerance":
pct_within = 100% of measured pairs over the corpus (every exception triaged
as their bug / spec ambiguity in docs/deviations-from-spec.md), with unmatched
characters covered by the text comparators' similarity instead.  We also count
`size_mismatch`: measured pairs whose sizes differ by more than 10%.

Stats per file (summed by run.py): pages, page_count_mismatch, ours_failed,
chars_ours, chars_ref, matched, unmatched_ours, unmatched_ref, compared (= the
measured pairs), within, size_mismatch.  Corpus-wide distance statistics (median,
p95, max) and the worst glyphs come from the module lists DISTS / WORST.

Status per file: agree (any result, unless below --min-within), disagree (percent
within below --min-within when given), known (the core does not open the document),
error (inspector crash / timeout / non-JSON output), skipped (mutool missing, failing
without any stext page, or timing out -- e.g. Tests/adversarial/xobject-fanout.pdf,
where mutool 1.25.1 runs for minutes and grows past 6 GB).
"""
import argparse
import array
import atexit
import difflib
import heapq
import html
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile

TIMEOUT = 600
TOL_ABS = 1.0
TOL_REL = 0.1
SIZE_REL = 0.1
SYNTHETIC = 4          # FZ_STEXT_SYNTHETIC
WORST_KEEP = 50
HERE = os.path.dirname(os.path.abspath(__file__))

# Filled by check_file (live mode) for run.py's corpus report.
DISTS = array.array("d")   # every measured distance (pt)
WORST = []                 # min-heap of (dist, file, page, char, ours(x,y), ref(x,y), size)


class Skip(Exception):
    pass


class Bad(Exception):
    pass


def _load_text_module():
    # python -I removes this directory from sys.path: load text.py by path.
    import importlib.util
    spec = importlib.util.spec_from_file_location("text_norm_for_positions",
                                                  os.path.join(HERE, "text.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_normalize = _load_text_module().normalize


def norm_chars(s):
    """Normalized code points of one glyph's text, whitespace removed."""
    return [ch for ch in _normalize(s) if not ch.isspace()]


# ---- our side -------------------------------------------------------------------
def load_ours(text):
    """-> ({page: [(char, x, y, size, tail)]}, page count, summary)."""
    pages, summary = {}, None
    for ln, line in enumerate(text.split("\n"), 1):
        if not line.strip():
            continue
        try:
            rec = json.loads(line)
        except ValueError as e:
            raise Bad("ours line %d: not JSON: %s" % (ln, e))
        if not isinstance(rec, dict):
            raise Bad("ours line %d: not an object" % ln)
        if "summary" in rec:
            summary = rec["summary"]
            continue
        if "page" not in rec:
            raise Bad("ours line %d: neither a page nor the summary" % ln)
        chars = []
        if rec.get("error") is None:
            if "glyphList" not in rec:
                raise Bad("ours line %d: no glyphList (SAFEPDF_TEXT_GLYPHS=1 not honoured)" % ln)
            for g in rec["glyphList"]:
                _, _, x, y, _, size, t = g
                for i, ch in enumerate(norm_chars(t)):
                    chars.append((ch, float(x), float(y), float(size), i > 0))
        pages[int(rec["page"])] = chars
    if summary is None:
        raise Bad("ours: no summary line")
    return pages, (max(pages) if pages else 0), summary


# ---- MuPDF side -----------------------------------------------------------------
_TAG = re.compile(r"<(page|font|char)\b([^>]*)>")
_ATTR = re.compile(r'([A-Za-z_:][-\w:.]*)="([^"]*)"')


def _attrs(s):
    return {k: html.unescape(v) for k, v in _ATTR.findall(s)}


def load_stext(text):
    """-> ({page: [(char, X, Y, size, tail)]} in device space, {page: height})."""
    pages, heights = {}, {}
    cur, size, n = None, 0.0, 0
    for m in _TAG.finditer(text):
        kind, a = m.group(1), _attrs(m.group(2))
        if kind == "page":
            n += 1
            mm = re.fullmatch(r"page(\d+)", a.get("id", ""))
            num = int(mm.group(1)) if mm else n
            cur = pages.setdefault(num, [])
            heights[num] = float(a.get("height", "0") or 0)
        elif kind == "font":
            size = float(a.get("size", "0") or 0)
        elif cur is not None:
            if int(a.get("flags", "0") or 0) & SYNTHETIC:
                continue
            try:
                X, Y = float(a["x"]), float(a["y"])
            except (KeyError, ValueError):
                # Origins are printed by MuPDF since long before 1.23; without them
                # there is nothing to compare (a skip, not an error).
                raise Skip("stext <char> without x/y origin: %r" % m.group(0)[:80])
            for i, ch in enumerate(norm_chars(a.get("c", ""))):
                cur.append((ch, X, Y, size, i > 0))
    return pages, heights


def load_ctm(text):
    """CTM lines {"page": N, "ctm": [a,b,c,d,e,f] | null} -> {page: ctm}."""
    out = {}
    for line in text.split("\n"):
        line = line.strip()
        if not line.startswith("{"):
            continue
        rec = json.loads(line)
        if rec.get("ctm") is not None:
            out[int(rec["page"])] = [float(v) for v in rec["ctm"]]
    return out


def invert(ctm, X, Y):
    a, b, c, d, e, f = ctm
    det = a * d - b * c
    if det == 0:
        raise Bad("singular page transform %r" % (ctm,))
    u, v = X - e, Y - f
    return (d * u - c * v) / det, (-b * u + a * v) / det


def mupdf_box_ctm(crop, rotate):
    """MuPDF's pdf_page_transform_box (UserUnit 1) for CropBox `crop`, /Rotate."""
    r = int(rotate)
    r = 360 - ((-r) % 360) if r < 0 else r % 360
    r = 90 * ((r + 45) // 90)
    if r >= 360:
        r = 0
    # Row-vector convention (p' = p . M), M = [a b c d e f].
    # fz_pre_rotate(scale(1,-1), -r) = rotate(-r) . scale(1,-1): rotate first.
    th = math.radians(-r)
    cs, sn = round(math.cos(th)), round(math.sin(th))   # exact for multiples of 90
    a, b, c, d = cs, -sn, -sn, -cs   # [cs sn -sn cs] . [1 0 0 -1]
    x0, y0, x1, y1 = crop
    xs = [a * x + c * y for x in (x0, x1) for y in (y0, y1)]
    ys = [b * x + d * y for x in (x0, x1) for y in (y0, y1)]
    return [a, b, c, d, -min(xs), -min(ys)]


# ---- comparison -----------------------------------------------------------------
def tolerance(size):
    return max(TOL_ABS, TOL_REL * size)


def compare_page(ours, ref, ctm):
    """-> dict with counts and the measured pairs [(dist, ch, (x,y), (rx,ry), size, ok)]."""
    sm = difflib.SequenceMatcher(None, [c[0] for c in ours], [c[0] for c in ref],
                                 autojunk=False)
    matched = 0
    pairs = []
    size_mismatch = 0
    for i, j, k in sm.get_matching_blocks():
        matched += k
        for t in range(k):
            o, r = ours[i + t], ref[j + t]
            if o[4] or r[4] or o[0] == "\ufffd":
                continue
            rx, ry = invert(ctm, r[1], r[2])
            d = math.hypot(o[1] - rx, o[2] - ry)
            size = min(o[3], r[3]) if o[3] > 0 and r[3] > 0 else max(o[3], r[3])
            if size > 0 and abs(o[3] - r[3]) > SIZE_REL * size:
                size_mismatch += 1
            pairs.append((d, o[0], (o[1], o[2]), (rx, ry), size, d <= tolerance(size)))
    return {"chars_ours": len(ours), "chars_ref": len(ref), "matched": matched,
            "unmatched_ours": len(ours) - matched, "unmatched_ref": len(ref) - matched,
            "pairs": pairs, "size_mismatch": size_mismatch}


def quantile(sorted_xs, q):
    if not sorted_xs:
        return 0.0
    k = min(len(sorted_xs) - 1, max(0, math.ceil(q * len(sorted_xs)) - 1))
    return sorted_xs[k]


def dist_summary(ds):
    s = sorted(ds)
    if not s:
        return {"median": None, "p95": None, "max": None}
    return {"median": quantile(s, 0.5), "p95": quantile(s, 0.95), "max": s[-1]}


def compare(ours_text, stext_text, ctms=None, name="input", min_within=None, notes=()):
    ours, n_ours, summary = load_ours(ours_text)
    ref, heights = load_stext(stext_text)
    ctms = dict(ctms or {})
    failed = "error" in summary and "pages" not in summary
    n = max([n_ours] + list(ref))
    rows = []
    for p in range(1, n + 1):
        ctm = ctms.get(p) or [1.0, 0.0, 0.0, -1.0, 0.0, heights.get(p, 0.0)]
        r = compare_page(ours.get(p, []), ref.get(p, []), ctm)
        r["page"] = p
        rows.append(r)
    pairs = [x for r in rows for x in r["pairs"]]
    within = sum(1 for x in pairs if x[5])
    rep = {
        "file": name, "pages_ours": n_ours, "pages_ref": len(ref),
        "ours_failed": summary.get("error") if failed else None,
        "chars_ours": sum(r["chars_ours"] for r in rows),
        "chars_ref": sum(r["chars_ref"] for r in rows),
        "matched": sum(r["matched"] for r in rows),
        "unmatched_ours": sum(r["unmatched_ours"] for r in rows),
        "unmatched_ref": sum(r["unmatched_ref"] for r in rows),
        "compared": len(pairs), "within": within,
        "size_mismatch": sum(r["size_mismatch"] for r in rows),
        "pct_within": 100.0 if not pairs else 100.0 * within / len(pairs),
        "notes": list(notes),
        "rows": rows,
    }
    rep.update(dist_summary([x[0] for x in pairs]))
    if failed:
        rep["status"] = "known"
    elif min_within is not None and pairs and rep["pct_within"] < min_within:
        rep["status"] = "disagree"
    else:
        rep["status"] = "agree"
    return rep


def _f(x):
    return "-" if x is None else "%.3f" % x


def format_report(rep):
    s = ("measured %d, within %.2f%% (median %s p95 %s max %s pt); matched %d, unmatched "
         "ours %d ref %d; pages ours %d ref %d" % (
             rep["compared"], rep["pct_within"], _f(rep["median"]), _f(rep["p95"]),
             _f(rep["max"]), rep["matched"], rep["unmatched_ours"], rep["unmatched_ref"],
             rep["pages_ours"], rep["pages_ref"]))
    if rep["size_mismatch"]:
        s += "; size-mismatch %d" % rep["size_mismatch"]
    if rep["notes"]:
        s += " [" + ", ".join(rep["notes"]) + "]"
    if rep["ours_failed"]:
        s += " ours-failed: %s" % rep["ours_failed"]
    return s


def stats_of(rep):
    return {
        "pages": len(rep["rows"]),
        "page_count_mismatch": int(rep["pages_ours"] != rep["pages_ref"]),
        "ours_failed": int(bool(rep["ours_failed"])),
        "chars_ours": rep["chars_ours"], "chars_ref": rep["chars_ref"],
        "matched": rep["matched"], "unmatched_ours": rep["unmatched_ours"],
        "unmatched_ref": rep["unmatched_ref"], "compared": rep["compared"],
        "within": rep["within"], "size_mismatch": rep["size_mismatch"],
    }


def worst_of(rep, n=10):
    """The n largest-distance measured pairs of a report: (dist, page, ch, o, r, size)."""
    items = [(x[0], r["page"], x[1], x[2], x[3], x[4]) for r in rep["rows"] for x in r["pairs"]]
    return heapq.nlargest(n, items, key=lambda t: t[0])


def worst_line(d, f, page, ch, o, r, size):
    return "  %8.3f pt %s p%d %r ours (%.3f, %.3f) mupdf (%.3f, %.3f) size %.3g tol %.3g" % (
        d, f, page, ch, o[0], o[1], r[0], r[1], size, tolerance(size))


def summary_lines(stats, min_within=None, tag="positions"):
    """Corpus report for run.py: (lines, report dict, failed)."""
    head = "%-8s" % tag
    if not stats.get("compared", 0):
        return ["%s no glyph pair measured" % head], {"pct_within": None}, False
    pct = 100.0 * stats["within"] / stats["compared"]
    ds = dist_summary(DISTS)
    lines = ["%s corpus: %d measured pair(s), %.4f%% within max(%g pt, %g x size); origin "
             "distance median %s p95 %s max %s pt; matched %d of ours %d / ref %d chars" % (
                 head, stats["compared"], pct, TOL_ABS, TOL_REL, _f(ds["median"]),
                 _f(ds["p95"]), _f(ds["max"]), stats.get("matched", 0),
                 stats.get("chars_ours", 0), stats.get("chars_ref", 0))]
    worst = [t for t in sorted(WORST, reverse=True) if t[0] >= 0.001]
    if worst:
        lines.append("%s worst glyphs:" % head)
        lines += [worst_line(*t) for t in worst[:10]]
    rep = {"tolerance": {"abs_pt": TOL_ABS, "rel_size": TOL_REL},
           "pct_within": pct, "min_within": min_within, "measured": stats["compared"]}
    rep.update(ds)
    rep["worst"] = [{"dist": t[0], "file": t[1], "page": t[2], "char": t[3],
                     "ours": list(t[4]), "ref": list(t[5]), "size": t[6]} for t in worst]
    fail = min_within is not None and pct < min_within
    if fail:
        lines.append("FAIL --min-within %.4f: corpus %.4f%% within tolerance" % (min_within, pct))
    return lines, rep, fail


# ---- live mode (run.py) -----------------------------------------------------------
_CTM_JS = r"""
var doc = Document.openDocument(scriptArgs[0]);
var n = doc.countPages();
for (var i = 0; i < n; i++) {
  var t = null;
  try { var p = doc.loadPage(i); if (typeof p.getTransform === "function") t = p.getTransform(); }
  catch (e) { t = null; }
  print(JSON.stringify({page: i + 1, ctm: t}));
}
"""
_JS_PATH = []


def _js_path():
    if not _JS_PATH:
        d = tempfile.mkdtemp(prefix="safepdf-positions-")
        p = os.path.join(d, "ctm.js")
        with open(p, "w") as fh:
            fh.write(_CTM_JS)
        atexit.register(shutil.rmtree, d, True)
        _JS_PATH.append(p)
    return _JS_PATH[0]


def run_ours(inspect, path):
    if not os.path.exists(inspect):
        raise Skip("inspector not built")
    env = dict(os.environ, SAFEPDF_TEXT_GLYPHS="1")
    env.pop("SAFEPDF_PAGE", None)
    p = subprocess.run([inspect, "--view", "text", "--json", path], capture_output=True,
                       timeout=TIMEOUT, env=env)
    out = p.stdout.decode("utf-8", "replace")
    if out.lstrip()[:1] != "{":
        if "unknown view" in (out + p.stderr.decode("utf-8", "replace")).lower():
            raise Skip("view not implemented")
        raise Bad("inspect exited %d without JSON: %s" % (
            p.returncode, p.stderr.decode("utf-8", "replace").strip()[:200]))
    if p.returncode != 0 and '"summary"' not in out:
        raise Bad("inspect exited %d: %s" % (p.returncode,
                  p.stderr.decode("utf-8", "replace")[:200]))
    return out


def run_stext(path):
    """MuPDF stext XML; partial output (a page failing) is kept with a note."""
    try:
        p = subprocess.run(["mutool", "draw", "-q", "-F", "stext", "-o", "-", path],
                           capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        raise Skip("mutool draw -F stext timed out after %d s" % TIMEOUT)
    out = p.stdout.decode("utf-8", "replace")
    if "<page" not in out:
        # One short reason: the first stderr line that is not MuPDF's ICC notice.
        err = [ln.strip() for ln in p.stderr.decode("utf-8", "replace").split("\n")
               if ln.strip() and "ICC support" not in ln]
        raise Skip("mutool draw -F stext failed (exit %d)%s" % (
            p.returncode, (": " + err[0][:100]) if err else ""))
    return out, ([] if p.returncode == 0 else ["mutool-exit-%d" % p.returncode])


def run_ctm(path):
    try:
        p = subprocess.run(["mutool", "run", _js_path(), path], capture_output=True,
                           timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return {}
    try:
        return load_ctm(p.stdout.decode("utf-8", "replace"))
    except ValueError:
        return {}


def ours_box_ctms(inspect, path):
    """Fallback page transforms from our `pages` view boxes (MuPDF's rule)."""
    p = subprocess.run([inspect, "--view", "pages", "--json", path], capture_output=True,
                       timeout=TIMEOUT)
    out = {}
    for line in p.stdout.decode("utf-8", "replace").split("\n"):
        try:
            rec = json.loads(line)
        except ValueError:
            continue
        if isinstance(rec, dict) and "index" in rec and "cropBox" in rec:
            out[int(rec["index"]) + 1] = mupdf_box_ctm(rec["cropBox"], rec.get("rotate", 0))
    return out


def check_file(inspect, path, min_within=None):
    """(status, detail, stats) for run.py; records DISTS / WORST."""
    if shutil.which("mutool") is None:
        raise Skip("tool missing: mutool")
    try:
        ours = run_ours(inspect, path)
        stext, notes = run_stext(path)
        ctms = run_ctm(path)
        n_ref = len(load_stext(stext)[0])
        if any(p not in ctms for p in range(1, n_ref + 1)):
            fb = ours_box_ctms(inspect, path)
            for p, m in fb.items():
                ctms.setdefault(p, m)
            notes = notes + ["ctm-ours"]
        rep = compare(ours, stext, ctms, path, min_within, notes)
    except Bad as e:
        return "error", str(e), {}
    except subprocess.TimeoutExpired as e:
        return "error", "timeout: %s" % e, {}
    for r in rep["rows"]:
        for x in r["pairs"]:
            DISTS.append(x[0])
            item = (x[0], path, r["page"], x[1], x[2], x[3], x[4])
            if len(WORST) < WORST_KEEP:
                heapq.heappush(WORST, item)
            elif item[0] > WORST[0][0]:
                heapq.heapreplace(WORST, item)
        r["pairs"] = []   # free memory; DISTS / WORST keep what run.py reports
    return rep["status"], format_report(rep), stats_of(rep)


# ---- self test ----------------------------------------------------------------------
FIXTURES = os.path.join(HERE, "fixtures")


def _fixture(name):
    with open(os.path.join(FIXTURES, name), encoding="utf-8") as fh:
        return fh.read()


def selftest():
    bad = []

    def want(cond, msg):
        if not cond:
            bad.append(msg)
            print("FAIL " + msg)

    # Inverse of the page transform, all four rotations of CropBox [30 40 500 760]
    # (ctm values printed by MuPDF 1.25.1 `page.getTransform()`).
    mupdf = {0: [1, 0, 0, -1, -30, 760], 90: [0, 1, 1, 0, -40, -30],
             180: [-1, 0, 0, 1, 500, -40], 270: [0, -1, -1, 0, 760, 500]}
    for rot, ctm in mupdf.items():
        want(mupdf_box_ctm([30, 40, 500, 760], rot) == ctm,
             "box ctm rot %d: %r != %r" % (rot, mupdf_box_ctm([30, 40, 500, 760], rot), ctm))
        a, b, c, d, e, f = ctm
        x, y = 72.0, 720.0
        X, Y = a * x + c * y + e, b * x + d * y + f
        rx, ry = invert(ctm, X, Y)
        want(abs(rx - x) < 1e-9 and abs(ry - y) < 1e-9, "invert rot %d" % rot)
    want(mupdf_box_ctm([0, 0, 612, 792], 450) == mupdf_box_ctm([0, 0, 612, 792], 90),
         "rotate 450 == 90")
    want(tolerance(5) == 1.0 and abs(tolerance(24) - 2.4) < 1e-12, "tolerance")
    # Parsing: synthetic spaces dropped, ligature tails, character references.
    pages, _ = load_stext('<page id="page2" width="10" height="20"><font name="F" size="8">'
                          '<char x="1" y="2" flags="4" c=" "/><char x="3" y="4" flags="0" '
                          'c="&#xfb01;"/><char x="5" y="6" flags="0" c="&amp;"/></font></page>')
    want(pages == {2: [("f", 3.0, 4.0, 8.0, False), ("i", 3.0, 4.0, 8.0, True),
                       ("&", 5.0, 6.0, 8.0, False)]}, "load_stext %r" % pages)
    # Fixture 1: our dump vs MuPDF on latin.pdf with CropBox [30 40 500 760] /Rotate 90.
    ctms = load_ctm(_fixture("positions_rot90.ctm.jsonl"))
    rep = compare(_fixture("positions_rot90.ours.jsonl"),
                  _fixture("positions_rot90.stext.xml"), ctms, "rot90")
    print("rot90:      %s: %s" % (rep["status"], format_report(rep)))
    want(rep["status"] == "agree" and rep["compared"] > 100 and rep["pct_within"] == 100.0
         and rep["max"] < 0.01 and rep["unmatched_ours"] == 0 and rep["unmatched_ref"] == 0,
         "rot90 fixture agrees exactly")
    # Same, without the transform: the identity-flip default must fail on rotation.
    rep0 = compare(_fixture("positions_rot90.ours.jsonl"),
                   _fixture("positions_rot90.stext.xml"), None, "rot90-noctm")
    want(rep0["pct_within"] < 10, "rot90 without ctm is far off (%.2f%%)" % rep0["pct_within"])
    # Fixture 2: MuPDF side edited: "W" moved by 3 pt, one "e" deleted, one "x" moved
    # by 0.9 pt (within), so 1 out of tolerance, 1 unmatched ours.
    rep2 = compare(_fixture("positions_rot90.ours.jsonl"),
                   _fixture("positions_diff.stext.xml"), ctms, "diff", min_within=100.0)
    print("diff:       %s: %s" % (rep2["status"], format_report(rep2)))
    worst = worst_of(rep2, 2)
    for t in worst:
        print(worst_line(t[0], "diff", *t[1:]))
    want(rep2["status"] == "disagree" and rep2["compared"] - rep2["within"] == 1
         and rep2["unmatched_ours"] == 1 and rep2["unmatched_ref"] == 0
         and abs(rep2["max"] - 3.0) < 0.01 and worst[0][2] == "W"
         and 0.85 < worst[1][0] < 0.95, "diff fixture")
    print("selftest: %s" % ("ok" if not bad else "%d failure(s)" % len(bad)))
    return 1 if bad else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description="Compare glyph positions offline")
    ap.add_argument("--ours", help="SAFEPDF_TEXT_GLYPHS=1 inspect --view text --json output")
    ap.add_argument("--ref", help="mutool draw -q -F stext -o - output")
    ap.add_argument("--ctm", help='page transforms, lines {"page": N, "ctm": [a,b,c,d,e,f]}')
    ap.add_argument("--min-within", type=float, default=None, metavar="PCT",
                    help="exit 1 when fewer than PCT %% of measured pairs are within tolerance")
    ap.add_argument("--json", metavar="OUT")
    ap.add_argument("--selftest", action="store_true", help="check against the fixtures")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    if not (a.ours and a.ref):
        ap.error("--ours and --ref are required (or --selftest)")
    with open(a.ours, encoding="utf-8") as f1, open(a.ref, encoding="utf-8") as f2:
        ctms = None
        if a.ctm:
            with open(a.ctm, encoding="utf-8") as f3:
                ctms = load_ctm(f3.read())
        try:
            rep = compare(f1.read(), f2.read(), ctms, a.ours, a.min_within)
        except (Bad, Skip) as e:
            print("error: %s" % e)
            return 2
    print("%s: %s" % (rep["status"], format_report(rep)))
    for t in worst_of(rep, 10):
        if t[0] > 0:
            print(worst_line(t[0], a.ours, *t[1:]))
    if a.json:
        out = dict(rep)
        out["rows"] = [{k: v for k, v in r.items() if k != "pairs"} for r in rep["rows"]]
        out["worst"] = [{"dist": t[0], "page": t[1], "char": t[2], "ours": list(t[3]),
                         "ref": list(t[4]), "size": t[5]} for t in worst_of(rep, 50)]
        with open(a.json, "w") as fh:
            json.dump(out, fh, indent=1)
    return 1 if rep["status"] == "disagree" else 0


if __name__ == "__main__":
    sys.exit(main())
