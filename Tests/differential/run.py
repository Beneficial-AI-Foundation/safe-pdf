#!/usr/bin/env python3
"""Differential-test runner skeleton (Plan.md section 7, item 1).

Run as:  python3 -I Tests/differential/run.py [options]   (stdlib only)

A *comparator* pairs an external reference tool with our inspector view.
For every corpus file it produces a reference dump and our dump, normalizes
both, and compares.  Outcomes per (comparator, file):
  agree | known (documented divergence) | disagree | skipped (reason) | error
A missing reference tool or an unimplemented inspector view is a skip, never
a failure.  Exit status 1 only if a comparator that actually ran produced a
disagreement or an error, or if --min-compared N is given and, for each of the
selected `objects` / `pages` comparators, fewer than N files had at least one
object (page) compared, or if --min-similarity X is given and the `text`
comparator's corpus-wide similarity is below X, or if --min-within P is given
and fewer than P percent of the `positions` comparator's measured glyph pairs
are within tolerance, or fewer than P percent of the `pixels` comparator's
pages are within its perceptual threshold.

Known reference defects (`known-reference-defects.json`, docs/corpus.md): pages where
the reference tool is demonstrably wrong are left out of the `text-mupdf` / `positions`
corpus numbers and printed separately; the file's status becomes `known` (with the
reason) instead of `agree`.  An entry applies only to the file with its SHA-256 and only
to pages whose reference output still shows its `signature`; others print as STALE.
`--no-known` disables the mechanism; `--selftest` checks it offline.
"""
import argparse
import fnmatch
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from typing import Callable, List, Optional

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
INSPECT = os.path.join(ROOT, ".lake", "build", "bin", "inspect")
TOOL_TIMEOUT = 60


class Skip(Exception):
    """Raised by a dump function to skip with a reason."""


def run_tool(argv: List[str]) -> str:
    p = subprocess.run(argv, capture_output=True, timeout=TOOL_TIMEOUT)
    out = p.stdout.decode("utf-8", "replace")
    if p.returncode != 0:
        raise RuntimeError("%s exited %d: %s" % (argv[0], p.returncode,
                           p.stderr.decode("utf-8", "replace").strip()[:200]))
    return out


def our_dump(path: str, view: Optional[str]) -> str:
    """Invoke the inspector.  Unknown view -> Skip('view not implemented')."""
    if not os.path.exists(INSPECT):
        raise Skip("inspector not built: %s" % os.path.relpath(INSPECT, ROOT))
    argv = [INSPECT, path] + ([view] if view else [])
    p = subprocess.run(argv, capture_output=True, timeout=TOOL_TIMEOUT)
    out = p.stdout.decode("utf-8", "replace")
    err = p.stderr.decode("utf-8", "replace")
    if view:
        # Current inspector ignores unknown views and prints the default line.
        unknown = re.search(r"unknown view|unsupported view|no such view", out + err, re.I)
        default_only = re.fullmatch(r".*: \d+ bytes\s*", out, re.S) is not None
        if unknown or default_only:
            raise Skip("view not implemented")
    if p.returncode != 0:
        raise RuntimeError("inspect exited %d: %s" % (p.returncode, err.strip()[:200]))
    return out


@dataclass
class Comparator:
    name: str
    tools: List[str]                       # external executables required
    view: Optional[str]                    # inspector view (None = default view)
    reference: Callable[[str], str]        # file -> reference dump
    normalize: Callable[[str], str] = lambda s: s.strip()
    compare: Callable[[str, str], bool] = lambda a, b: a == b
    # Optional whole-file check: (path) -> (status, detail[, stats]); may raise
    # Skip.  `stats` (a dict of ints) is summed per comparator.
    custom: Optional[Callable[[str], tuple]] = None

    def missing_tool(self) -> Optional[str]:
        for t in self.tools:
            if shutil.which(t) is None:
                return t
        return None


# --- seed comparators --------------------------------------------------------

def _ref_size(path: str) -> str:
    return str(os.path.getsize(path))


def _norm_ours_size(s: str) -> str:
    # Loose on purpose: first integer followed by " bytes".  Will move to a
    # dedicated inspector view.
    m = re.search(r"(\d+) bytes", s)
    if not m:
        raise RuntimeError("no '<N> bytes' in inspector output: %r" % s[:100])
    return m.group(1)


def _load_objects_module():
    # python -I removes this directory from sys.path: load by file path.
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "objects_cmp", os.path.join(os.path.dirname(os.path.abspath(__file__)), "objects.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _objects_check(path: str):
    mod = _load_objects_module()
    try:
        return mod.check_file(INSPECT, path)
    except mod.Skip as e:
        raise Skip(str(e))


STREAMS_PER_FILE = 20   # set from --per-file in main()


def _load_streams_module():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "streams_cmp", os.path.join(os.path.dirname(os.path.abspath(__file__)), "streams.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _streams_check(path: str):
    mod = _load_streams_module()
    try:
        return mod.check_file(INSPECT, path, STREAMS_PER_FILE)
    except mod.Skip as e:
        raise Skip(str(e))


def _load_pages_module():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "pages_cmp", os.path.join(os.path.dirname(os.path.abspath(__file__)), "pages.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _pages_check(path: str):
    mod = _load_pages_module()
    try:
        return mod.check_file(INSPECT, path)
    except mod.Skip as e:
        raise Skip(str(e))


# ---- known reference defects ---------------------------------------------------
KNOWN_DEFECTS_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                  "known-reference-defects.json")
KNOWN_DEFECTS: list = []   # entries of the data file (set in main(); [] = mechanism off)
KNOWN_TEXT: dict = {}      # comparator -> [(sim, file, page, dist, maxlen, excerpt)] excluded
STALE: list = []           # (comparator, file, message): entries that no longer apply
_SIG_CACHE: dict = {}      # path -> list of MuPDF page texts
_SHA_CACHE: dict = {}      # path -> sha256 hex


def load_known_defects(path: str = KNOWN_DEFECTS_PATH) -> list:
    """The `defects` list of the data file, validated (ValueError on a malformed entry)."""
    with open(path, encoding="utf-8") as fh:
        data = json.load(fh)
    out = []
    for n, e in enumerate(data.get("defects", [])):
        for key in ("file", "sha256", "pages", "comparators", "signature", "reason",
                    "evidence"):
            if key not in e:
                raise ValueError("known defect %d: missing %r" % (n, key))
        if not all(isinstance(pg, int) and pg >= 1 for pg in e["pages"]):
            raise ValueError("known defect %d: pages must be positive ints" % n)
        unknown = [c for c in e["comparators"] if c not in KNOWN_COMPARATORS]
        if unknown:
            raise ValueError("known defect %d: comparator(s) %r not supported (have %s)"
                             % (n, unknown, ", ".join(KNOWN_COMPARATORS)))
        re.compile(e["signature"])
        out.append(e)
    return out


def verify_pages(entry: dict, ref_pages: List[str]):
    """-> (confirmed pages, stale pages): a listed page is confirmed when the reference
    text of that page (index page-1 of `ref_pages`) matches the entry's signature."""
    sig = re.compile(entry["signature"])
    ok, stale = [], []
    for pg in entry["pages"]:
        txt = ref_pages[pg - 1] if pg - 1 < len(ref_pages) else ""
        (ok if sig.search(txt) else stale).append(pg)
    return ok, stale


def _sha256(path: str) -> str:
    if path not in _SHA_CACHE:
        h = hashlib.sha256()
        with open(path, "rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        _SHA_CACHE[path] = h.hexdigest()
    return _SHA_CACHE[path]


def _mupdf_pages(path: str) -> List[str]:
    if path not in _SIG_CACHE:
        out = run_tool(["mutool", "draw", "-q", "-F", "txt", "-o", "-", path])
        _SIG_CACHE[path] = out.split("\f")
    return _SIG_CACHE[path]


def known_pages(comparator: str, path: str, ref_pages=None) -> dict:
    """{page: reason} of the confirmed known-defect pages of `path` for `comparator`.
    Mismatching hashes and pages without the signature are recorded in STALE."""
    out = {}
    for e in KNOWN_DEFECTS:
        if comparator not in e["comparators"] or os.path.basename(path) != e["file"]:
            continue
        if _sha256(path) != e["sha256"]:
            STALE.append((comparator, path, "sha256 differs from the known-defect entry; "
                          "entry ignored"))
            continue
        try:
            pages = ref_pages if ref_pages is not None else _mupdf_pages(path)
        except Exception as ex:  # noqa: BLE001 - no signature check, no exclusion
            STALE.append((comparator, path, "signature not checked (%s); entry ignored" % ex))
            continue
        ok, stale = verify_pages(e, pages)
        if stale:
            STALE.append((comparator, path, "pages %s no longer show the signature %r; "
                          "compared normally" % (stale, e["signature"])))
        for pg in ok:
            out[pg] = e["reason"]
    return out


def _ranges(pages) -> str:
    out, ps, i = [], sorted(pages), 0
    while i < len(ps):
        j = i
        while j + 1 < len(ps) and ps[j + 1] == ps[j] + 1:
            j += 1
        out.append("p%d" % ps[i] + ("" if i == j else "-%d" % ps[j]))
        i = j + 1
    return ",".join(out)


def split_text_known(rows: list, stats: dict, known: dict):
    """Move the text rows (sim, file, page, dist, maxlen, excerpt) of the pages in `known`
    out of `rows` and out of the per-file `stats` (pages, compared, pages_exact, dist,
    maxlen); the excluded rows are returned with the matching known_* stats."""
    keep, out = [], []
    for t in rows:
        (out if t[2] in known else keep).append(t)
    st = dict(stats)
    for t in out:
        st["pages"] -= 1
        st["compared"] -= 1
        st["pages_exact"] -= int(t[3] == 0)
        st["dist"] -= t[3]
        st["maxlen"] -= t[4]
    st["known_pages"] = len(out)
    st["known_dist"] = sum(t[3] for t in out)
    st["known_maxlen"] = sum(t[4] for t in out)
    return keep, out, st


TEXT_FOLD = True   # set from --no-fold in main()
# One text.py module instance per reference extractor, so each comparator keeps its own
# list of compared pages (`PAGES`) for its worst-pages report.
_TEXT_MODULES: dict = {}
# Comparator name -> reference extractor in text.py's REFERENCES.
TEXT_REFS = {"text": "pdftotext", "text-mupdf": "mupdf"}


def _load_text_module(ref: str = "pdftotext"):
    if ref not in _TEXT_MODULES:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "text_cmp_" + ref.replace("-", "_"),
            os.path.join(os.path.dirname(os.path.abspath(__file__)), "text.py"))
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _TEXT_MODULES[ref] = mod
    return _TEXT_MODULES[ref]


def _text_checker(ref: str, name: str):
    def check(path: str):
        mod = _load_text_module(ref)
        start = len(mod.PAGES)
        try:
            res = mod.check_file(INSPECT, path, TEXT_FOLD, ref=ref)
        except mod.Skip as e:
            raise Skip(str(e))
        if len(res) < 3 or not res[2] or name not in KNOWN_COMPARATORS:
            return res
        known = known_pages(name, path)
        if not known:
            return res
        keep, out, st = split_text_known(mod.PAGES[start:], res[2], known)
        if not out:
            return res
        del mod.PAGES[start:]
        mod.PAGES.extend(keep)
        KNOWN_TEXT.setdefault(name, []).extend(out)
        ml = st["known_maxlen"]
        detail = ("similarity %.4f over %d page(s) without the known pages; all pages: %s; "
                  "KNOWN reference defect on %s (excluded: similarity %.4f): %s" % (
                      1.0 if st["maxlen"] == 0 else 1 - st["dist"] / st["maxlen"], st["pages"],
                      res[1], _ranges([t[2] for t in out]),
                      1.0 if ml == 0 else 1 - st["known_dist"] / ml,
                      "; ".join(sorted({known[t[2]] for t in out}))))
        status = "known" if res[0] == "agree" else res[0]
        return status, detail, st
    return check


def text_summary(stats: dict, min_similarity: Optional[float], name: str = "text"):
    """Corpus-wide text report for comparator `name`: (lines, similarity or None, failed)."""
    tag = "%-8s" % name
    known = KNOWN_TEXT.get(name, [])
    klines = []
    if known:
        kd, kml = sum(t[3] for t in known), sum(t[4] for t in known)
        klines.append("%s known reference defects (EXCLUDED from the corpus similarity): %d "
                      "page(s) in %d file(s), similarity %.4f" % (
                          tag, len(known), len({t[1] for t in known}),
                          1.0 if kml == 0 else 1 - kd / kml))
        klines += ["  %.4f %s p%d (lev %d / %d)" % (t[0], t[1], t[2], t[3], t[4])
                   for t in sorted(known, key=lambda t: (t[1], t[2]))]
    if not stats.get("pages", 0):
        return ["%s no page compared" % tag] + klines, None, False
    maxlen = stats.get("maxlen", 0)
    sim = 1.0 if maxlen == 0 else 1 - stats.get("dist", 0) / maxlen
    lines = ["%s corpus similarity vs %s (character-weighted, 1 - sum lev / sum max len): %.4f "
             "over %d page(s), %d exact" % (tag, TEXT_REFS[name], sim, stats["pages"],
                                            stats.get("pages_exact", 0))]
    mod = _TEXT_MODULES.get(TEXT_REFS[name])
    if mod is not None and mod.PAGES:
        lines.append("%s worst pages:" % tag)
        lines += mod.worst_lines(mod.PAGES, 10)
    lines += klines
    fail = min_similarity is not None and sim < min_similarity
    if fail:
        lines.append("FAIL --min-similarity %.4f: corpus similarity %.4f" % (min_similarity, sim))
    return lines, sim, fail


_POSITIONS = []


def _load_positions_module():
    if not _POSITIONS:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "positions_cmp", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                          "positions.py"))
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _POSITIONS.append(mod)
    return _POSITIONS[0]


def _positions_check(path: str):
    mod = _load_positions_module()
    try:
        known = known_pages("positions", path) if KNOWN_DEFECTS else {}
        return mod.check_file(INSPECT, path, known=known)
    except mod.Skip as e:
        raise Skip(str(e))


_PIXELS = []
PIXELS_DPI = 72   # set from --dpi in main()


def _load_pixels_module():
    if not _PIXELS:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "pixels_cmp", os.path.join(os.path.dirname(os.path.abspath(__file__)), "pixels.py"))
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _PIXELS.append(mod)
    return _PIXELS[0]


def _pixels_check(path: str):
    mod = _load_pixels_module()
    mod.DPI = PIXELS_DPI
    try:
        return mod.check_file(INSPECT, path, dpi=PIXELS_DPI)
    except mod.Skip as e:
        raise Skip(str(e))


# Comparators that honour known-reference-defects.json.
KNOWN_COMPARATORS = ("text-mupdf", "positions")

# Comparators whose stats carry a "compared" count checked by --min-compared.
MIN_COMPARED = ("objects", "pages")


COMPARATORS = {
    c.name: c for c in [
        Comparator("size", [], None, _ref_size),
        # Placeholders: normalizers are identity until the views exist.
        Comparator("objects", ["qpdf"], "objects", lambda p: "", custom=_objects_check),
        # Flate decoder vs Python zlib (stdlib; no external tool needed).
        Comparator("streams", [], "streams", lambda p: "", custom=_streams_check),
        # Page count, refs, MediaBox, CropBox, Rotate vs qpdf (pages.py).
        Comparator("pages", ["qpdf"], "pages", lambda p: "", custom=_pages_check),
        # Page text vs poppler's pdftotext, normalized edit distance (text.py).
        Comparator("text", ["pdftotext"], "text", lambda p: "",
                   custom=_text_checker("pdftotext", "text")),
        # Page text vs MuPDF's `mutool draw -F txt`, same metric (text.py, ref "mupdf").
        Comparator("text-mupdf", ["mutool"], "text", lambda p: "",
                   custom=_text_checker("mupdf", "text-mupdf")),
        # Per-glyph origins vs MuPDF's `mutool draw -F stext` char origins (positions.py).
        Comparator("positions", ["mutool"], "text", lambda p: "", custom=_positions_check),
        # Rendered pages vs MuPDF `mutool draw -F pnm`, perceptual pixel diff (pixels.py).
        Comparator("pixels", ["mutool"], "raster", lambda p: "", custom=_pixels_check),
    ]
}
# Comparator-specific normalization of OUR dump (applied before compare).
OUR_NORMALIZERS = {"size": _norm_ours_size}


def short_diff(a: str, b: str, n: int = 160) -> str:
    a1, b1 = a[:n].replace("\n", "\\n"), b[:n].replace("\n", "\\n")
    return "ref=%r ours=%r" % (a1, b1)


def check(comp: Comparator, path: str):
    """Returns (status, detail) or (status, detail, stats)."""
    missing = comp.missing_tool()
    if missing:
        return "skipped", "tool missing: %s" % missing
    if comp.custom:
        try:
            return tuple(comp.custom(path))
        except Skip as e:
            return "skipped", str(e)
        except Exception as e:  # noqa: BLE001
            return "error", "%s: %s" % (type(e).__name__, e)
    try:
        ours = our_dump(path, comp.view)
        ref = comp.reference(path)
        on = OUR_NORMALIZERS.get(comp.name, comp.normalize)
        a, b = comp.normalize(ref), on(ours)
    except Skip as e:
        return "skipped", str(e)
    except Exception as e:  # noqa: BLE001 - report as error, keep going
        return "error", "%s: %s" % (type(e).__name__, e)
    if comp.compare(a, b):
        return "agree", ""
    return "disagree", short_diff(a, b)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--comparator", action="append", metavar="NAME",
                    help="comparator to run (repeatable; default: all). One of: " + ", ".join(COMPARATORS))
    ap.add_argument("--corpus", default=os.path.join(ROOT, "corpus", "files"))
    ap.add_argument("--files", help="glob (relative to cwd) selecting files; overrides --corpus")
    ap.add_argument("--limit", type=int, help="use at most N files")
    ap.add_argument("--json", metavar="OUT", help="write full results as JSON")
    ap.add_argument("--per-file", type=int, default=None, metavar="N",
                    help="streams comparator: byte-compare at most N streams per file "
                         "(0 = all; default 20, or all when --files is given)")
    ap.add_argument("--min-compared", type=int, default=0, metavar="N",
                    help="fail unless at least N files had >= 1 object (page) compared by "
                         "each selected objects / pages comparator (default 0 = no minimum)")
    ap.add_argument("--min-similarity", type=float, default=None, metavar="X",
                    help="text comparator: fail when the corpus-wide character-weighted "
                         "similarity is below X (default: report only)")
    ap.add_argument("--min-within", type=float, default=None, metavar="P",
                    help="positions comparator: fail when fewer than P percent of the "
                         "measured glyph pairs are within tolerance; pixels comparator: fail "
                         "when fewer than P percent of the pages are within the perceptual "
                         "threshold (default: report only)")
    ap.add_argument("--dpi", type=int, default=72, metavar="D",
                    help="pixels comparator: render resolution (default 72, as mutool)")
    ap.add_argument("--exclude", action="append", default=[], metavar="GLOB",
                    help="skip files matching GLOB (fnmatch on the path; repeatable)")
    ap.add_argument("--no-fold", action="store_true",
                    help="text comparator: do not fold dashes and quotes")
    ap.add_argument("--known", default=KNOWN_DEFECTS_PATH, metavar="JSON",
                    help="known reference defects data file (default: %(default)s)")
    ap.add_argument("--no-known", action="store_true",
                    help="ignore the known reference defects (count every page)")
    ap.add_argument("--selftest", action="store_true",
                    help="check the known-defect mechanism offline and exit")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()

    global STREAMS_PER_FILE, TEXT_FOLD, PIXELS_DPI, KNOWN_DEFECTS
    KNOWN_DEFECTS = [] if args.no_known else load_known_defects(args.known)
    PIXELS_DPI = args.dpi
    TEXT_FOLD = not args.no_fold
    STREAMS_PER_FILE = args.per_file if args.per_file is not None else (0 if args.files else 20)
    names = args.comparator or list(COMPARATORS)
    for n in names:
        if n not in COMPARATORS:
            ap.error("unknown comparator %r (have: %s)" % (n, ", ".join(COMPARATORS)))

    if args.files:
        files = sorted(glob.glob(args.files, recursive=True))
    elif os.path.isdir(args.corpus):
        files = sorted(os.path.join(args.corpus, f) for f in os.listdir(args.corpus)
                       if f.lower().endswith(".pdf"))
    else:
        files = []
    files = [f for f in files if os.path.isfile(f)
             and not any(fnmatch.fnmatch(f, g) for g in args.exclude)]
    if args.limit is not None:
        files = files[:args.limit]
    print("files: %d" % len(files))

    results = []
    counts = {n: {"agree": 0, "known": 0, "disagree": 0, "skipped": 0, "error": 0} for n in names}
    skip_reasons = {n: set() for n in names}
    stats = {n: {} for n in names}
    files_compared = {n: 0 for n in names}
    for f in files:
        for n in names:
            res = check(COMPARATORS[n], f)
            st, detail = res[0], res[1]
            extra = res[2] if len(res) > 2 else {}
            counts[n][st] += 1
            if st == "skipped":
                skip_reasons[n].add(detail)
            for k, v in extra.items():
                stats[n][k] = stats[n].get(k, 0) + v
            if extra.get("compared", 0) > 0:
                files_compared[n] += 1
            r = {"comparator": n, "file": f, "status": st, "detail": detail}
            if extra:
                r["stats"] = extra
            results.append(r)

    bad = False
    for n in names:
        c = counts[n]
        extra = ""
        if skip_reasons[n]:
            extra = "  [skipped (%s)]" % "; ".join(sorted(skip_reasons[n]))
        print("%-8s agree=%d known=%d disagree=%d skipped=%d error=%d%s" %
              (n, c["agree"], c["known"], c["disagree"], c["skipped"], c["error"], extra))
        if stats[n]:
            print("%-8s totals: %s; files with >=1 item compared: %d" % (
                n, " ".join("%s=%d" % kv for kv in sorted(stats[n].items())), files_compared[n]))
        if c["disagree"] or c["error"]:
            bad = True
    for r in results:
        if r["status"] == "known":
            print("KNOWN %s %s: %s" % (r["comparator"], r["file"], r["detail"]))
    for comp, f, msg in STALE:
        print("STALE known-defect entry %s %s: %s" % (comp, f, msg))
    for r in results:
        if r["status"] in ("disagree", "error"):
            print("%s %s %s: %s" % (r["status"].upper(), r["comparator"], r["file"], r["detail"]))

    text_reports = {}
    for tname in ("text", "text-mupdf"):
        if tname not in names:
            continue
        lines, sim, fail = text_summary(stats[tname], args.min_similarity, tname)
        for ln in lines:
            print(ln)
        bad = bad or fail
        mod = _TEXT_MODULES.get(TEXT_REFS[tname])
        text_reports[tname] = {
            "reference": TEXT_REFS[tname],
            "similarity": sim, "min_similarity": args.min_similarity,
            "worst_pages": [] if mod is None else [
                {"similarity": t[0], "file": t[1], "page": t[2], "lev": t[3], "maxlen": t[4],
                 "excerpt": t[5]}
                for t in sorted(mod.PAGES, key=lambda t: (t[0], -t[4]))[:50] if t[3] > 0],
            "known_pages": [
                {"similarity": t[0], "file": t[1], "page": t[2], "lev": t[3], "maxlen": t[4]}
                for t in KNOWN_TEXT.get(tname, [])]}

    positions_report = {}
    if "positions" in names:
        mod = _load_positions_module()
        lines, positions_report, fail = mod.summary_lines(stats["positions"], args.min_within)
        for ln in lines:
            print(ln)
        bad = bad or fail

    pixels_report = {}
    if "pixels" in names:
        mod = _load_pixels_module()
        lines, pixels_report, fail = mod.summary_lines(stats["pixels"], args.min_within)
        for ln in lines:
            print(ln)
        bad = bad or fail

    if args.min_compared > 0:
        checked = [n for n in names if n in MIN_COMPARED]
        if not checked:
            print("FAIL --min-compared %d: neither the objects nor the pages comparator was selected"
                  % args.min_compared)
            bad = True
        for n in checked:
            got = files_compared.get(n, 0)
            if got < args.min_compared:
                print("FAIL --min-compared %d: only %d file(s) had >= 1 item compared by '%s'"
                      % (args.min_compared, got, n))
                bad = True

    if args.json:
        with open(args.json, "w") as fh:
            out = {"counts": counts, "stats": stats, "files_compared": files_compared,
                   "min_compared": args.min_compared, "results": results,
                   "stale_known_defects": [{"comparator": c, "file": f, "detail": m}
                                           for c, f, m in STALE]}
            out.update(text_reports)
            if "positions" in names:
                out["positions"] = positions_report
            if "pixels" in names:
                out["pixels"] = pixels_report
            json.dump(out, fh, indent=1)
    return 1 if bad else 0


def selftest() -> int:
    """Offline checks of the known-reference-defect mechanism (no tools needed)."""
    global KNOWN_DEFECTS
    bad = []

    def want(cond, msg):
        if not cond:
            bad.append(msg)
            print("FAIL " + msg)

    # The committed data file loads and every entry is well-formed.
    entries = load_known_defects()
    want(len(entries) >= 1 and all(len(e["sha256"]) == 64 for e in entries),
         "data file loads")
    # Signature check: only pages whose reference text shows it are confirmed.
    e = {"file": "x.pdf", "sha256": "0" * 64, "pages": [1, 2, 4], "comparators": ["positions"],
         "signature": "[\\u0001-\\u0008]", "reason": "r", "evidence": "e"}
    ok, stale = verify_pages(e, ["T\x02able", "no digits lost", "x", "\x05"])
    want(ok == [1, 4] and stale == [2], "verify_pages %r %r" % (ok, stale))
    # known_pages: hash gate and signature gate (fake file, fake reference pages).
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, "x.pdf")
        with open(f, "wb") as fh:
            fh.write(b"%PDF-1.4 test")
        saved = KNOWN_DEFECTS
        try:
            KNOWN_DEFECTS = [dict(e, sha256=hashlib.sha256(b"%PDF-1.4 test").hexdigest())]
            STALE.clear()
            got = known_pages("positions", f, ref_pages=["a\x01", "b", "c", "d\x03"])
            want(got == {1: "r", 4: "r"} and len(STALE) == 1, "known_pages %r %r" % (got, STALE))
            want(known_pages("text-mupdf", f, ref_pages=["\x01"] * 4) == {},
                 "comparator not listed in the entry")
            KNOWN_DEFECTS = [e]   # wrong hash
            STALE.clear()
            want(known_pages("positions", f, ref_pages=["\x01"] * 4) == {} and len(STALE) == 1,
                 "hash mismatch ignores the entry")
        finally:
            KNOWN_DEFECTS = saved
            STALE.clear()
            _SHA_CACHE.clear()
    # Text split: the known page leaves the per-file stats, the others stay.
    rows = [(1.0, "f", 1, 0, 10, ""), (0.5, "f", 2, 5, 10, "x"), (0.9, "f", 3, 1, 10, "y")]
    stats = {"pages": 3, "compared": 3, "pages_exact": 1, "dist": 6, "maxlen": 30}
    keep, out, st = split_text_known(rows, stats, {2: "r"})
    want([t[2] for t in keep] == [1, 3] and [t[2] for t in out] == [2]
         and st["pages"] == 2 and st["compared"] == 2 and st["pages_exact"] == 1
         and st["dist"] == 1 and st["maxlen"] == 20 and st["known_pages"] == 1
         and st["known_dist"] == 5 and st["known_maxlen"] == 10, "split_text_known %r" % st)
    want(_ranges([51, 60, 61, 62, 72]) == "p51,p60-62,p72", "_ranges")
    print("selftest: %s" % ("ok" if not bad else "%d failure(s)" % len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
