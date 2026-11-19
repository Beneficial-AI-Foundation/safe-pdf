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
comparator's corpus-wide similarity is below X.
"""
import argparse
import fnmatch
import glob
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


def _text_checker(ref: str):
    def check(path: str):
        mod = _load_text_module(ref)
        try:
            return mod.check_file(INSPECT, path, TEXT_FOLD, ref=ref)
        except mod.Skip as e:
            raise Skip(str(e))
    return check


def text_summary(stats: dict, min_similarity: Optional[float], name: str = "text"):
    """Corpus-wide text report for comparator `name`: (lines, similarity or None, failed)."""
    tag = "%-8s" % name
    if not stats.get("pages", 0):
        return ["%s no page compared" % tag], None, False
    maxlen = stats.get("maxlen", 0)
    sim = 1.0 if maxlen == 0 else 1 - stats.get("dist", 0) / maxlen
    lines = ["%s corpus similarity vs %s (character-weighted, 1 - sum lev / sum max len): %.4f "
             "over %d page(s), %d exact" % (tag, TEXT_REFS[name], sim, stats["pages"],
                                            stats.get("pages_exact", 0))]
    mod = _TEXT_MODULES.get(TEXT_REFS[name])
    if mod is not None and mod.PAGES:
        lines.append("%s worst pages:" % tag)
        lines += mod.worst_lines(mod.PAGES, 10)
    fail = min_similarity is not None and sim < min_similarity
    if fail:
        lines.append("FAIL --min-similarity %.4f: corpus similarity %.4f" % (min_similarity, sim))
    return lines, sim, fail


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
        Comparator("text", ["pdftotext"], "text", lambda p: "", custom=_text_checker("pdftotext")),
        # Page text vs MuPDF's `mutool draw -F txt`, same metric (text.py, ref "mupdf").
        Comparator("text-mupdf", ["mutool"], "text", lambda p: "",
                   custom=_text_checker("mupdf")),
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
    ap.add_argument("--no-fold", action="store_true",
                    help="text comparator: do not fold dashes and quotes")
    args = ap.parse_args(argv)

    global STREAMS_PER_FILE, TEXT_FOLD
    TEXT_FOLD = not args.no_fold
    STREAMS_PER_FILE = args.per_file if args.per_file is not None else (0 if args.files else 20)
    names = args.comparator or list(COMPARATORS)
    for n in names:
        if n not in COMPARATORS:
            ap.error("unknown comparator %r (have: %s)" % (n, ", ".join(COMPARATORS)))

    if args.files:
        files = sorted(glob.glob(args.files))
    elif os.path.isdir(args.corpus):
        files = sorted(os.path.join(args.corpus, f) for f in os.listdir(args.corpus)
                       if f.lower().endswith(".pdf"))
    else:
        files = []
    files = [f for f in files if os.path.isfile(f)]
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
                for t in sorted(mod.PAGES, key=lambda t: (t[0], -t[4]))[:50] if t[3] > 0]}

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
                   "min_compared": args.min_compared, "results": results}
            out.update(text_reports)
            json.dump(out, fh, indent=1)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
