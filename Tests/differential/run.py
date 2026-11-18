#!/usr/bin/env python3
"""Differential-test runner skeleton (Plan.md section 7, item 1).

Run as:  python3 -I Tests/differential/run.py [options]   (stdlib only)

A *comparator* pairs an external reference tool with our inspector view.
For every corpus file it produces a reference dump and our dump, normalizes
both, and compares.  Outcomes per (comparator, file):
  agree | disagree | skipped (reason) | error
A missing reference tool or an unimplemented inspector view is a skip, never
a failure.  Exit status 1 only if a comparator that actually ran produced a
disagreement or an error.
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


def _placeholder(tool_argv):
    def ref(path):
        return run_tool([a.replace("{file}", path) for a in tool_argv])
    return ref


COMPARATORS = {
    c.name: c for c in [
        Comparator("size", [], None, _ref_size),
        # Placeholders: normalizers are identity until the views exist.
        Comparator("objects", ["qpdf"], "objects",
                   _placeholder(["qpdf", "--json", "{file}"])),
        Comparator("pages", ["mutool"], "pages",
                   _placeholder(["mutool", "info", "{file}"])),
        Comparator("text", ["pdftotext"], "text",
                   _placeholder(["pdftotext", "-layout", "{file}", "-"])),
    ]
}
# Comparator-specific normalization of OUR dump (applied before compare).
OUR_NORMALIZERS = {"size": _norm_ours_size}


def short_diff(a: str, b: str, n: int = 160) -> str:
    a1, b1 = a[:n].replace("\n", "\\n"), b[:n].replace("\n", "\\n")
    return "ref=%r ours=%r" % (a1, b1)


def check(comp: Comparator, path: str):
    """Returns (status, detail)."""
    missing = comp.missing_tool()
    if missing:
        return "skipped", "tool missing: %s" % missing
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
    args = ap.parse_args(argv)

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
    counts = {n: {"agree": 0, "disagree": 0, "skipped": 0, "error": 0} for n in names}
    skip_reasons = {n: set() for n in names}
    for f in files:
        for n in names:
            st, detail = check(COMPARATORS[n], f)
            counts[n][st] += 1
            if st == "skipped":
                skip_reasons[n].add(detail)
            results.append({"comparator": n, "file": f, "status": st, "detail": detail})

    bad = False
    for n in names:
        c = counts[n]
        extra = ""
        if skip_reasons[n]:
            extra = "  [skipped (%s)]" % "; ".join(sorted(skip_reasons[n]))
        print("%-8s agree=%d disagree=%d skipped=%d error=%d%s" %
              (n, c["agree"], c["disagree"], c["skipped"], c["error"], extra))
        if c["disagree"] or c["error"]:
            bad = True
    for r in results:
        if r["status"] in ("disagree", "error"):
            print("%s %s %s: %s" % (r["status"].upper(), r["comparator"], r["file"], r["detail"]))

    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"counts": counts, "results": results}, fh, indent=1)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
