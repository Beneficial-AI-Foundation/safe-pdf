#!/usr/bin/env python3
"""Compare two test-runner outputs suite by suite (task 12.6).  Run as:

  python3 -I scripts/suite-diff.py COMPILED INTERPRETED [--suites a,b,c] [--ignore a,b]

Both files have the format of `lake exe tests`: each suite's own lines, then its summary line
`[PASS] name (n failures)` or `[FAIL] name (n failures)`.  The output is split into one block
per suite (the lines since the previous summary line, plus the summary line).  Wall-clock
figures ("12.345 ms", "7 ms", "1.2 s") are replaced by "<t>" before comparing, since they
differ between any two runs; every other character must agree.

--suites   compare only these suites (default: every suite of INTERPRETED); each must
           appear in both files.
--ignore   suites whose block may differ (reported, not failures): use only for suites
           whose output depends on wall-clock time beyond the figures normalized above,
           and say why at the call site.

Exit status 0 when every compared block agrees, 1 otherwise, 2 on usage errors.  Stdlib only.
"""
import difflib
import re
import sys

SUMMARY = re.compile(r"^\[(PASS|FAIL)\] (\S+) \((\d+) failures\)$")
TIMING = re.compile(r"\b\d+(?:\.\d+)?(?: ?)(ms|µs|us|ns|s)\b")


def blocks(path):
    """Ordered mapping suite name -> list of normalized lines; plus stray trailing lines."""
    out, cur = {}, []
    with open(path, encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = TIMING.sub(r"<t> \1", raw.rstrip("\n"))
            cur.append(line)
            m = SUMMARY.match(line)
            if m:
                out[m.group(2)] = cur
                cur = []
    return out, cur


def main(argv):
    pos, opts = [], {}
    i = 0
    while i < len(argv):
        if argv[i] in ("--suites", "--ignore"):
            if i + 1 >= len(argv):
                print("suite-diff: %s needs a value" % argv[i], file=sys.stderr)
                return 2
            opts[argv[i]] = [s for s in argv[i + 1].split(",") if s]
            i += 2
        elif argv[i].startswith("--"):
            print("suite-diff: unknown option %s" % argv[i], file=sys.stderr)
            return 2
        else:
            pos.append(argv[i])
            i += 1
    if len(pos) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    comp, comp_rest = blocks(pos[0])
    interp, interp_rest = blocks(pos[1])
    names = opts.get("--suites") or list(interp)
    ignore = set(opts.get("--ignore", []))
    bad = 0
    for n in names:
        if n not in comp or n not in interp:
            where = " and ".join(w for w, d in (("compiled", comp), ("interpreted", interp)) if n not in d)
            print("MISSING %s: no summary line in the %s output" % (n, where))
            bad += 1
            continue
        if comp[n] == interp[n]:
            print("same    %s (%d lines)" % (n, len(comp[n])))
            continue
        tag = "IGNORED" if n in ignore else "DIFFER "
        print("%s %s" % (tag, n))
        for d in difflib.unified_diff(comp[n], interp[n], "compiled", "interpreted", lineterm="", n=1):
            print("    " + d)
        if n not in ignore:
            bad += 1
    for label, rest in (("compiled", comp_rest), ("interpreted", interp_rest)):
        if [ln for ln in rest if ln.strip()]:
            print("NOTE: %d trailing %s line(s) after the last summary line" % (len(rest), label))
    if interp_rest != comp_rest and not opts.get("--suites"):
        print("DIFFER  trailing lines after the last summary line")
        bad += 1
    print("suite-diff: %d suite(s) compared, %d differing or missing" % (len(names), bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
