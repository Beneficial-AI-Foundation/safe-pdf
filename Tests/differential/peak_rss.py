#!/usr/bin/env python3
"""Peak memory of rendering PDF files with the inspector (task 8.6).

Plan.md section 6 Phase 8 (M8: "daily-drivable viewer on the corpus"; the corpus check of
docs/viewer-corpus.md bounds the peak RSS at 1 GiB per file).  Stdlib only (python3 -I).

    python3 -I Tests/differential/peak_rss.py [--inspect BIN] [--dpi D] [--max-mib M] FILE...

Runs `inspect --view raster FILE` (every page, one process per file, PPMs not written) and
reports the peak resident set size of each process (`resource.getrusage(RUSAGE_CHILDREN)`
read in a fresh child interpreter per file, so the maxima do not mix) and its wall time.
With `--max-mib` the exit status is 1 when some file exceeds the bound.  Skips cleanly (exit
0) when the inspector is not built or no file exists.
"""
import argparse
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
INSPECT = os.path.join(ROOT, ".lake", "build", "bin", "inspect")

CHILD = r"""
import resource, subprocess, sys, time
t = time.time()
r = subprocess.run(sys.argv[1:], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
print("%d %.3f %d" % (resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss, time.time() - t,
                      r.returncode))
"""


def peak(inspect, path, dpi):
    """(peak RSS in MiB, seconds, exit status) of one render of `path`."""
    env = dict(os.environ, SAFEPDF_DPI=str(dpi))
    env.pop("SAFEPDF_RASTER_DIR", None)
    out = subprocess.run([sys.executable, "-I", "-c", CHILD, inspect, "--view", "raster", path],
                         env=env, stdout=subprocess.PIPE, text=True, check=True).stdout.split()
    return int(out[0]) / 1024.0, float(out[1]), int(out[2])


def main(argv=None):
    ap = argparse.ArgumentParser(description="Peak RSS of inspect --view raster per file")
    ap.add_argument("files", nargs="*")
    ap.add_argument("--inspect", default=INSPECT)
    ap.add_argument("--dpi", type=int, default=72)
    ap.add_argument("--max-mib", type=float, default=None)
    a = ap.parse_args(argv)
    if not os.path.exists(a.inspect):
        print("peak_rss: inspector not built (%s); skipped" % a.inspect)
        return 0
    files = [f for f in a.files if os.path.exists(f)]
    if not files:
        print("peak_rss: no files; skipped")
        return 0
    over = 0
    for f in files:
        mib, sec, rc = peak(a.inspect, f, a.dpi)
        bad = a.max_mib is not None and mib > a.max_mib
        over += bad
        print("%-40s %8.0f MiB %7.1f s  exit %d%s" % (os.path.basename(f), mib, sec, rc,
                                                      "  OVER" if bad else ""))
    if a.max_mib is not None:
        print("peak_rss: %d of %d files over %.0f MiB" % (over, len(files), a.max_mib))
    return 1 if over else 0


if __name__ == "__main__":
    sys.exit(main())
