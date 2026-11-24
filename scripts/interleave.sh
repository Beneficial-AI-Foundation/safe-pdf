#!/usr/bin/env bash
# The interleave scenario (task 12.3, milestone M12: "an interleaved zoom/search/thumbnail CI
# scenario stays within published memory ceilings"; docs/viewer.md "Budgets and ceilings").
# Run from the repo root.
#   scripts/interleave.sh [--no-build] [--file PDF]
#
# Runs the viewer in smoke mode SAFEPDF_VIEWER_SMOKE_MODE=interleave (`Viewer.smokeInterleave`:
# rounds of zoom in, a frequent and a missing word searched, the thumbnails panel scrolled,
# page changes and zoom out, all overlapping) on a real paper (default the pinned corpus file
# corpus/files/arxiv-1706.03762.pdf; a generated two-page PDF when it is missing), and samples
# every 0.2 s the resident memory of the viewer and of every document worker it starts (`ps`;
# on Linux also VmHWM from /proc/PID/status, the kernel's own peak). Checks:
#   * viewer peak RSS <= Budget.ceilings.viewerRssMiB, each worker's <= workerRssMiB (the
#     numbers are read from SafePdf/Shell/App/Budget.lean, the published source);
#   * the viewer's own report: done, no reservation held at the end (no leak), the pool's peak
#     under its ceiling, nothing refused, no text request without a reservation, renders made.
# Headless: on macOS the viewer runs in the smoke tests' background mode (never activated,
# windows hidden; SAFEPDF_SMOKE_BG=1) and the sampler watches the front application: should
# the viewer ever become frontmost, it kills the processes it started (only those) and fails.
# Elsewhere it uses $DISPLAY when an X server answers, else `xvfb-run -a`.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

build=1
file="corpus/files/arxiv-1706.03762.pdf"
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) build=0 ;;
    --file) file="$2"; shift ;;
    *) echo "usage: $0 [--no-build] [--file PDF]" >&2; exit 2 ;;
  esac
  shift
done

if [ "$build" = 1 ]; then
  lake build viewer worker
fi
viewer="$repo/.lake/build/bin/viewer"
[ -x "$viewer" ] || { echo "interleave: $viewer not built" >&2; exit 1; }
[ -x "$repo/.lake/build/bin/worker" ] || { echo "interleave: no worker executable" >&2; exit 1; }

ceil() { sed -n "s/^ *$1 : Nat := \([0-9]*\)$/\1/p" SafePdf/Shell/App/Budget.lean; }
viewer_mib="$(ceil viewerRssMiB)"
worker_mib="$(ceil workerRssMiB)"
[ -n "$viewer_mib" ] && [ -n "$worker_mib" ] || { echo "interleave: ceilings not found in Budget.lean" >&2; exit 1; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
if [ ! -f "$file" ]; then
  echo "interleave: $file missing; using a generated two-page PDF (much smaller peaks)"
  python3 -I "$here/viewer-smoke-pdf.py" "$work/two.pdf"
  file="$work/two.pdf"
fi

wrap=(env)
if [ "$(uname -s)" = Darwin ]; then
  export SAFEPDF_SMOKE_BG=1
  echo "interleave: macOS, smoke background mode (never activated, windows hidden)"
elif [ -n "${DISPLAY:-}" ] && command -v xdpyinfo >/dev/null 2>&1 && xdpyinfo >/dev/null 2>&1; then
  echo "interleave: using DISPLAY=$DISPLAY"
elif command -v xvfb-run >/dev/null 2>&1; then
  wrap=(xvfb-run -a -s "-screen 0 1280x1024x24")
  echo "interleave: using xvfb-run"
else
  echo "interleave: no X display and no xvfb-run" >&2
  exit 1
fi

mkdir -p "$work/out"
echo "interleave: $file; ceilings: viewer ${viewer_mib} MiB, worker ${worker_mib} MiB"
SAFEPDF_VIEWER_VIEW= SAFEPDF_VIEWER_SMOKE="$work/out" SAFEPDF_VIEWER_SMOKE_MODE=interleave \
  timeout 300 "${wrap[@]}" "$viewer" "$file" >"$work/viewer.log" 2>&1 &
root=$!

# Sampler: every 0.2 s, the processes descending from $root (ps), their RSS and on Linux their
# VmHWM; the peak per process; on macOS the front application (abort rule above).
set +e
python3 -I -c '
import json, os, subprocess, sys, time
root, viewer, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
worker = os.path.join(os.path.dirname(viewer), "worker")
mac = sys.platform == "darwin"
peak, kind, samples, leak = {}, {}, 0, None
def tree():
    try:
        txt = subprocess.run(["ps", "-axo", "pid=,ppid=,rss=,stat=,command="], capture_output=True, text=True).stdout
    except OSError:
        return {}
    procs = {}
    for line in txt.splitlines():
        parts = line.split(None, 4)
        if len(parts) < 5: continue
        if parts[3].startswith("Z"): continue
        procs[int(parts[0])] = (int(parts[1]), int(parts[2]), parts[4])
    keep, frontier = {}, {root}
    while frontier:
        nxt = set()
        for pid, (ppid, rss, cmd) in procs.items():
            if ppid in frontier and pid not in keep:
                keep[pid] = (rss, cmd); nxt.add(pid)
        frontier = nxt
    if root in procs: keep[root] = (procs[root][1], procs[root][2])
    return keep
def hwm(pid):
    try:
        for l in open("/proc/%d/status" % pid):
            if l.startswith("VmHWM:"): return int(l.split()[1])
    except OSError:
        pass
    return 0
def front_pid():
    try:
        asn = subprocess.run(["lsappinfo", "front"], capture_output=True, text=True).stdout.strip()
        txt = subprocess.run(["lsappinfo", "info", "-only", "pid", asn], capture_output=True, text=True).stdout
    except OSError:
        return None
    digits = "".join(c for c in txt.split("=")[-1] if c.isdigit())
    return int(digits) if digits else None
while True:
    ps = tree()
    for pid, (rss, cmd) in ps.items():
        exe = cmd.split()[0] if cmd.split() else ""
        k = "viewer" if exe == viewer else "worker" if exe == worker else None
        if k is None: continue
        kind[pid] = k
        peak[pid] = max(peak.get(pid, 0), rss, hwm(pid))
    samples += 1
    if mac and ps:
        f = front_pid()
        if f is not None and f in ps:
            leak = "pid %d (%s)" % (f, ps[f][1])
            for pid in ps:
                try: os.kill(pid, 9)
                except OSError: pass
            break
    if root not in ps: break
    time.sleep(0.2)
json.dump({"samples": samples, "front_leak": leak,
           "peaks": [{"pid": p, "kind": kind[p], "kib": peak[p]} for p in sorted(peak)]},
          open(out, "w"))
' "$root" "$viewer" "$work/peaks.json"
sampler=$?
wait "$root"; rc=$?
set -e
cat "$work/viewer.log"
echo "--- interleave.txt"
cat "$work/out/interleave.txt" 2>/dev/null || echo "(missing)"
echo "---"
python3 -I -c '
import json, re, sys
peaks, report, vmib, wmib, rc, src = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
errs = []
p = json.load(open(peaks))
if p["front_leak"]: errs.append("the viewer became the front application (%s): processes killed" % p["front_leak"])
views = [x for x in p["peaks"] if x["kind"] == "viewer"]
works = [x for x in p["peaks"] if x["kind"] == "worker"]
vk = max([x["kib"] for x in views] or [0])
wk = max([x["kib"] for x in works] or [0])
print("interleave: %d samples; viewer peak %.1f MiB (ceiling %d); %d worker(s), peak %.1f MiB (ceiling %d)"
      % (p["samples"], vk / 1024, vmib, len(works), wk / 1024, wmib))
for x in works: print("interleave:   worker pid %d peak %.1f MiB" % (x["pid"], x["kib"] / 1024))
if not views: errs.append("the viewer was never sampled")
if not works: errs.append("no document worker was sampled")
if vk > vmib * 1024: errs.append("viewer peak %.1f MiB above %d MiB" % (vk / 1024, vmib))
for x in works:
    if x["kib"] > wmib * 1024: errs.append("worker %d peak %.1f MiB above %d MiB" % (x["pid"], x["kib"] / 1024, wmib))
if rc != 0: errs.append("viewer exit status %d" % rc)
if src != 0: errs.append("sampler exit status %d" % src)
try: lines = open(report, encoding="utf-8").read().splitlines()
except OSError: lines = []
v = dict(l.split(": ", 1) for l in lines if ": " in l)
def n(k):
    try: return int(v.get(k, "-1"))
    except ValueError: return -1
if "done" not in lines: errs.append("the scenario did not finish: %r" % v.get("error"))
else:
    if n("pool-used-end") != 0 or n("pool-held-end") != 0: errs.append("reservations held at the end (leak): %s bytes in %s" % (v.get("pool-used-end"), v.get("pool-held-end")))
    if not (0 < n("pool-peak") <= n("pool-ceiling")): errs.append("pool peak %s vs ceiling %s" % (v.get("pool-peak"), v.get("pool-ceiling")))
    if n("refused") != 0: errs.append("refused: %s" % v.get("refused"))
    if n("unreserved") != 0: errs.append("text requests without a reservation: %s" % v.get("unreserved"))
    if n("renders") <= 0: errs.append("no render")
    print("interleave: pool peak %.1f MiB of %.0f MiB; waits %s, lowered thumbnails %s, search stops %s, renders %s, thumbnails %s, spawns %s, timeouts %s"
          % (n("pool-peak") / 1048576, n("pool-ceiling") / 1048576, v.get("waits"), v.get("degraded"),
             v.get("search-stops"), v.get("renders"), v.get("thumbs-rendered"), v.get("spawns"), v.get("timeouts")))
for e in errs: print("FAIL: interleave: " + e, file=sys.stderr)
print("interleave: " + ("FAILED" if errs else "OK"))
sys.exit(1 if errs else 0)
' "$work/peaks.json" "$work/out/interleave.txt" "$viewer_mib" "$worker_mib" "$rc" "$sampler"
