#!/usr/bin/env bash
# Smoke test of the native viewer (tasks 8.2a, 8.2b; docs/viewer.md). Run from the repo root.
#   scripts/viewer-smoke.sh [--no-build]
#
# Builds `viewer` (needs Tcl/Tk development files), then runs it headless in smoke mode
# (SAFEPDF_VIEWER_SMOKE=DIR) on
#   1. a generated two-page PDF (scripts/viewer-smoke-pdf.py): page 1 must contain non-white
#      pixels, the viewer must reach page 2 through a Tk key event (from the prefetch cache),
#      and page 2 (/Rotate 90) must come out landscape; then, driven by key events: 100 %,
#      zoom in (125 %), zoom out twice (75 %), rotate (sizes and non-white pixel counts must
#      scale/swap accordingly); at 200 % the zoom must keep the window centre on the page
#      centre (C2 anchoring), Down/Next must scroll within the page, repeated Next must reach
#      page 2 and Prior at its top the bottom of page 1;
#   2. a malformed and a non-PDF file: the viewer must exit normally with an error in the
#      status line.
# Uses $DISPLAY when an X server answers there, else `xvfb-run -a`. Exit 0 on success.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

if [ "${1:-}" != "--no-build" ]; then
  lake build viewer
fi
viewer="$repo/.lake/build/bin/viewer"
[ -x "$viewer" ] || { echo "viewer-smoke: $viewer not built" >&2; exit 1; }

# Pick a display.
wrap=()
if [ -n "${DISPLAY:-}" ] && { command -v xdpyinfo >/dev/null 2>&1 && xdpyinfo >/dev/null 2>&1 \
    || [ -S "/tmp/.X11-unix/X${DISPLAY#*:}" ]; }; then
  echo "viewer-smoke: using DISPLAY=$DISPLAY"
elif command -v xvfb-run >/dev/null 2>&1; then
  wrap=(xvfb-run -a -s "-screen 0 1280x1024x24")
  echo "viewer-smoke: using xvfb-run"
else
  echo "viewer-smoke: no X display and no xvfb-run" >&2
  exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# run_viewer DIR FILE: smoke-mode run with a 60 s timeout.
run_viewer() {
  mkdir -p "$1"
  SAFEPDF_VIEWER_SMOKE="$1" timeout 60 "${wrap[@]}" "$viewer" "$2"
}

# ppm_stats FILE: prints "W H NONWHITE" for a binary PPM (P6, maxval 255).
ppm_stats() {
  python3 -I -c '
import sys
d = open(sys.argv[1], "rb").read()
parts, i = [], 0
while len(parts) < 4:
    while d[i:i+1].isspace(): i += 1
    if d[i:i+1] == b"#":
        while d[i:i+1] not in (b"\n", b""): i += 1
        continue
    j = i
    while not d[j:j+1].isspace(): j += 1
    parts.append(d[i:j]); i = j
i += 1
assert parts[0] == b"P6" and parts[3] == b"255", parts
w, h = int(parts[1]), int(parts[2])
px = d[i:i + 3 * w * h]
assert len(px) == 3 * w * h, "short pixel data"
nonwhite = sum(1 for k in range(0, len(px), 3) if px[k:k+3] != b"\xff\xff\xff")
print(w, h, nonwhite)
' "$1"
}

fail=0

# 1. Two-page vector PDF.
python3 -I "$here/viewer-smoke-pdf.py" "$work/two.pdf"
run_viewer "$work/out" "$work/two.pdf"
cat "$work/out/state.txt"
read -r w1 h1 n1 < <(ppm_stats "$work/out/page-1.ppm")
read -r w2 h2 n2 < <(ppm_stats "$work/out/page-2.ppm")
echo "page 1: ${w1}x${h1}, $n1 non-white pixels"
echo "page 2: ${w2}x${h2}, $n2 non-white pixels"
if [ "$n1" -lt $((w1 * h1 / 10)) ]; then echo "FAIL: page 1 is (nearly) blank" >&2; fail=1; fi
if [ "$n2" -lt 100 ]; then echo "FAIL: page 2 is (nearly) blank" >&2; fail=1; fi
if [ "$w2" -le "$h2" ]; then echo "FAIL: page 2 (/Rotate 90) is not landscape" >&2; fail=1; fi
grep -q '^page: 2/2$' "$work/out/state.txt" || { echo "FAIL: Next key did not reach page 2" >&2; fail=1; }
grep -q '^title: two.pdf - page 2/2 - safe-pdf$' "$work/out/state.txt" \
  || { echo "FAIL: unexpected window title" >&2; fail=1; }
grep -q '^status: .*from cache' "$work/out/state.txt" \
  || { echo "FAIL: page 2 was not prefetched into the cache" >&2; fail=1; }

# 1a. Zoom and rotation (task 8.2b): image sizes and ink scale with the zoom; rotation swaps.
read -r wa ha na < <(ppm_stats "$work/out/zoom-100.ppm")
read -r wi hi ni < <(ppm_stats "$work/out/zoom-in.ppm")
read -r wo ho no < <(ppm_stats "$work/out/zoom-out.ppm")
read -r wr hr nr < <(ppm_stats "$work/out/rot.ppm")
echo "100%: ${wa}x${ha} ($na); in: ${wi}x${hi} ($ni); out: ${wo}x${ho} ($no); rotated: ${wr}x${hr} ($nr)"
# within LO HI NUM DEN: LO <= NUM/DEN <= HI
within() { python3 -I -c 'import sys; lo, hi, n, d = map(float, sys.argv[1:]); sys.exit(0 if d > 0 and lo <= n / d <= hi else 1)' "$@"; }
within 1.22 1.28 "$wi" "$wa" || { echo "FAIL: zoom in is not 125%" >&2; fail=1; }
within 0.72 0.78 "$wo" "$wa" || { echo "FAIL: zoom out is not 75%" >&2; fail=1; }
within 1.45 1.68 "$ni" "$na" || { echo "FAIL: ink does not grow with zoom in" >&2; fail=1; }
within 0.50 0.62 "$no" "$na" || { echo "FAIL: ink does not shrink with zoom out" >&2; fail=1; }
if [ "$wr" != "$ho" ] || [ "$hr" != "$wo" ]; then echo "FAIL: rotation did not swap the sides" >&2; fail=1; fi
within 0.95 1.05 "$nr" "$no" || { echo "FAIL: rotated page has different ink" >&2; fail=1; }

# 1b. Scrolling and C2 anchoring at 200% (view.txt from the viewer's smoke mode).
cat "$work/out/view.txt"
python3 -I -c '
import sys
v = {}
for line in open(sys.argv[1]):
    k, _, val = line.partition(": ")
    v[k] = val.strip()
f = lambda k: [float(x) for x in v[k].split()]
errs = []
for ax in ("x0", "y0"):
    a, b = f(ax)
    if abs((a + b) / 2 - 0.5) > 0.01: errs.append(ax + ": zoom did not keep the centre fixed")
if not f("y-down")[0] > f("y0")[0]: errs.append("Down did not scroll")
if v["page-after-pagedown"] != "1" or not f("y-pagedown")[0] > f("y-down")[0]:
    errs.append("Next did not scroll within the page")
if v["page-after-pagedowns"] != "2" or f("y-page2")[0] != 0.0:
    errs.append("repeated Next did not reach the top of page 2")
if v["page-after-prior"] != "1" or f("y-prior")[1] != 1.0:
    errs.append("Prior at the top of page 2 did not reach the bottom of page 1")
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out/view.txt" || fail=1

# 1c. A file name full of Tcl metacharacters reaches the title verbatim (no script injection:
# every data word goes through the proved `Tcl.quote`).
odd='odd [exit 7] $HOME {x" \.pdf'
cp "$work/two.pdf" "$work/$odd"
run_viewer "$work/out-odd" "$work/$odd"
grep -qxF "title: $odd - page 2/2 - safe-pdf" "$work/out-odd/state.txt" \
  || { echo "FAIL: odd file name not shown verbatim" >&2; fail=1; }
echo "odd name: $(grep '^title:' "$work/out-odd/state.txt")"

# 2. Bad inputs: the viewer must not crash and must report the error.
printf 'this is not a PDF\n' > "$work/garbage.pdf"
for f in "$work/garbage.pdf" "Tests/adversarial/pages-kids-cycle.pdf" "$work/missing.pdf"; do
  d="$work/bad-$(basename "$f" .pdf)"
  if run_viewer "$d" "$f"; then
    status="$(grep '^status:' "$d/state.txt" || true)"
    echo "$(basename "$f"): $status"
    case "$status" in
      *cannot*|*error*|*no\ pages*|*page\ 1/*) ;;
      *) echo "FAIL: no error shown for $f" >&2; fail=1 ;;
    esac
  else
    echo "FAIL: viewer exited with an error on $f" >&2
    fail=1
  fi
done

if [ "$fail" = 0 ]; then echo "viewer-smoke: OK"; else echo "viewer-smoke: FAILED" >&2; fi
exit $fail
