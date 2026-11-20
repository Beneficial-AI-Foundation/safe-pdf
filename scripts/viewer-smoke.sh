#!/usr/bin/env bash
# Smoke test of the native viewer (tasks 8.2a–8.2d; docs/viewer.md). Run from the repo root.
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
#   1d. a generated two-page text PDF (SAFEPDF_VIEWER_SMOKE_MODE=text): select all + copy
#      gives the page text, double click a word, drag a range, search across pages (8.2c);
#   1e. a generated three-page PDF with page labels, an outline, an internal and a URI link
#      (SAFEPDF_VIEWER_SMOKE_MODE=nav): outline clicks, link hover/click, back/forward, the
#      URI confirmation dialog and clipboard, Ctrl+G with labels, F9 (8.2d);
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

# 1d. Selection, copy and search (task 8.2c) on a generated two-page text PDF (Helvetica):
# Ctrl+A + Ctrl+C must put the page text (as the inspector's text view extracts it) on the
# clipboard; a double click on "safe" copies "safe"; a drag from the first glyph to the end of
# "world" copies "Hello safe world"; searching "ZEBRA  crossing" moves to page 2 and reports
# hit 1/1; an absent phrase reports "not found".
python3 -I -c '
import sys
# The renderer does not paint non-embedded standard fonts, so a black marker rectangle lies
# under "safe": x = 72 + 18 * 2.556 (Helvetica widths of "Hello ") = 118.008, width
# 18 * 1.890 = 34.02, from the baseline up 0.7 em.
pages = [b"0 g 118.008 700 34.02 12.6 re f\n"
         b"BT /F1 18 Tf 72 700 Td (Hello safe world) Tj 0 -30 Td (Second line here) Tj ET\n",
         b"BT /F1 18 Tf 72 700 Td (A zebra crossing on page two) Tj ET\n"]
objs = [b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R 5 0 R] /Count 2 >>"]
for i, c in enumerate(pages):
    objs.append(b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents %d 0 R "
                b"/Resources << /Font << /F1 7 0 R >> >> >>" % (4 + 2 * i))
    objs.append(b"<< /Length %d >>\nstream\n" % len(c) + c + b"endstream")
objs.append(b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>")
out = bytearray(b"%PDF-1.4\n")
offs = []
for i, body in enumerate(objs, start=1):
    offs.append(len(out))
    out += b"%d 0 obj\n" % i + body + b"\nendobj\n"
x = len(out)
out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
out += b"".join(b"%010d 00000 n \n" % o for o in offs)
out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, x)
open(sys.argv[1], "wb").write(out)
' "$work/text.pdf"
mkdir -p "$work/out-text"
SAFEPDF_VIEWER_SMOKE_MODE=text run_viewer "$work/out-text" "$work/text.pdf"
SAFEPDF_PAGE=1 "$repo/.lake/build/bin/inspect" --json --view text "$work/text.pdf" > "$work/text.json" || true
for f in clip-all word drag; do echo "$f: $(cat "$work/out-text/$f.txt" | tr '\n' '|')"; done
cat "$work/out-text/sel.txt" "$work/out-text/find.txt"
python3 -I -c '
import json, sys
d = sys.argv[1]
expected = None
for line in open(sys.argv[2]):
    o = json.loads(line)
    if o.get("page") == 1: expected = o["text"]
rd = lambda n: open(d + "/" + n, encoding="utf-8").read()
kv = lambda n: dict(l.split(": ", 1) for l in rd(n).splitlines() if ": " in l)
errs = []
if expected is None or not expected.strip(): errs.append("inspector extracted no text for page 1")
elif rd("clip-all.txt") != expected:
    errs.append("select-all + copy %r != page text %r" % (rd("clip-all.txt"), expected))
if rd("word.txt") != "safe": errs.append("double click did not select the word: %r" % rd("word.txt"))
if rd("drag.txt") != "Hello safe world": errs.append("drag selection: %r" % rd("drag.txt"))
s = kv("sel.txt")
if int(s["sel-items"]) < 2: errs.append("select-all drew no highlight per line")
f = kv("find.txt")
if f["page"] != "2": errs.append("search did not move to page 2")
if "hit 1/1 on page 2" not in f["status"]: errs.append("search status: " + f["status"])
if int(f["hit-items"]) < 1: errs.append("search hit not highlighted")
if "hit 1/1 on page 2 (wrapped)" not in f["status-f3"]: errs.append("F3: " + f["status-f3"])
if "hit 1/1 on page 2" not in f["status-shift-f3"]: errs.append("Shift+F3: " + f["status-shift-f3"])
if "not found" not in f["status-absent"]: errs.append("absent query: " + f["status-absent"])
if f["hit-items-closed"] != "0": errs.append("closing the search left highlights")
# The highlight of "safe" (canvas coordinates, minus the image offset) must cover the marker
# under the word in the rendered page (an independent check of the page <-> device mapping):
# >= 95% of all dark pixels of the page inside it, >= 50% of it dark.
r = rd("word-rect.txt").split("\n")
x0, y0, x1, y1 = (float(v) for v in r[0].split()[:4])
ix, iy = (int(v) for v in r[1].split())
p = open(d + "/text-page-1.ppm", "rb").read()
magic, size, _, px = p.split(b"\n", 3)  # Tk writes "P6\nW H\n255\n" + pixels
w, h = (int(v) for v in size.split())
dark = tot = 0
for y in range(max(0, int(y0) - iy), min(h, int(y1) - iy)):
    for x in range(max(0, int(x0) - ix), min(w, int(x1) - ix)):
        tot += 1
        k = 3 * (y * w + x)
        dark += px[k] < 128
alldark = sum(1 for k in range(0, 3 * w * h, 3) if px[k] < 128)
if tot == 0 or alldark == 0 or dark * 2 < tot or dark * 100 < 95 * alldark:
    errs.append("word highlight %s does not cover the marker (%d/%d dark, %d on the page)"
                % (r[0], dark, tot, alldark))
print("word highlight %s: %d/%d dark pixels (%d on the page)" % (r[0], dark, tot, alldark))
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-text" "$work/text.json" || fail=1

# 1e. Outline, links, history, page labels (task 8.2d) on a generated three-page PDF labelled
# i, ii, 1 (SAFEPDF_VIEWER_SMOKE_MODE=nav): the outline panel opens with Intro, Chapter (a
# UTF-16 title) > Section; hovering the internal link shows a hand cursor and its target, a
# click jumps to page 3, Alt+Left/Alt+Right walk the history; the URI link (an address full
# of Tcl metacharacters) shows the confirmation dialog with the exact address, which (auto-
# confirmed) lands on the clipboard; clicking Section goes to page 2 (named destination),
# Chapter at 200 % to page 3 scrolled to its /XYZ top 400; Ctrl+G accepts labels ("ii" ->
# page 2, the label "1" -> page 3) and rejects unknown ones; F9 hides the outline.
python3 -I -c '
import sys
uri = b"https://example.org/p?q=[exit_7]&v=$HOME{x}\\"
pages = [b"0.8 g 72 600 228 40 re f 0.6 g 72 500 228 40 re f\n",
         b"0.5 g 100 100 200 200 re f\n",
         b"0 g 72 380 400 20 re f\n"]
objs = {
    1: b"<< /Type /Catalog /Pages 2 0 R /Outlines 9 0 R /Names << /Dests 13 0 R >> "
       b"/PageLabels << /Nums [0 << /S /r >> 2 << /S /D >>] >> >>",
    2: b"<< /Type /Pages /Kids [3 0 R 5 0 R 7 0 R] /Count 3 >>",
    9: b"<< /Type /Outlines /First 10 0 R /Last 11 0 R /Count 3 >>",
    10: b"<< /Title (Intro) /Parent 9 0 R /Next 11 0 R /Dest [3 0 R /Fit] >>",
    11: b"<< /Title <FEFF0043006800610070007400650072> /Parent 9 0 R /Prev 10 0 R "
        b"/First 12 0 R /Last 12 0 R /Count 1 /Dest [7 0 R /XYZ 0 400 0] >>",
    12: b"<< /Title (Section) /Parent 11 0 R /Dest (sec) >>",
    13: b"<< /Names [(sec) [5 0 R /XYZ null null null]] >>",
    14: b"<< /Type /Annot /Subtype /Link /Rect [72 600 300 640] /Border [0 0 0] "
        b"/Dest [7 0 R /Fit] >>",
    15: b"<< /Type /Annot /Subtype /Link /Rect [72 500 300 540] /Border [0 0 0] "
        b"/A << /S /URI /URI (" + uri.replace(b"\\", b"\\\\") + b") >> >>",
}
for i, c in enumerate(pages):
    annots = b" /Annots [14 0 R 15 0 R]" if i == 0 else b""
    objs[3 + 2 * i] = (b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents %d 0 R"
                       % (4 + 2 * i) + annots + b" >>")
    objs[4 + 2 * i] = b"<< /Length %d >>\nstream\n" % len(c) + c + b"endstream"
n = max(objs) + 1
out = bytearray(b"%PDF-1.4\n")
offs = {}
for k in sorted(objs):
    offs[k] = len(out)
    out += b"%d 0 obj\n" % k + objs[k] + b"\nendobj\n"
x = len(out)
out += b"xref\n0 %d\n0000000000 65535 f \n" % n
out += b"".join(b"%010d 00000 n \n" % offs[k] for k in range(1, n))
out += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (n, x)
open(sys.argv[1], "wb").write(out)
open(sys.argv[2], "wb").write(uri)
' "$work/nav.pdf" "$work/nav-uri.txt"
mkdir -p "$work/out-nav"
SAFEPDF_VIEWER_SMOKE_MODE=nav run_viewer "$work/out-nav" "$work/nav.pdf"
cat "$work/out-nav/nav.txt"
echo "uri shown: $(cat "$work/out-nav/uri-shown.txt"); clipboard: $(cat "$work/out-nav/uri-clip.txt")"
python3 -I -c '
import sys
d = sys.argv[1]
uri = open(sys.argv[2], encoding="ascii").read()
v = dict(l.split(": ", 1) for l in open(d + "/nav.txt", encoding="utf-8").read().splitlines()
         if ": " in l)
rd = lambda n: open(d + "/" + n, encoding="utf-8").read()
want = {
    "title0": "nav.pdf - page i (1/3) - safe-pdf",
    "outline-shown": "true",
    "outline-titles": "Intro|Chapter|Section",
    "outline-depths": "[0, 0, 1]",
    "links-page1": "2",
    "cursor-internal": "hand2",
    "status-hover-internal": "go to page 1 (3/3)",
    "page-after-link": "3",
    "title-after-link": "nav.pdf - page 1 (3/3) - safe-pdf",
    "page-after-back": "1",
    "page-after-forward": "3",
    "page-after-back2": "1",
    "cursor-uri": "hand2",
    "status-hover-uri": "external link (click to copy the address): " + uri,
    "page-after-uri": "1",
    "page-after-outline-section": "2",
    "title-after-outline-section": "nav.pdf - page ii (2/3) - safe-pdf",
    "page-after-outline-chapter": "3",
    "page-after-goto-ii": "2",
    "page-after-goto-1": "3",
    "page-after-goto-nope": "3",
    "outline-shown-after-f9": "false",
    "panes-after-f9": ".v",
}
errs = ["%s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
if rd("uri-shown.txt") != uri: errs.append("dialog showed %r, not %r" % (rd("uri-shown.txt"), uri))
if rd("uri-clip.txt") != uri: errs.append("clipboard holds %r, not %r" % (rd("uri-clip.txt"), uri))
if "not opened" not in v.get("status-after-uri", ""): errs.append("URI status: %r" % v.get("status-after-uri"))
if "no page with label" not in v.get("status-goto-nope", ""): errs.append("Ctrl+G nope: %r" % v.get("status-goto-nope"))
# Chapter: /XYZ top 400 on a 792 pt page puts the window top at (792 - 400) / 792 of the page.
y = float(v.get("yview-after-outline-chapter", "0 0").split()[0])
if not 0.45 <= y <= 0.53: errs.append("outline /XYZ position not applied: yview %r" % y)
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-nav" "$work/nav-uri.txt" || fail=1

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
