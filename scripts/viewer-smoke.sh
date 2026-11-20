#!/usr/bin/env bash
# Smoke test of the native viewer (tasks 8.2a–8.2d, 9.1–9.4, 9.5c, 9.5g, 9.7, 9.8, 9.11; docs/viewer.md). Run from the repo root.
#   scripts/viewer-smoke.sh [--no-build]
#
# Builds `viewer` (needs Tcl/Tk development files), then runs it headless in smoke mode
# (SAFEPDF_VIEWER_SMOKE=DIR) on
#   1. a generated two-page PDF (scripts/viewer-smoke-pdf.py), shown at fit page (`f`; the
#      viewer opens in Automatic Zoom): page 1 must contain non-white
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
#   1f. the same PDF through the menubar (SAFEPDF_VIEWER_SMOKE_MODE=menu): File / Edit / View /
#      Go entries invoked by their .menubar paths, enabled states (9.1); mouse wheel across page
#      boundaries both ways, small deltas, Button-4/5, Shift+wheel (9.2);
#   1g. the toolbar and sidebar after PDF.js (SAFEPDF_VIEWER_SMOKE_MODE=toolbar) on that PDF and
#      on the two-page one without an outline: page field, arrows, zoom drop-down, overflow
#      menu, tool states (Highlight enabled since 9.4, the others disabled), sidebar shown/hidden
#      with its toggle, disclosure triangles (9.7);
#   1h. highlights and notes on the text PDF (SAFEPDF_VIEWER_SMOKE_MODE=marks): highlight,
#      recolour, delete (pixel colours), a note at a point with its popup, marks kept across
#      zoom, rotation and page changes (9.4);
#   1i. the selection bubble and the Highlight pop-over (SAFEPDF_VIEWER_SMOKE_MODE=bubble) on the
#      text PDF: bubble highlight, edit bubble recolour via its picker and delete, pop-over
#      swatch, tool-mode highlight on mouse-up, thickness slider, Show all off/on (pixels),
#      comment, Escape and page change dismiss (9.8);
#   1j. saving marks into the PDF (SAFEPDF_VIEWER_SMOKE_MODE=save, then =reopen on the saved
#      file): unsaved indicator, Save / Save As / quit and close prompts, saved marks restored
#      and selectable, no duplicates; qpdf --check, original bytes a prefix (cmp -n), mutool
#      shows the highlight (9.5c); then (SAFEPDF_VIEWER_SMOKE_MODE=edit on a copy of the
#      result) saved marks recoloured, deleted, commented and edited, saved, reopened, and a
#      third revision on top; qpdf --check, prefixes, no duplicate ids, mutool shows the new
#      colour and not the deleted highlight (9.5g);
#   1j''. XFDF (SAFEPDF_VIEWER_SMOKE_MODE=xfdf) on a copy of the text PDF: highlight + comment +
#      note, File → Export annotations… (the comment as <contents> inside the <highlight>),
#      every mark deleted, import brings them back (pixels, texts, status counts), re-import
#      adds nothing, hostile files (Tests/xfdf/) and broken ones show an error and change
#      nothing (9.11);
#   1k. view modes (SAFEPDF_VIEWER_SMOKE_MODE=modes) on a generated three-page text PDF, each mode
#      chosen through the View menu: continuous (three page frames, the wheel scrolls the
#      document and the page field follows 1, 2, 3, a highlight on page 2, a search hit on page
#      3 scrolled into view), continuous facing (pages 1|2 side by side, the highlight drawn),
#      facing (two pages, Next/Previous by two, a wheel notch turns a spread), even spreads
#      (1 alone, then 2|3), back to single page (9.3);
#   1l. Tcl lockdown (SAFEPDF_VIEWER_SMOKE_MODE=lockdown): Tk send from another interpreter on
#      the display fails and hostile X resources reach no widget; with SAFEPDF_VIEWER_DRIVE=1
#      send works (8.7);
#   1m. non-blocking rendering (SAFEPDF_VIEWER_SMOKE_MODE=async) on a PDF with a slow page 1
#      (viewer-smoke-pdf.py --slow): placeholder, a timer runs and zoom/End/Home return at once
#      while it renders, End shows page 2 meanwhile, the old zoom's render is discarded (8.8);
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
# The marker check below needs the non-embedded Helvetica text to stay unpainted (only the
# marker is dark), so substitute fonts (task 7.7) are switched off for this run.
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=text run_viewer "$work/out-text" "$work/text.pdf"
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

# 1f. Menubar (task 9.1) on the same three-page PDF (SAFEPDF_VIEWER_SMOKE_MODE=menu): the
# menubar File / Edit / View / Go is attached to the window with the expected entries; every
# action is invoked through `.menubar.*` entries: Go (next, last, first, previous, Go to
# page..., Back, Forward; entries are disabled where they cannot run), View (Outline check,
# zoom, fit, rotate), Edit (Find..., Select all), File (Close, then Quit ends the run).
# Wheel (task 9.2, generated Tk 9 <MouseWheel> events): in fit page one notch turns a page
# each way; at 200 % notches scroll page 1 to its bottom and only the one notch after that
# turns to the top of page 2; eleven 1/12-notch deltas up do not turn back, the twelfth does
# (to the bottom of page 1); twelve 1/12 notches scroll as far as one notch; Button-5/4
# scroll; Shift+wheel scrolls horizontally to the edge without turning the page.
mkdir -p "$work/out-menu"
SAFEPDF_VIEWER_SMOKE_MODE=menu run_viewer "$work/out-menu" "$work/nav.pdf"
cat "$work/out-menu/menu.txt"
python3 -I -c '
import sys
v = dict(l.split(": ", 1) for l in open(sys.argv[1], encoding="utf-8").read().splitlines()
         if ": " in l)
want = {
    "menubar": ".menubar",
    "cascades": "File|Edit|View|Go",
    "entries.menubar.file": "Open...|Save|Save As...|Import annotations...|Export annotations...|Close|Quit",
    "entries.menubar.edit": "Copy|Select all|Highlight selection|Highlight colour|Add note...|Delete mark|Highlight tool|Show all highlights|Find...",
    "entries.menubar.view": "Outline|Zoom in|Zoom out|Actual size|Fit page|Fit width|Rotate right|Rotate left|"
                            "Page Scrolling|Vertical Scrolling|No Spreads|Odd Spreads|Even Spreads",
    "entries.menubar.go": "Previous page|Next page|First page|Last page|Go to page...|Back|Forward",
    "states-page1": "Previous page=disabled,Next page=normal,First page=disabled,Last page=normal,"
                    "Back=disabled,Forward=disabled,Copy=disabled,Outline=normal",
    "toolbar-prev-page1": "disabled",
    "page-after-next": "2",
    "page-after-last": "3",
    "states-page3": "Previous page=normal,Next page=disabled,First page=normal,Last page=disabled,"
                    "Back=disabled,Forward=disabled",
    "page-after-next-at-end": "3",
    "page-after-first": "1",
    "page-after-prev-at-start": "1",
    "goto-bar-mapped": "1",
    "page-after-goto": "2",
    "states-after-goto": "Back=normal,Forward=disabled",
    "page-after-back": "1",
    "page-after-forward": "2",
    "outline-after-view-outline": "false 0",
    "outline-after-view-outline2": "true 1",
    "zoom-actual": "100",
    "zoom-in": "125",
    "zoom-out": "100",
    "mode-fit-width": "fit width",
    "mode-fit-page": "fit page",
    "rot-after-right": "90",
    "rot-after-left": "0",
    "find-bar-mapped": "1",
    "title-after-close": "safe-pdf",
    "states-after-close": "Close=disabled,Next page=disabled,Zoom in=disabled,Open...=normal,Quit=normal",
}
want.update({
    "page-after-wheel-fit-down": "2",
    "page-after-wheel-fit-up": "1",
    "wheel-zoom": "200",
    "wheel-down-events-at-end": "1",
    "page-after-wheel-down": "2",
    "page-after-11-tiny-up": "2",
    "page-after-12-tiny-up": "1",
    "page-after-shift-wheel": "1",
})
errs = ["%s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
if "no text" not in v.get("status-select-all", ""): errs.append("Select all: %r" % v.get("status-select-all"))
f = lambda k: [float(x) for x in v.get(k, "").split()] if v.get(k) else []
try:
    if int(v["wheel-down-events"]) < 3: errs.append("the wheel turned page 1 without scrolling it")
    if f("y-before-turn")[1] != 1.0: errs.append("the page turned before its bottom: %r" % v["y-before-turn"])
    if f("y-after-wheel-down")[0] != 0.0: errs.append("page 2 not shown at its top: %r" % v["y-after-wheel-down"])
    if f("y-after-tiny-up")[1] != 1.0: errs.append("page 1 not shown at its bottom: %r" % v["y-after-tiny-up"])
    y0, y1, y2 = f("y-frac")
    one = 1.5 / int(v["region-h"])
    if not y0 - y1 > 0.01 or abs((y0 - y1) - (y1 - y2)) > one:
        errs.append("12 small deltas did not scroll one notch: %r" % v["y-frac"])
    b0, b1, b2 = f("button-5-4")
    if not (b1 > b0 and abs(b2 - b0) < 1e-6): errs.append("Button-5/4 did not scroll: %r" % v["button-5-4"])
    x0, x1, xa, xb = f("shift-wheel")
    if not (x1 > x0 and xb == 1.0): errs.append("Shift+wheel did not scroll horizontally: %r" % v["shift-wheel"])
except (KeyError, ValueError) as e:
    errs.append("wheel results missing: %r" % e)
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-menu/menu.txt" || fail=1

# 1g. Toolbar and sidebar after PDF.js (task 9.7, SAFEPDF_VIEWER_SMOKE_MODE=toolbar), on the
# three-page PDF with labels i, ii, 1 and an outline, and on the two-page PDF without one:
# layout of the three toolbar groups; the sidebar opens (with its toggle shown and pressed)
# only with an outline; the page field shows the label or number and "(k of N)" / "of N";
# generated clicks on the arrows page (and are disabled at the ends); Enter in the page field
# jumps (number, label), an out-of-range number or text reverts to the current page, leaving
# the field reverts it; End/Home update the field; the zoom drop-down lists the twelve PDF.js
# choices, shows the chosen one, and shows custom zooms reached with -/+ as a percentage; the
# overflow menu pages; Highlight is enabled (9.4), the other tool buttons are disabled and
# ignore clicks; a disclosure triangle
# collapses and expands its subtree; the toggle button hides and shows the sidebar.
mkdir -p "$work/out-tb-nav" "$work/out-tb-two"
SAFEPDF_VIEWER_SMOKE_MODE=toolbar run_viewer "$work/out-tb-nav" "$work/nav.pdf"
SAFEPDF_VIEWER_SMOKE_MODE=toolbar run_viewer "$work/out-tb-two" "$work/two.pdf"
cat "$work/out-tb-nav/toolbar.txt" "$work/out-tb-two/toolbar.txt"
python3 -I -c '
import sys
def load(path):
    return dict(l.split(": ", 1) for l in open(path, encoding="utf-8").read().splitlines() if ": " in l)
nav, two = load(sys.argv[1]), load(sys.argv[2])
layout_r = ".bar.r=.bar.highlight,.bar.comment,.bar.text,.bar.draw,.bar.image,.bar.s3,.bar.print,.bar.save,.bar.s4,.bar.more"
layout_m = ".bar.m=.bar.zout,.bar.s2,.bar.zin,.bar.zoom"
common = {
    "zoom-label0": "Automatic Zoom",
    "zoom-sel0": "auto",
    "zoom-menu": "Automatic Zoom|Actual Size|Page Fit|Page Width|50%|75%|100%|125%|150%|200%|300%|400%",
    "more-menu": "Open...|Import annotations...|Export annotations...|Find...|Go to page...|First page|Last page|Rotate right|Rotate left|"
                 "Page Scrolling|Vertical Scrolling|No Spreads|Odd Spreads|Even Spreads",
    "states0": ".bar.prev=disabled,.bar.next=normal,.bar.zout=normal,.bar.zin=normal,.bar.more=normal",
    "tools": ".bar.highlight=normal," + ",".join(w + "=disabled" for w in [
        ".bar.comment", ".bar.text", ".bar.draw", ".bar.image", ".bar.print", ".bar.save"]),  # Save: no unsaved marks
    "status-unchanged-after-tool": "true",
    "history-after-entry": "2",
}
want_nav = dict(common, **{
    "pages": "3", "has-outline": "true", "sidebar-shown": "true", "panes": ".ol .v",
    "toggle-mapped": "1",
    "layout": ".bar.l=.bar.sidebar,.bar.s0,.bar.prev,.bar.s1,.bar.next,.bar.pg,.bar.of " + layout_m + " " + layout_r,
    "field0": "i", "of0": "(1 of 3)",
    "after-next": "2 ii (2 of 3)", "after-next-prev": "2 ii", "after-prev-at-start": "1 i",
    "entry-last": "3 1", "entry-999": "3 1", "entry-abc": "3 1", "entry-first": "1 i",
    "entry-revert": "1 i", "key-end": "3 1", "key-home": "1 i",
    "more-last": "3 1", "more-first": "1 i",
    "child-visible": "true", "child-visible-after-collapse": "false",
    "child-visible-after-expand": "true",
    "toggle-pressed0": "1", "after-toggle": "false .v 0", "after-toggle2": "true .ol .v",
})
want_two = dict(common, **{
    "pages": "2", "has-outline": "false", "sidebar-shown": "false", "panes": ".v",
    "toggle-mapped": "0",
    "layout": ".bar.l=.bar.prev,.bar.s1,.bar.next,.bar.pg,.bar.of " + layout_m + " " + layout_r,
    "field0": "1", "of0": "of 2",
    "after-next": "2 2 of 2", "after-next-prev": "1 1", "after-prev-at-start": "1 1",
    "entry-last": "2 2", "entry-999": "2 2", "entry-abc": "2 2", "entry-first": "1 1",
    "entry-revert": "1 1", "key-end": "2 2", "key-home": "1 1",
    "more-last": "2 2", "more-first": "1 1",
})
errs = []
for name, v, want in (("nav", nav, want_nav), ("two", two, want_two)):
    errs += ["%s %s: %r, expected %r" % (name, k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
    if name == "two":
        errs += ["two: unexpected %s" % k for k in ("child-visible", "after-toggle") if k in v]
    # Zoom: label | radio value | shown percentage.
    zw = {"zoom-page-width": ("Page Width", "page-width", None),
          "zoom-page-fit": ("Page Fit", "page-fit", None),
          "zoom-actual": ("Actual Size", "actual", 100),
          "zoom-150": ("150%", "150", 150),
          "zoom-in-200": ("200%", "200", 200),
          "zoom-out-125": ("125%", "125", 125),
          "zoom-custom-33": ("33%", "", 33),
          "zoom-auto": ("Automatic Zoom", "auto", None)}
    for k, (lbl, sel, pct) in zw.items():
        parts = v.get(k, "||").split("|")
        if parts[0] != lbl or parts[1] != sel or (pct is not None and abs(int(parts[2]) - pct) > 1):
            errs.append("%s %s: %r, expected %s|%s|%s" % (name, k, v.get(k), lbl, sel, pct))
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-tb-nav/toolbar.txt" "$work/out-tb-two/toolbar.txt" || fail=1

# 1h. Highlights and notes (task 9.4, SAFEPDF_VIEWER_SMOKE_MODE=marks) on the text PDF of 1d
# (page 1 white except the black marker under "safe"; substitute fonts off): a double click on
# "world" + the toolbar's Highlight turns its pixels PDF.js yellow (#FFFF98); Edit > Highlight
# colour > Green recolours it (#53FFBC); "safe" + Edit > Highlight selection highlights in
# green with multiply (the black marker stays black, the paper above it turns green); a click
# selects the "world" highlight and Delete makes it white again; right button at a blank
# point + Add note... opens the note popup, its text (Tcl metacharacters) is saved verbatim
# and the icon is drawn where the model puts it; a click on the icon reopens the popup with
# that text, which is edited; zoom in, rotation, page 2 (no marks) and back keep the marks
# in place; Edit > Delete mark removes the selected note; ids are never reused.
mkdir -p "$work/out-marks"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=marks run_viewer "$work/out-marks" "$work/text.pdf"
cat "$work/out-marks/marks.txt"
python3 -I -c '
import sys
v = dict(l.split(": ", 1) for l in open(sys.argv[1], encoding="utf-8").read().splitlines()
         if ": " in l)
white, yellow, green, black = "255 255 255", "255 255 152", "83 255 188", "0 0 0"
want = {
    "world-before": white,
    "sel-before-highlight": "true",
    "marks-after-highlight": "1",
    "world-yellow": yellow,
    "sel-after-highlight": "false",
    "selected-after-highlight": "true",
    "world-green": green,
    "color-var": "green",
    "edit-highlight-state": "normal",
    "marks-after-edit-highlight": "2",
    "safe-marker": black,
    "safe-above-marker": green,
    "selected-world": "true",
    "marks-after-delete": "1",
    "world-after-delete": white,
    "pop-delete-state": "disabled",
    "pop-entries": "separator Highlight|Add note...|Delete mark",
    "note-popup": "1",
    "marks-after-note": "2",
    "note-text-ok": "true",
    "note-popup-after-save": "0",
    "note-icon": "true true",
    "note-popup-reopened": "1",
    "note-popup-text-ok": "true",
    "note-edited-ok": "true",
    "zoom-safe": black + "|" + green,
    "zoom-note-icon": "true true",
    "rot-deg": "90",
    "rot-safe": black + "|" + green,
    "rot-note-icon": "true true",
    "page2-mark-items": "2 0",
    "back-safe": "1 " + black + "|" + green,
    "back-note-icon": "true true",
    "edit-delete-state0": "disabled",
    "edit-delete-state1": "normal",
    "marks-after-note-delete": "1 0",
    "ids": "[2] next 4",
}
errs = ["%s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
try:
    if not int(v["zoom-pct1"]) > int(v["zoom-pct0"]): errs.append("zoom in did not zoom")
except (KeyError, ValueError) as e:
    errs.append("zoom results missing: %r" % e)
if "choose the highlight colour" not in v.get("status-highlight-nosel", ""):
    errs.append("Highlight without a selection: %r" % v.get("status-highlight-nosel"))
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-marks/marks.txt" || fail=1

# 1i. Selection bubble and Highlight pop-over (task 9.8, SAFEPDF_VIEWER_SMOKE_MODE=bubble) on the
# text PDF of 1d: a drag over "world" shows the float bubble at the end of the selection; its
# Highlight button highlights in yellow (pixels) and the edit bubble replaces it; a click on
# blank paper dismisses it; a click on the highlight brings the edit bubble back, which follows
# a zoom; its colour button opens the picker and the blue row recolours the highlight; its
# Delete removes it (white again). The toolbar's Highlight button without a selection turns the
# tool on and opens the pop-over (right-aligned under the button); its pink swatch makes pink
# current; with the tool on a drag over "safe" highlights at once in pink; the slider follows a
# press and a drag (thickness 20, then 24); "Show all" off makes the paper white again (and the
# hidden highlight cannot be selected), on brings the pink back; the edit bubble's Comment adds
# a note anchored to the highlight and reopens it later; Escape closes the pop-over and
# dismisses the bubble; with the tool off (Edit menu) a new selection's bubble goes on Escape
# and on a page change.
mkdir -p "$work/out-bubble"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=bubble run_viewer "$work/out-bubble" "$work/text.pdf"
cat "$work/out-bubble/bubble.txt"
python3 -I -c '
import sys
v = dict(l.split(": ", 1) for l in open(sys.argv[1], encoding="utf-8").read().splitlines()
         if ": " in l)
white, yellow, blue, pink = "255 255 255", "255 255 152", "128 235 255", "255 203 230"
want = {
    "bubble0": "none 0",
    "sel-world": "true",
    "bubble-float": "float true",
    "bubble-at-end": "true",
    "marks-after-bubble-highlight": "1",
    "world-yellow": yellow,
    "bubble-after-highlight": "edit true",
    "bubble-after-blank": "none 0",
    "bubble-edit": "edit true",
    "bubble-zoom": "edit true",
    "picker-open": "true true",
    "world-blue": blue,
    "picker-closed": "true 0",
    "bubble-after-pick": "edit",
    "marks-after-bubble-delete": "0",
    "world-after-delete": white,
    "bubble-after-delete": "none 0",
    "popover": "1 1 1",
    "popover-right-aligned": "true",
    "color-after-swatch": "pink pink",
    "marks-tool": "1 false",
    "safe-pink": pink,
    "thickness": "20 24",
    "showall-off": white + " 0",
    "hidden-not-selectable": "true",
    "showall-on": pink + " 1",
    "bubble-safe": "edit",
    "comment-popup": "1 2",
    "comment-anchored": "true",
    "comment-reopened": "1 On safe 2",
    "before-escape": "edit 1 2",
    "after-escape": "none 0 0 true",
    "tool-off": "false 0",
    "float-again": "float 2",
    "float-escape": "none false",
    "page-change": "2 none 0",
}
errs = ["%s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-bubble/bubble.txt" || fail=1

# 1j. Saving marks into the PDF (task 9.5c, SAFEPDF_VIEWER_SMOKE_MODE=save, then =reopen) on a
# copy of the text PDF of 1d: a highlight on "world" and a note make the title start with "* "
# and enable Save; Quit and Ctrl+W answered Cancel keep them; Ctrl+S writes
# text-annotated.pdf next to the PDF without a question and opens it (the highlight now drawn
# by the renderer from its /AP: yellow pixels; the note text restored); a second Ctrl+S has
# nothing to save; the saved highlight can be selected; a new highlight + Ctrl+S
# appends to the same file (3 marks, distinct ids); Save As writes saveas.pdf; Ctrl+W with an
# unsaved note answered No discards it. The reopen run restores the 3 marks (pixels, note popup
# text), refuses then (after Yes) performs Save As onto the opened file, and Quit answered Yes
# saves a last note before quitting. Externally: `qpdf --check` on the written files, the
# original bytes (and the first saved revision) are a byte-for-byte prefix of the later files
# (`cmp -n`), each mark's annotation object is written exactly once, and `mutool draw` shows the
# highlight.
mkdir -p "$work/save" "$work/out-save" "$work/out-reopen"
cp "$work/text.pdf" "$work/save/text.pdf"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=save run_viewer "$work/out-save" "$work/save/text.pdf"
cat "$work/out-save/save.txt"
cp "$work/save/text-annotated.pdf" "$work/out-save/after-run1.pdf" 2>/dev/null || true
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=reopen run_viewer "$work/out-reopen" "$work/save/text-annotated.pdf"
cat "$work/out-reopen/reopen.txt"
python3 -I -c '
import sys
def kv(p):
    return dict(l.split(": ", 1) for l in open(p, encoding="utf-8").read().splitlines() if ": " in l)
v, r = kv(sys.argv[1]), kv(sys.argv[2])
yellow = "255 255 152"
want = {
    "dirty0": "false false disabled disabled",
    "dirty1": "true true normal normal 2",
    "quit-cancel": "1 true true",
    "close-cancel": "true true",
    "wm-delete": "::safepdf::emit quit",
    "saved-path": "true true true",
    "after-save": "2 2 false false disabled",
    "world-after-save": yellow,
    "note-after-save": "true 0",
    "save-nothing": "true true",
    "saved-selected": "true",
    "dirty2": "true true",
    "second-save": "true 3 false true",
    "file-marks": "3 3",
    "save-as": "true true 3 false",
    "dirty3": "true true",
    "close-discard": "true true 3 3",
}
want_r = {
    "restored": "3 3 false false true",
    "world-px": yellow,
    "note-text": "true 0",
    "note-popup": "1 true",
    "dirty1": "true true",
    "overwrite-no": "true true true",
    "overwrite-yes": "true false 4 4 4",
    "dirty2": "true true",
}
errs = ["save %s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
errs += ["reopen %s: %r, expected %r" % (k, r.get(k), w) for k, w in want_r.items() if r.get(k) != w]
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-save/save.txt" "$work/out-reopen/reopen.txt" || fail=1
# The quit in the reopen run saved the last note: 5 marks, each annotation object written once.
python3 -I -c '
import sys
d = open(sys.argv[1], "rb").read()
n = d.count(b"(safepdf-mark-") + d.count(b"<" + b"safepdf-mark-".hex().upper().encode())  # strings are written in hex
print("annotated file: %d bytes, %d mark annotations, %d revisions" % (len(d), n, d.count(b"startxref")))
sys.exit(0 if n == 5 and d.count(b"startxref") == 5 else 1)
' "$work/save/text-annotated.pdf" || { echo "FAIL: quit did not save, or marks were duplicated" >&2; fail=1; }
for f in "$work/save/text-annotated.pdf" "$work/out-save/saveas.pdf"; do
  if command -v qpdf >/dev/null 2>&1; then
    qpdf --check "$f" >/dev/null 2>&1 || { echo "FAIL: qpdf --check $f" >&2; fail=1; }
  else echo "viewer-smoke: qpdf missing, check skipped"; fi
done
# S8: the original bytes are a prefix of every written file, each revision of the next one.
for pair in "save/text.pdf out-save/first.pdf" "out-save/first.pdf out-save/after-run1.pdf" \
    "out-save/after-run1.pdf save/text-annotated.pdf" "save/text.pdf out-save/saveas.pdf"; do
  set -- $pair
  cmp -n "$(stat -c %s "$work/$1")" "$work/$1" "$work/$2" \
    || { echo "FAIL: $1 is not a prefix of $2" >&2; fail=1; }
done
cmp -s "$work/text.pdf" "$work/save/text.pdf" || { echo "FAIL: the original was modified" >&2; fail=1; }
# Another reader draws the highlight: mutool at 72 dpi, inside the box of "world".
if command -v mutool >/dev/null 2>&1; then
  mutool draw -q -r 72 -c rgb -F pnm -o "$work/out-save/mutool.ppm" "$work/out-save/saveas.pdf" 1
  python3 -I -c '
import sys
d = open(sys.argv[1], "rb").read()
parts, i = [], 0
while len(parts) < 4:
    while d[i:i+1].isspace(): i += 1
    j = i
    while not d[j:j+1].isspace(): j += 1
    parts.append(d[i:j]); i = j
i += 1
w, h = int(parts[1]), int(parts[2])
box = [l.split(": ", 1)[1] for l in open(sys.argv[2], encoding="utf-8") if l.startswith("world-box: ")][0]
x0, y0, x1, y1 = map(float, box.split())
n = yel = 0
for y in range(int(792 - y1) + 2, int(792 - y0) - 1):
    for x in range(int(x0) + 2, int(x1) - 1):
        o = i + 3 * (y * w + x)
        r, g, b = d[o], d[o + 1], d[o + 2]
        n += 1
        if r > 240 and g > 240 and 135 < b < 170: yel += 1
print("mutool: %d/%d yellow pixels in the world box" % (yel, n))
sys.exit(0 if n and yel * 3 >= n else 1)
' "$work/out-save/mutool.ppm" "$work/out-save/save.txt" || { echo "FAIL: mutool does not show the highlight" >&2; fail=1; }
else echo "viewer-smoke: mutool missing, check skipped"; fi

# 1j'. Editing saved marks (task 9.5g, SAFEPDF_VIEWER_SMOKE_MODE=edit) on a copy of the
# text-annotated.pdf left by the reopen run (5 saved marks): the whole-page highlight and the
# "safe" highlight are deleted, the "world" highlight recoloured green and commented, a note's
# text edited; the pages follow at once (preview); Ctrl+S writes one revision into the opened
# file and reopens it (4 marks: the comment as /Contents + /Popup of the highlight, restored
# with its id); a second round (blue, comment deleted) adds a third revision on top (3 marks).
# Externally: qpdf --check, each revision a byte prefix of the next, no duplicate ids, and
# mutool draws "world" in the new colour and "safe" without a highlight.
mkdir -p "$work/edit" "$work/out-edit"
cp "$work/save/text-annotated.pdf" "$work/edit/text-annotated.pdf"
cp "$work/save/text-annotated.pdf" "$work/out-edit/before.pdf"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=edit run_viewer "$work/out-edit" "$work/edit/text-annotated.pdf"
cat "$work/out-edit/edit.txt"
python3 -I -c '
import sys
v = dict(l.split(": ", 1) for l in open(sys.argv[1], encoding="utf-8").read().splitlines() if ": " in l)
green, blue = "83 255 188", "128 235 255"
want = {
    "restored": "5 false false",
    "del-all": "4 true true true true",
    "recolour": "(some green) " + green,
    "comment": "true 5",
    "del-safe": "true true",
    "pending": "5 true true",
    "saved": "true 4 false false true",
    "after-world": "(some green) " + green,
    "after-safe": "true true",
    "after-comment": "true true true",
    "after-note": "true",
    "file-marks1": "4 4",
    "third": "3 false (some blue) true " + blue,
    "file-marks2": "3 3",
}
errs = ["edit %s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-edit/edit.txt" || fail=1
for f in "$work/out-edit/edit1.pdf" "$work/edit/text-annotated.pdf"; do
  if command -v qpdf >/dev/null 2>&1; then
    qpdf --check "$f" >/dev/null 2>&1 || { echo "FAIL: qpdf --check $f" >&2; fail=1; }
  else echo "viewer-smoke: qpdf missing, check skipped"; fi
done
for pair in "out-edit/before.pdf out-edit/edit1.pdf" "out-edit/edit1.pdf edit/text-annotated.pdf"; do
  set -- $pair
  cmp -n "$(stat -c %s "$work/$1")" "$work/$1" "$work/$2" \
    || { echo "FAIL: $1 is not a prefix of $2" >&2; fail=1; }
done
if command -v mutool >/dev/null 2>&1; then
  mutool draw -q -r 72 -c rgb -F pnm -o "$work/out-edit/edit1.ppm" "$work/out-edit/edit1.pdf" 1
  mutool draw -q -r 72 -c rgb -F pnm -o "$work/out-edit/final.ppm" "$work/edit/text-annotated.pdf" 1
  python3 -I -c '
import sys
def ppm(p):
    d = open(p, "rb").read()
    parts, i = [], 0
    while len(parts) < 4:
        while d[i:i+1].isspace(): i += 1
        j = i
        while not d[j:j+1].isspace(): j += 1
        parts.append(d[i:j]); i = j
    return d, i + 1, int(parts[1])
def box(name):
    b = [l.split(": ", 1)[1] for l in open(sys.argv[3], encoding="utf-8") if l.startswith(name + ": ")][0]
    return list(map(float, b.split()))
def share(p, b, test):
    d, i, w = ppm(p)
    x0, y0, x1, y1 = b
    n = k = 0
    for y in range(int(792 - y1) + 2, int(792 - y0) - 1):
        for x in range(int(x0) + 2, int(x1) - 1):
            o = i + 3 * (y * w + x)
            n += 1
            if test(d[o], d[o + 1], d[o + 2]): k += 1
    return k, n
green = lambda r, g, b: r < 110 and g > 240 and 170 < b < 205
blue = lambda r, g, b: 110 < r < 145 and 220 < g < 245 and b > 240
tinted = lambda r, g, b: max(r, g, b) - min(r, g, b) > 40
ok = True
for p, col, cname in ((sys.argv[1], green, "green"), (sys.argv[2], blue, "blue")):
    name = p.rsplit("/", 1)[-1]
    k, n = share(p, box("world-box"), col)
    print("mutool %s: %d/%d %s pixels in the world box" % (name, k, n, cname))
    ok = ok and n > 0 and k * 3 >= n
    k, n = share(p, box("safe-box"), tinted)
    print("mutool %s: %d/%d tinted pixels in the safe box" % (name, k, n))
    ok = ok and n > 0 and k == 0
sys.exit(0 if ok else 1)
' "$work/out-edit/edit1.ppm" "$work/out-edit/final.ppm" "$work/out-edit/edit.txt" \
    || { echo "FAIL: mutool does not show the edited marks" >&2; fail=1; }
else echo "viewer-smoke: mutool missing, check skipped"; fi

# Encrypted input (SAFEPDF_VIEWER_SMOKE_MODE=encrypted): Ctrl+S with a note must not crash; until
# task 9.5f the writer's refusal shows in the status line and nothing is written ("refused"),
# afterwards the file is written ("saved").
mkdir -p "$work/enc" "$work/out-enc"
cp Tests/adversarial/encrypted/rc4-128.pdf "$work/enc/rc4-128.pdf"
SAFEPDF_VIEWER_SMOKE_MODE=encrypted run_viewer "$work/out-enc" "$work/enc/rc4-128.pdf"
cat "$work/out-enc/encrypted.txt"
grep -qx 'alive: 1' "$work/out-enc/encrypted.txt" && grep -qE '^outcome: (refused|saved)$' "$work/out-enc/encrypted.txt" \
  || { echo "FAIL: saving an encrypted file" >&2; fail=1; }
if grep -qx 'outcome: refused' "$work/out-enc/encrypted.txt"; then
  grep -q '^status: cannot save to rc4-128-annotated.pdf: ' "$work/out-enc/encrypted.txt" \
    && [ ! -e "$work/enc/rc4-128-annotated.pdf" ] || { echo "FAIL: encrypted refusal not shown, or a file was written" >&2; fail=1; }
fi

# 1j''. XFDF import/export (task 9.11, SAFEPDF_VIEWER_SMOKE_MODE=xfdf, `Viewer.smokeXfdf`) on a
# copy of the text PDF: a highlight on "world" with a comment and a note are exported through
# File → Export annotations… (the dialog answered by ::safepdf::autoPath) into marks.xfdf,
# which must hold the comment in the standard form <highlight …><contents>…</contents><popup …/>
# and no separate <text> for it; all marks deleted, the import restores them (yellow pixels,
# comment and note text equal, unsaved) with the status "3 imported, 0 already present, 0
# skipped"; a second import adds nothing; the hostile samples of Tests/xfdf/, a missing and a
# non-XFDF file each give "cannot import NAME: …" and leave the marks unchanged.
mkdir -p "$work/xfdf" "$work/out-xfdf"
cp "$work/text.pdf" "$work/xfdf/text.pdf"
for f in billion-laughs xxe undeclared-entity acrobat; do cp "Tests/xfdf/$f.xfdf" "$work/out-xfdf/"; done
printf '<?xml version="1.0"?>\n<fdf><annots/></fdf>\n' > "$work/out-xfdf/not-xfdf.xfdf"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=xfdf run_viewer "$work/out-xfdf" "$work/xfdf/text.pdf"
cat "$work/out-xfdf/xfdf.txt"
python3 -I -c '
import re, sys
v = dict(l.split(": ", 1) for l in open(sys.argv[1], encoding="utf-8").read().splitlines() if ": " in l)
yellow = "255 255 152"
want = {
    "marks": "3 2 true true true",
    "world-px": yellow,
    "menu-states": "normal normal",
    "export-status": "exported 3 mark(s) to marks.xfdf",
    "export-default": "text.xfdf",
    "removed": "0 255 255 255",
    "import-status": "marks.xfdf: 3 imported, 0 already present, 0 skipped",
    "imported": "3 2 true true true",
    "imported-px": yellow + " true",
    "reimport-status": "marks.xfdf: 0 imported, 3 already present, 0 skipped",
    "reimported": "3 2 true true true",
    "acrobat": "6",
}
for n in ("billion-laughs", "xxe", "undeclared-entity", "missing", "not-xfdf"):
    want["hostile %s.xfdf" % n] = "true true 1"
errs = ["xfdf %s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
a = v.get("acrobat-status", "")
if not a.startswith("acrobat.xfdf: 3 imported, 0 already present, 2 skipped"):
    errs.append("xfdf acrobat-status: %r" % a)
for n, frag in (("billion-laughs", "document type declarations"), ("xxe", "document type declarations"),
                ("undeclared-entity", "unknown entity &nbsp;"), ("not-xfdf", "not an XFDF file")):
    if frag not in v.get("hostile-status %s.xfdf" % n, ""):
        errs.append("xfdf hostile-status %s: %r" % (n, v.get("hostile-status %s.xfdf" % n)))
# The exported file: the comment in the standard form, inside its highlight, and nowhere else.
x = open(sys.argv[2], encoding="utf-8").read()
if not re.search("<highlight [^>]*name=\"safepdf-mark-1\"[^>]*><contents>Comment ✓ &lt;&amp;&gt;</contents>"
                 "<popup [^>]*name=\"safepdf-mark-1-popup-2\"[^>]*/></highlight>", x):
    errs.append("marks.xfdf: no <highlight ...><contents> comment")
if x.count("<text ") != 1 or "name=\"safepdf-mark-2\"" in x:
    errs.append("marks.xfdf: the comment is also a separate element")
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-xfdf/xfdf.txt" "$work/out-xfdf/marks.xfdf" || fail=1

# 1k. View modes (task 9.3) on a three-page text PDF (Helvetica, substitute fonts off: white
# pages): `Alpha` on page 1, `Bravo` on page 2 (y 400), `zebra` on page 3. Every mode through its
# View menu entry (SAFEPDF_VIEWER_SMOKE_MODE=modes, `Viewer.smokeModes`).
python3 -I -c '
import sys
pages = [b"BT /F1 18 Tf 72 700 Td (Alpha on page one) Tj ET\n",
         b"BT /F1 18 Tf 72 400 Td (Bravo on page two) Tj ET\n",
         b"BT /F1 18 Tf 72 700 Td (A zebra on page three) Tj ET\n"]
n = len(pages)
objs = [b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [%s] /Count %d >>" % (b" ".join(b"%d 0 R" % (3 + 2 * i) for i in range(n)), n)]
for i, c in enumerate(pages):
    objs.append(b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents %d 0 R "
                b"/Resources << /Font << /F1 %d 0 R >> >> >>" % (4 + 2 * i, 3 + 2 * n))
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
' "$work/modes.pdf"
mkdir -p "$work/out-modes"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=modes run_viewer "$work/out-modes" "$work/modes.pdf"
cat "$work/out-modes/modes.txt"
python3 -I -c '
import sys
v = dict(l.split(": ", 1) for l in open(sys.argv[1], encoding="utf-8").read().splitlines()
         if ": " in l)
yellow = "255 255 152"
want = {
    "frames-single": "1",
    "scroll-var": "vertical", "frames-continuous": "3", "slots-continuous": "1,2,3",
    "wheel-pages-seen": "1,2,3", "wheel-monotone": "true", "page-at-end": "3",
    "page-after-home": "1 1", "page-after-next": "2 2", "zoom-anchor": "true 2",
    "sel-page": "2", "marks": "[2]", "hl-continuous": yellow,
    "find-status": "\"zebra\": hit 1/1 on page 3", "page-after-find": "3 3", "hit-in-view": "true",
    "spread-var": "odd", "cfacing-rows": "true", "hl-cfacing": yellow,
    "facing-frames": "2 1,2 1", "hl-facing": yellow,
    "facing-next": "3 3 3", "facing-next-state": "disabled", "facing-next-at-end": "3",
    "facing-prev": "1 1,2", "facing-wheel": "3 3", "facing-wheel-up": "1 1,2",
    "even-first": "1 1", "even-next": "2 2,3", "even-next-state": "disabled", "hl-even": yellow,
    "single-again": "2 2 1",
}
errs = ["%s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
if "error" in v: errs.append("smoke step failed: %s" % v["error"])
try:
    rh, ch = map(int, v["region-vs-canvas"].split())
    if rh < 3 * ch: errs.append("the continuous scroll region is not three pages high: %d" % rh)
    if int(v["wheel-notches"]) < 10: errs.append("the wheel went through the document too fast")
    if v["wheel-end"].split()[1] not in ("1.0", "1"): errs.append("the wheel did not reach the end")
    if v["y-after-home"].split()[0] not in ("0.0", "0"): errs.append("Home did not go to the top")
    if not 2 <= int(v["max-photos"]) <= 3: errs.append("photos kept: %s" % v["max-photos"])
except (KeyError, ValueError) as e:
    errs.append("missing or bad value: %r" % e)
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-modes/modes.txt" || fail=1

# 1l. Tcl lockdown (task 8.7; SAFEPDF_VIEWER_SMOKE_MODE=lockdown): HOME holds a hostile
#     ~/.Xdefaults (script-valued resources that would create the file `pwned`), and a second
#     Tk interpreter on the same display tries `send` into the viewer. Without the test hook
#     the viewer has no `send` command, is not in `winfo interps`, every send fails, and the
#     resources reach no widget; with SAFEPDF_VIEWER_DRIVE=1 the send works (the corpus
#     driver's path). The other interpreter also checks that it got the hostile resources
#     itself (so the guard, not a missing resource file, is what the test sees).
lockwish=""
for w in wish9.0 wish8.6 wish; do
  if command -v "$w" >/dev/null; then lockwish="$w"; break; fi
done
if [ -z "$lockwish" ]; then
  echo "viewer-smoke: wish missing, lockdown case skipped"
else
  cat > "$work/attacker.tcl" <<'TCL'
wm withdraw .
lassign $argv dir
namespace eval ::safepdf {}
set t0 [clock milliseconds]
while {![file exists $dir/up] && [clock milliseconds] - $t0 < 40000} { after 50 }
set f [open $dir/attack.txt w]
entry .ctl
puts $f "control-resources: [.ctl cget -validate] [.ctl cget -validatecommand]"
.ctl configure -validate none
puts $f "interps: [winfo interps]"
set ok 0
foreach i [lsort -unique [concat [winfo interps] tk viewer safe-pdf]] {
  if {$i eq [tk appname]} continue
  set code [catch {send $i {set ::safepdf::lockSent 1}} r]
  puts $f "send $i: $code $r"
  if {$code == 0} { incr ok }
}
puts $f "sends-ok: $ok"
close $f
close [open $dir/attacked w]
exit
TCL
  # lock_run DIR [ENV...]: the viewer (smoke mode lockdown) and the attacker on one display.
  lock_run() {
    local d="$1"; shift
    mkdir -p "$d/home"
    cat > "$d/home/.Xdefaults" <<XD
*Entry.validate: all
*Entry.validateCommand: exec touch $d/pwned
*TEntry.validate: all
*TEntry.validateCommand: exec touch $d/pwned
*Menu.postCommand: exec touch $d/pwned
*Menu.tearOffCommand: exec touch $d/pwned
*takeFocus: exec touch $d/pwned
*Entry.textVariable: ::safepdf::btn(cmd,.bar.save)
*Toplevel.container: 1
XD
    env HOME="$d/home" SAFEPDF_VIEWER_SMOKE="$d" SAFEPDF_VIEWER_SMOKE_MODE=lockdown "$@" \
      timeout 60 "${wrap[@]}" bash -c '"$1" "$2" & v=$!; "$3" "$4" "$5"; wait $v' _ \
      "$viewer" "$work/two.pdf" "$lockwish" "$work/attacker.tcl" "$d"
  }
  lock_run "$work/out-lock" || { echo "FAIL: lockdown run failed" >&2; fail=1; }
  cat "$work/out-lock/lockdown.txt" "$work/out-lock/attack.txt" 2>/dev/null || true
  python3 -I -c '
import os, sys
d = sys.argv[1]
def kv(name):
    try:
        text = open(os.path.join(d, name), encoding="utf-8").read()
    except FileNotFoundError:
        return {}
    return dict(l.split(": ", 1) for l in text.splitlines() if ": " in l)
v, a = kv("lockdown.txt"), kv("attack.txt")
want = {"send-command": "[]", "pg-validate": "[none] []", "more-postcommand": "[]",
        "root-takefocus": "[]", "probe-entry": "[none] [] [] []", "probe-menu": "[] []",
        "probe-toplevel": "[] [] [0]", "attacked-file": "true"}
errs = ["%s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
if "error" in v: errs.append("smoke step failed: %s" % v["error"])
if a.get("sends-ok") != "0": errs.append("a send into the viewer worked: %r" % a)
if not a.get("control-resources", "").startswith("all exec touch"):
    errs.append("the hostile resources were not loaded (control): %r" % a.get("control-resources"))
if a.get("interps", "").split() not in ([], ["attacker.tcl"]):
    errs.append("the viewer is still registered: %r" % a.get("interps"))
if os.path.exists(os.path.join(d, "pwned")): errs.append("a hostile resource ran (pwned exists)")
for e in errs: print("FAIL: lockdown: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-lock" || fail=1
  lock_run "$work/out-drive" SAFEPDF_VIEWER_DRIVE=1 || { echo "FAIL: drive-hook run failed" >&2; fail=1; }
  cat "$work/out-drive/attack.txt" 2>/dev/null || true
  grep -q '^sends-ok: [1-9]' "$work/out-drive/attack.txt" 2>/dev/null \
    || { echo "FAIL: with SAFEPDF_VIEWER_DRIVE=1 send does not reach the viewer" >&2; fail=1; }
  [ ! -e "$work/out-drive/pwned" ] || { echo "FAIL: a hostile resource ran with the hook" >&2; fail=1; }
fi

# 1m. Non-blocking rendering (task 8.8; SAFEPDF_VIEWER_SMOKE_MODE=async, no event waits for a
#     render): page 1 of the generated PDF strokes 3000 curves and takes the renderer seconds.
#     While it renders the window shows the placeholder, a 20 ms Tcl timer keeps firing, a
#     zoom change returns at once, and End shows the light page 2 (page field 2) while page 1
#     still renders; the render for the old zoom is discarded (stale) and page 1 finally shows
#     at the new zoom.
python3 -I "$here/viewer-smoke-pdf.py" --slow 3000 "$work/slow.pdf"
SAFEPDF_VIEWER_SMOKE_MODE=async run_viewer "$work/out-async" "$work/slow.pdf" \
  || { echo "FAIL: async run failed" >&2; fail=1; }
cat "$work/out-async/async.txt" 2>/dev/null || true
python3 -I -c '
import re, sys
try:
    t = open(sys.argv[1], encoding="utf-8").read()
except FileNotFoundError:
    t = "error: no async.txt"
v = dict(l.split(": ", 1) for l in t.splitlines() if ": " in l)
errs = []
def need(cond, msg):
    if not cond: errs.append(msg)
def num(k, rx, i=1):
    m = re.search(rx, v.get(k, ""))
    return int(m.group(i)) if m else -1
if "error" in v: errs.append("smoke step failed: %s" % v["error"])
need(re.match(r"page 1 photo false jobs [1-9]\d* placeholders 1$", v.get("start", "")),
     "no placeholder while page 1 renders: %r" % v.get("start"))
need(0 <= num("zoom-event-ms", r"(\d+)") < 250, "the zoom event blocked: %r" % v.get("zoom-event-ms"))
need(v.get("after-zoom") == "jobs 2 photo false placeholders 1",
     "after zoom: %r (expected the old and the new render running)" % v.get("after-zoom"))
need(num("ticks", r"(\d+)") >= 5, "the timer did not run while rendering: %r" % v.get("ticks"))
need(v.get("during") == "jobs 2 photo false placeholders 1", "during: %r" % v.get("during"))
need(0 <= num("end-event-ms", r"(\d+)") < 250, "End blocked: %r" % v.get("end-event-ms"))
need(re.match(r"page 2 field 2 photo true slow-jobs [1-9]", v.get("page2", "")),
     "page 2 not shown while page 1 renders: %r" % v.get("page2"))
need(0 <= num("home-event-ms", r"(\d+)") < 250, "Home blocked: %r" % v.get("home-event-ms"))
need(num("final", r"stale (\d+)") >= 1, "no stale render discarded: %r" % v.get("final"))
need(re.match(r"page 1 jobs 0 ", v.get("final", "")), "final: %r" % v.get("final"))
m = re.match(r"(\d+)x(\d+) slot (\d+)x(\d+)$", v.get("final-photo", ""))
need(m and m.group(1) == m.group(3) and m.group(2) == m.group(4),
     "page 1 photo does not match its slot (new zoom): %r" % v.get("final-photo"))
need("rendered in" in v.get("status", ""), "status: %r" % v.get("status"))
need("done" in t, "the run did not finish")
for e in errs: print("FAIL: async: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-async/async.txt" || fail=1

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
