#!/usr/bin/env bash
# Smoke test of the native viewer (tasks 8.2a–8.2d, 9.1–9.4, 9.5c, 9.5g, 9.6–9.9, 9.11, 9.r1, 9.r2, 9.r3, 9.r4, 9.r6, 9.r8, 9.r9, 9.r10, 9.r11b, 9.r12; docs/viewer.md). Run from the repo root.
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
#      with its toggle (also without an outline since 9.r9: thumbnails), disclosure triangles (9.7);
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
#      shows the highlight (9.5c); Save overwrites the opened file after the first-overwrite
#      question, keeps its mode, refuses a read-only or changed-on-disk file; the
#      unsaved-changes prompt on Quit, Ctrl+W and the close button (Cancel keeps the window,
#      Don't Save leaves the file untouched, Save saves) (9.r2); then (SAFEPDF_VIEWER_SMOKE_MODE=edit on a copy of the
#      result) saved marks recoloured, deleted, commented and edited, saved, reopened, and a
#      third revision on top; qpdf --check, prefixes, no duplicate ids, mutool shows the new
#      colour and not the deleted highlight (9.5g);
#   1j''. XFDF (SAFEPDF_VIEWER_SMOKE_MODE=xfdf) on a copy of the text PDF: highlight + comment +
#      note, File → Export annotations… (the comment as <contents> inside the <highlight>),
#      every mark deleted, import brings them back (pixels, texts, status counts), re-import
#      adds nothing, hostile files (Tests/xfdf/) and broken ones show an error and change
#      nothing (9.11);
#   1j'''. Add text and Draw (SAFEPDF_VIEWER_SMOKE_MODE=editors) on a copy of the text PDF: a
#      text box placed, typed, edited (double click), recoloured and resized from the pop-over;
#      two strokes drawn as one drawing; saved and reopened (read back, painted by the
#      renderer); the text box moved by dragging and saved; both deleted and saved; qpdf
#      --check, prefixes, mutool shows the text and the strokes (9.9);
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
#   1n. the consolidated Phase 9 / M9 run (SAFEPDF_VIEWER_SMOKE_MODE=m9, then =m9-reopen) on two
#      generated fixtures and on real papers (SAFEPDF_SMOKE_PAPERS, default the git-ignored
#      corpus/files/arxiv-1706.03762.pdf when present): menubar, page box, zoom drop-down, the
#      wheel end to end in all four view modes, bubble highlight + note + Add text + Draw, Save ->
#      Close -> reopen (pixels), XFDF export/import round trip, a fresh process on the saved file
#      (free text visible on screen before any click, with and without substitute fonts, 9.r5),
#      qpdf, byte prefix, mutool (9.6);
#   1o. wheel flow (SAFEPDF_VIEWER_SMOKE_MODE=wheelflow) on the four-page M9 fixture and the M9
#      papers: a fresh file opens in Vertical Scrolling; bursts of small trackpad and wheel
#      deltas cross page boundaries without stalling, going back or jumping in every view mode
#      (9.r1); every other case runs with SAFEPDF_VIEWER_VIEW=single unless it says otherwise;
#   1p. platform keys and the icon (SAFEPDF_VIEWER_SMOKE_MODE=keys, as installed and with
#      SAFEPDF_VIEWER_PLATFORM=aqua): accelerator labels, Command twins of the Ctrl bindings,
#      ::tk::mac::Quit, the six icon sizes, _NET_WM_ICON when xprop is installed (9.r3);
#   1q. the review of 2026-11-23 (SAFEPDF_VIEWER_SMOKE_MODE=r4): the view-mode drop-down next to
#      the page count in sync with the View and » menus, the float bubble's Add comment, no
#      intermediate page position when the outline closes or opens at Page Fit (9.r4);
#   1r. the save dialogs (SAFEPDF_VIEWER_SMOKE_MODE=savedlg, as installed and with
#      SAFEPDF_VIEWER_PLATFORM=aqua): keyboard of the three-way prompt, Save As… / Export
#      options, extensions, long/odd names, refused targets, a vanished file (9.r6);
#   1s. document open settings (SAFEPDF_VIEWER_SMOKE_MODE=opensettings) on generated files:
#      every /PageLayout, /PageMode with an outline, /OpenAction destinations (page 3 at
#      150 %, Fit, a named one), JavaScript/URI open actions ignored, ViewerPreferences
#      (hiding, DisplayDocTitle, R2L, FullScreen, FitWindow/CenterWindow), then a file without
#      settings opens in the defaults again (9.r8);
#   1t. closing a note popup without Save (SAFEPDF_VIEWER_SMOKE_MODE=noteclose): Escape in the
#      text widget, Cancel and the window's close button delete an empty new note (no icon
#      left), save the typed text of a new one, keep a stored text; an empty highlight comment
#      goes, the highlight stays (9.r12);
#   1u. the thumbnails panel (SAFEPDF_VIEWER_SMOKE_MODE=thumbs) on generated files: view buttons
#      per content, lazy rendering, click / keyboard / highlight following the main view, the
#      image budget, rotation, /PageMode /UseThumbs, the toggle without an outline; and
#      (=thumbperf, reported only) timings and memory on the corpus paper when present (9.r9);
#   1v. attachments panel (SAFEPDF_VIEWER_SMOKE_MODE=attach): the panel lists a generated
#      file's attachments (name tree with kids + file attachment annotation) without decoding,
#      Save attachment as... writes exactly the decoded bytes, refused targets, UseAttachments
#      opens the panel, an icon click selects its row, no Attachments button without (9.r10);
#   1w. layers panel (SAFEPDF_VIEWER_SMOKE_MODE=layers) on generated files with optional
#      content: /PageMode /UseOC opens it, the tree follows /Order (heading, nesting, locked,
#      groups not in /Order under "Additional Layers"),
#      toggling an OFF group paints its content and makes its word findable, a radio member
#      turns its sibling off, the locked group stays, thumbnails follow, Save keeps the state
#      and leaves /OCProperties alone, reopening restores the defaults, no Layers button
#      without optional content (9.r11b);
#   10.10. highlight fills (SAFEPDF_VIEWER_SMOKE_MODE=tint): on Aqua the selection and search hits
#      are translucent photo items over the page (ink visible through, paper tinted, composited
#      from the probed pixels), on X11 the hits are stippled rectangles and the selection photo
#      items; the selection is one band per line, joined lines touching (10.18); drawing times
#      printed;
#   2. a malformed and a non-PDF file: the viewer must exit normally with an error in the
#      status line;
#   12.5. honest UI for hidden content (SAFEPDF_VIEWER_SMOKE_MODE=honest): copy of a `3 Tr`
#      line announces its invisible characters, the trusted identity line in document full
#      screen and with hidden chrome, the revision-retention notice after deleting a saved
#      mark and saving;
#   12.2c. the document worker (SAFEPDF_VIEWER_SMOKE_MODE=worker): pages rendered by the worker
#      process, no event blocked while a (test-hook) slow render runs, a stalled render killed
#      after the deadline with the status saying so, a fresh worker for the same document and
#      for the next file, render times in-process vs through the worker; (12.2d) the page text
#      index and links read by the worker equal the in-process ones.
# Uses $DISPLAY when an X server answers there, else `xvfb-run -a`; on macOS the viewer runs
# natively on Tk Aqua (task 10.11, docs/viewer.md "Smoke test on macOS"). Ends with a summary of
# the cases passed / skipped / failed. Exit 0 on success.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

if [ "${1:-}" != "--no-build" ]; then
  # Task 12.2c: the viewer renders through the `worker` executable next to it.
  lake build viewer worker
fi
viewer="$repo/.lake/build/bin/viewer"
[ -x "$repo/.lake/build/bin/worker" ] || echo "viewer-smoke: WARNING: no worker executable; pages render in the viewer process" >&2
[ -x "$viewer" ] || { echo "viewer-smoke: $viewer not built" >&2; exit 1; }

# Pick the platform (task 10.11): on macOS (Darwin) the viewer runs natively on Tk Aqua, its
# window shown on screen, with no X server; everywhere else the X logic below is unchanged.
# `wrap=(env)` keeps "${wrap[@]}" non-empty for bash 3.2 (/bin/bash on macOS) under set -u.
platform=x11
if [ "$(uname -s)" = Darwin ]; then platform=aqua; fi

# Per-case results for the summary at the end. case_begin NAME starts a case (the global
# `fail` flag is saved and cleared), case_end records it as passed or failed and merges the
# flag back; skip_case NAME REASON records a case (or a variant of one) that cannot run on
# this platform. A failure outside any case is reported as such.
cases_pass=(); cases_fail=(); cases_skip=()
cur_case=""; fail_saved=0
# Tcl errors (task 10.20): `run_viewer` appends every `Tcl error` line the viewer prints on
# stdout or stderr to $tcl_log; a case fails when it added any (the lines are printed).
tcl_log=""; tcl_seen=0
tcl_count() { if [ -f "$tcl_log" ]; then wc -l < "$tcl_log" | tr -d ' '; else echo 0; fi; }
case_begin() {
  if [ -n "$cur_case" ]; then case_end; fi
  cur_case="$1"; fail_saved="$fail"; fail=0; tcl_seen="$(tcl_count)"
}
case_end() {
  [ -n "$cur_case" ] || return 0
  if [ "$(tcl_count)" -gt "$tcl_seen" ]; then
    echo "FAIL: $cur_case: the viewer printed Tcl errors:" >&2
    tail -n +"$((tcl_seen + 1))" "$tcl_log" | sed 's/^/  /' >&2
    fail=1
  fi
  if [ "$fail" = 0 ]; then cases_pass+=("$cur_case"); else cases_fail+=("$cur_case"); fi
  if [ "$fail_saved" != 0 ]; then fail=1; fi
  cur_case=""; fail_saved=0
}
skip_case() {
  echo "viewer-smoke: SKIP ($platform): $1 — $2"
  cases_skip+=("$1 — $2")
}
# known_bug NAME REASON (macOS only): the case NAME is expected to fail there because of a
# real viewer bug (not a test-environment difference); its checks still run and fail, and the
# summary names the bug next to the failure.
known_bugs=()
known_bug() {
  if [ "$platform" = aqua ]; then known_bugs+=("$1|$2"); fi
}

# Pick a display.
wrap=()
if [ "$platform" = aqua ]; then
  wrap=(env)
  echo "viewer-smoke: using Tk Aqua (macOS; the viewer window appears on screen)"
  # A locked screen (front application loginwindow) gives no app the keyboard focus or full
  # screen: the focus-dependent cases (1q, 1r, 1s, 1t) then fail.
  if [ "${SAFEPDF_SMOKE_FOREGROUND:-}" = 1 ] && command -v lsappinfo >/dev/null 2>&1 \
      && lsappinfo info -only name "$(lsappinfo front)" 2>/dev/null | grep -q loginwindow; then
    echo "viewer-smoke: WARNING (aqua): the screen is locked; focus-dependent cases will fail" >&2
  fi
elif [ -n "${DISPLAY:-}" ] && { command -v xdpyinfo >/dev/null 2>&1 && xdpyinfo >/dev/null 2>&1 \
    || [ -S "/tmp/.X11-unix/X${DISPLAY#*:}" ]; }; then
  echo "viewer-smoke: using DISPLAY=$DISPLAY"
elif command -v xvfb-run >/dev/null 2>&1; then
  wrap=(xvfb-run -a -s "-screen 0 1280x1024x24")
  echo "viewer-smoke: using xvfb-run"
else
  echo "viewer-smoke: no X display and no xvfb-run" >&2
  exit 1
fi

# File size and permission bits (GNU stat on Linux, BSD stat on macOS); cmp_prefix A B:
# A's bytes are a prefix of B (BSD `cmp -n` reports EOF when A ends at the limit).
if [ "$platform" = aqua ]; then
  file_size() { stat -f %z "$1"; }
  file_mode() { stat -f %Lp "$1"; }
  cmp_prefix() { head -c "$(file_size "$1")" "$2" | cmp - "$1"; }
else
  file_size() { stat -c %s "$1"; }
  file_mode() { stat -c %a "$1"; }
  cmp_prefix() { cmp -n "$(file_size "$1")" "$1" "$2"; }
fi

# Background mode (task 10.11, the macOS default): the shim (c/tk_shim.c) makes a smoke run
# never activate and keeps its windows invisible and off screen, so the user can keep working
# (since 10.16 it also blocks Tk's own activation requests and native full screen;
# SAFEPDF_SMOKE_TRACE_ACTIVATION=1 logs each blocked call).
# With no active application Tk has no keyboard focus: checks that read the focus are relaxed
# (the focus part is dropped) and 1q is skipped. SAFEPDF_SMOKE_FOREGROUND=1 runs the old
# foreground mode (windows on screen, the app activated: leave the machine alone meanwhile).
SAFEPDF_SMOKE_BG=0
if [ "$platform" = aqua ] && [ "${SAFEPDF_SMOKE_FOREGROUND:-}" != 1 ]; then
  SAFEPDF_SMOKE_BG=1
  echo "viewer-smoke: background mode (windows hidden, never activated; SAFEPDF_SMOKE_FOREGROUND=1 for the foreground run)"
fi
export SAFEPDF_SMOKE_BG

work="$(mktemp -d)"
tcl_log="$work/tcl-errors.log"
if [ -n "${SAFEPDF_SMOKE_KEEP:-}" ]; then
  echo "viewer-smoke: keeping the outputs in $work (SAFEPDF_SMOKE_KEEP)"
else
  trap 'rm -rf "$work"' EXIT
fi

# run_viewer DIR FILE: smoke-mode run with a 60 s timeout (`viewer_timeout=S` before the call: S s). Files open in vertical scrolling
# since 9.r1; the cases written for the single-page view keep it through SAFEPDF_VIEWER_VIEW
# (set it empty for the real default, as case 1o does).
run_viewer() {
  mkdir -p "$1"
  local o e rc=0
  o="$(mktemp)"; e="$(mktemp)"
  SAFEPDF_VIEWER_VIEW="${SAFEPDF_VIEWER_VIEW-single}" SAFEPDF_VIEWER_SMOKE="$1" \
    timeout "${viewer_timeout:-60}" "${wrap[@]}" "$viewer" "$2" >"$o" 2>"$e" || rc=$?
  cat "$o"; cat "$e" >&2
  grep -h 'Tcl error' "$o" "$e" >> "$tcl_log" || true
  rm -f "$o" "$e"
  return "$rc"
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

case_begin "1 two-page PDF"
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
grep -q '^title: two.pdf - page 2/2 - SafePDF$' "$work/out/state.txt" \
  || { echo "FAIL: unexpected window title" >&2; fail=1; }
grep -q '^status: .*from cache' "$work/out/state.txt" \
  || { echo "FAIL: page 2 was not prefetched into the cache" >&2; fail=1; }

case_begin "1a zoom/rotation"
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

case_begin "1b scrolling/anchoring"
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

case_begin "1c odd file name"
# 1c. A file name full of Tcl metacharacters reaches the title verbatim (no script injection:
# every data word goes through the proved `Tcl.quote`).
odd='odd [exit 7] $HOME {x" \.pdf'
cp "$work/two.pdf" "$work/$odd"
run_viewer "$work/out-odd" "$work/$odd"
grep -qxF "title: $odd - page 2/2 - SafePDF" "$work/out-odd/state.txt" \
  || { echo "FAIL: odd file name not shown verbatim" >&2; fail=1; }
echo "odd name: $(grep '^title:' "$work/out-odd/state.txt")"

case_begin "1d text/select/search"
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

case_begin "1e nav"
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
    "title0": "nav.pdf - page i (1/3) - SafePDF",
    "outline-shown": "true",
    "outline-titles": "Intro|Chapter|Section",
    "outline-depths": "[0, 0, 1]",
    "links-page1": "2",
    "cursor-internal": "hand2",
    "status-hover-internal": "go to page 1 (3/3)",
    "page-after-link": "3",
    "title-after-link": "nav.pdf - page 1 (3/3) - SafePDF",
    "page-after-back": "1",
    "page-after-forward": "3",
    "page-after-back2": "1",
    "cursor-uri": "hand2",
    "status-hover-uri": "external link (click to copy the address): " + uri,
    "page-after-uri": "1",
    "page-after-outline-section": "2",
    "title-after-outline-section": "nav.pdf - page ii (2/3) - SafePDF",
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

case_begin "1f menubar"
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
    "cascades": "File|Edit|View|Go|Help",
    "entries.menubar.file": "Open...|Save|Save As...|Import annotations...|Export annotations...|Close|Quit",
    "entries.menubar.edit": "Undo|Redo|Copy|Select all|Highlight selection|Highlight colour|Add note...|Delete mark|Highlight tool|Show all highlights|Find...",
    "entries.menubar.view": "Sidebar|Zoom in|Zoom out|Actual size|Fit page|Fit width|Rotate right|Rotate left|"
                            "Page Scrolling|Vertical Scrolling|No Spreads|Odd Spreads|Even Spreads",
    "entries.menubar.go": "Previous page|Next page|First page|Last page|Go to page...|Back|Forward",
    "entries.menubar.help": "About SafePDF",
    "states-page1": "Previous page=disabled,Next page=normal,First page=disabled,Last page=normal,"
                    "Back=disabled,Forward=disabled,Copy=disabled,Sidebar=normal",
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
    "title-after-close": "SafePDF",
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

case_begin "1g toolbar"
# 1g. Toolbar and sidebar after PDF.js (task 9.7, SAFEPDF_VIEWER_SMOKE_MODE=toolbar), on the
# three-page PDF with labels i, ii, 1 and an outline, and on the two-page PDF without one:
# layout of the three toolbar groups; the sidebar opens (with its toggle shown and pressed)
# only with an outline; the page field shows the label or number and "(k of N)" / "of N";
# generated clicks on the arrows page (and are disabled at the ends); Enter in the page field
# jumps (number, label), an out-of-range number or text reverts to the current page, leaving
# the field reverts it; End/Home update the field; the zoom drop-down lists the twelve PDF.js
# choices, shows the chosen one, and shows custom zooms reached with -/+ as a percentage; the
# overflow menu pages; Highlight (9.4), Add comment, Add text and Draw (9.9) are enabled,
# Add image and Print are disabled and ignore clicks; a disclosure triangle
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
layout_r = ".bar.r=.bar.select,.bar.highlight,.bar.comment,.bar.text,.bar.draw,.bar.image,.bar.s3,.bar.print,.bar.save,.bar.s4,.bar.more"
layout_m = ".bar.m=.bar.zout,.bar.s2,.bar.zin,.bar.zoom"
common = {
    "zoom-label0": "Automatic Zoom",
    "zoom-sel0": "auto",
    "zoom-menu": "Automatic Zoom|Actual Size|Page Fit|Page Width|50%|75%|100%|125%|150%|200%|300%|400%",
    "more-menu": "Open...|Import annotations...|Export annotations...|Find...|Go to page...|First page|Last page|Rotate right|Rotate left|"
                 "Page Scrolling|Vertical Scrolling|No Spreads|Odd Spreads|Even Spreads",
    "states0": ".bar.prev=disabled,.bar.next=normal,.bar.zout=normal,.bar.zin=normal,.bar.more=normal",
    "tools": ".bar.highlight=normal,.bar.comment=normal,.bar.text=normal,.bar.draw=normal," +
        ",".join(w + "=disabled" for w in [".bar.image", ".bar.print", ".bar.save"]),  # Save: no unsaved marks
    "status-unchanged-after-tool": "true",
    "history-after-entry": "2",
}
want_nav = dict(common, **{
    "pages": "3", "has-outline": "true", "sidebar-shown": "true", "panes": ".ol .v",
    "toggle-mapped": "1",
    "layout": ".bar.l=.bar.sidebar,.bar.s0,.bar.prev,.bar.s1,.bar.next,.bar.pg,.bar.of,.bar.vmode " + layout_m + " " + layout_r,
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
    "toggle-mapped": "1",
    "toggle-pressed0": "0", "after-toggle": "true .ol .v 1", "after-toggle2": "false .v",
    "layout": ".bar.l=.bar.sidebar,.bar.s0,.bar.prev,.bar.s1,.bar.next,.bar.pg,.bar.of,.bar.vmode " + layout_m + " " + layout_r,
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
        errs += ["two: unexpected %s" % k for k in ("child-visible",) if k in v]
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

case_begin "1h marks"
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

case_begin "1i bubble"
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

case_begin "1j save/reopen"
# 1j. Saving marks into the PDF (tasks 9.5c, 9.r2; SAFEPDF_VIEWER_SMOKE_MODE=save, then =reopen)
# on a copy of the text PDF of 1d (mode 640): a highlight on "world" and a note make the title
# start with "* " and enable Save; Quit, Ctrl+W and the window's close button answered Cancel
# keep them (the unsaved-changes prompt asked); Ctrl+S asks before the first overwrite —
# Cancel writes nothing, Overwrite writes the marks into the opened file and reopens it (the
# highlight now drawn by the renderer from its /AP: yellow pixels; the note text restored); a
# second Ctrl+S has nothing to save; the saved highlight can be selected; a new highlight +
# Ctrl+S appends to the same file without a question (3 marks, distinct ids); Save As writes
# saveas.pdf; with a new note Ctrl+S on a read-only saveas.pdf and on one changed on disk is
# refused (file unchanged); Ctrl+W answered Don't Save closes and leaves the file untouched.
# The reopen run restores the 3 marks (pixels, note popup text), refuses then (after Yes)
# performs Save As onto the opened file, and with a last note Quit answered Cancel keeps the
# window, Quit answered Save saves it and quits (the save on quit is the prompt's answer —
# task 9.r2 removed nothing silent here: there never was a save without the prompt).
# Externally: `qpdf --check` on the written files, the original bytes (and the first saved
# revision) are a byte-for-byte prefix of the later files (`cmp -n`), each mark's annotation
# object is written exactly once, the overwritten file kept its mode 640 and no temporary
# file is left, and `mutool draw` shows the highlight.
mkdir -p "$work/save" "$work/out-save" "$work/out-reopen"
cp "$work/text.pdf" "$work/save/text.pdf"
chmod 640 "$work/save/text.pdf"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=save run_viewer "$work/out-save" "$work/save/text.pdf"
cat "$work/out-save/save.txt"
cp "$work/save/text.pdf" "$work/out-save/after-run1.pdf" 2>/dev/null || true
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=reopen run_viewer "$work/out-reopen" "$work/save/text.pdf"
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
    "wm-delete": "::safepdf::quit",
    "wm-close-cancel": "1 true true true",
    "overwrite-cancel": "true true true true",
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
    "read-only": "true true true true",
    "changed-on-disk": "true true true true",
    "close-discard": "true true 3 3 true",
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
    "quit-ask": "1 true true",
}
errs = ["save %s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
errs += ["reopen %s: %r, expected %r" % (k, r.get(k), w) for k, w in want_r.items() if r.get(k) != w]
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-save/save.txt" "$work/out-reopen/reopen.txt" || fail=1
# Quit answered Save in the reopen run saved the last note: 5 marks, each annotation object
# written once.
python3 -I -c '
import sys
d = open(sys.argv[1], "rb").read()
n = d.count(b"(safepdf-mark-") + d.count(b"<" + b"safepdf-mark-".hex().upper().encode())  # strings are written in hex
print("annotated file: %d bytes, %d mark annotations, %d revisions" % (len(d), n, d.count(b"startxref")))
sys.exit(0 if n == 5 and d.count(b"startxref") == 5 else 1)
' "$work/save/text.pdf" || { echo "FAIL: Quit answered Save did not save, or marks were duplicated" >&2; fail=1; }
[ "$(file_mode "$work/save/text.pdf")" = 640 ] || { echo "FAIL: the overwritten file lost its mode 640: $(file_mode "$work/save/text.pdf")" >&2; fail=1; }
! ls -A "$work/save" "$work/out-save" | grep -q '\.tmp$' || { echo "FAIL: a temporary file was left behind" >&2; fail=1; }
for f in "$work/save/text.pdf" "$work/out-save/saveas.pdf"; do
  if command -v qpdf >/dev/null 2>&1; then
    qpdf --check "$f" >/dev/null 2>&1 || { echo "FAIL: qpdf --check $f" >&2; fail=1; }
  else echo "viewer-smoke: qpdf missing, check skipped"; fi
done
# S8: the original bytes are a prefix of every written file, each revision of the next one.
for pair in "text.pdf out-save/first.pdf" "out-save/first.pdf out-save/after-run1.pdf" \
    "out-save/after-run1.pdf save/text.pdf" "text.pdf out-save/saveas.pdf"; do
  set -- $pair
  cmp_prefix "$work/$1" "$work/$2" \
    || { echo "FAIL: $1 is not a prefix of $2" >&2; fail=1; }
done
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

case_begin "1j' edit"
# 1j'. Editing saved marks (task 9.5g, SAFEPDF_VIEWER_SMOKE_MODE=edit) on a copy of the
# text.pdf left by the reopen run (5 saved marks): the whole-page highlight and the
# "safe" highlight are deleted, the "world" highlight recoloured green and commented, a note's
# text edited; the pages follow at once (preview); Ctrl+S writes one revision into the opened
# file and reopens it (4 marks: the comment as /Contents + /Popup of the highlight, restored
# with its id); a second round (blue, comment deleted) adds a third revision on top (3 marks).
# Externally: qpdf --check, each revision a byte prefix of the next, no duplicate ids, and
# mutool draws "world" in the new colour and "safe" without a highlight.
mkdir -p "$work/edit" "$work/out-edit"
cp "$work/save/text.pdf" "$work/edit/text-annotated.pdf"
cp "$work/save/text.pdf" "$work/out-edit/before.pdf"
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
  cmp_prefix "$work/$1" "$work/$2" \
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

case_begin "1j encrypted"
# Encrypted input (SAFEPDF_VIEWER_SMOKE_MODE=encrypted): Ctrl+S with a note must not crash; until
# task 9.5f the writer's refusal shows in the status line before any question (task 9.r2) and
# nothing is written ("refused": the file byte for byte unchanged), afterwards the opened file
# is written ("saved").
mkdir -p "$work/enc" "$work/out-enc"
cp Tests/adversarial/encrypted/rc4-128.pdf "$work/enc/rc4-128.pdf"
SAFEPDF_VIEWER_SMOKE_MODE=encrypted run_viewer "$work/out-enc" "$work/enc/rc4-128.pdf"
cat "$work/out-enc/encrypted.txt"
grep -qx 'alive: 1' "$work/out-enc/encrypted.txt" && grep -qE '^outcome: (refused|saved)$' "$work/out-enc/encrypted.txt" \
  || { echo "FAIL: saving an encrypted file" >&2; fail=1; }
if grep -qx 'outcome: refused' "$work/out-enc/encrypted.txt"; then
  grep -q '^status: cannot save to rc4-128.pdf: ' "$work/out-enc/encrypted.txt" \
    && grep -qx 'asked: false' "$work/out-enc/encrypted.txt" \
    && cmp -s Tests/adversarial/encrypted/rc4-128.pdf "$work/enc/rc4-128.pdf" \
    || { echo "FAIL: encrypted refusal not shown, asked first, or the file was written" >&2; fail=1; }
fi

case_begin "1j'' xfdf"
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

case_begin "1j''' editors"
# 1j'''. Add text and Draw (task 9.9, SAFEPDF_VIEWER_SMOKE_MODE=editors, `Viewer.smokeEditors`)
# on a copy of the text PDF (substitute fonts on, so the saved free text is painted): Add text
# turns its mode and pop-over on; a click at (100, 400) opens a text box, typed text + Escape
# make a free-text mark; a double click edits it, a click elsewhere commits; the pop-over's red
# swatch and size slider restyle it; Draw: blue, thickness 4, two strokes = one drawing;
# Ctrl+S (Overwrite) writes into text.pdf and reopens it (both marks read back exactly, drawn by the
# renderer: text pixels, a blue stroke pixel); the text box dragged 50 units right, saved;
# Delete and the drawing's bubble Delete remove both, saved (none left, white paper).
# Externally: qpdf --check, the original a prefix of the first save and that of the final
# file, and mutool draws the red text and the blue strokes of the first save.
mkdir -p "$work/editors" "$work/out-editors"
cp "$work/text.pdf" "$work/editors/text.pdf"
SAFEPDF_VIEWER_SMOKE_MODE=editors run_viewer "$work/out-editors" "$work/editors/text.pdf"
cat "$work/out-editors/editors.txt"
python3 -I -c '
import sys
v = dict(l.split(": ", 1) for l in open(sys.argv[1], encoding="utf-8").read().splitlines() if ": " in l)
want = {
    "text-mode": "true 1 normal", "editor-open": "1 true", "edit-open": "true",
    "draw-mode": "true 1 normal", "drawn": "2 ink 2 [5, 4] 4 100 #0060DF 2",
    "modes-off": "true 0", "saved": "2 2 false 2 2",
    "after-save-ink": "ink 2 [5, 4] 4 100 #0060DF", "canvas-after-save": "0 0",
    "moved": "true true", "moved-saved": "true false 2 2",
    "text-selected": "true (some true)", "ink-selected": "true (some true)",
    "deleted": "0 true true", "deleted-saved": "0 false 0 0",
    "after-delete-pixels": "0 255 255 255",
}
# task 9.r5: without a substitute Helvetica the saved free text is drawn on the canvas
if v.get("subst") != "true": want["canvas-after-save"] = "1 0"
errs = ["editors %s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
starts = {"text-added": ("1 text Hello text ", " 10 #000000 1 0"),
          "text-edited": ("text Edited text ✓ ", " 10 #000000 true"),
          "text-styled": ("text Edited text ✓ ", " 20 #D70022 20"),
          "after-save-text": ("text Edited text ✓ ", " 20 #D70022")}
for k, (a, b) in starts.items():
    x = v.get(k, "")
    if not (x.startswith(a) and x.endswith(b)):
        errs.append("editors %s: %r, expected %r...%r" % (k, x, a, b))
if v.get("subst") == "true" and v.get("text-pixels") != "true":
    errs.append("editors: the saved free text is not painted")
px = [int(t) for t in v.get("ink-px", "255 255 255").split()]
if not (px[2] > 150 and px[0] < 100):
    errs.append("editors: the saved stroke is not blue: %r" % v.get("ink-px"))
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-editors/editors.txt" || fail=1
for f in "$work/out-editors/editors1.pdf" "$work/editors/text.pdf"; do
  if command -v qpdf >/dev/null 2>&1; then
    qpdf --check "$f" >/dev/null 2>&1 || { echo "FAIL: qpdf --check $f" >&2; fail=1; }
  else echo "viewer-smoke: qpdf missing, check skipped"; fi
done
for pair in "text.pdf out-editors/editors1.pdf" "out-editors/editors1.pdf editors/text.pdf"; do
  set -- $pair
  cmp_prefix "$work/$1" "$work/$2" \
    || { echo "FAIL: $1 is not a prefix of $2" >&2; fail=1; }
done
if command -v mutool >/dev/null 2>&1; then
  mutool draw -q -r 72 -c rgb -F pnm -o "$work/out-editors/mutool.ppm" "$work/out-editors/editors1.pdf" 1
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
px = d[i:]
v = dict(l.split(": ", 1) for l in open(sys.argv[2], encoding="utf-8").read().splitlines() if ": " in l)
x0, y0, x1, y1 = (float(t) for t in v["text-box"].split())
red = n = 0
for y in range(int(792 - y1), int(792 - y0)):
    for x in range(int(x0), int(x1)):
        k = 3 * (y * w + x); r, g, b = px[k], px[k + 1], px[k + 2]; n += 1
        if r > 150 and g < 90 and b < 110: red += 1
mx, my = (float(t) for t in v["ink-mid"].split())
blue = 0
for y in range(int(792 - my) - 1, int(792 - my) + 2):
    for x in range(int(mx) - 1, int(mx) + 2):
        k = 3 * (y * w + x)
        if px[k + 2] > 150 and px[k] < 100: blue += 1
print("mutool: %d/%d red pixels in the text box, %d/9 blue at the stroke" % (red, n, blue))
sys.exit(0 if red > 20 and blue >= 5 else 1)
' "$work/out-editors/mutool.ppm" "$work/out-editors/editors.txt" || { echo "FAIL: mutool does not show the free text and the strokes" >&2; fail=1; }
else echo "viewer-smoke: mutool missing, check skipped"; fi

case_begin "1k view modes"
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

case_begin "1l lockdown"
# 1l. Tcl lockdown (task 8.7; SAFEPDF_VIEWER_SMOKE_MODE=lockdown): HOME holds a hostile
#     ~/.Xdefaults (script-valued resources that would create the file `pwned`), and a second
#     Tk interpreter on the same display tries `send` into the viewer. Without the test hook
#     the viewer has no `send` command, is not in `winfo interps`, every send fails, and the
#     resources reach no widget; with SAFEPDF_VIEWER_DRIVE=1 the send works (the corpus
#     driver's path; on X11 a synchronous send answered by the viewer also counts, task
#     10.c2). The other interpreter also checks that it got the hostile resources
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
lassign $argv dir plat
namespace eval ::safepdf {}
set t0 [clock milliseconds]
while {![file exists $dir/up] && [clock milliseconds] - $t0 < 40000} { after 50 }
set f [open $dir/attack.txt w]
entry .ctl
puts $f "control-resources: [.ctl cget -validate] [.ctl cget -validatecommand]"
.ctl configure -validate none
puts $f "interps: [winfo interps]"
set ok 0
# The viewer started with SAFEPDF_VIEWER_DRIVE=1 reports its unique application name in
# lockdown.txt (task 10.19): the control sends to exactly that one, asynchronously (a send the
# viewer never services blocks until it exits), and the viewer proves the script ran by
# creating $dir/sent; the attacker polls for the file. Without it (the lockdown run) every
# registered interpreter (X11: the display is the test's own) or, on Aqua, only the usual names
# (`winfo interps` there lists every Tk interpreter of the user, including other runs' and
# foreign programs, which must not be sent scripts) are tried.
set vname ""
catch {
  set lf [open $dir/lockdown.txt]
  foreach l [split [read $lf] "\n"] {
    if {[string match "appname: *" $l]} { set vname [string range $l 9 end] }
  }
  close $lf
}
if {$vname ne ""} {
  set t1 [clock milliseconds]
  set code [catch {send -async $vname "close \[open $dir/sent w\]; set ::safepdf::lockSent 1"} r]
  puts $f "send-async $vname: $code $r"
  # Task 10.c2: on X11 an asynchronous send is a property change that sits in Xlib's output
  # buffer until the client flushes it; `after 50` alone never does, `update` does.
  update
  while {![file exists $dir/sent] && [clock milliseconds] - $t1 < 15000} { after 50; update }
  puts $f "sent-file: [file exists $dir/sent] after [expr {[clock milliseconds] - $t1}] ms"
  if {[file exists $dir/sent]} { incr ok } elseif {$plat ne "aqua"} {
    # X11 (task 10.c1 diagnostic, 10.c2 control): a synchronous send that comes back from the
    # viewer with its Tk version and application name also proves that a send reaches the
    # viewer (it ran the script); otherwise its error says why the viewer refused (Tk ignores
    # sends when the X server's host list lets other hosts in: "X server insecure"). One the
    # viewer never services returns once it exits (at most ~20 s).
    flush $f
    set code [catch {send $vname {list [package provide Tk] [tk appname]}} r]
    puts $f "send-sync $vname: $code $r"
    if {$code == 0 && [lindex $r 1] eq $vname} { incr ok; puts $f "send-sync-ok: 1" }
  }
} else {
  set cands [expr {$plat eq "aqua" ? {tk viewer safe-pdf} : [concat [winfo interps] tk viewer safe-pdf]}]
  foreach i [lsort -unique $cands] {
    if {$i eq [tk appname]} continue
    set code [catch {send $i {set ::safepdf::lockSent 1}} r]
    puts $f "send $i: $code $r"
    if {$code == 0} { incr ok }
  }
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
    # X11 (task 10.c1): Tk executes a received send only when the X server is "secure" (access
    # control on, no host-based entries but SI:localuser/localgroup). The test's own server
    # gets its host list printed (xhost.txt) and cleared of other entries first; the
    # lockdown run's expectations do not depend on it (its viewer has no send at all).
    env HOME="$d/home" SAFEPDF_VIEWER_SMOKE="$d" SAFEPDF_VIEWER_SMOKE_MODE=lockdown "$@" \
      timeout 60 "${wrap[@]}" bash -c '
        if [ "$6" != aqua ] && command -v xhost >/dev/null 2>&1; then
          { echo "before:"; xhost; } > "$5/xhost.txt" 2>&1
          xhost - >/dev/null 2>&1
          xhost 2>/dev/null | tail -n +2 | while read -r h; do
            case "$h" in
              SI:localuser:*|SI:localgroup:*|"") ;;
              *) xhost "-$(printf %s "${h%%:*}" | tr "[:upper:]" "[:lower:]"):${h#*:}" >/dev/null 2>&1 ;;
            esac
          done
          { echo "after:"; xhost; } >> "$5/xhost.txt" 2>&1
        fi
        "$1" "$2" & v=$!; "$3" "$4" "$5" "$6"; wait $v' _ \
      "$viewer" "$work/two.pdf" "$lockwish" "$work/attacker.tcl" "$d" "$platform"
  }
  # aqua_send_works: two plain wish processes, one asynchronous send between them (15 s).
  aqua_send_works() {
    local b="$work/send-base"
    rm -rf "$b"; mkdir -p "$b"
    cat > "$b/srv.tcl" <<'TCL'
wm withdraw .
tk appname safepdf-send-baseline
close [open [lindex $argv 0]/up w]
after 20000 exit
TCL
    cat > "$b/cli.tcl" <<'TCL'
wm withdraw .
set d [lindex $argv 0]
set t0 [clock milliseconds]
while {![file exists $d/up] && [clock milliseconds] - $t0 < 10000} { after 50 }
catch {send -async safepdf-send-baseline "close \[open $d/got w\]"}
set t0 [clock milliseconds]
while {![file exists $d/got] && [clock milliseconds] - $t0 < 15000} { after 50 }
exit
TCL
    "$lockwish" "$b/srv.tcl" "$b" & local sv=$!
    "$lockwish" "$b/cli.tcl" "$b"
    kill "$sv" 2>/dev/null || true
    wait "$sv" 2>/dev/null || true
    [ -e "$b/got" ]
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
if sys.argv[2] == "aqua":
    # On Tk Aqua `winfo interps` lists every Tk interpreter of the user, not of one display,
    # so other Tk programs may appear. Every send must fail as "no application" or inside an
    # interpreter without ::safepdf (not a viewer: the viewer always has that namespace).
    for k, r in a.items():
        if k.startswith("send ") and not (r.startswith("1 no application named")
                or r.startswith("1 can\x27t set \"::safepdf::lockSent\": parent namespace doesn\x27t exist")):
            errs.append("%s: %r (a registered viewer?)" % (k, r))
elif a.get("interps", "").split() not in ([], ["attacker.tcl"]):
    errs.append("the viewer is still registered: %r" % a.get("interps"))
if os.path.exists(os.path.join(d, "pwned")): errs.append("a hostile resource ran (pwned exists)")
for e in errs: print("FAIL: lockdown: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-lock" "$platform" || fail=1
  lock_run "$work/out-drive" SAFEPDF_VIEWER_DRIVE=1 || { echo "FAIL: drive-hook run failed" >&2; fail=1; }
  cat "$work/out-drive/attack.txt" 2>/dev/null || true
  [ ! -f "$work/out-drive/xhost.txt" ] || sed 's/^/xhost: /' "$work/out-drive/xhost.txt"
  if ! grep -q '^sends-ok: [1-9]' "$work/out-drive/attack.txt" 2>/dev/null; then
    # The control failed. If Tk Aqua cannot deliver a send between two plain wish processes
    # either (task 10.19: AppleEvents are not dispatched in a session with a locked screen),
    # the control is inconclusive in this session: skipped, not failed. Any other failure
    # stays one.
    if [ "$platform" = aqua ] && ! aqua_send_works; then
      skip_case "1l drive control" "Tk Aqua send does not deliver between two plain wish processes in this session (locked screen?)"
    else
      echo "FAIL: with SAFEPDF_VIEWER_DRIVE=1 send does not reach the viewer" >&2; fail=1
    fi
  fi
  [ ! -e "$work/out-drive/pwned" ] || { echo "FAIL: a hostile resource ran with the hook" >&2; fail=1; }
fi

case_begin "1m async"
# 1m. Non-blocking rendering (task 8.8; SAFEPDF_VIEWER_SMOKE_MODE=async, no event waits for a
#     render): page 1 of the generated PDF strokes 3000 curves and takes the renderer seconds.
#     While it renders the window shows the placeholder, a 20 ms Tcl timer keeps firing, a
#     zoom change returns at once, and End shows the light page 2 (page field 2) while page 1
#     still renders; the render for the old zoom is discarded (stale) and page 1 finally shows
#     at the new zoom. Since task 12.2c the renders go through the document worker, one at a
#     time: the old zoom's render is cancelled (the worker killed and restarted), so "during"
#     may count one render instead of two, and page 2 preempts page 1's render.
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
need(re.match(r"jobs [12] photo false placeholders 1$", v.get("during", "")), "during: %r" % v.get("during"))
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

case_begin "1n m9"
# 1n. The consolidated Phase 9 / M9 run (task 9.6; SAFEPDF_VIEWER_SMOKE_MODE=m9, then =m9-reopen
#     in a fresh process; `Viewer.smokeM9`): menubar entries; toolbar page box, arrows and zoom
#     drop-down; the wheel alone reads the document end to end in single, continuous, facing and
#     continuous facing mode (every spread passed in order, the page box ends on the last
#     page's spread, the view at its bottom); the selection bubble's Highlight on the first
#     five-letter word, a note, Add text (red) and Draw (blue); Ctrl+S, File → Close, reopened
#     from disk: the four marks equal and drawn by the renderer (pixels); XFDF export, every
#     mark deleted (no colour left), import brings the same four back; a second process on
#     the saved file restores them (pixels) and shows the free text on screen before any click,
#     with and without substitute fonts (task 9.r5); qpdf --check, the original a byte prefix, and
#     `mutool draw` shows all four. Runs on two generated fixtures (3 and 4 pages: an odd and
#     an even last spread) and on real papers: SAFEPDF_SMOKE_PAPERS (space-separated paths),
#     default corpus/files/arxiv-1706.03762.pdf when present (git-ignored; skipped otherwise).
m9_fixture() {  # m9_fixture OUT NPAGES
  python3 -I -c '
import sys
n = int(sys.argv[2])
words = ["Alpha", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot"]
pages = [b"BT /F1 18 Tf 72 700 Td (%s on page %d of the fixture) Tj ET\n" % (words[i % 6].encode(), i + 1)
         for i in range(n)]
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
' "$1" "$2"
}
# m9_case NAME SOURCE: the whole M9 sequence on a copy of SOURCE in $work/m9-NAME.
m9_case() {
  local d="$work/m9-$1" src="$2"
  mkdir -p "$d/out" "$d/out2"
  cp "$src" "$d/$1.pdf"
  echo "viewer-smoke: M9 run on $1 ($(basename "$src"))"
  SAFEPDF_VIEWER_SMOKE_MODE=m9 run_viewer "$d/out" "$d/$1.pdf" || { echo "FAIL: m9 $1: run failed" >&2; fail=1; }
  if ! cmp -s "$src" "$d/$1.pdf"; then
    SAFEPDF_VIEWER_SMOKE_MODE=m9-reopen run_viewer "$d/out2" "$d/$1.pdf" \
      || { echo "FAIL: m9 $1: reopen run failed" >&2; fail=1; }
    # Task 9.r5: the saved free text must be visible on screen right after opening, before any
    # click — also without a substitute Helvetica (as on macOS without Ghostscript/TeX Gyre
    # fonts), where the renderer cannot paint its non-embedded font and the canvas draws it.
    mkdir -p "$d/out3"
    SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=m9-reopen run_viewer "$d/out3" "$d/$1.pdf" \
      || { echo "FAIL: m9 $1: reopen run without substitute fonts failed" >&2; fail=1; }
    for o in out2 out3; do
      st=$(sed -n 's/^screen-text: //p' "$d/$o/m9-reopen.txt" 2>/dev/null)
      echo "viewer-smoke: m9 $1 ($o) screen-text: $st"
      case "$st" in
        skipped*) echo "viewer-smoke: ImageMagick import missing, screen check skipped" ;;
        *) [ "${st%% *}" -ge 3 ] 2>/dev/null \
             || { echo "FAIL: m9 $1 ($o): reopened free text not visible on screen: $st" >&2; fail=1; } ;;
      esac
      # still visible after rotating (90°, back) and in vertical / single page mode (the
      # Page Width and page-change shots are reported only: the box may be scrolled away)
      sa=$(sed -n 's/^screen-after: //p' "$d/$o/m9-reopen.txt" 2>/dev/null)
      echo "viewer-smoke: m9 $1 ($o) screen-after: $sa"
      for k in rot90 rot0 vertical single; do
        v=$(printf '%s\n' "$sa" | tr ' ' '\n' | sed -n "s/^$k=\([0-9a-z]*\)\/.*/\1/p")
        case "$v" in
          skipped) ;;
          *) [ "${v:-0}" -ge 3 ] 2>/dev/null \
               || { echo "FAIL: m9 $1 ($o): free text not visible on screen after $k: $v" >&2; fail=1; } ;;
        esac
      done
    done
  fi
  cat "$d/out/m9.txt" "$d/out2/m9-reopen.txt" 2>/dev/null | grep -v '^saved-status' || true
  python3 -I -c '
import sys
def kv(p):
    try:
        t = open(p, encoding="utf-8").read()
    except FileNotFoundError:
        return {"error": "missing %s" % p}
    return dict(l.split(": ", 1) for l in t.splitlines() if ": " in l)
name, v, r = sys.argv[1], kv(sys.argv[2]), kv(sys.argv[3])
errs = []
def need(c, msg):
    if not c: errs.append(msg)
for x in (v, r):
    if "error" in x: errs.append("smoke step failed: %s" % x["error"])
try:
    n = int(v.get("pages", "0"))
    need(n >= 2, "pages: %r" % v.get("pages"))
    want = {"menubar": ".menubar", "menus": "File,Edit,View,Go,Help", "arrow-next": "2", "arrow-prev": "1",
            "bubble": "float true", "bubble-highlight": "1 edit", "note": "2",
            "saved": "true false 4 4", "closed": "true 0 SafePDF", "reopened": "true 4 4 false false",
            "canvas-items": "0 0 0", "export": "exported 4 mark(s) to m9.xfdf",
            "removed": "0 hl=0 note=0 text=0 ink=0", "back-to-single": "1 1",
            "import": "m9.xfdf: 4 imported, 0 already present, 0 skipped"}
    for k, w in want.items(): need(v.get(k) == w, "%s: %r, expected %r" % (k, v.get(k), w))
    need(v.get("menu-entries", "").endswith(" bad="), "menu entries: %r" % v.get("menu-entries"))
    last = v.get("pagebox-last", "").split()
    need(last[:1] == [str(n)], "page box Enter on the last page: %r" % v.get("pagebox-last"))
    need(v.get("pagebox-abc", "").split() == last[:2], "page box text did not revert: %r" % v.get("pagebox-abc"))
    need(v.get("pagebox-first", "").startswith("1 "), "page box back to 1: %r" % v.get("pagebox-first"))
    for k, lbl in (("zoom-width", "Page Width|"), ("zoom-fit", "Page Fit|"), ("zoom-auto", "Automatic Zoom|")):
        need(v.get(k, "").startswith(lbl), "%s: %r" % (k, v.get(k)))
    for mode, spreads in (("single", n), ("continuous", n), ("facing", (n - 1) // 2 + 1), ("cfacing", (n - 1) // 2 + 1)):
        w = dict(t.split("=", 1) for t in v.get("wheel-" + mode, "").split() if "=" in t)
        ok = (w.get("seen") == ",".join(str(i) for i in range(1, spreads + 1)) and
              w.get("spreads") == str(spreads) and w.get("monotone") == "true" and
              w.get("last") == "true" and w.get("bottom") == "true")
        need(ok, "the wheel did not read the document end to end in %s mode: %r" % (mode, v.get("wheel-" + mode)))
    t = v.get("text", "")
    need(t.startswith("3 text M9 text ") and t.endswith(" 16 #D70022"), "text: %r" % t)
    dr = v.get("draw", "")
    need(dr.startswith("4 ink 2 [5, 5] 4 100 ") and dr.endswith(" true"), "draw: %r" % dr)
    before = v.get("marks-before", "")
    need(before.count(" | ") == 3, "marks-before: %r" % before)
    for k, x in (("marks-reopened", v), ("marks-imported", v), ("marks (fresh process)", r)):
        got = x.get(k.split()[0])
        need(got == before, "%s differ: %r vs %r" % (k, got, before))
    need(r.get("restored") == "4 4 false", "fresh process restored: %r" % r.get("restored"))
    def px(s):
        return {a: int(b) for a, b in (t.split("=") for t in s.split())}
    for k, x in (("pixels-reopened", v), ("pixels", r)):
        p = px(x.get(k, "hl=0 note=0 text=0 ink=0"))
        need(p["hl"] >= 5 and p["note"] >= 5 and p["text"] >= 3 and p["ink"] >= 3,
             "%s: a mark is not drawn: %r" % (k, x.get(k)))
    need(px(v.get("imported-hl", "hl=0"))["hl"] >= 5, "imported highlight not drawn: %r" % v.get("imported-hl"))
    c = [int(t) for t in v.get("imported-canvas", "0 0 0").split()]
    need(all(x >= 1 for x in c), "imported note/text/drawing not on the canvas: %r" % c)
except (KeyError, ValueError, IndexError) as e:
    errs.append("missing or bad value: %r" % e)
for e in errs: print("FAIL: m9 %s: %s" % (name, e), file=sys.stderr)
sys.exit(1 if errs else 0)
' "$1" "$d/out/m9.txt" "$d/out2/m9-reopen.txt" || fail=1
  # Save wrote into the opened copy (task 9.r2); $src stays the original.
  cmp -s "$src" "$d/$1.pdf" && { echo "FAIL: m9 $1: nothing saved" >&2; fail=1; return; }
  if command -v qpdf >/dev/null 2>&1; then
    qpdf --check "$d/$1.pdf" >/dev/null 2>&1 || { echo "FAIL: m9 $1: qpdf --check" >&2; fail=1; }
  else echo "viewer-smoke: qpdf missing, check skipped"; fi
  cmp_prefix "$src" "$d/$1.pdf" \
    || { echo "FAIL: m9 $1: the original is not a prefix of the saved file" >&2; fail=1; }
  if command -v mutool >/dev/null 2>&1; then
    mutool draw -q -r 72 -c rgb -F pnm -o "$d/mutool.ppm" "$d/$1.pdf" 1
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
px = d[i:]
v = dict(l.split(": ", 1) for l in open(sys.argv[2], encoding="utf-8").read().splitlines() if ": " in l)
cx0, cy0, cx1, cy1 = (float(t) for t in v["cropbox"].split())
tests = {"hl": lambda r, g, b: r > 200 and g > 200 and b < 200,
         "note": lambda r, g, b: r > 200 and g > 200 and b < 200,
         "text": lambda r, g, b: r > 150 and g < 90 and b < 110,
         "ink": lambda r, g, b: b > 150 and r < 100}
need = {"hl": 5, "note": 5, "text": 3, "ink": 3}
got = {}
for part in v["boxes"].split(";"):
    kind, *nums = part.split()
    x0, y0, x1, y1 = (float(t) for t in nums)
    n = 0
    for y in range(max(0, int(cy1 - y1)), min(h, int(cy1 - y0) + 1)):
        for x in range(max(0, int(x0 - cx0)), min(w, int(x1 - cx0) + 1)):
            k = 3 * (y * w + x)
            if tests[kind](px[k], px[k + 1], px[k + 2]): n += 1
    got[kind] = n
print("mutool: coloured pixels per mark: %r" % got)
bad = [k for k in need if got.get(k, 0) < need[k]]
if bad: print("FAIL: mutool does not show %s" % bad, file=sys.stderr)
sys.exit(1 if bad else 0)
' "$d/mutool.ppm" "$d/out/m9.txt" || { echo "FAIL: m9 $1: mutool check" >&2; fail=1; }
  else echo "viewer-smoke: mutool missing, check skipped"; fi
}
m9_fixture "$work/m9three.pdf" 3
m9_fixture "$work/m9four.pdf" 4
m9_case three "$work/m9three.pdf"
m9_case four "$work/m9four.pdf"
m9papers="${SAFEPDF_SMOKE_PAPERS-corpus/files/arxiv-1706.03762.pdf}"
for p in $m9papers; do
  if [ -f "$p" ]; then m9_case "paper-$(basename "$p" .pdf)" "$p"
  else echo "viewer-smoke: $p missing, M9 paper run skipped"; fi
done

case_begin "1o wheelflow"
# 1o. Wheel flow across page boundaries and the default view mode (task 9.r1;
#     SAFEPDF_VIEWER_SMOKE_MODE=wheelflow, `Viewer.smokeWheelFlow`), on the four-page M9 fixture
#     and the M9 papers, opened without SAFEPDF_VIEWER_VIEW: the file opens in Vertical
#     Scrolling without spreads (state and View menu radio variables); then in single,
#     continuous, facing and continuous facing mode at Page Width, and single at Page Fit, a
#     trackpad-like burst of 12 px <TouchpadScroll> deltas with +-1 px sideways jitter and a
#     burst of third-notch <MouseWheel> deltas, 8 ms apart and never pausing, must reach page 5
#     (or the last page) without going back; the longest run of events that move nothing is at
#     most the page-turn push (a quarter view of trackpad travel on a page that fits, a notch
#     for the wheel) and zero in the vertical modes; no step jumps further than one event plus
#     the push carried onto a new page. Tk 8.6 (Ubuntu's tk-dev, the Linux CI) has no
#     <TouchpadScroll>: there the trackpad bursts are skipped (task 10.c1). Task 10.c2: a third
#     burst per mode presses <Button-5> (the X11 wheel of Tk 8.6, one notch each); every burst
#     stops after 300 events that move nothing or 8 s, the run (150 s timeout) after 140 s with an `error:`
#     line; the viewer writes wheelflow.txt line by line and prints `wheelflow-progress:`
#     lines, and a failed run shows what it wrote and the end of its trace.
wheelflow_case() {  # wheelflow_case NAME PDF
  local d="$work/wheelflow-$1"
  if ! viewer_timeout=150 SAFEPDF_VIEWER_VIEW= SAFEPDF_VIEWER_SMOKE_MODE=wheelflow run_viewer "$d" "$2"; then
    echo "FAIL: wheelflow $1: run failed" >&2; fail=1
    [ ! -f "$d/wheelflow.txt" ] || sed "s/^/wheelflow $1 partial: /" "$d/wheelflow.txt" >&2
    [ ! -f "$d/wheelflow-trace.txt" ] || tail -n 5 "$d/wheelflow-trace.txt" | sed "s/^/wheelflow $1 trace: /" >&2
    return
  fi
  python3 -I -c '
import math, sys
name, path = sys.argv[1], sys.argv[2]
lines = open(path, encoding="utf-8").read().splitlines()
errs = []
v = dict(l.split(": ", 1) for l in lines if ": " in l)
if "error" in v: errs.append("smoke step failed: %s" % v["error"])
if v.get("default") != "scroll=vertical spread=none radio=vertical none continuous=1":
    errs.append("a fresh file is not in Vertical Scrolling: %r" % v.get("default"))
seen = 0
tk = v.get("tk", "")
for l in lines:
    if not l.startswith("flow-"): continue
    seen += 1
    label, rest = l[5:].split(": ", 1)
    # Task 10.c1: Tk 8.6 (Ubuntu) has no <TouchpadScroll>; only the trackpad bursts may skip.
    if rest.startswith("skipped"):
        if not label.endswith("-pad") or "touchpad=false" not in tk:
            errs.append("%s skipped with %r" % (label, tk))
        print("wheelflow %s: %s" % (name, l))
        continue
    f = dict(t.split("=", 1) for t in rest.split())
    view = int(f["view"])
    pad = label.endswith("-pad")
    button = label.endswith("-button")
    vertical = label.startswith("continuous")
    # Button-5 (task 10.c2) is one notch: a tenth of the view, and the page-turn push is one
    # notch, so at most one event at the edge moves nothing.
    step = 12 if pad else math.ceil(view / (10 if button else 30)) + 1
    stall_max = 0 if vertical else (math.ceil(view / 4 / 12) + 1 if pad else 1 if button else 3)
    step_max = step if vertical else 2 * step
    if f["reached"] != "true": errs.append("%s stopped on page %s after %s events in %s ms (stopped=%s)" % (label, f["page"], f["events"], f["ms"], f.get("stopped")))
    if f["back"] != "0": errs.append("%s went backwards %s times" % (label, f["back"]))
    if int(f["max-stall"]) > stall_max: errs.append("%s stalled for %s events (max %d)" % (label, f["max-stall"], stall_max))
    if int(f["max-step"]) > step_max: errs.append("%s jumped %s px (max %d)" % (label, f["max-step"], step_max))
    print("wheelflow %s: %s" % (name, l))
if seen != 15: errs.append("expected 15 bursts, got %d (%r)" % (seen, lines[:3]))
if "touchpad=false" in tk and sys.argv[3] == "aqua": errs.append("Tk Aqua without <TouchpadScroll>: %r" % tk)
for e in errs: print("FAIL: wheelflow %s: %s" % (name, e), file=sys.stderr)
sys.exit(1 if errs else 0)
' "$1" "$d/wheelflow.txt" "$platform" || fail=1
}
wheelflow_case four "$work/m9four.pdf"
for p in $m9papers; do
  if [ -f "$p" ]; then wheelflow_case "paper-$(basename "$p" .pdf)" "$p"; fi
done

case_begin "1p keys"
# 1p. Platform keys and the icon (task 9.r3, SAFEPDF_VIEWER_SMOKE_MODE=keys, `Viewer.smokeKeys`)
#     on the text PDF, twice: as installed here (X11: Ctrl labels, no Command binding) and
#     with SAFEPDF_VIEWER_PLATFORM=aqua (the macOS mapping on X11, where Tk's Command is
#     Meta): Command-S labels, Command twins of every Ctrl binding (Save, Save As both ways,
#     Quit also in the find bar), ::tk::mac::Quit = File -> Quit, the Save tooltip as ⌘S,
#     Command+A selects all; 10.9: the macOS conventions (⌘G/⇧⌘G find, ⌥⌘G go to page,
#     ⌘[ back, ⌘↑ first page, ⌃⌘S sidebar, ⌘L rotate left, ⌘9 fit page, ⌘. in dialogs) and
#     their labels, none of them on X11. Both: the six embedded icons load at their sizes and, when xprop
#     is installed, the window carries _NET_WM_ICON starting with the 512 px image.
for kp in x11 aqua; do
  if [ "$kp" = x11 ] && [ "$platform" = aqua ]; then
    skip_case "1p keys (x11 variant)" "Tk Aqua cannot install the X11 key mapping; the aqua run checks the native one"
    continue
  fi
  if [ "$kp" = aqua ]; then
    SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=keys SAFEPDF_VIEWER_PLATFORM=aqua \
      run_viewer "$work/out-keys-$kp" "$work/text.pdf" || true
  else
    SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=keys run_viewer "$work/out-keys-$kp" "$work/text.pdf" || true
  fi
  cat "$work/out-keys-$kp/keys.txt" 2>/dev/null | cut -c1-160 || true
  python3 -I -c '
import sys
kp, path = sys.argv[1], sys.argv[2]
try: lines = open(path, encoding="utf-8").read().splitlines()
except OSError: print("FAIL: keys %s: no keys.txt" % kp, file=sys.stderr); sys.exit(1)
v = {}
for l in lines:
    k, _, r = l.partition(": ")
    v[k] = r
errs = []
def want(k, x):
    if v.get(k) != x: errs.append("%s = %r, want %r" % (k, v.get(k), x))
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
for n in (16, 32, 64, 128, 256, 512): want("icon%d" % n, "%dx%d" % (n, n))
if "net-wm-icon" in v and not v["net-wm-icon"].startswith("_NET_WM_ICON(CARDINAL) = 512, 512"):
    errs.append("net-wm-icon: %r" % v["net-wm-icon"])
if kp == "aqua":
    want("accel-open", "Command-O"); want("accel-save", "Command-S")
    want("accel-saveas", "Command-Shift-S"); want("accel-quit", "Command-Q")
    want("accel-zoomin", "Command-+"); want("accel-back", "Command-[")  # 10.9: was Option-Left
    want("accel-pop-copy", "Command-C"); want("accel-pop-delete", "Delete")
    want("bind <Control-Key-s>", "[::safepdf::emit save]")
    want("bind <Command-Key-s>", "[::safepdf::emit save]")
    want("bind <Command-Key-S>", "[::safepdf::emit saveAs]")
    want("bind <Shift-Command-Key-s>", "[::safepdf::emit saveAs]")
    want("bind <Command-Key-q>", "[::safepdf::emit quit]")
    want("bind <Command-Key-plus>", "[::safepdf::emit zoom in]")
    want("bind-find", "[::safepdf::emit quit]")
    want("mac-quit", "[::tk::mac::Quit] [::safepdf::emit quit]")
    want("save-tip", "Save (⌘S)")
    if "⌘C copies" not in v.get("status-selectall", ""): errs.append("Command+A: %r" % v.get("status-selectall"))
    # 10.9: macOS conventions (Preview, HIG).
    want("accel-goto", "Command-Option-G"); want("accel-first", "Command-Up")
    want("accel-forward", "Command-]"); want("accel-outline", "Control-Command-S")
    want("accel-rotccw", "Command-L")
    want("bind <Command-Key-g>", "[::safepdf::emit find next $::safepdf::query]")
    want("bind <Command-Key-G>", "[::safepdf::emit find prev $::safepdf::query]")
    want("bind <Option-Command-Key-g>", "[::safepdf::showGoto]")
    want("bind <Control-Key-g>", "[::safepdf::showGoto]")
    want("bind <Command-Key-bracketleft>", "[::safepdf::emit back]")
    want("bind <Command-Key-Up>", "[::safepdf::emit first]")
    want("bind <Control-Command-Key-s>", "[::safepdf::emit outlineToggle]")
    want("bind <Command-Key-l>", "[::safepdf::emit rotate ccw]")
    want("bind <Command-Key-9>", "[::safepdf::emit zoom fitpage]")
    want("bind-find-next", "[::safepdf::emit find next $::safepdf::query; break]")
    want("cancelBind", "[bind $w <Command-Key-period> $script]")
else:
    want("accel-open", "Ctrl+O"); want("accel-save", "Ctrl+S")
    want("accel-saveas", "Ctrl+Shift+S"); want("accel-quit", "Ctrl+Q")
    want("accel-zoomin", "+"); want("accel-back", "Alt+Left"); want("accel-pop-copy", "Ctrl+C")
    want("bind <Control-Key-s>", "[::safepdf::emit save]")
    want("bind <Control-Key-S>", "[::safepdf::emit saveAs]")
    for s in ("<Command-Key-s>", "<Command-Key-S>", "<Shift-Command-Key-s>", "<Command-Key-q>"):
        want("bind " + s, "[]")
    want("bind-find", "[]")
    want("mac-quit", "[] []")
    want("save-tip", "Save (Ctrl+S)")
    if "Ctrl+C copies" not in v.get("status-selectall", ""): errs.append("Ctrl+A: %r" % v.get("status-selectall"))
    # 10.9: X11 keeps Ctrl+G = Go to page, Alt+Left, Home, F9, Shift+R; no Command binding.
    want("accel-goto", "Ctrl+G"); want("accel-first", "Home"); want("accel-forward", "Alt+Right")
    want("accel-outline", "F9"); want("accel-rotccw", "Shift+R")
    want("bind <Control-Key-g>", "[::safepdf::showGoto]")
    for s in ("<Command-Key-g>", "<Command-Key-G>", "<Option-Command-Key-g>", "<Command-Key-bracketleft>",
              "<Command-Key-Up>", "<Control-Command-Key-s>", "<Command-Key-l>", "<Command-Key-9>"):
        want("bind " + s, "[]")
    want("bind-find-next", "[]"); want("cancelBind", "[]")
for e in errs: print("FAIL: keys %s: %s" % (kp, e), file=sys.stderr)
sys.exit(1 if errs else 0)
' "$kp" "$work/out-keys-$kp/keys.txt" || fail=1
done

case_begin "1q r4"
# 1q. Review 2026-11-23 (task 9.r4, SAFEPDF_VIEWER_SMOKE_MODE=r4, `Viewer.smokeR4`), in the
#     default view (Vertical Scrolling): the toolbar's view-mode drop-down next to the page
#     count (its four entries, each invoked, scroll/spread variables and icon; the View menu's
#     Even Spreads and the » menu's Vertical Scrolling followed by it; Two Pages keeps even
#     spreads); on the text PDF the float bubble has Highlight and Add comment, and Add comment
#     adds one note anchored to the selection, opens its popup and closes the bubble; on the
#     outline PDF (and the M9 papers when they have an outline), at Page Fit in Single Page and
#     Vertical Scrolling, closing and opening the outline moves the page frame straight from
#     its start to its final position (sampled at every canvas <Configure> and every 2 ms):
#     no intermediate x, in the canvas or on the screen.
r4_case() {
  local name="$1" pdf="$2" d="$work/out-r4-$1"
  SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_VIEW= SAFEPDF_VIEWER_SMOKE_MODE=r4 run_viewer "$d" "$pdf" || true
  python3 -I -c '
import re, sys
name, path = sys.argv[1], sys.argv[2]
try: lines = open(path, encoding="utf-8").read().splitlines()
except OSError: print("FAIL: r4 %s: no r4.txt" % name, file=sys.stderr); sys.exit(1)
v = {}
for l in lines:
    k, _, r = l.partition(": ")
    v[k] = r
errs = []
def starts(k, x):
    if not v.get(k, "").startswith(x): errs.append("%s = %r, want %r..." % (k, v.get(k), x))
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
starts("view0", "vertical vertical none icon=vertical items=2 on=1")
if v.get("view-entries") != "Single Page|Vertical Scrolling|Two Pages|Two Pages Scrolling":
    errs.append("entries %r" % v.get("view-entries"))
if not v.get("view-left", "").endswith(".bar.next .bar.pg .bar.of .bar.vmode"):
    errs.append("view-mode button not after the page count: %r" % v.get("view-left"))
starts("view-tip", "View mode: Vertical Scrolling")
for k, want in (("single", "single page none icon=single items=1"),
                ("two", "two page odd icon=two items=2"),
                ("two-scroll", "two-scroll vertical odd icon=two-scroll items=4"),
                ("vertical", "vertical vertical none icon=vertical items=2")):
    starts("view-" + k, want)
    st = v.get("view-" + k, "").split(" state=")[-1].split(" slots")[0]
    if st != " ".join(want.split()[1:3]): errs.append("view-%s: state %r" % (k, st))
starts("menu-even", "two-scroll vertical even icon=two-scroll")
starts("view-two-even", "two page even icon=two")
starts("more-vertical", "two-scroll vertical even icon=two-scroll")
starts("menu-none", "vertical vertical none icon=vertical")
if name == "text":
    if "[highlight, comment]" not in v.get("bubble", ""): errs.append("bubble: %r" % v.get("bubble"))
    if v.get("bubble-in-region") != "true": errs.append("bubble outside the scroll region")
    if v.get("bubble-bind") != "::safepdf::bubTip b:comment {Add comment}":
        errs.append("tooltip %r" % v.get("bubble-bind"))
    if v.get("bubble-tip") != "1 Add comment": errs.append("tooltip shown: %r" % v.get("bubble-tip"))
    starts("comment", "added=1 note-on-selection=true popup=1 bubble-after=false sel-after=false")
outl = [k for k in v if k.startswith("outline-")]
if name == "nav" and len(outl) != 4: errs.append("outline cases: %r" % outl)
for k in outl:
    samples = re.findall(r"\{(\w+) (\d+) (\S+) (\S+) (\S+)\}", v[k])
    want_shown = "shown=true" if "-open-" in k else "shown=false"
    if not v[k].startswith(want_shown): errs.append("%s: %r" % (k, v[k][:20]))
    if not any(s[0] == "conf" for s in samples): errs.append("%s: the canvas never changed size" % k)
    for col, what in ((2, "x"), (4, "screen x")):
        seq = []
        for s in samples:
            if not seq or seq[-1] != s[col]: seq.append(s[col])
        if len(seq) > 2 or "none" in seq:
            errs.append("%s: %s went %s (intermediate position)" % (k, what, " -> ".join(seq)))
        else:
            print("r4 %s %s: %s %s (%d samples)" % (name, k, what, " -> ".join(seq), len(samples)))
for e in errs: print("FAIL: r4 %s: %s" % (name, e), file=sys.stderr)
sys.exit(1 if errs else 0)
' "$name" "$d/r4.txt" || fail=1
}
if [ "$SAFEPDF_SMOKE_BG" = 1 ]; then
  skip_case "1q r4" "background mode: without an active app the run times out (seen with a locked screen); SAFEPDF_SMOKE_FOREGROUND=1 runs it"
else
r4_case text "$work/text.pdf"
r4_case nav "$work/nav.pdf"
for p in $m9papers; do
  if [ -f "$p" ]; then r4_case "paper-$(basename "$p" .pdf)" "$p"; fi
done
fi

case_begin "1r savedlg"
# 1r. Save dialogs (task 9.r6, SAFEPDF_VIEWER_SMOKE_MODE=savedlg, `Viewer.smokeSaveDialogs`) on
#     a copy of the text PDF alone in a folder, as installed and with
#     SAFEPDF_VIEWER_PLATFORM=aqua: the three-way prompt from the keyboard (Return on the
#     default, Tab to Cancel + Return cancels, Escape, Space; focus back on the canvas); Save
#     As… options (-filetypes off aqua only, -defaultextension .pdf, the file's folder); a
#     240-character name, a dotted name without .pdf (gets it), the extended name of an
#     existing file (asks; No keeps it), a read-only file, a folder, a read-only folder
#     (refused, still unsaved, Save enabled), spaces/Tcl metacharacters/quotes/non-ASCII; Export
#     onto the opened PDF (writes NAME.pdf.xfdf, the PDF unchanged) and without .xfdf; the
#     opened file deleted behind the viewer's back (asks, creates nothing); no temporary file.
for sp in x11 aqua; do
  if [ "$sp" = x11 ] && [ "$platform" = aqua ]; then
    skip_case "1r savedlg (x11 variant)" "the X11 dialog options do not apply on Tk Aqua; the aqua run checks the native ones"
    continue
  fi
  sd="$work/savedlg-$sp"
  mkdir -p "$sd"
  cp "$work/text.pdf" "$sd/text.pdf"
  if [ "$sp" = aqua ]; then
    SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=savedlg SAFEPDF_VIEWER_PLATFORM=aqua \
      run_viewer "$work/out-savedlg-$sp" "$sd/text.pdf" || true
  else
    SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=savedlg run_viewer "$work/out-savedlg-$sp" "$sd/text.pdf" || true
  fi
  cat "$work/out-savedlg-$sp/savedlg.txt" 2>/dev/null | cut -c1-160 || true
  python3 -I -c '
import sys
sp, path, root = sys.argv[1], sys.argv[2], sys.argv[3] == "0"
try: lines = open(path, encoding="utf-8").read().splitlines()
except OSError: print("FAIL: savedlg %s: no savedlg.txt" % sp, file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
want = {
    "choose-return": "overwrite .c", "choose-tab-cancel": "cancel .c",
    "choose-escape": "cancel .c", "choose-space": "saveas .c",
    "dialog-dir": "true text-annotated.pdf",
    "dialog-filetypes": "false true true" if sp == "aqua" else "true false true",
    "long-name": "true true", "dotted-name": "true true true", "ext-exists": "true true true",
    "read-only": "true true", "folder": "true", "ro-folder": "true true",
    "refused-state": "true true normal", "weird-name": "true true true false",
    "export-onto-pdf": "true true true", "vanished": "true true true",
}
if root: want.pop("read-only"); want.pop("ro-folder")  # root writes anyway
import os
if os.environ.get("SAFEPDF_SMOKE_BG") == "1":  # no keyboard focus in background mode
    for k in ("choose-return", "choose-tab-cancel", "choose-escape", "choose-space"):
        want[k] = want[k].split()[0]; v[k] = v.get(k, "").split(" ")[0]
errs = ["%s = %r, want %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
xe = v.get("export-ext", "")
if not xe.startswith("true true %s " % ("false" if sp == "aqua" else "true")) or not xe.endswith(".xfdf"):
    errs.append("export-ext = %r" % xe)
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
for e in errs: print("FAIL: savedlg %s: %s" % (sp, e), file=sys.stderr)
sys.exit(1 if errs else 0)
' "$sp" "$work/out-savedlg-$sp/savedlg.txt" "$(id -u)" || fail=1
  if find "$sd" -name '*.tmp' | grep -q .; then
    echo "FAIL: savedlg $sp: a temporary file was left behind: $(find "$sd" -name '*.tmp')" >&2; fail=1
  fi
  chmod -R u+w "$sd" 2>/dev/null || true
done

case_begin "1s opensettings"
# 1s. Document open settings (task 9.r8, SAFEPDF_VIEWER_SMOKE_MODE=opensettings,
#     `Viewer.smokeOpenSettings`), in the real default view: generated five-page PDFs with an
#     outline, each opened in turn through the File → Open path: every /PageLayout (view mode
#     and the View menu's variables; TwoColumnRight/TwoPageRight put page 1 alone on the
#     right), /PageMode UseOutlines / UseNone / UseThumbs (outline open / closed / thumbnails
#     open, task 9.r9), /OpenAction [page 3 /XYZ 0 792 1.5] (page 3
#     at 150 %, its top at the window top), the user's Two Pages + Actual Size kept by the
#     reopen after Save (`keepView`), [p1 /Fit] (Page Fit), a GoTo to a named destination in a
#     /Names /Dests tree (page 4, Page Width), JavaScript and URI open actions (ignored, noted),
#     /ViewerPreferences HideToolbar + HideMenubar + HideWindowUI + DisplayDocTitle (window
#     title from /Info /Title; Escape shows them again), TwoPageLeft + /Direction /R2L (page 1
#     right of page 2), FullScreen with /NonFullScreenPageMode /UseOutlines (outline closed,
#     Escape leaves and opens it), FitWindow + CenterWindow at /XYZ zoom 0.5; then a file
#     without settings opens in Vertical Scrolling, Automatic Zoom, page 1 (nothing carried
#     over).
mkdir -p "$work/os"
python3 -I -c '
import sys
out = sys.argv[1]
def pdf(cat, title):
    objs = {1: "<< /Type /Catalog /Pages 2 0 R /Outlines 13 0 R " + cat + " >>",
            2: "<< /Type /Pages /Kids [3 0 R 4 0 R 5 0 R 6 0 R 7 0 R] /Count 5 /MediaBox [0 0 612 792] >>"}
    for i in range(5):
        objs[3 + i] = "<< /Type /Page /Parent 2 0 R /Contents %d 0 R >>" % (8 + i)
        c = "0.%d g 72 72 %d %d re f" % (2 + i, 100 + 60 * i, 100 + 100 * i)
        objs[8 + i] = "<< /Length %d >>\nstream\n%s\nendstream" % (len(c), c)
    objs[13] = "<< /Type /Outlines /First 14 0 R /Last 15 0 R /Count 2 >>"
    objs[14] = "<< /Title (One) /Parent 13 0 R /Next 15 0 R /Dest [3 0 R /Fit] >>"
    objs[15] = "<< /Title (Four) /Parent 13 0 R /Prev 14 0 R /Dest [6 0 R /Fit] >>"
    objs[16] = "<< /Title (%s) >>" % title
    body, offs = b"%PDF-1.7\n", {}
    for n in sorted(objs):
        offs[n] = len(body)
        body += ("%d 0 obj\n%s\nendobj\n" % (n, objs[n])).encode("latin-1")
    x = len(body)
    body += b"xref\n0 17\n0000000000 65535 f \n" + b"".join(b"%010d 00000 n \n" % offs[n] for n in range(1, 17))
    body += ("trailer\n<< /Size 17 /Root 1 0 R /Info 16 0 R >>\nstartxref\n%d\n%%%%EOF\n" % x).encode()
    return body
cases = {"none": ""}
for l in ["SinglePage", "OneColumn", "TwoColumnLeft", "TwoColumnRight", "TwoPageLeft", "TwoPageRight"]:
    cases["layout-" + l] = "/PageLayout /" + l
for m in ["UseOutlines", "UseNone", "UseThumbs"]:
    cases["mode-" + m] = "/PageMode /" + m
cases["xyz"] = "/OpenAction [5 0 R /XYZ 0 792 1.5]"
cases["fit"] = "/PageMode /UseOutlines /OpenAction [3 0 R /Fit]"
cases["named"] = "/OpenAction << /S /GoTo /D (four) >> /Names << /Dests << /Names [(four) [6 0 R /FitH 792]] >> >>"
cases["js"] = "/OpenAction << /S /JavaScript /JS (app.alert\\(1\\)) >>"
cases["uri"] = "/OpenAction << /S /URI /URI (https://example.org/) >>"
cases["prefs"] = "/ViewerPreferences << /HideToolbar true /HideMenubar true /HideWindowUI true /DisplayDocTitle true >>"
cases["window"] = "/OpenAction [3 0 R /XYZ null null 0.5] /ViewerPreferences << /FitWindow true /CenterWindow true >>"
cases["r2l"] = "/PageLayout /TwoPageLeft /ViewerPreferences << /Direction /R2L >>"
cases["full"] = "/PageMode /FullScreen /ViewerPreferences << /NonFullScreenPageMode /UseOutlines >>"
for name, cat in cases.items():
    open("%s/%s.pdf" % (out, name), "wb").write(pdf(cat, "Open Settings Test" if name == "prefs" else "unused"))
' "$work/os"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_VIEW= SAFEPDF_VIEWER_SMOKE_MODE=opensettings \
  run_viewer "$work/out-os" "$work/os/none.pdf" || true
python3 -I -c '
import re, sys
try: lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
except OSError: print("FAIL: opensettings: no opensettings.txt", file=sys.stderr); sys.exit(1)
rows = {}
for l in lines:
    name, _, rest = l.partition(": ")
    head, _, status = rest.partition(" status=")
    d = dict(p.split("=", 1) for p in re.split(r" (?=[a-z]+=)", head) if "=" in p)
    d["status"] = status
    rows[name] = d
errs = []
def want(name, **kv):
    r = rows.get(name)
    if r is None: errs.append("%s: missing" % name); return
    for k, v in kv.items():
        k = k.rstrip("_")
        if r.get(k) != v: errs.append("%s: %s = %r, want %r" % (name, k, r.get(k), v))
def has(name, k, part):
    if part not in rows.get(name, {}).get(k, ""): errs.append("%s: %s lacks %r" % (name, k, part))
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
default = dict(view="vertical,none", vars="vertical,none", rtl="false", zoom="Automatic Zoom",
               page="1", outline="true", bar="1", menu=".menubar", ys="1")
want("start", **default)
for l, v in [("SinglePage", "page,none"), ("OneColumn", "vertical,none"),
             ("TwoColumnLeft", "vertical,odd"), ("TwoColumnRight", "vertical,even"),
             ("TwoPageLeft", "page,odd"), ("TwoPageRight", "page,even")]:
    want("layout-" + l, view=v, vars=v, zoom="Automatic Zoom", page="1")
aqua = sys.argv[2] == "aqua"
for l in ["TwoColumnRight", "TwoPageRight"]:
    xs = rows.get("layout-" + l, {}).get("xs", "")
    if aqua:
        # The canvas width differs on Tk Aqua (native widgets), so the pixel x does: page 1
        # alone sits centred between the two columns of TwoColumnLeft (xs 0@L,1@R).
        m = re.match(r"0@(\d+),1@(\d+)$", rows.get("layout-TwoColumnLeft", {}).get("xs", ""))
        m1 = re.match(r"0@(\d+)", xs)
        ok = m and m1 and abs(int(m1.group(1)) - (int(m.group(1)) + int(m.group(2))) / 2) <= 1
    else:
        ok = xs.startswith("0@237")
    if not ok:
        errs.append("%s: page 1 not alone on the right: %r" % (l, rows.get("layout-" + l, {}).get("xs")))
want("mode-UseOutlines", outline="true"); want("mode-UseNone", outline="false")
want("mode-UseThumbs", outline="true", panel="thumbnails")
if "not available" in rows.get("mode-UseThumbs", {}).get("status", ""): errs.append("mode-UseThumbs: note left")
want("mode-UseOutlines", panel="outline"); want("full-escape", panel="outline")
want("xyz", page="3", zoom="150%", off="0", view="vertical,none")
want("xyz-user", view="page,odd", zoom="Actual Size")
want("xyz-keep", view="page,odd", zoom="Actual Size")
want("fit", zoom="Page Fit", page="1", outline="true")
want("named", page="4", zoom="Page Width", off="0")
want("js", page="1", zoom="Automatic Zoom"); has("js", "status", "open action /JavaScript ignored (not executed)")
want("uri", page="1"); has("uri", "status", "open action /URI ignored (not executed)")
want("prefs", bar="0", menu="", ys="0"); has("prefs", "title", "Open Settings Test - page 1/5 - SafePDF")
has("prefs", "status", "Escape shows them")
want("prefs-escape", bar="1", menu=".menubar", ys="1")
want("r2l", view="page,odd", rtl="true")
m = re.match(r"0@(\d+),1@(\d+)$", rows.get("r2l", {}).get("xs", ""))
if not m or int(m.group(1)) <= int(m.group(2)): errs.append("r2l: page 1 not right of page 2: %r" % rows.get("r2l", {}).get("xs"))
# Without a window manager (Xvfb) `wm attributes . -fullscreen` reads back 0; Tk Aqua has one.
import os
fs = "true,1" if aqua and os.environ.get("SAFEPDF_SMOKE_BG") != "1" else "true,0"
want("full", full=fs, outline="false"); has("full", "status", "full screen (Escape leaves)")
want("full-escape", full="false,0", outline="true")
want("window", zoom="50%")
if rows.get("window", {}).get("geom", "").startswith("1200x960"): errs.append("window: FitWindow did not resize")
want("none", **default); has("none", "title", "none.pdf - page 1/5")
for n in ["start", "layout-OneColumn", "xyz", "js", "prefs", "r2l", "full", "window", "none"]:
    r = rows.get(n, {})
    print("opensettings %s: %s %s %s p%s outline=%s full=%s bar=%s rtl=%s" % (n, r.get("view"), r.get("zoom"), r.get("geom"), r.get("page"), r.get("outline"), r.get("full"), r.get("bar"), r.get("rtl")))
for e in errs: print("FAIL: opensettings %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-os/opensettings.txt" "$platform" || fail=1

case_begin "1t noteclose"
# 1t. Closing a note popup without Save (task 9.r12, SAFEPDF_VIEWER_SMOKE_MODE=noteclose,
#     `Viewer.smokeNoteClose`) on the text PDF: a new note + Escape (focus in the text widget)
#     -> no note, no icon; a new note + typed text + Escape -> kept with the typed text; that
#     note saved, reopened by a click, cleared + Escape -> kept with its text, still saved; an
#     empty saved note reopened + Escape -> removed, an unsaved change (`*`); an empty
#     highlight comment + Escape -> the comment goes, the highlight stays; white space only
#     on a selection -> removed; Cancel and the window's close button as Escape; Add note…
#     while an empty note's popup is open removes that note; a note deleted while its popup
#     is open closes the popup, a stale close is ignored.
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=noteclose run_viewer "$work/out-noteclose" "$work/text.pdf" || true
cat "$work/out-noteclose/noteclose.txt" 2>/dev/null | cut -c1-160 || true
python3 -I -c '
import sys
try: lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
except OSError: print("FAIL: noteclose: no noteclose.txt", file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
want = {
    "menu-open": "notes=1 icons=true popup=1  focus=.note.t",
    "menu-esc": "notes=0 icons=false popup=0 ",
    "typed-esc": "notes=1 icons=true popup=0 typed text",
    "saved-clear-esc": "notes=1 icons=false popup=0 typed text shown=typed text dirty=false star=false",
    "saved-empty-before": "notes=2 icons=false popup=0  star=false",
    "saved-empty-open": "1",
    "saved-empty-esc": "notes=1 icons=false popup=0 <gone> dirty=true star=true",
    "comment-open": "1 anchored=true",
    "comment-esc": "notes=1 icons=false popup=0 <gone> highlight=true",
    "selection-blank-esc": "notes=1 icons=false popup=0 <gone>",
    "cancel-empty": "notes=1 icons=false popup=0 <gone>",
    "cancel-typed": "notes=2 icons=true popup=0 via cancel",
    "wm-empty": "notes=2 icons=true popup=0 <gone>",
    "wm-typed": "notes=3 icons=true popup=0 via close",
    "switch": "notes=4 icons=true popup=1 <gone> other=true for=true",
    "switch-esc": "notes=3 icons=true popup=0 <gone>",
    "deleted-open": "notes=3 icons=true popup=0 <gone>",
    "stale-close": "notes=3 icons=true popup=0 ",
    "texts": "[typed text, via cancel, via close]",
}
import os, re
if os.environ.get("SAFEPDF_SMOKE_BG") == "1":  # no keyboard focus in background mode
    nf = lambda s: re.sub(r" ?focus=\S*", "", s)
    want = {k: nf(w) for k, w in want.items()}; v = {k: nf(x) for k, x in v.items()}
errs = ["%s = %r, want %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
for e in errs: print("FAIL: noteclose: %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-noteclose/noteclose.txt" || fail=1

case_begin "1u thumbs"
# 1u. Thumbnails panel (task 9.r9, SAFEPDF_VIEWER_SMOKE_MODE=thumbs, `Viewer.smokeThumbs`) on
#     generated files: th-outline.pdf (60 pages, an outline, page 5 /Rotate 90) opens with the
#     outline and both view buttons (Thumbnails, Document outline); the Thumbnails button shows
#     the panel with only the visible thumbnails and the margin rendered (lazy); a click on
#     thumbnail 3 goes to page 3; Go to page 40 moves the highlight (scrolled into view); Down,
#     Down, Return in the panel go to page 42; the panel scrolled to the end keeps at most the
#     budget of images; a rotation lays the thumbnails out rotated; th-thumbs.pdf
#     (/PageMode /UseThumbs, no outline) opens with the thumbnails, only the Thumbnails button,
#     no "not available" note; th-plain.pdf (3 pages, nothing) opens closed with the sidebar
#     toggle shown, and the toggle opens the thumbnails.
mkdir -p "$work/th"
python3 -I -c '
import sys
out = sys.argv[1]
def pdf(n, cat, outline, rot=()):
    kids = " ".join("%d 0 R" % (10 + 2 * i) for i in range(n))
    objs = {1: "<< /Type /Catalog /Pages 2 0 R %s%s >>" % ("/Outlines 3 0 R " if outline else "", cat),
            2: "<< /Type /Pages /Kids [%s] /Count %d /MediaBox [0 0 612 792] >>" % (kids, n)}
    if outline:
        objs[3] = "<< /Type /Outlines /First 4 0 R /Last 5 0 R /Count 2 >>"
        objs[4] = "<< /Title (Start) /Parent 3 0 R /Next 5 0 R /Dest [10 0 R /Fit] >>"
        objs[5] = "<< /Title (Middle) /Parent 3 0 R /Prev 4 0 R /Dest [%d 0 R /Fit] >>" % (10 + 2 * (n // 2))
    for i in range(n):
        r = " /Rotate 90" if i in rot else ""
        objs[10 + 2 * i] = "<< /Type /Page /Parent 2 0 R /Contents %d 0 R%s >>" % (11 + 2 * i, r)
        c = "0.%d g 72 %d 300 200 re f 0 0 1 rg 400 600 100 100 re f" % (1 + i % 8, 72 + 8 * i)
        objs[11 + 2 * i] = "<< /Length %d >>\nstream\n%s\nendstream" % (len(c), c)
    body, offs = b"%PDF-1.7\n", {}
    for k in sorted(objs):
        offs[k] = len(body)
        body += ("%d 0 obj\n%s\nendobj\n" % (k, objs[k])).encode("latin-1")
    x, size = len(body), max(objs) + 1
    body += ("xref\n0 %d\n" % size).encode()
    for k in range(size):
        body += (b"%010d 00000 n \n" % offs[k]) if k in offs else b"0000000000 65535 f \n"
    body += ("trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (size, x)).encode()
    return body
open(out + "/th-outline.pdf", "wb").write(pdf(60, "", True, rot=(4,)))
open(out + "/th-thumbs.pdf", "wb").write(pdf(60, "/PageMode /UseThumbs", False))
open(out + "/th-plain.pdf", "wb").write(pdf(3, "", False))
' "$work/th"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_VIEW= SAFEPDF_VIEWER_SMOKE_MODE=thumbs \
  run_viewer "$work/out-th" "$work/th/th-outline.pdf" || true
cut -c1-220 "$work/out-th/thumbs.txt" 2>/dev/null || true
python3 -I -c '
import re, sys
try: lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
except OSError: print("FAIL: thumbs: no thumbs.txt", file=sys.stderr); sys.exit(1)
rows = {}
for l in lines:
    name, _, rest = l.partition(": ")
    head, _, status = rest.partition(" status=")
    d = dict(p.split("=", 1) for p in re.split(r" (?=[a-z0-9-]+=)", head) if "=" in p)
    d["status"] = status
    d["raw"] = rest
    rows[name] = d
errs = []
def want(name, **kv):
    r = rows.get(name)
    if r is None: errs.append("%s: missing" % name); return
    for k, v in kv.items():
        k = k.replace("_", "-")
        if r.get(k) != v: errs.append("%s: %s = %r, want %r" % (name, k, r.get(k), v))
def num(name, k): return int(rows.get(name, {}).get(k, "-1"))
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
want("outline-open", shown="true", panel="outline", buttons="thumbnails,outline", toggle="1",
     head="Document outline", rendered="0")
want("thumbs-open", shown="true", panel="thumbnails", buttons="thumbnails,outline", head="Thumbnails",
     slots="60", marked="1")
vis, ren = num("thumbs-open", "visible"), num("thumbs-open", "rendered")
if not (0 < vis and 0 < ren <= vis + 2 * 3 and ren < 60):
    errs.append("thumbs-open: not lazy: visible=%d rendered=%d" % (vis, ren))
if rows.get("rot-slot", {}).get("raw") != "98x76 98x127": errs.append("rot-slot: %r" % rows.get("rot-slot", {}).get("raw"))
want("click-3", page="3", marked="3")
want("main-40", page="40", marked="40")
f = num("main-40", "first-visible")
if not (f <= 40 < f + num("main-40", "visible")): errs.append("main-40: thumbnail 40 not in view (first %d)" % f)
want("keys-down2", page="40", sel="42")
want("keys-return", page="42", marked="42", sel="0")
if num("scrolled-end", "max-have") > 40 or num("scrolled-end", "have") > 40:
    errs.append("scrolled-end: over the budget: %r" % rows.get("scrolled-end", {}).get("raw"))
if num("scrolled-end", "photos") != num("scrolled-end", "have"):
    errs.append("scrolled-end: photos %d != kept %d" % (num("scrolled-end", "photos"), num("scrolled-end", "have")))
want("rotated", slots="60", marked="42"); want("rotated-slots", slot1="98x76", slot5="98x127")
want("usethumbs", shown="true", panel="thumbnails", buttons="thumbnails", toggle="1", head="Thumbnails", page="1")
if "not available" in rows.get("usethumbs", {}).get("status", "x not available"): errs.append("usethumbs: note %r" % rows.get("usethumbs", {}).get("status"))
if not (0 < num("usethumbs", "rendered") < 60): errs.append("usethumbs: rendered %d" % num("usethumbs", "rendered"))
want("plain", shown="false", buttons="", toggle="1")
want("plain-toggle", shown="true", panel="thumbnails", buttons="thumbnails", rendered="3", have="3")
want("plain-toggle2", shown="false")
for e in errs: print("FAIL: thumbs %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-th/thumbs.txt" || fail=1
case_begin "1u thumbperf (reported only)"
# Performance (task 9.r9, SAFEPDF_VIEWER_SMOKE_MODE=thumbperf), reported only: the
# git-ignored corpus paper when present.
for f in corpus/files/arxiv-1706.03762.pdf; do
  [ -f "$f" ] || continue
  SAFEPDF_VIEWER_VIEW= SAFEPDF_VIEWER_SMOKE_MODE=thumbperf run_viewer "$work/out-thperf" "$f" || true
  tr '\n' ' ' < "$work/out-thperf/thumbperf.txt" 2>/dev/null | sed 's/^/thumbperf: /'; echo
done

case_begin "1v attach"
# 1v. Attachments panel (task 9.r10, SAFEPDF_VIEWER_SMOKE_MODE=attach, `Viewer.smokeAttach`)
#     on generated PDFs: att.pdf (/PageMode /UseAttachments, an outline, /EmbeddedFiles tree
#     with kids: hello.txt (plain, /Desc, /Params) and data.bin (FlateDecode, no /Size), an
#     external file specification, a file attachment annotation on page 2 whose /UF is
#     "../../etc/evil:name.txt" with a right-to-left override) opens on the attachments panel
#     with both switcher buttons; Save attachment as... writes exactly the decoded bytes of
#     every embedded file (compared with the generator's payloads and with pdfdetach when
#     installed), proposes the sanitized name (evil_name.txt), refuses the external one, the
#     opened PDF (unchanged), a read-only file (unchanged), a read-only folder and a folder;
#     listing decodes nothing (data.bin: "?" until its tooltip probe); a click on the
#     annotation's icon opens the panel on its row; outline.pdf and noatt.pdf (no
#     attachments) have no Show Attachments button.
mkdir -p "$work/att" "$work/out-att"
python3 -I -c '
import sys, zlib
out = sys.argv[1]
hello = b"Hello from an attachment.\n"
data = bytes(range(256)) * 40
evil = b"note \xe2\x9c\x93 inside\n"
def pdf(cat, pages, extra):
    objs = {1: "<< /Type /Catalog /Pages 2 0 R " + cat + " >>",
            2: "<< /Type /Pages /Kids [%s] /Count %d /MediaBox [0 0 612 792] >>" % (
                " ".join("%d 0 R" % (3 + i) for i in range(len(pages))), len(pages))}
    for i, annots in enumerate(pages):
        objs[3 + i] = "<< /Type /Page /Parent 2 0 R /Contents 9 0 R %s >>" % annots
    c = "0.6 g 72 600 300 100 re f"
    objs[9] = "<< /Length %d >>\nstream\n%s\nendstream" % (len(c), c)
    objs.update(extra)
    n = max(objs) + 1
    body, offs = b"%PDF-1.7\n", {}
    for k in sorted(objs):
        offs[k] = len(body)
        v = objs[k]
        if isinstance(v, str): v = v.encode("latin-1")
        body += b"%d 0 obj\n" % k + v + b"\nendobj\n"
    x = len(body)
    body += b"xref\n0 %d\n0000000000 65535 f \n" % n
    body += b"".join((b"%010d 00000 n \n" % offs[k]) if k in offs else b"0000000000 65535 f \n" for k in range(1, n))
    body += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (n, x)
    return body
def stream(d, raw):
    return b"<< " + d.encode() + b" /Length %d >>\nstream\n" % len(raw) + raw + b"\nendstream"
outline = {20: "<< /Type /Outlines /First 21 0 R /Last 21 0 R /Count 1 >>",
           21: "<< /Title (Start) /Parent 20 0 R /Dest [3 0 R /Fit] >>"}
uf = "".join("%04X" % ord(ch) for ch in "../../etc/evil:name.txt‮")
att = {10: "<< /Kids [11 0 R 12 0 R] >>",
       11: "<< /Limits [(data.bin) (hello.txt)] /Names [(data.bin) 14 0 R (hello.txt) 13 0 R] >>",
       12: "<< /Limits [(z) (z)] /Names [(z) 15 0 R] >>",
       13: "<< /Type /Filespec /F (hello.txt) /UF (hello.txt) /Desc (A greeting) /EF << /F 16 0 R >> >>",
       14: "<< /Type /Filespec /F (data.bin) /EF << /F 17 0 R >> >>",
       15: "<< /Type /Filespec /F (external.pdf) >>",
       16: stream("/Type /EmbeddedFile /Subtype /text#2Fplain /Params << /Size %d /CreationDate (D:20251123101500Z) /ModDate (D:20251124) >>" % len(hello), hello),
       17: stream("/Type /EmbeddedFile /Filter /FlateDecode", zlib.compress(data)),
       18: "<< /Type /Annot /Subtype /FileAttachment /Rect [400 600 430 640] /FS 19 0 R /Contents (attached) /AP << /N 22 0 R >> >>",
       19: "<< /Type /Filespec /F (evil.txt) /UF <FEFF" + uf + "> /EF << /F 23 0 R >> >>",
       22: stream("/Type /XObject /Subtype /Form /BBox [0 0 30 40]", b"0 0 1 rg 0 0 30 40 re f"),
       23: stream("/Type /EmbeddedFile", evil)}
att.update(outline)
open(out + "/att.pdf", "wb").write(pdf("/PageMode /UseAttachments /Outlines 20 0 R /Names << /EmbeddedFiles 10 0 R >>", ["", "/Annots [18 0 R]"], att))
open(out + "/outline.pdf", "wb").write(pdf("/Outlines 20 0 R", ["", ""], outline))
open(out + "/noatt.pdf", "wb").write(pdf("", ["", ""], {}))
for n, b in [("hello", hello), ("data", data), ("evil", evil)]:
    open("%s/%s.expect" % (out, n), "wb").write(b)
' "$work/att"
cp "$work/att/att.pdf" "$work/att/att.orig"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_VIEW= SAFEPDF_VIEWER_SMOKE_MODE=attach \
  run_viewer "$work/out-att" "$work/att/att.pdf" || true
cut -c1-200 "$work/out-att/attach.txt" 2>/dev/null || true
if command -v pdfdetach >/dev/null 2>&1; then
  mkdir -p "$work/att/detach"
  pdfdetach -saveall -o "$work/att/detach" "$work/att/att.pdf" >/dev/null 2>&1 || true
fi
python3 -I -c '
import os, sys
att, outd = sys.argv[1], sys.argv[2]
try: lines = open(outd + "/attach.txt", encoding="utf-8").read().splitlines()
except OSError: print("FAIL: attach: no attach.txt", file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
errs = []
def want(k, part):
    if part not in v.get(k, ""): errs.append("%s = %r lacks %r" % (k, v.get(k), part))
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
want("start", "shown=true panel=attachments outlineBtn=1 attBtn=1 list=1 toggle=1 atts=4")
want("rows", "data.bin|?;hello.txt|26 B;external.pdf|\u2014;../../etc/evil:name.txt|16 B")
want("tip0", "Stored: ")
want("tip0", "(compressed)")
want("probed", "data.bin|10 KB;hello.txt|26 B")
want("tip1", "A greeting / Type: text/plain / Created: 2025-11-23 10:15 / Modified: 2025-11-24")
read = lambda p: open(p, "rb").read()
expect = {0: "data", 1: "hello", 3: "evil"}
for k, n in expect.items():
    want("save-%d" % k, "saved attachment")
    p = "%s/save-%d.bin" % (outd, k)
    if not os.path.exists(p) or read(p) != read("%s/%s.expect" % (att, n)):
        errs.append("save-%d: bytes differ from %s" % (k, n))
want("save-3", "proposed=evil_name.txt")
want("save-1", "proposed=hello.txt")
want("save-2", "cannot save attachment external.pdf: not embedded")
if os.path.exists(outd + "/save-2.bin"): errs.append("save-2: external file written")
want("refused-pdf", "is the opened document")
want("refused-ro", "is read-only")
want("refused-rodir", "is not writable")
want("refused-folder", "is a folder")
if read(att + "/att.pdf") != read(att + "/att.orig"): errs.append("the opened PDF changed")
if read(outd + "/ro.bin") != b"read-only\n": errs.append("the read-only file changed")
if os.path.exists(outd + "/rodir/x.bin"): errs.append("written into the read-only folder")
want("select-a1", "attachment hello.txt (26 B)")
want("menu", "Save attachment as…")
want("switch-outline", "shown=true panel=outline outlineBtn=1 attBtn=1")
want("switch-outline", "list=0")
want("switch-attachments", "panel=attachments outlineBtn=1 attBtn=1")
want("switch-attachments", "list=1")
want("toggle-off", "shown=false panel=attachments")
want("toggle-on", "shown=true panel=attachments")
want("icon", "shown=true panel=attachments")
want("icon", "sel=a3 entry=3")
want("outline", "shown=true panel=outline outlineBtn=1 attBtn=0 list=0 toggle=1 atts=0")
want("noatt", "shown=false")
want("noatt", "attBtn=0 list=0 toggle=1 atts=0")
d = att + "/detach"
if os.path.isdir(d):
    for k, name in [(0, "data.bin"), (1, "hello.txt")]:
        p = os.path.join(d, name)
        if os.path.exists(p) and read(p) != read("%s/save-%d.bin" % (outd, k)):
            errs.append("save-%d differs from pdfdetach" % k)
for e in errs: print("FAIL: attach: %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/att" "$work/out-att" || fail=1

case_begin "1w layers"
# 1w. Layers panel (task 9.r11b, SAFEPDF_VIEWER_SMOKE_MODE=layers, `Viewer.smokeLayers`) on
#     generated PDFs (none in the corpus has optional content): oc.pdf (/PageMode /UseOC; one
#     page whose squares and words are in the groups Base ON, Extra OFF, Notes ON, the radio
#     pair English ON / French OFF under the UTF-16 heading "Languages" + U+202E, Locked
#     (locked, ON, nested under Notes by an unlabelled array), Orphan (ON, not in /Order:
#     listed under the collapsed "Additional Layers" heading, as PDF.js), and
#     an OCMD AllOn(Base, Extra)); oc-nomode.pdf (no page mode: Layers button, sidebar closed),
#     oc-noorder.pdf (no /Order: every group by name) and plain.pdf (/UseOC without
#     /OCProperties: no button, no note). The viewer runs on a copy (saved.pdf), adds a note,
#     saves it (incremental update) and opens it again.
mkdir -p "$work/oc" "$work/out-oc"
python3 -I -c '
import sys
out = sys.argv[1]
def pdf(objs):
    n = max(objs) + 1
    body, offs = b"%PDF-1.7\n", {}
    for k in sorted(objs):
        offs[k] = len(body)
        v = objs[k]
        if isinstance(v, str): v = v.encode("latin-1")
        body += b"%d 0 obj\n" % k + v + b"\nendobj\n"
    x = len(body)
    body += b"xref\n0 %d\n0000000000 65535 f \n" % n
    body += b"".join((b"%010d 00000 n \n" % offs[k]) if k in offs else b"0000000000 65535 f \n" for k in range(1, n))
    body += b"trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % (n, x)
    return body
def sq(tag, rgb, x, y, word=None):
    s = "/OC /%s BDC %s rg %d %d 100 100 re f" % (tag, rgb, x, y)
    if word: s += " BT /F1 20 Tf %d %d Td (%s) Tj ET" % (x, y - 30, word)
    return s + " EMC\n"
c = (sq("oa", "1 0 0", 50, 600, "alpha") + sq("ob", "0 0 1", 200, 600, "bravo") +
     sq("om", "0 0.6 0", 350, 600) + sq("oe", "1 0.5 0", 50, 400, "english") +
     sq("of", "0.5 0 0.5", 200, 400, "french") + sq("ol", "0.3 0.3 0.3", 350, 400) +
     sq("on", "0 0.5 0.5", 50, 200) + "0 g BT /F1 20 Tf 50 120 Td (always visible) Tj ET\n")
label = "<FEFF" + "".join("%04X" % ord(ch) for ch in "Languages‮") + ">"
def doc(cat, props):
    objs = {1: "<< /Type /Catalog /Pages 2 0 R " + cat + " >>",
            2: "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
            3: "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Resources << /Font << /F1 5 0 R >> "
               "/Properties << /oa 10 0 R /ob 11 0 R /om 20 0 R /oe 13 0 R /of 14 0 R /ol 15 0 R /on 16 0 R >> >> >>",
            4: "<< /Length %d >>\nstream\n%sendstream" % (len(c), c),
            5: "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
            20: "<< /Type /OCMD /OCGs [10 0 R 11 0 R] /P /AllOn >>"}
    for k, nm in [(10, "Base"), (11, "Extra"), (12, "Notes"), (13, "English"), (14, "French"),
                  (15, "Locked"), (16, "Orphan")]:
        objs[k] = "<< /Type /OCG /Name (%s) >>" % nm
    if props is not None:
        objs[1] = objs[1][:-3] + " /OCProperties 21 0 R >>"
        objs[21] = props
    return pdf(objs)
ocgs = "/OCGs [10 0 R 11 0 R 12 0 R 13 0 R 14 0 R 15 0 R 16 0 R]"
d = "/Name (Default) /OFF [11 0 R 14 0 R] /RBGroups [[13 0 R 14 0 R]] /Locked [15 0 R]"
order = "/Order [10 0 R 11 0 R [%s 13 0 R 14 0 R] 12 0 R [15 0 R]]" % label
props = "<< %s /D << %s %s >> >>" % (ocgs, d, order)
open(out + "/oc.pdf", "wb").write(doc("/PageMode /UseOC", props))
open(out + "/oc-nomode.pdf", "wb").write(doc("", props))
open(out + "/oc-noorder.pdf", "wb").write(doc("/PageMode /UseOC", "<< %s /D << %s >> >>" % (ocgs, d)))
open(out + "/plain.pdf", "wb").write(doc("/PageMode /UseOC", None))
 ' "$work/oc"
cp "$work/oc/oc.pdf" "$work/oc/saved.pdf"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=layers \
  run_viewer "$work/out-oc" "$work/oc/saved.pdf" || true
cut -c1-200 "$work/out-oc/layers.txt" 2>/dev/null || true
python3 -I -c '
import sys
ocd, outd = sys.argv[1], sys.argv[2]
try: lines = open(outd + "/layers.txt", encoding="utf-8").read().splitlines()
except OSError: print("FAIL: layers: no layers.txt", file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
errs = []
def want(k, part):
    if part not in v.get(k, ""): errs.append("%s = %r lacks %r" % (k, v.get(k), part))
def lacks(k, part):
    if part in v.get(k, ""): errs.append("%s = %r has %r" % (k, v.get(k), part))
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
white, blue, green, orange, purple = "(255 255 255)", "(0 0 255)", "(0 153 0)", "(255 128 0)", "(128 0 128)"
want("start", "shown=true panel=layers layersBtn=true list=1 rows=9 title=Layers")
lacks("start", "not available")
tree = "0:Base:1;0:Extra:0;0:[Languages];1:English:1;1:French:0;0:Notes:1;1:Locked:1:locked;0:[Additional Layers];1:Orphan:1:hidden"
want("rows", tree)
want("additional-open", ";0:[Additional Layers];1:Orphan:1")
lacks("additional-open", "Orphan:1:hidden")
want("orphan-off", "1:Orphan:0")
want("px-orphan", "orphan=%s" % white)
want("px-orphan-on", "orphan=(0 128 128)")
want("px-start", "base=(255 0 0) extra=%s ocmd=%s en=%s fr=%s locked=(77 77 77) orphan=(0 128 128)" % (white, white, orange, white))
want("text-start", "alpha=1 bravo=0 english=1 french=0 always=1")
want("thumb-start", "have=true px=%s" % white)
want("extra-on", "0:Extra:1;")
want("px-extra", "extra=%s ocmd=%s" % (blue, green))
want("text-extra", "bravo=1")
want("french-on", "1:English:0;1:French:1;")
want("px-french", "en=%s fr=%s" % (white, purple))
want("text-french", "english=0 french=1")
want("locked", "1:Locked:1:locked")
want("locked", "status=layer Locked is locked")
want("px-locked", "locked=(77 77 77)")
want("collapsed", "1:English:0:hidden;1:French:1:hidden;")
want("expanded", "1:English:0;1:French:1;")
want("thumb-after", "have=true px=%s" % blue)
want("saved", "dirty=false status=saved 1 new")
want("saved-rows", "0:Extra:1;0:[Languages];1:English:0;1:French:1;")
want("px-saved", "extra=%s ocmd=%s en=%s fr=%s" % (blue, green, white, purple))
want("reopened", "shown=true panel=layers layersBtn=true")
want("reopened-rows", tree)
want("px-reopened", "extra=%s ocmd=%s en=%s fr=%s" % (white, white, orange, white))
want("text-reopened", "alpha=1 bravo=0 english=1 french=0")
want("oc-nomode", "shown=false")
want("oc-nomode", "layersBtn=true")
want("oc-noorder", "shown=true panel=layers layersBtn=true list=1 rows=7")
lacks("oc-noorder-rows", "Additional")
want("oc-noorder-rows", "0:Base:1;0:Extra:0;0:Notes:1;0:English:1;0:French:0;0:Locked:1:locked;0:Orphan:1")
want("plain", "shown=false")
want("plain", "layersBtn=false")
lacks("plain", "not available")
# Save wrote an incremental update that leaves /OCProperties (and the catalog) alone.
orig = open(ocd + "/oc.pdf", "rb").read()
saved = open(ocd + "/saved.pdf", "rb").read()
if not saved.startswith(orig) or len(saved) <= len(orig):
    errs.append("saved.pdf is not an incremental update of oc.pdf")
else:
    tail = saved[len(orig):]
    for bad in [b"OCProperties", b"/OCGs", b"/ON", b"/OFF", b"\n1 0 obj", b"\n21 0 obj"]:
        if bad in tail: errs.append("the update writes %r" % bad)
for e in errs: print("FAIL: layers: %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/oc" "$work/out-oc" || fail=1
if command -v qpdf >/dev/null 2>&1; then
  qpdf --check "$work/oc/saved.pdf" >/dev/null 2>&1 || { echo "FAIL: layers: qpdf --check saved.pdf" >&2; fail=1; }
fi

case_begin "2 bad inputs"
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
case_end

# New cases go here, each starting with `case_begin "NAME"` so the summary names it.

case_begin "1x undo"
# 1x. Delete and undo/redo on marks (task 10.7, SAFEPDF_VIEWER_SMOKE_MODE=undo, `Viewer.smokeUndo`)
# on a copy of the text PDF of 1d: Backspace removes the selected highlight, Ctrl+Z restores it
# (pixels), Ctrl+Shift+Z removes it again, undoing everything is clean (Undo disabled); a
# note's text edit and creation are undone and redone; after Ctrl+S (Overwrite) the saved
# highlight is deleted with Delete and restored with Ctrl+Z (clean again, drawn from the
# file), then recoloured green and saved: the file holds both marks; with the highlight
# selected, Backspace and Delete typed into the find entry and a note popup edit their text
# (marks and page unchanged). Clicks carry -time and take `world`'s position from the current
# view each time (task 10.14: on Aqua untimed clicks were double clicks selecting the word, so
# the note became the highlight's comment and went with it). Externally: qpdf --check.
mkdir -p "$work/undo" "$work/out-undo"
cp "$work/text.pdf" "$work/undo/text.pdf"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=undo run_viewer "$work/out-undo" "$work/undo/text.pdf"
cat "$work/out-undo/undo.txt"
python3 -I -c '
import sys
v = dict(l.split(": ", 1) for l in open(sys.argv[1], encoding="utf-8").read().splitlines() if ": " in l)
want = {
    "start": "0 white disabled disabled",
    "highlighted": "1 tinted true normal disabled",
    "select-click": "true false",
    "backspace": "true 0 white normal disabled",
    "undo-delete": "1 tinted true normal normal",
    "redo-delete": "0 white normal disabled",
    "undo-all": "0 white false false disabled normal",
    "undo-empty": "0 nothing to undo",
    "redo-highlight": "1 tinted normal normal",
    "note": "true first normal disabled",
    "note-anchor": "(some point)",
    "note-edited": "second",
    "note-undo1": "first",
    "note-undo2": "[]",
    "note-undo3": "<none> 1",
    "note-redo": "first 2 normal normal",
    "saved": "true 2 false false tinted disabled disabled",
    "saved-select": "true false",
    "saved-delete": "true 1 true true white normal",
    "saved-undo": "2 false false tinted disabled true true",
    "resaved": "2 false (some green) 83 255 188 disabled disabled",
    "file-marks": "2 2",
    "find-keys": "ad 2 true false true",
    "note-keys": "fst 2 true",
    "note-far": "true point false",
    "note-inside": "quads false",
}
errs = ["undo %s: %r, expected %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
for e in errs: print("FAIL: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-undo/undo.txt" || fail=1
if command -v qpdf >/dev/null 2>&1; then
  qpdf --check "$work/undo/text.pdf" >/dev/null 2>&1 || { echo "FAIL: undo: qpdf --check" >&2; fail=1; }
else echo "viewer-smoke: qpdf missing, check skipped"; fi
case_begin "10.6 dismiss"
# 10.6. Escape and click-away dismiss every transient (task 10.6, SAFEPDF_VIEWER_SMOKE_MODE=dismiss,
#     `Viewer.smokeDismiss`, rule in `Toolbar.Transient`) on the text PDF: the find bar closes
#     on a drag on the page (which still selects) and on Escape; Ctrl+F closes the go-to bar;
#     a press inside the go-to bar keeps it, one on the status line closes it; the Highlight
#     and Add text pop-overs stay on presses inside them and on the page, close on a press
#     elsewhere and on Escape (tool / mode stay on); the colour picker closes on a press off
#     the page; a note popup closes on a press on the page keeping its typed text (9.r12) and,
#     empty, on Escape in the main window (the note goes).
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=dismiss run_viewer "$work/out-dismiss" "$work/text.pdf" || true
cat "$work/out-dismiss/dismiss.txt" 2>/dev/null | cut -c1-160 || true
python3 -I -c '
import sys
try: lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
except OSError: print("FAIL: dismiss: no dismiss.txt", file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
want = {
    "find-open": "1 focus=.find.e",
    "find-drag": "0 sel=true focus=.c",
    "find-esc": "0",
    "goto-open": "1",
    "goto-rival": "goto=0 find=1",
    "goto-inside": "1",
    "goto-away": "0",
    "hl-open": "1 tool=true",
    "hl-inside": "1",
    "hl-page": "1",
    "hl-away": "0 tool=true",
    "hl-reopen": "1 tool=true",
    "hl-esc": "0 tool=true",
    "hl-off": "false",
    "ed-open": "1 text=true",
    "ed-away": "0 text=true",
    "ed-esc": "0 text=true",
    "picker-open": "true",
    "picker-away": "false false",
    "note-inside": "1",
    "note-away": "popup=0 notes=1 text=kept by a click away",
    "note-open": "popup=1 notes=2",
    "note-esc": "popup=0 notes=1",
}
import os, re
if os.environ.get("SAFEPDF_SMOKE_BG") == "1":  # no keyboard focus in background mode
    nf = lambda s: re.sub(r" ?focus=\S*", "", s)
    want = {k: nf(w) for k, w in want.items()}; v = {k: nf(x) for k, x in v.items()}
errs = ["%s = %r, want %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
for e in errs: print("FAIL: dismiss: %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-dismiss/dismiss.txt" || fail=1

case_begin "10.10 tint"
# 10.10. Highlight fills (SAFEPDF_VIEWER_SMOKE_MODE=tint, `Viewer.smokeTint`) on a generated page:
# "Hello safe world" over a black marker under "safe" (as 1d), then 40 lines of 14 "safe"s
# (561 search hits; Helvetica unpainted). On Aqua the selection (Ctrl+A) and the search hits
# are translucent photo image items above the page image (one photo per colour and size,
# none left once closed); the probed fill pixels composited over the probed page pixels keep
# the marker's ink dark and tint white paper (selection blue, current hit orange, other hits
# yellow). Background mode cannot capture the window, so the composite is computed here from
# the two image pixels and the stacking order. On X11 the hits stay stippled rectangles; the
# selection is photo items on both platforms (10.18). Drawing times are printed, not checked.
# Selection bands (10.18): Ctrl+A draws one band per line (41), each spanning its line's full
# width; the 40 body lines' bands touch (each bottom is the next top), the heading's band is not
# joined to them (paragraph break); a selection from mid line 3 to mid line 5 draws 3 bands
# (start glyph to line end, full line, line start to end glyph) that touch, and the paper
# between two selected lines is tinted (a sel photo pixel with alpha there).
python3 -I -c '
import sys
lines = b"".join(b"0 -15 Td (%s) Tj\n" % (b"safe " * 14) for _ in range(40))
c = (b"0 g 118.008 700 34.02 12.6 re f\n"
     b"BT /F1 18 Tf 72 700 Td (Hello safe world) Tj ET\n"
     b"BT /F1 12 Tf 72 675 Td " + lines + b"ET\n")
objs = [b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R "
        b"/Resources << /Font << /F1 5 0 R >> >> >>",
        b"<< /Length %d >>\nstream\n" % len(c) + c + b"endstream",
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>"]
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
' "$work/tint.pdf"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=tint run_viewer "$work/out-tint" "$work/tint.pdf" \
  || { echo "FAIL: tint: run failed" >&2; fail=1; }
cat "$work/out-tint/tint.txt" 2>/dev/null || true
python3 -I -c '
import re, sys
try: lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
except OSError: print("FAIL: tint: no tint.txt", file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
errs = []
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
aqua = v.get("aqua") == "true"
if aqua != (sys.argv[2] == "aqua"): errs.append("aqua = %r on %s" % (v.get("aqua"), sys.argv[2]))
kind = "image" if aqua else "rectangle"
kv = lambda k: dict(re.findall(r"(\w+)=(\S+)", v.get(k, "")))
sel, hit, closed = kv("sel"), kv("hit"), kv("closed")
if sel.get("kind") != "image": errs.append("selection drawn as %r, want image (both platforms, 10.18)" % sel.get("kind"))
if hit.get("kind") != kind: errs.append("hits drawn as %r, want %s" % (hit.get("kind"), kind))
if int(sel.get("items", 0)) != 41: errs.append("select-all: %r items, want one band per line (41)" % sel.get("items"))
# Selection bands (10.18).
bands = lambda k: [tuple(int(t) for t in b.split(",")) for b in v.get(k, "").split(";") if b.count(",") == 3]
sb, lx = bands("sel-bands"), [tuple(int(t) for t in b.split(",")) for b in v.get("sel-lines", "").split(";") if "," in b]
print("tint sel-bands: %d bands, first %r, last %r" % (len(sb), sb[:2], sb[-1:]))
if len(sb) != 41 or len(lx) != 41: errs.append("select-all: %d bands, %d lines, want 41" % (len(sb), len(lx)))
else:
    for i, (b, l) in enumerate(zip(sb, lx)):
        if abs(b[0] - l[0]) > 1 or abs(b[2] - l[1]) > 1: errs.append("band %d x %r, line %r" % (i, (b[0], b[2]), l)); break
    for i in range(1, 40):
        if sb[i][3] != sb[i + 1][1]: errs.append("bands %d/%d do not touch: %r %r" % (i, i + 1, sb[i], sb[i + 1])); break
    if sb[0][3] >= sb[1][1]: errs.append("heading band joined to the body: %r %r" % (sb[0], sb[1]))
    if not all(b[3] - b[1] >= 15 for b in sb[1:]): errs.append("body bands thinner than a line: %r" % sb[1:3])
s3 = bands("sel3-bands")
ends = [int(t) for t in v.get("sel3-ends", "").split(",") if t.lstrip("-").isdigit()]
print("tint sel3: %r ends %r" % (s3, ends))
if len(s3) != 3 or len(ends) != 2 or len(lx) != 41: errs.append("3-line selection: %r ends %r" % (s3, v.get("sel3-ends")))
else:
    (f, m, l) = s3
    if abs(f[0] - ends[0]) > 1 or abs(f[2] - lx[3][1]) > 1: errs.append("first band %r: want start %d to line end %d" % (f, ends[0], lx[3][1]))
    if abs(m[0] - lx[4][0]) > 1 or abs(m[2] - lx[4][1]) > 1: errs.append("interior band %r: want line %r" % (m, lx[4]))
    if abs(l[0] - lx[5][0]) > 1 or abs(l[2] - ends[1]) > 1: errs.append("last band %r: want line start %d to end %d" % (l, lx[5][0], ends[1]))
    if f[3] != m[1] or m[3] != l[1]: errs.append("3-line bands do not touch: %r" % (s3,))
gap = re.search(r"sel=image\((\d+) (\d+) (\d+) (\d+)\)", v.get("sel3-gap", ""))
if not gap or int(gap.group(4)) == 0: errs.append("paper between selected lines not tinted: %r" % v.get("sel3-gap"))
if int(hit.get("items", 0)) != 561: errs.append("search: %r hit items, want 561" % hit.get("items"))
if "hit 1/561 on page 1" not in v.get("hit", ""): errs.append("search status: %r" % v.get("hit"))
if closed != {"items": "0", "photos": "0"}: errs.append("after closing: %r" % v.get("closed"))
if aqua and int(hit.get("photos", 99)) > 12:
    errs.append("561 hits made %r photos (one per colour and size expected)" % hit.get("photos"))
def probe(k):
    # [(tag, kind, (r, g, b, a) or None)] bottom to top
    out = []
    for part in v.get(k, "").split(";"):
        m = re.match(r"([^=]*)=(\w+)(?:\(([^)]*)\))?$", part)
        if not m: continue
        px = tuple(int(t) for t in m.group(3).split()) if m.group(3) and m.group(3)[0].isdigit() else None
        out.append((m.group(1), m.group(2), px))
    return out
over = lambda a, f, p: (f * a + p * (255 - a) + 127) // 255
def comp(k, tag, rgb, alpha):
    items = probe(k)
    pg = [i for i, t in enumerate(items) if t[0] == "pimg"]
    fl = [i for i, t in enumerate(items) if t[0] == tag]
    if not pg or not fl: errs.append("%s: page or %s item missing: %r" % (k, tag, v.get(k))); return None
    if fl[-1] < pg[0]: errs.append("%s: the fill lies under the page image" % k)
    p, f = items[pg[0]][2], items[fl[-1]][2]
    if p is None or f is None or len(f) != 4: errs.append("%s: pixels %r" % (k, v.get(k))); return None
    if f[:3] != rgb or not alpha[0] <= f[3] <= alpha[1]:
        errs.append("%s: fill pixel %r, want %r at alpha %r" % (k, f, rgb, alpha))
    c = tuple(over(f[3], f[i], p[i]) for i in range(3))
    print("tint %s: page %r + fill %r -> %r" % (k, p[:3], f, c))
    return p[:3], c
lum = lambda c: (299 * c[0] + 587 * c[1] + 114 * c[2]) // 1000
# The selection is a photo fill on both platforms (10.18), the hits on Aqua only.
rs = [comp("sel-ink", "sel", (56, 116, 242), (64, 128)), comp("sel-paper", "sel", (56, 116, 242), (64, 128))]
if None not in rs:
    (pi, si), (pp, sp) = rs
    # The ink shows through: the fill over the marker stays much darker than over paper.
    if lum(si) + 100 > lum(sp): errs.append("selection hides the ink: %r vs paper %r" % (si, sp))
    if not (sp[2] - sp[0] > 40 and sp[0] < 230 and sp[0] > 100): errs.append("selection paper tint %r" % (sp,))
if aqua:
    r = [comp("hit-ink", "hit", (255, 165, 0), (96, 160)), comp("hit-paper", "hit", (255, 255, 0), (96, 160))]
    if None not in r and None not in rs:
        (pi, si), (pp, sp) = rs
        (hpi, hi), (hpp, hp) = r
        if max(pi + hpi) > 64 or min(pp + hpp) < 250: errs.append("probe points: ink %r %r, paper %r %r" % (pi, hpi, pp, hpp))
        if lum(hi) + 60 > lum(hp): errs.append("current hit hides the ink: %r vs paper %r" % (hi, hp))
        # The paper is tinted, not white and not opaque colour.
        if not (hp[0] > 240 and hp[1] > 240 and 80 < hp[2] < 200): errs.append("hit paper tint %r" % (hp,))
for k in ("ms-sel", "ms-hits", "ms-all", "ms-all-other", "ms-fullpage-photo"):
    print("tint %s: %s" % (k, v.get(k)))
for e in errs: print("FAIL: tint: %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-tint/tint.txt" "$platform" || fail=1

case_begin "10.8 tools"
# 10.8. Select-text tool and cursors (SAFEPDF_VIEWER_SMOKE_MODE=tools, `Viewer.smokeTools`, model
#     `Toolbar.Mode` / `Toolbar.cursorFor`) on a page with "Hello safe world" and a link over
#     blank paper: Select text is the default tool, pressed; the canvas cursor is the I-beam
#     over text, the hand over the link, the default arrow on blank paper; Draw unpresses
#     Select text and shows the crosshair (at once and over text); its button again gives
#     Select text back; Escape keeps Highlight on, the Select text button ends it; Add text
#     shows the I-beam over the link.
python3 -I -c '
import sys
c = b"BT /F1 18 Tf 72 700 Td (Hello safe world) Tj ET\n"
objs = [b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Contents 4 0 R "
        b"/Resources << /Font << /F1 5 0 R >> >> /Annots [6 0 R] >>",
        b"<< /Length %d >>\nstream\n" % len(c) + c + b"endstream",
        b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>",
        b"<< /Type /Annot /Subtype /Link /Rect [72 500 300 540] /Border [0 0 0] /Dest [3 0 R /Fit] >>"]
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
' "$work/tools.pdf"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=tools run_viewer "$work/out-tools" "$work/tools.pdf" || true
cat "$work/out-tools/tools.txt" 2>/dev/null || true
python3 -I -c '
import sys
try: lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
except OSError: print("FAIL: tools: no tools.txt", file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
want = {
    "tool0": "select select=1 highlight=0 text=0 draw=0",
    "select-state": "normal",
    "cursor-text": "[xterm]",
    "cursor-link": "[hand2]",
    "cursor-empty": "[]",
    "draw-on": "draw select=0 highlight=0 text=0 draw=1",
    "cursor-draw-still": "[crosshair]",
    "cursor-draw-text": "[crosshair]",
    "draw-off": "select select=1 highlight=0 text=0 draw=0",
    "cursor-after-draw": "[xterm]",
    "hl-on": "highlight select=0 highlight=1 text=0 draw=0 popover=true",
    "hl-esc": "highlight select=0 highlight=1 text=0 draw=0 popover=false",
    "select-btn": "select select=1 highlight=0 text=0 draw=0 popover=false",
    "select-again": "select select=1 highlight=0 text=0 draw=0",
    "text-on": "text select=0 highlight=0 text=1 draw=0",
    "cursor-text-link": "[xterm]",
    "cursor-select-link": "[hand2]",
}
errs = ["%s = %r, want %r" % (k, v.get(k), w) for k, w in want.items() if v.get(k) != w]
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
for e in errs: print("FAIL: tools: %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-tools/tools.txt" || fail=1

case_begin "12.5 honest"
# 12.5. Honest UI for hidden content (SAFEPDF_VIEWER_SMOKE_MODE=honest, `Viewer.smokeHonest`)
#     on generated files: select all + copy on a page with a `3 Tr` line copies it and says
#     how many copied characters the page does not show; the trusted identity line (.ident,
#     file name and path, drawn by the viewer outside the page) is packed in document full
#     screen (/PageMode /FullScreen) and while /HideToolbar hides the toolbar, and gone after
#     Escape and on a plain file; saving a highlight gives no notice, deleting that saved
#     highlight and saving again gives the revision-retention notice.
mkdir -p "$work/honest"
python3 -I -c '
import sys
out = sys.argv[1]
def pdf(cat, content):
    objs = {1: "<< /Type /Catalog /Pages 2 0 R " + cat + " >>",
            2: "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
            3: "<< /Type /Page /Parent 2 0 R /Contents 4 0 R /Resources << /Font << /F1 5 0 R >> >> >>",
            4: "<< /Length %d >>\nstream\n%s\nendstream" % (len(content), content),
            5: "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>"}
    body, offs = b"%PDF-1.7\n", {}
    for n in sorted(objs):
        offs[n] = len(body)
        body += ("%d 0 obj\n%s\nendobj\n" % (n, objs[n])).encode("latin-1")
    x = len(body)
    body += b"xref\n0 6\n0000000000 65535 f \n" + b"".join(b"%010d 00000 n \n" % offs[n] for n in range(1, 6))
    body += ("trailer\n<< /Size 6 /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n" % x).encode()
    return body
text = "BT /F1 24 Tf 72 700 Td (Visible line) Tj ET BT /F1 24 Tf 3 Tr 72 650 Td (hidden words) Tj ET"
open(out + "/ocr.pdf", "wb").write(pdf("", text))
open(out + "/full.pdf", "wb").write(pdf("/PageMode /FullScreen", text))
open(out + "/prefs.pdf", "wb").write(pdf("/ViewerPreferences << /HideToolbar true >>", text))
' "$work/honest"
SAFEPDF_SUBST_FONTS=0 SAFEPDF_VIEWER_SMOKE_MODE=honest run_viewer "$work/out-honest" "$work/honest/ocr.pdf" || true
cat "$work/out-honest/honest.txt" 2>/dev/null || true
python3 -I -c '
import sys
try: lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
except OSError: print("FAIL: honest: no honest.txt", file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
errs = []
def has(k, *parts):
    for p in parts:
        if p not in v.get(k, ""): errs.append("%s lacks %r: %r" % (k, p, v.get(k)))
def lacks(k, p):
    if k not in v or p in v[k]: errs.append("%s has %r (or is missing): %r" % (k, p, v.get(k)))
has("copy", "hidden-in-clipboard=true", "status=copied ", "; the copied text includes 12 characters that are not visible on the page")
has("plain", "ident= ")
for f in ["full", "prefs"]:
    has(f, "ident=pack", "text=SafePDF is showing %s.pdf (" % f, "/%s.pdf) - this line is drawn by SafePDF" % f)
    has(f + "-escape", "ident= full=false")
has("full", "full=true", "full screen (Escape leaves)")
has("prefs", "the document hides parts of the window")
has("save1", "marks=1 saved=1", "status=saved 1 new, changed or deleted mark(s)")
lacks("save1", "deleted mark(s) are still")
has("deleted", "dirty=true deletedSaved=1")
has("save2", "marks=0", "note: the 1 deleted mark(s) are still in the file" + chr(39) + "s earlier revision (Save only appends an update) and can be recovered from it")
if "done" not in lines: errs.append("not done: %r" % lines[-1:])
for e in errs: print("FAIL: honest: %s" % e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-honest/honest.txt" || fail=1

case_begin "12.2c worker"
# 12.2c. The document worker (SAFEPDF_VIEWER_SMOKE_MODE=worker, `Viewer.smokeWorker`, deadline
#     SAFEPDF_WORKER_DEADLINE_MS=4000): the two-page PDF's pages come from the worker; render
#     times in the viewer process and through the worker are printed (reported only);
#     (a) no-block: workers that sleep 1.5 s before each render (`Worker.TestHooks`), no event
#     waiting for renders, a 10 ms Tcl heartbeat: the zoom event returns at once, the largest
#     heartbeat gap stays under 250 ms, the page arrives; (b) kill/restart: workers that sleep
#     ten minutes: after the deadline the page and the status line say "rendering stopped: the
#     document took too long", the worker was killed (timeouts counted); (c) the same document
#     renders again in a fresh worker; (d) the next file (the corpus paper of
#     SAFEPDF_SMOKE_WORKER_PAPER when present, else the nav PDF of 1e) opens, renders and has
#     its outline, read by its own worker.
wpaper="${SAFEPDF_SMOKE_WORKER_PAPER-corpus/files/arxiv-1706.03762.pdf}"
mkdir -p "$work/out-worker"
if [ -n "$wpaper" ] && [ -f "$wpaper" ]; then cp "$wpaper" "$work/out-worker/next.pdf"
else cp "$work/nav.pdf" "$work/out-worker/next.pdf"; fi
if [ ! -x "$repo/.lake/build/bin/worker" ]; then
  echo "FAIL: worker: no worker executable" >&2; fail=1
else
  SAFEPDF_VIEWER_SMOKE_MODE=worker SAFEPDF_WORKER_DEADLINE_MS=4000 \
    run_viewer "$work/out-worker" "$work/two.pdf" || { echo "FAIL: worker run failed" >&2; fail=1; }
  cat "$work/out-worker/worker.txt" 2>/dev/null || true
  python3 -I -c '
import re, sys
try: lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
except OSError: print("FAIL: worker: no worker.txt", file=sys.stderr); sys.exit(1)
v = dict(l.split(": ", 1) for l in lines if ": " in l)
errs = []
def need(cond, msg):
    if not cond: errs.append(msg)
def num(k, rx):
    m = re.search(rx, v.get(k, ""))
    return int(m.group(1)) if m else -1
if "error" in v: errs.append("smoke step failed: %s" % v["error"])
need(re.match(r"page 1 image \d+x\d+ worker-renders [1-9]", v.get("open", "")), "open: %r" % v.get("open"))
need(num("open", r"spawns (\d+)") == 1, "open: one worker expected: %r" % v.get("open"))
need("worker" in v.get("measure-a", ""), "measure-a: %r" % v.get("measure-a"))
# Task 12.2d: the page text index and links came from the worker and equal the in-process ones.
need(num("text", r"worker-texts (\d+)") >= 1 and "same-text true" in v.get("text", "")
     and num("text", r"chars (\d+)") >= 0, "text: %r" % v.get("text"))
need(num("text", r"worker-links (\d+)") >= 1 and "same-links true" in v.get("text", ""),
     "links: %r" % v.get("text"))
print("worker: text: %s" % v.get("text"))
need(0 <= num("a-event-ms", r"(\d+)") < 250, "the zoom event blocked: %r" % v.get("a-event-ms"))
need(v.get("noblock", "").startswith("image "), "no-block: no page image: %r" % v.get("noblock"))
need(num("noblock", r"elapsed-ms (\d+)") >= 1500, "no-block: the stall did not happen: %r" % v.get("noblock"))
need(0 <= num("noblock", r"max-gap-ms (\d+)") < 250, "no-block: the heartbeat stalled: %r" % v.get("noblock"))
need(0 <= num("b-event-ms", r"(\d+)") < 250, "the zoom event blocked (b): %r" % v.get("b-event-ms"))
need("error: rendering stopped: the document took too long" in v.get("stalled", ""), "stalled page: %r" % v.get("stalled"))
need(num("stalled", r"timeouts (\d+)") >= 1, "no timeout counted: %r" % v.get("stalled"))
need(4000 <= num("stalled", r"elapsed-ms (\d+)") < 30000, "stalled: elapsed: %r" % v.get("stalled"))
need(0 <= num("stalled", r"max-gap-ms (\d+)") < 250, "stalled: the heartbeat stalled: %r" % v.get("stalled"))
need("cannot render: rendering stopped: the document took too long" in v.get("stalled-status", ""), "status: %r" % v.get("stalled-status"))
need(v.get("respawn", "").startswith("image ") and num("respawn", r"spawns (\d+)") > num("stalled", r"spawns (\d+)"),
     "same document in a fresh worker: %r" % v.get("respawn"))
need(re.match(r"page 1/\d+ image \d+x\d+ outline [1-9]", v.get("next", "")), "next file: %r" % v.get("next"))
need(num("next", r"spawns (\d+)") > num("respawn", r"spawns (\d+)"), "next file: no new worker: %r" % v.get("next"))
need("rendered in" in v.get("next-status", ""), "next status: %r" % v.get("next-status"))
need("done" in lines, "the run did not finish")
for k in ["measure-a", "measure-b"]: print("worker: %s: %s" % (k, v.get(k)))
for e in errs: print("FAIL: worker: " + e, file=sys.stderr)
sys.exit(1 if errs else 0)
' "$work/out-worker/worker.txt" || fail=1
fi

# Summary (task 10.11): cases passed / skipped (with the reason) / failed on this platform.
case_end
if [ "$fail" != 0 ] && [ "${#cases_fail[@]}" = 0 ]; then cases_fail+=("(a check outside any case_begin)"); fi
echo "viewer-smoke: summary ($platform): ${#cases_pass[@]} passed, ${#cases_skip[@]} skipped, ${#cases_fail[@]} failed"
for c in ${cases_skip[@]+"${cases_skip[@]}"}; do echo "viewer-smoke:   skipped: $c"; done
for c in ${cases_fail[@]+"${cases_fail[@]}"}; do
  why=""
  for k in ${known_bugs[@]+"${known_bugs[@]}"}; do
    if [ "${k%%|*}" = "$c" ]; then why=" (KNOWN-MAC-BUG: ${k#*|})"; fi
  done
  echo "viewer-smoke:   FAILED: $c$why"
done
if [ "$fail" = 0 ]; then echo "viewer-smoke: OK"; else echo "viewer-smoke: FAILED" >&2; fi
exit $fail
