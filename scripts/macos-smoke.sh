#!/usr/bin/env bash
# Native smoke of the macOS app (task 11.5; Plan.md §6 Phase 11, M11; docs/macos-smoke.md): the
# cases of the Tk smoke (scripts/viewer-smoke.sh) that apply to the native app, each a scripted
# headless session of the app itself (macos/App/SmokeSession.swift), run from the repo root:
#   scripts/macos-smoke.sh [--no-build] [CASE ...]     (CASE: a case name prefix, e.g. 1j)
#
# Every case writes a session script (the command language of docs/macos-smoke.md) and runs
#   SAFEPDF_MACOS_SESSION=SCRIPT SAFEPDF_MACOS_SESSION_OUT=DIR macos/build/safepdf-mac
# (SAFEPDF_SMOKE_BUNDLE=1: the bundle's binary, run in place, never through LaunchServices).
# Background discipline (10.16): the app's activation policy is Prohibited, it never activates
# or shows a window (the session also fails a step when any of its windows is visible), and a
# watcher samples the front application every 0.2 s with `lsappinfo` (no Automation or
# Accessibility permission): if the PID this script started ever is the front app or a
# Foreground app, it is killed and the case fails. Other processes are never touched.
# Fixtures: generated (scripts/viewer-smoke-pdf.py as the Tk smoke, the self-test's generators
# through the session's `fixture` command) or taken from Tests/ (copies in the work directory;
# nothing is written next to the goldens). qpdf / mutool checks run when the tools exist.
# Ends with the Tk smoke's summary: cases passed / skipped (with the reason) / failed, plus the
# watcher's samples and alerts. Exit 0 on success.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

if [ "$(uname -s)" != Darwin ]; then
  echo "macos-smoke: macOS only" >&2
  exit 1
fi

build=1
only=()
for a in "$@"; do
  case "$a" in
    --no-build) build=0 ;;
    -h|--help) sed -n '2,22p' "$0"; exit 0 ;;
    *) only+=("$a") ;;
  esac
done
if [ "$build" = 1 ]; then macos/build.sh; fi
if [ "${SAFEPDF_SMOKE_BUNDLE:-0}" = 1 ]; then
  bin="$repo/macos/build/SafePdf.app/Contents/MacOS/SafePdf"
else
  bin="$repo/macos/build/safepdf-mac"
fi
[ -x "$bin" ] || { echo "macos-smoke: $bin not built (macos/build.sh)" >&2; exit 1; }

work="$(mktemp -d)"
if [ -n "${SAFEPDF_SMOKE_KEEP:-}" ]; then
  echo "macos-smoke: keeping the outputs in $work (SAFEPDF_SMOKE_KEEP)"
else
  trap 'rm -rf "$work"' EXIT
fi

# Per-case results (the Tk smoke's bookkeeping): case_begin NAME, case_end, skip_case NAME WHY.
cases_pass=(); cases_fail=(); cases_skip=()
cur_case=""; fail=0; fail_saved=0
case_begin() {
  if [ -n "$cur_case" ]; then case_end; fi
  cur_case="$1"; fail_saved="$fail"; fail=0
}
case_end() {
  [ -n "$cur_case" ] || return 0
  if [ "$fail" = 0 ]; then cases_pass+=("$cur_case"); else cases_fail+=("$cur_case"); fi
  if [ "$fail_saved" != 0 ]; then fail=1; fi
  cur_case=""; fail_saved=0
}
skip_case() {
  echo "macos-smoke: SKIP: $1 — $2"
  cases_skip+=("$1 — $2")
}
# wanted NAME: whether the case runs (no CASE arguments, or one is a prefix of NAME).
wanted() {
  [ "${#only[@]}" = 0 ] && return 0
  local o
  for o in "${only[@]}"; do case "$1" in "$o"*) return 0 ;; esac; done
  return 1
}

# The front-app watcher's totals over the whole run.
samples=0; alerts=0
watchlog="$work/front-app.log"
: > "$watchlog"

# run_session NAME SCRIPT: runs the app on SCRIPT under the watcher (hard limit
# ${session_timeout:-300} s); its log is in $work/out-NAME/session.txt. Fails the case on a
# non-zero exit, a timeout or a watcher alert; a session's `skip` lines become skipped variants.
run_session() {
  local name="$1" script="$2" out="$work/out-$1" pid rc=0 t=0 leaked=0 limit
  limit=$(( ${session_timeout:-300} * 5 ))
  mkdir -p "$out"
  SAFEPDF_MACOS_SESSION="$script" SAFEPDF_MACOS_SESSION_OUT="$out" SAFEPDF_SESSION_IN="$work" \
    "$bin" 2>"$out/stderr.log" &
  pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    # Only the PID this script started counts (a copy launched by hand is not ours).
    local front front_pid
    front="$(lsappinfo front 2>/dev/null || true)"
    front_pid="$(lsappinfo info -only pid "$front" 2>/dev/null | tr -dc '0-9' || true)"
    printf '%s %s %s\n' "$(date +%T)" "$name" "front pid ${front_pid:-?}" >> "$watchlog"
    samples=$((samples + 1))
    if [ "$front_pid" = "$pid" ]; then
      echo "FAIL: $name: the app became the front app; killing PID $pid" >&2
      kill "$pid" 2>/dev/null || true; leaked=1
    fi
    if lsappinfo list 2>/dev/null | grep -E "pid = $pid[^0-9].*type=\"Foreground\"" >/dev/null; then
      echo "FAIL: $name: the app registered as a Foreground app; killing PID $pid" >&2
      kill "$pid" 2>/dev/null || true; leaked=1
    fi
    t=$((t + 1))
    if [ "$t" -gt "$limit" ]; then
      echo "FAIL: $name: no result after ${session_timeout:-300} s; killing PID $pid" >&2
      kill -9 "$pid" 2>/dev/null || true
    fi
    sleep 0.2
  done
  wait "$pid" || rc=$?
  if [ "$leaked" = 1 ]; then alerts=$((alerts + 1)); fi
  grep -E '^(FAIL|session:|  expect .*FAILED)' "$out/stderr.log" | sed "s/^/  [$name] /" || true
  local s
  while IFS= read -r s; do
    skip_case "$cur_case (${s#*SKIP: })" "the session skipped this step"
  done < <(grep -E '^  SKIP: ' "$out/stderr.log" || true)
  if [ "$rc" != 0 ] || [ "$leaked" = 1 ]; then
    echo "FAIL: $name: session exit $rc$([ "$leaked" = 1 ] && echo ', watcher alert')" >&2
    if [ -n "${SAFEPDF_SMOKE_VERBOSE:-}" ]; then sed 's/^/    /' "$out/stderr.log" >&2; fi
    fail=1
  fi
  return 0
}

# Fixtures shared by the cases.
python3 -I "$here/viewer-smoke-pdf.py" "$work/two.pdf"
python3 -I "$here/viewer-smoke-pdf.py" --slow 3000 "$work/slow.pdf"
cp Tests/golden/pages/tree.pdf Tests/golden/pages/outline.pdf Tests/golden/text/latin.pdf "$work/"
cp Tests/adversarial/encrypted/rc4-128.pdf Tests/adversarial/encrypted/aesv3.pdf "$work/"
mkdir -p "$work/xfdf"
cp Tests/xfdf/*.xfdf "$work/xfdf/"
have_qpdf=0; command -v qpdf >/dev/null 2>&1 && have_qpdf=1
have_mutool=0; command -v mutool >/dev/null 2>&1 && have_mutool=1

# qpdf_check FILE: qpdf --check (warnings allowed, errors not), when qpdf exists.
qpdf_check() {
  if [ "$have_qpdf" = 1 ]; then
    local r=0
    qpdf --check "$1" >"$work/qpdf.log" 2>&1 || r=$?
    if [ "$r" = 0 ] || [ "$r" = 3 ]; then echo "  qpdf --check $(basename "$1"): ok ($r)"
    else echo "FAIL: qpdf --check $(basename "$1") exit $r" >&2; sed 's/^/    /' "$work/qpdf.log" >&2; fail=1; fi
  else
    echo "  qpdf missing, check skipped"
  fi
}

# annots FILE: the /Subtype of every annotation, page by page ("p1: Highlight Text; p2: ..."),
# read by mutool (an independent PDF reader) from the last revision; empty without mutool.
# Pages through trailer/Root/Pages/Kids/N (mutool paths count from 1; flat page trees only:
# the generated fixtures).
annots() {
  [ "$have_mutool" = 1 ] || return 0
  local f="$1" n i r refs out=""
  n="$(mutool show "$f" trailer/Root/Pages/Count 2>/dev/null | tr -dc '0-9')"
  for i in $(seq 1 "${n:-0}"); do
    refs="$(mutool show "$f" "trailer/Root/Pages/Kids/$i/Annots" 2>/dev/null | grep -oE '[0-9]+ 0 R' | cut -d' ' -f1 || true)"
    local subs=""
    for r in $refs; do
      subs="$subs $(mutool show "$f" "$r" 2>/dev/null | grep -oE '/Subtype */[A-Za-z]+' | head -1 | sed 's|.*/||')"
    done
    out="$out p$i:${subs:- -};"
  done
  echo "$out"
}
# expect_annots FILE PATTERN: mutool sees the annotations PATTERN (an extended regex over
# annots' output); skipped without mutool.
expect_annots() {
  if [ "$have_mutool" = 0 ]; then echo "  mutool missing, annotation check skipped"; return 0; fi
  local got
  got="$(annots "$1")"
  if printf '%s\n' "$got" | grep -Eq "$2"; then echo "  mutool: $(basename "$1"):$got"
  else echo "FAIL: mutool: $(basename "$1"):$got does not match $2" >&2; fail=1; fi
}

# ---------------------------------------------------------------------------------------------
# Each case: `wanted NAME && { case_begin NAME; write its script; run_session; extra checks; }`.
# The Tk case each one ports is named first (docs/macos-smoke.md has the full table).

# 1 (Tk 1): the two-page vector PDF: page 1 has ink, Next page reaches page 2 (/Rotate 90:
# landscape), the window title and subtitle.
if wanted "1 two-page"; then
case_begin "1 two-page PDF"
cat > "$work/c1.txt" <<'EOF'
open $IN/two.pdf
expect pages = 2
expect title = two.pdf
expect choice = Automatic Zoom
expect errors = 0
zoom Page Fit
measure-ink
expect ink > 0.1
expect orient = portrait
cmd nextPage
expect page = 2
expect subtitle ^ page 2/2
measure-ink
expect ink > 0.001
expect orient = landscape
EOF
run_session c1 "$work/c1.txt"
fi

# 1a (Tk 1a): zoom and rotation through the Cmd keys of the menubar: Actual size, zoom in and
# out (the exported steps), page sizes scale with the zoom; rotation swaps the sides.
if wanted "1a zoom"; then
case_begin "1a zoom/rotation"
cat > "$work/c1a.txt" <<'EOF'
open $IN/two.pdf
key cmd+0
expect choice = Actual Size
expect zoom = 100
remember w100 page-w
remember h100 page-h
key cmd+plus
expect zoom = 125
key cmd+minus
key cmd+minus
expect zoom = 75
remember w75 page-w
remember h75 page-h
key cmd+r
expect rotation = 90
expect page-w near @h75 1
expect page-h near @w75 1
key cmd+l
expect rotation = 0
key cmd+l
expect rotation = 270
key cmd+r
expect rotation = 0
key cmd+9
expect choice = Page Fit
key w
expect choice = Page Width
EOF
run_session c1a "$work/c1a.txt"
fi

# 1b (Tk 1b): scrolling and anchoring (C2) at 200 %: a zoom step keeps the page point at the
# centre of the view; arrows and space scroll within the page; Page Down / Up turn pages.
if wanted "1b scroll"; then
case_begin "1b scrolling/anchoring"
cat > "$work/c1b.txt" <<'EOF'
open $IN/two.pdf
zoompct 200
remember cx centre-x
remember cy centre-y
expect centre-page = 1
key cmd+plus
expect zoom > 200
expect centre-page = 1
expect centre-x near @cx 1
expect centre-y near @cy 1
key cmd+minus
expect centre-x near @cx 1.5
expect centre-y near @cy 1.5
zoompct 200
remember top0 top
key down
key down
expect page = 1
expect top > @top0
remember top1 top
key space
expect top > @top1
cmd firstPage
key pagedown
expect page = 2
key pageup
expect page = 1
key cmd+down
expect page = 2
key cmd+up
expect page = 1
EOF
run_session c1b "$work/c1b.txt"
fi

# 1c (Tk 1c): an odd file name (spaces, brackets, braces, a dollar sign, non-ASCII).
if wanted "1c odd"; then
case_begin "1c odd file name"
odd='odd name [ü] {x} $y.pdf'
cp "$work/two.pdf" "$work/$odd"
cat > "$work/c1c.txt" <<EOF
open \$IN/$odd
expect pages = 2
expect title = $odd
expect errors = 0
EOF
run_session c1c "$work/c1c.txt"
fi

# 1d (Tk 1d, 12.5 copy): text: Select All + Copy gives the page text, a double click a word, a
# drag a range, Find across pages (the NEED path) with wrap; hidden text announced on copy.
if wanted "1d text"; then
case_begin "1d text/select/search"
cat > "$work/c1d.txt" <<'EOF'
fixture text3 $OUT/find.pdf
open $OUT/find.pdf
expect enabled:copy = 0
key cmd+a
expect selection = p1:0-19
expect enabled:copy = 1
key cmd+c
expect clipboard = needle in a haystack
dblclick 1 12
expect selection = p1:12-19
key cmd+c
expect clipboard = haystack
drag 1 0 8
expect selection ^ p1:0-
expect pill ^ page 1: selected
find needle
expect find = "needle": hit 1/1 on page 1
find-next
expect find = "needle": hit 1/2 on page 3
expect page = 3
find-next
expect find = "needle": hit 2/2 on page 3
find-next
expect find ~ (wrapped)
expect hit = 1:0
find-prev
expect hit = 3:1
find zzqqxj
expect find = "zzqqxj": not found
find-close
open $IN/latin.pdf
key cmd+a
key cmd+c
expect pill ~ 19 characters that are not visible
expect clipboard ^ First line of text.
EOF
run_session c1d "$work/c1d.txt"
fi

# 1e (Tk 1e): navigation: page labels in the page field and subtitle, an internal link with
# Back / Forward, the external link asked first (Cancel, then Copy Address: never opened), the
# outline (a jump, an external item copied, never opened), the sidebar toggle by its key.
if wanted "1e nav"; then
case_begin "1e nav"
cat > "$work/c1e.txt" <<'EOF'
open $IN/tree.pdf
expect pages = 4
expect subtitle ^ page i (1/4)
goto A-5
expect page = 3
expect subtitle ^ page A-5 (3/4)
goto nonsense
expect page = 3
cmd firstPage
link 1 1
expect page = 4
expect history-back = 1
key cmd+bracketleft
expect page = 1
key cmd+bracketright
expect page = 4
cmd firstPage
link 1 2
expect uri = http://x
expect hover_cursor = hand
link-answer cancel
expect pill = external link not followed: http://x
expect clipboard =
link 1 2
link-answer copy
expect clipboard = http://x
expect pill = copied the link address to the clipboard (not opened): http://x
open $IN/outline.pdf
expect sidebar = shown
expect panel = outline
expect outline-rows > 3
outline 0
expect page = 2
outline 3
expect uri-pending = http://example.com
outline-answer cancel
expect pill ^ external link not followed
outline 3
outline-answer copy
expect clipboard ^ http
key ctrl+cmd+s
expect sidebar = hidden
key f9
expect sidebar = shown
EOF
run_session c1e "$work/c1e.txt"
fi

# 1f (Tk 1f): the menubar's commands and their enabled states; the wheel across page
# boundaries both ways (precise deltas).
if wanted "1f menubar"; then
case_begin "1f menubar"
cat > "$work/c1f.txt" <<'EOF'
fixture text3 $OUT/m.pdf
open $OUT/m.pdf
expect enabled:prevPage = 0
expect enabled:firstPage = 0
expect enabled:nextPage = 1
expect enabled:back = 0
expect enabled:undo = 0
expect enabled:redo = 0
expect enabled:copy = 0
expect enabled:deleteMark = 0
expect enabled:save = 0
cmd lastPage
expect page = 3
expect enabled:nextPage = 0
cmd prevPage
expect page = 2
cmd firstPage
cmd fitWidth
expect choice = Page Width
cmd actualSize
expect zoom = 100
cmd fitPage
wheel -40 40
expect page > 1
expect wheel_monotonic = 1
wheel 40 80
expect page = 1
expect wheel_monotonic = 1
EOF
run_session c1f "$work/c1f.txt"
fi

# 1g (Tk 1g): the toolbar's drop-downs and page field: zoom presets, view choices, the page
# entry; the sidebar shown and hidden without an outline (thumbnails).
if wanted "1g toolbar"; then
case_begin "1g toolbar"
cat > "$work/c1g.txt" <<'EOF'
open $IN/two.pdf
expect sidebar = hidden
zoom 150%
expect zoom = 150
zoom Page Width
expect choice = Page Width
view Two Pages
expect viewchoice = Two Pages
expect radio:scrollPage = 1
view Vertical Scrolling
expect viewchoice = Vertical Scrolling
expect radio:scrollVertical = 1
goto 2
expect page = 2
cmd outline
expect sidebar = shown
expect panel = thumbnails
cmd outline
expect sidebar = hidden
EOF
run_session c1g "$work/c1g.txt"
fi

# 1h / 1x / 10.8 (Tk 1h, 1x, 10.8): highlight (yellow pixels), recolour from the Highlight
# menu, delete, undo / redo (Cmd keys), a note, marks kept across zoom, rotation and pages; the
# tool states.
if wanted "1h marks"; then
case_begin "1h marks/undo/tools"
cat > "$work/c1h.txt" <<'EOF'
fixture text3 $OUT/h.pdf
open $OUT/h.pdf
dblclick 1 0
key ctrl+cmd+h
expect marks = 1
expect last-mark ~ highlight p1 yellow
expect edited = 1
measure-mark
expect mark.b < 0.75
expect mark.g > 0.45
color red
expect last-mark ~ highlight p1 red
measure-mark
expect mark.g < 0.35
key delete
expect marks = 0
key cmd+z
expect marks = 1
key cmd+shift+z
expect marks = 0
key cmd+z
note a note
expect marks = 2
expect kinds = HN
zoompct 150
key cmd+r
cmd nextPage
cmd prevPage
expect marks = 2
expect errors = 0
tool highlight
expect tool = 1
drag 1 12 19
expect marks = 3
tool highlight
expect tool = 0
cmd showAll
expect radio:showAll = 0
cmd showAll
expect radio:showAll = 1
EOF
run_session c1h "$work/c1h.txt"
fi

# 11.6a (no Tk case: the native app's Cmd-X / Cmd-V on marks): Cut of a selected highlight
# (its text on the private pasteboard, one undo step), Paste on its page and on another page
# (each one undo step), Paste again, undo / redo; Cut of a note; Cut / Paste disabled without a
# selected mark / a cut one.
if wanted "1hx cutpaste"; then
case_begin "1hx cut/paste marks"
cat > "$work/c1hx.txt" <<'EOF'
fixture text3 $OUT/x.pdf
open $OUT/x.pdf
key cmd+x
expect ran = 0
key cmd+v
expect ran = 0
dblclick 1 0
key ctrl+cmd+h
expect marks = 1
key cmd+x
expect ran = 1
expect marks = 0
expect clipboard ~ e
expect pill ~ highlight cut
key cmd+v
expect marks = 1
expect last-mark ~ highlight p1 yellow
expect mark-selected = 1
key cmd+z
expect marks = 0
key cmd+shift+z
expect marks = 1
cmd nextPage
key cmd+v
expect marks = 2
expect last-mark ~ highlight p2 yellow
key cmd+v
expect marks = 3
key cmd+z
expect marks = 2
note cut me
expect kinds = HHN
select-mark last
key cmd+x
expect kinds = HH
expect clipboard = cut me
key cmd+v
expect kinds = HHN
expect last-mark ~ cut me
EOF
run_session c1hx "$work/c1hx.txt"
fi

# 1t (Tk 1t): closing a note without Save: an empty new note goes, a typed one is saved, a
# stored text stays; an empty highlight comment goes, the highlight stays.
if wanted "1t note"; then
case_begin "1t noteclose"
cat > "$work/c1t.txt" <<'EOF'
fixture text3 $OUT/n.pdf
open $OUT/n.pdf
note-at 1 300 500
expect note-open = 1
note-close
expect marks = 0
expect pill = empty note removed
note-at 1 300 500
note-close typed
expect marks = 1
expect last-mark ~ typed
open-mark last
expect note-open = 1
note-close changed but not saved
expect last-mark ~ typed
dblclick 1 0
cmd highlight
cmd addNote
expect note-open = 1
note-close
expect kinds = NH
EOF
run_session c1t "$work/c1t.txt"
fi

# 1j / 1j' / 9.r2 / 12.5 (Tk 1j, 1j', 1r): Save into the opened file (the first-overwrite
# question, C7 prefix, reopen with the marks saved and the view kept), Save As (STEM-annotated
# proposed), a second save without a question, editing saved marks (recolour, delete: the
# revision-retention note), a third revision; the unsaved-marks decisions on Close and Quit
# (Cancel / Don't Save / Save), a read-only file and a file changed on disk.
if wanted "1j save"; then
case_begin "1j save/reopen/edit"
cat > "$work/c1j.txt" <<'EOF'
fixture text3 $OUT/orig.pdf
copy-file $OUT/orig.pdf $OUT/s.pdf
open $OUT/s.pdf
zoompct 150
cmd nextPage
dblclick 1 0
cmd highlight
note first note
expect edited = 1
remember size0 size:$OUT/s.pdf
answer cancel
key cmd+s
expect asked ^ Save [saveas cancel overwrite]
expect size:$OUT/s.pdf = @size0
answer overwrite
key cmd+s
prefix $OUT/orig.pdf $OUT/s.pdf
expect saved = 2
expect dirty = 0
expect edited = 0
expect choice = 150%
expect pill ^ saved 2 new, changed or deleted mark(s) as an incremental update
copy-file $OUT/s.pdf $OUT/s1.pdf
note second
key cmd+s
expect asked-count = 2
prefix $OUT/s1.pdf $OUT/s.pdf
copy-file $OUT/s.pdf $OUT/s2.pdf
select-mark first
color red
select-mark last
key delete
key cmd+s
prefix $OUT/s2.pdf $OUT/s.pdf
expect pill ~ deleted mark(s) are still in the file's earlier revision
close
expect closed = 1
open $OUT/s.pdf
expect kinds = HN
expect saved = 2
expect last-mark ^ note
select-mark first
expect last-mark !~ yellow
saveurl $OUT/as.pdf
key cmd+shift+s
expect asked = Save As [] s-annotated.pdf
expect doc = as.pdf
note unsaved
answer cancel
close
expect closed = 0
expect dirty = 1
remember sz size:$OUT/as.pdf
answer dontsave
close
expect closed = 1
expect size:$OUT/as.pdf = @sz
open $OUT/as.pdf
note to save
answer save
close
expect closed = 1
expect size:$OUT/as.pdf > @sz
open $OUT/as.pdf
note quit
answer cancel
quit
expect quit = 0
answer dontsave
quit
expect quit = 1
chmod 444 $OUT/as.pdf
key cmd+s
expect dirty = 1
expect pill ~ as.pdf
chmod 644 $OUT/as.pdf
append-file $OUT/as.pdf %changed
answer cancel
key cmd+s
expect asked ^ File changed on disk [cancel saveas]
expect pill ^ not saved: as.pdf changed on disk
saveurl $OUT/other.pdf
answer saveas
key cmd+s
expect doc = other.pdf
expect dirty = 0
EOF
run_session c1j "$work/c1j.txt"
for f in s.pdf as.pdf other.pdf; do [ -f "$work/out-c1j/$f" ] && qpdf_check "$work/out-c1j/$f"; done
# s.pdf: the red highlight with its comment (the note added while it was selected: its Popup) on
# page 1; the deleted note of page 2 is gone from the last revision (its page has none left).
expect_annots "$work/out-c1j/s.pdf" '^ p1: Highlight Popup; p2: -; p3: -;$'

fi

# 1j encrypted (Tk 1j encrypted, 12.4): an RC4 and an AES-256 file saved by incremental update
# with fresh random bytes (the RC4 note), refused without them.
if wanted "1j enc"; then
case_begin "1j encrypted"
cat > "$work/c1je.txt" <<'EOF'
copy-file $IN/rc4-128.pdf $OUT/rc4.pdf
copy-file $IN/rc4-128.pdf $OUT/rc4-orig.pdf
open $OUT/rc4.pdf
expect encrypted = 1
note encrypted note
answer overwrite
key cmd+s
expect dirty = 0
expect pill ~ legacy RC4
prefix $OUT/rc4-orig.pdf $OUT/rc4.pdf
note seedless
seedless
remember sz size:$OUT/rc4.pdf
key cmd+s
expect pill ~ no fresh random bytes
expect size:$OUT/rc4.pdf = @sz
seeded
key cmd+s
expect dirty = 0
copy-file $IN/aesv3.pdf $OUT/aes.pdf
open $OUT/aes.pdf
expect encrypted = 1
note aes note
answer overwrite
key cmd+s
expect dirty = 0
expect pill !~ legacy RC4
close
open $OUT/aes.pdf
expect saved = 1
EOF
run_session c1je "$work/c1je.txt"
for f in rc4.pdf aes.pdf; do [ -f "$work/out-c1je/$f" ] && qpdf_check "$work/out-c1je/$f"; done
expect_annots "$work/out-c1je/rc4.pdf" 'Text Text'
expect_annots "$work/out-c1je/aes.pdf" '^ p1: Text;$'
fi

# 1j'' (Tk 1j''): XFDF export, every mark deleted, import (one undo step), a second import adds
# nothing, the hostile samples of Tests/xfdf refused with the store unchanged.
if wanted "1j'' xfdf"; then
case_begin "1j'' xfdf"
{
cat <<'EOF'
fixture text3 $OUT/x.pdf
open $OUT/x.pdf
dblclick 1 0
cmd highlight
note xfdf note
saveurl $OUT/marks.xfdf
cmd exportXfdf
expect pill = exported 2 mark(s) to marks.xfdf
expect file:$OUT/marks.xfdf ~ <xfdf
select-mark last
key delete
select-mark last
key delete
expect marks = 0
openurl $OUT/marks.xfdf
cmd importXfdf
expect pill ^ marks.xfdf: 2 imported, 0 already present
expect marks = 2
openurl $OUT/marks.xfdf
cmd importXfdf
expect pill ^ marks.xfdf: 0 imported, 2 already present
key cmd+z
expect marks = 0
key cmd+shift+z
expect marks = 2
EOF
for x in billion-laughs xxe undeclared-entity; do
  printf 'openurl $IN/xfdf/%s.xfdf\ncmd importXfdf\nexpect pill ^ cannot import %s.xfdf\nexpect marks = 2\n' "$x" "$x"
done
for x in acrobat foxit okular-style pdfjs-style; do
  printf 'openurl $IN/xfdf/%s.xfdf\ncmd importXfdf\nexpect pill ^ %s.xfdf: \nmeasure\n' "$x" "$x"
done
printf 'openurl $OUT/missing.xfdf\ncmd importXfdf\nexpect pill ^ cannot import missing.xfdf\n'
} > "$work/c1jx.txt"
run_session c1jx "$work/c1jx.txt"
fi

# 1j''' (Tk 1j'''): Add text and Draw: a text box and a drawing placed, saved, reopened (read
# back as saved marks).
if wanted "1j''' editors"; then
case_begin "1j''' editors"
cat > "$work/c1jt.txt" <<'EOF'
fixture text3 $OUT/e.pdf
copy-file $OUT/e.pdf $OUT/e-orig.pdf
open $OUT/e.pdf
freetext 1 100 500 Boxed text
expect last-mark ~ Boxed text
ink 1 100 400
expect kinds = TI
tool text
expect tool = 3
escape
tool select
answer overwrite
key cmd+s
prefix $OUT/e-orig.pdf $OUT/e.pdf
close
open $OUT/e.pdf
expect kinds = TI
expect saved = 2
expect errors = 0
EOF
run_session c1jt "$work/c1jt.txt"
[ -f "$work/out-c1jt/e.pdf" ] && qpdf_check "$work/out-c1jt/e.pdf"
expect_annots "$work/out-c1jt/e.pdf" '^ p1: (FreeText Ink|Ink FreeText); p2: -; p3: -;$'
fi

# 1k (Tk 1k): view modes through the View menu: continuous, continuous facing (1|2 side by
# side), facing (Next by two), even spreads (1 alone, then 2|3), back to single page.
if wanted "1k modes"; then
case_begin "1k view modes"
cat > "$work/c1k.txt" <<'EOF'
fixture text3 $OUT/k.pdf
open $OUT/k.pdf
expect scroll = vertical
expect laid-out = 3
cmd spreadOdd
expect spread = odd
expect radio:spreadOdd = 1
remember p1x page1-x
expect page2-x > @p1x
cmd scrollPage
expect scroll = page
expect page = 1
cmd nextPage
expect page = 3
cmd prevPage
expect page = 1
cmd spreadEven
expect spread = even
cmd nextPage
expect page = 2
expect enabled:nextPage = 0
cmd prevPage
expect page = 1
cmd spreadNone
cmd lastPage
expect page = 3
expect radio:scrollPage = 1
expect radio:spreadNone = 1
EOF
run_session c1k "$work/c1k.txt"
fi

# 1m (Tk 1m, 8.8): non-blocking rendering on a slow page 1: commands return at once while it
# renders, Last page shows page 2 meanwhile.
if wanted "1m async"; then
case_begin "1m async"
cat > "$work/c1m.txt" <<'EOF'
async on
open $IN/slow.pdf
expect last_ms < 1000
cmd zoomIn
expect last_ms < 250
cmd lastPage
expect last_ms < 250
expect page = 2
async off
wait
expect errors = 0
expect maxblock < 1000
EOF
run_session c1m "$work/c1m.txt"
fi

# 1o (Tk 1o): wheel flow: bursts of small precise deltas cross page boundaries without going
# back, in continuous mode; in page-at-a-time mode the wheel turns the page.
if wanted "1o wheel"; then
case_begin "1o wheelflow"
cat > "$work/c1o.txt" <<'EOF'
fixture text3 $OUT/w.pdf
open $OUT/w.pdf
wheel -6 400
expect wheel_monotonic = 1
expect page > 1
wheel 6 800
expect wheel_monotonic = 1
expect page = 1
cmd scrollPage
cmd fitPage
wheel-turn -30
expect page = 2
wheel-turn 30
expect page = 1
EOF
run_session c1o "$work/c1o.txt"
fi

# 1p (Tk 1p): platform keys: every accelerator of the exported key table reaches its own
# command through the menubar's key equivalents (or the page view's keys).
if wanted "1p keys"; then
case_begin "1p keys"
cat > "$work/c1p.txt" <<'EOF'
list-keys
expect keys = 27/27
fixture text3 $OUT/p.pdf
open $OUT/p.pdf
key cmd+g
expect via = menu:Find next
key opt+cmd+g
expect via = menu:Go to page...
key cmd+f
expect via = menu:Find...
key cmd+down
expect page = 3
key cmd+up
expect page = 1
key cmd+w
expect doc =
EOF
run_session c1p "$work/c1p.txt"
skip_case "1p keys (icon sizes)" "the icon is the bundle's .icns built by macos/build.sh (iconutil); no X11 _NET_WM_ICON on macOS"
fi

# 1q (Tk 1q): the view-mode drop-down in sync with the View menu's radio entries.
if wanted "1q r4"; then
case_begin "1q r4"
cat > "$work/c1q.txt" <<'EOF'
fixture text3 $OUT/q.pdf
open $OUT/q.pdf
expect viewchoice = Vertical Scrolling
cmd scrollPage
expect viewchoice = Single Page
cmd spreadOdd
expect viewchoice = Two Pages
cmd scrollVertical
expect viewchoice = Two Pages Scrolling
view Single Page
expect radio:scrollPage = 1
expect radio:spreadNone = 1
EOF
run_session c1q "$work/c1q.txt"
fi

# 1r (Tk 1r): the save dialogs: Save As proposes STEM-annotated.pdf, adds the extension,
# refuses a folder and an XFDF export onto the opened PDF.
if wanted "1r savedlg"; then
case_begin "1r savedlg"
mkdir -p "$work/folder.pdf" "$work/folder.xfdf"
cat > "$work/c1r.txt" <<'EOF'
fixture text3 $OUT/r.pdf
open $OUT/r.pdf
note r note
cmd saveAs
expect asked = Save As [] r-annotated.pdf
expect dirty = 1
saveurl $IN/folder.pdf
cmd saveAs
expect pill ~ folder
expect dirty = 1
saveurl $OUT/noext
cmd saveAs
expect doc = noext.pdf
saveurl $IN/folder.xfdf
cmd exportXfdf
expect pill = cannot export: folder.xfdf is a folder; choose a file name
EOF
run_session c1r "$work/c1r.txt"
fi

# 1s (Tk 1s): document open settings on generated files, through the window's open path.
if wanted "1s open"; then
case_begin "1s opensettings"
cat > "$work/c1s.txt" <<'EOF'
fixture settings $OUT/xyz.pdf /OpenAction [5 0 R /XYZ 0 792 1.5]
fixture settings $OUT/r2l.pdf /PageLayout /TwoPageLeft /ViewerPreferences << /Direction /R2L >>
fixture settings $OUT/tcr.pdf /PageLayout /TwoColumnRight
fixture settings $OUT/named.pdf /OpenAction << /S /GoTo /D (four) >> /Names << /Dests << /Names [(four) [6 0 R /FitH 792]] >> >>
fixture settings $OUT/js.pdf /OpenAction << /S /JavaScript /JS (app.alert\(1\)) >>
fixture settings $OUT/prefs.pdf /ViewerPreferences << /HideToolbar true /DisplayDocTitle true >>
fixture settings $OUT/thumbs.pdf /PageMode /UseThumbs
fixture settings $OUT/none-mode.pdf /PageMode /UseNone
fixture settings $OUT/full.pdf /PageMode /FullScreen
fixture settings $OUT/none.pdf
open $OUT/xyz.pdf
expect page = 3
expect choice = 150%
expect scroll = vertical
cmd rotateCw
open $OUT/r2l.pdf
expect rotation = 0
expect scroll = page
expect spread = odd
expect rtl = 1
open $OUT/tcr.pdf
expect scroll = vertical
expect spread = even
open $OUT/named.pdf
expect page = 4
expect choice = Page Width
open $OUT/js.pdf
expect pills ~ not executed
expect page = 1
open $OUT/prefs.pdf
expect title = Open Settings Test
expect pills ~ not honoured
open $OUT/thumbs.pdf
expect sidebar = shown
expect panel = thumbnails
open $OUT/none-mode.pdf
expect sidebar = hidden
open $OUT/full.pdf
expect sidebar = hidden
skip /PageMode /FullScreen: native full screen needs a visible window (the setting is applied only once the window is on screen)
open $OUT/none.pdf
expect sidebar = shown
expect panel = outline
expect choice = Automatic Zoom
expect page = 1
expect scroll = vertical
expect title = none.pdf
EOF
run_session c1s "$work/c1s.txt"
fi

# 1u (Tk 1u): the thumbnails panel: shown with its toggle, a click jumps (history), it follows
# the page view.
if wanted "1u thumbs"; then
case_begin "1u thumbs"
cat > "$work/c1u.txt" <<'EOF'
fixture text3 $OUT/u.pdf
open $OUT/u.pdf
panel thumbnails
expect sidebar = shown
expect panel = thumbnails
thumb 3
expect page = 3
expect history-back = 1
key cmd+bracketleft
expect page = 1
key cmd+r
expect rotation = 90
EOF
run_session c1u "$work/c1u.txt"
skip_case "1u thumbperf (reported only)" "the corpus timings are scripts/macos-corpus.sh's"
fi

# 1v (Tk 1v): the attachments panel: listed without decoding, saved exactly.
if wanted "1v attach"; then
case_begin "1v attach"
cat > "$work/c1v.txt" <<'EOF'
fixture attachments $OUT/att.pdf
open $OUT/att.pdf
expect sidebar = shown
expect panel = attachments
expect attachments > 1
measure
attach-save 1 $OUT/first.bin
expect attach ^ saved attachment
expect size:$OUT/first.bin = 1024
attach-save 1 $OUT/att.pdf
expect attach ^ cannot save attachment
EOF
run_session c1v "$work/c1v.txt"
fi

# 1w (Tk 1w): the layers panel: optional content listed, a toggle re-renders.
if wanted "1w layers"; then
case_begin "1w layers"
cat > "$work/c1w.txt" <<'EOF'
fixture layers $OUT/oc.pdf
open $OUT/oc.pdf
expect sidebar = shown
expect panel = layers
expect layer-rows > 1
remember l1 layer:1
layer 1
expect layer_changed = 1
expect layer:1 != @l1
expect errors = 0
layer 1
expect layer:1 = @l1
EOF
run_session c1w "$work/c1w.txt"
fi

# 10.10 / M11 dark mode (Tk 10.10 tint): the paper stays white, the canvas darkens, the selection
# keeps its accent tint in light and dark.
if wanted "dark"; then
case_begin "10.10 dark mode"
cat > "$work/cdark.txt" <<'EOF'
fixture text3 $OUT/d.pdf
open $OUT/d.pdf
measure-paper
remember bglight background.lum
expect paper.lum > 0.97
dark on
measure-paper
expect paper.lum > 0.97
expect background.lum < @bglight
key cmd+a
measure-selection
expect selection.b > 0.5
snapshot dark-selection
dark off
measure-selection
expect selection.b > 0.6
EOF
run_session cdark "$work/cdark.txt"
fi

# M11 Retina: backing scale 2 -> 1 -> 2: the render key follows the pixels, the zoom in points
# and the page in points stay.
if wanted "retina"; then
case_begin "M11 retina 1x/2x"
cat > "$work/cret.txt" <<'EOF'
open $IN/two.pdf
zoompct 100
expect backing = 2
expect key = 2/1
remember w page-w
scale 1
expect backing = 1
expect key = 1/1
expect zoom = 100
expect page-w near @w 0.5
expect errors = 0
scale 2
expect key = 2/1
expect page-w near @w 0.5
EOF
run_session cret "$work/cret.txt"
fi

# 2 (Tk 2): a malformed and a non-PDF file: an error text, the app goes on.
if wanted "2 bad"; then
case_begin "2 bad inputs"
printf 'not a pdf at all\n' > "$work/notpdf.pdf"
head -c 200 "$work/two.pdf" > "$work/truncated.pdf"
cat > "$work/c2.txt" <<'EOF'
open-error $IN/notpdf.pdf
expect error !=
open-error $IN/truncated.pdf
expect error !=
open-error $IN/missing.pdf
open $IN/two.pdf
expect pages = 2
EOF
run_session c2 "$work/c2.txt"
fi

# 12.2c (Tk 12.2c): pages, the text index and links come from the confined worker process.
if wanted "12.2c worker"; then
case_begin "12.2c worker"
cat > "$work/cw.txt" <<'EOF'
open $IN/tree.pdf
expect errors = 0
link 1 1
expect page = 4
measure
EOF
run_session cw "$work/cw.txt"
if grep -q '^session: worker ' "$work/out-cw/stderr.log"; then echo "  $(grep '^session: worker ' "$work/out-cw/stderr.log")"
else echo "FAIL: 12.2c: no worker" >&2; fail=1; fi
skip_case "12.2c worker (stalled render)" "the Tk test hook for a stalled render has no native counterpart; the core's deadline is the C API's (macos/tests)"
fi

# Not applicable to the native app (docs/macos-smoke.md says why).
if [ "${#only[@]}" = 0 ]; then
  skip_case "1l lockdown" "Tk send / X resources: the native app has no Tcl interpreter"
  skip_case "1n m9" "the M9 paper run is scripts/macos-corpus.sh's session"
  skip_case "1i bubble buttons" "the selection bubble's buttons are views over the page; their actions (highlight, recolour, comment, delete) run here through the menu, and macos/selftest.sh (SelfTestMarks) drives the bubble itself"
  skip_case "12.5 identity line in full screen" "native full screen needs a visible window"
fi

case_end
echo "macos-smoke: summary (macos): ${#cases_pass[@]} passed, ${#cases_skip[@]} skipped, ${#cases_fail[@]} failed"
echo "macos-smoke: front-app watcher: $samples samples, $alerts alerts (log: $watchlog)"
for c in ${cases_skip[@]+"${cases_skip[@]}"}; do echo "macos-smoke:   skipped: $c"; done
for c in ${cases_fail[@]+"${cases_fail[@]}"}; do echo "macos-smoke:   FAILED: $c"; done
if [ "$fail" = 0 ] && [ "$alerts" = 0 ]; then echo "macos-smoke: OK"; else echo "macos-smoke: FAILED" >&2; fail=1; fi
exit $fail
