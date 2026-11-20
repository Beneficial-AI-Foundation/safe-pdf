#!/usr/bin/env bash
# M8 corpus check of the native viewer (task 8.5; Plan.md §6 Phase 8, docs/viewer-corpus.md).
# Run from the repo root.
#
#   scripts/viewer-corpus.sh [--no-build] [--json OUT] [--out DIR] [--timeout SEC]
#                            [--no-session] [--no-corpus] [FILE.pdf ...]
#
# 1. Corpus pass: for every PDF (default: corpus/files/*.pdf) the compiled viewer is started
#    under its own Xvfb (window 1600x1000, continuous mode: SAFEPDF_VIEWER_VIEW=continuous) and
#    a driver (wish, talking to the viewer's Tk interpreter with Tk `send`, which the viewer keeps
#    only under the test hook SAFEPDF_VIEWER_DRIVE=1 set here, task 8.7) re-opens the file
#    through File > Open (tk_getOpenFile answered by the driver) and goes through every page
#    with Go > Next page, waiting after each step until the page is on screen and no deferred
#    render is pending. The driver wraps `::safepdf::emit` (the one entry point of every Tk
#    event into the viewer) to time each event and to see which page photos (or render-error
#    texts) each one created. Per file: opened, pages, per-page time-to-display, events over
#    5 s (hangs), exit status, peak RSS (VmHWM). Hard timeout per file (--timeout, default 900 s).
# 2. Session on three papers (outline, encrypted NTSB, long): open, outline jump, search a word
#    and go to the hit, double-click it and copy, highlight, add a note, Save, close, reopen the
#    saved file and check the marks are back, close, quit; then qpdf --check and the byte prefix
#    of the saved file.
# Output: a table and a summary on stdout; --json OUT writes everything as JSON; --out DIR keeps
# the raw driver logs (default: a temporary directory, removed at the end).
# Needs: the viewer (lake build viewer), Xvfb, wish (Tk 8.6/9.0), python3; qpdf optional.
# Exit status: 0 when M8 holds under the thresholds of docs/viewer-corpus.md, else 1.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

build=1 json="" outdir="" timeout_s=900 do_session=1 do_corpus=1
files=()
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) build=0 ;;
    --json) json="$2"; shift ;;
    --out) outdir="$2"; shift ;;
    --timeout) timeout_s="$2"; shift ;;
    --no-session) do_session=0 ;;
    --no-corpus) do_corpus=0 ;;
    -h|--help) sed -n '2,24p' "$0"; exit 0 ;;
    *) files+=("$1") ;;
  esac
  shift
done
if [ ${#files[@]} -eq 0 ]; then
  shopt -s nullglob
  files=(corpus/files/*.pdf)
  shopt -u nullglob
fi

if [ "$build" = 1 ]; then lake build viewer; fi
viewer="$repo/.lake/build/bin/viewer"
[ -x "$viewer" ] || { echo "viewer-corpus: $viewer not built" >&2; exit 1; }
command -v Xvfb >/dev/null || { echo "viewer-corpus: Xvfb missing" >&2; exit 1; }
wish=""
for w in wish9.0 wish8.6 wish; do
  if command -v "$w" >/dev/null; then wish="$w"; break; fi
done
[ -n "$wish" ] || { echo "viewer-corpus: wish (Tk) missing" >&2; exit 1; }

if [ -n "$outdir" ]; then
  mkdir -p "$outdir"; work="$(cd "$outdir" && pwd)"; keep=1
else
  work="$(mktemp -d)"; keep=0
fi
xvfb_pid=""
viewer_pid=""
cleanup() {
  [ -n "$viewer_pid" ] && kill -9 "$viewer_pid" 2>/dev/null || true
  [ -n "$xvfb_pid" ] && kill "$xvfb_pid" 2>/dev/null || true
  if [ "$keep" = 0 ]; then rm -rf "$work"; fi
}
trap cleanup EXIT

# ---------------------------------------------------------------------------------------------
# The driver (Tcl, run by wish on the viewer's display). Arguments:
#   corpus OUT FILE VIEWER_PID
#   session OUT FILE VIEWER_PID WORD NOTE_TEXT
# Writes tab-separated records into OUT (line-buffered, so a timeout keeps what was done).
cat > "$work/driver.tcl" <<'TCL'
wm withdraw .
lassign $argv mode out file vpid word notetext
set fh [open $out w]
fconfigure $fh -buffering line -encoding utf-8
proc rec {args} { puts $::fh [join $args "\t"] }
proc ms {us} { format %.3f [expr {$us / 1000.0}] }
proc now {} { clock microseconds }
proc hwm {} {
  set kb 0
  catch {
    set f [open /proc/$::vpid/status]
    foreach l [split [read $f] \n] { if {[regexp {^VmHWM:\s+(\d+)} $l -> kb]} break }
    close $f
  }
  return $kb
}
# v SCRIPT: evaluate SCRIPT in the viewer (fatal when the viewer is gone).
proc v {script} {
  if {[catch {send $::app $script} r]} {
    if {[string match "*no application named*" $r] || [string match "*target application died*" $r]} {
      rec fatal send-failed $r
      rec hwm [hwm]
      exit 2
    }
    error $r
  }
  return $r
}
# Wait for the viewer's interpreter (the first `send` returns once its event loop runs, i.e.
# after the initial open and first render).
set t0 [now]
set app ""
while {$app eq ""} {
  foreach i [winfo interps] { if {$i ne [tk appname] && [string match tk* $i]} { set app $i } }
  if {$app eq ""} {
    if {[now] - $t0 > 120000000} { rec fatal no-interp; exit 2 }
    if {![file exists /proc/$vpid]} { rec fatal viewer-exited-at-start; exit 2 }
    after 50
  }
}
v {update}
rec connect_ms [ms [expr {[now] - $t0}]]
rec status0 [v {.status cget -text}]

# Instrumentation inside the viewer: every Tk event reaches the viewer through
# ::safepdf::emit; the wrapper times it and records the pages it put on screen.
v {
  namespace eval ::m85 { variable log {} }
  proc ::m85::shown {} {
    set r {}
    foreach c [info commands ::safepdf::pg*] { if {[regexp {pg(\d+)$} $c -> n]} { lappend r $n } }
    foreach i [.c find withtag perr] {
      foreach t [.c gettags $i] { if {[regexp {^e(\d+)$} $t -> n]} { lappend r e$n } }
    }
    return $r
  }
  # Pages put on screen during the current event: a page photo created
  # (image create photo ::safepdf::pgN) or a render-error text (tags "perr eN").
  set ::m85::new {}
  proc ::m85::imgTrace {cmd code res op} {
    if {[lrange $cmd 0 1] eq {image create} && [regexp {::safepdf::pg(\d+)$} [lindex $cmd 3] -> n]} {
      lappend ::m85::new $n
    }
  }
  proc ::m85::canvasTrace {cmd code res op} {
    if {[lindex $cmd 1] eq "create" && [lsearch -exact $cmd -tags] >= 0} {
      set tags [lindex $cmd [expr {[lsearch -exact $cmd -tags] + 1}]]
      if {"perr" in $tags} {
        foreach t $tags { if {[regexp {^e(\d+)$} $t -> n]} { lappend ::m85::new e$n } }
      }
    }
  }
  trace add execution image leave ::m85::imgTrace
  trace add execution .c leave ::m85::canvasTrace
  rename ::safepdf::emit ::m85::emit0
  proc ::safepdf::emit {args} {
    set outer $::m85::new
    set ::m85::new {}
    # ::safepdf::ttd(N): ms from the request of page N's render to its display (task 8.8:
    # renders run on worker threads and are shown by a later `poll` event).
    set outerTtd [array get ::safepdf::ttd]
    array unset ::safepdf::ttd
    set t0 [clock microseconds]
    set code [catch {::m85::emit0 {*}$args} res opts]
    set dt [expr {[clock microseconds] - $t0}]
    lappend ::m85::log [list $t0 $dt $args $::m85::new [array get ::safepdf::ttd]]
    array set ::safepdf::ttd $outerTtd
    set ::m85::new [concat $outer $::m85::new]
    return -options $opts $res
  }
  proc ::m85::busy {} {
    foreach id [after info] {
      set script [lindex [after info $id] 0]
      if {[string match *renderMore* $script] || [string match {*emit poll*} $script]} { return 1 }
    }
    return 0
  }
  proc ::m85::cur {} {
    if {[regexp {: page (?:[^,]* \()?(\d+)/(\d+)} [.status cget -text] -> p n]} { return [list $p $n] }
    return {0 0}
  }
  proc ::tk_getOpenFile {args} { return $::m85::path }
  set ::safepdf::autoAnswer {}
}
# open PATH: File > Open with the dialog answered; returns the event time in microseconds.
proc vopen {path} {
  v [list set ::m85::path $path]
  v {set ::m85::log {}}
  set t [now]
  v {.menubar.file invoke {Open...}}
  return [expr {[now] - $t}]
}
# Waits until page index P is on screen (photo or error text) and no deferred render is
# pending; returns the microseconds until P was first seen on screen, or -1 after LIMIT us.
proc waitPage {p t limit} {
  set seen -1
  while 1 {
    lassign [v {list [::m85::shown] [::m85::busy]}] sh busy
    if {$seen < 0 && ($p in $sh || "e$p" in $sh)} { set seen [expr {[now] - $t}] }
    if {$seen >= 0 && !$busy} { return $seen }
    if {[now] - $t > $limit} { return $seen }
    after 2
  }
}
proc dumpLog {} {
  foreach e [v {set ::m85::log}] {
    lassign $e t0 dt args new ttd
    rec ev [ms $dt] $new $args $ttd
  }
  v {set ::m85::log {}}
}
proc status {} { v {.status cget -text} }
proc finish {code} {
  rec hwm [hwm]
  catch {send -async $::app {destroy .}}
  close $::fh
  exit $code
}

if {$mode eq "corpus"} {
  set dt [vopen $file]
  set st [status]
  rec open_ms [ms $dt] $st
  lassign [v ::m85::cur] cur n
  rec pages $n
  if {$n == 0} { dumpLog; finish 0 }
  set seen [waitPage 0 [now] 60000000]
  rec page 1 [ms 0] $st
  dumpLog
  for {set i 1} {$i < $n} {incr i} {
    set t [now]
    v {.menubar.go invoke {Next page}}
    set seen [waitPage $i $t 60000000]
    lassign [v ::m85::cur] cur _
    rec page [expr {$i + 1}] [expr {$seen < 0 ? -1 : [ms $seen]}] $cur [status]
    dumpLog
    if {$i % 10 == 0} { rec hwm [hwm] }
  }
  finish 0
}

# ---- session ----
proc winOf {cx cy} {
  list [expr {round($cx - [v {.c canvasx 0}])}] [expr {round($cy - [v {.c canvasy 0}])}]
}
proc click {x y {b 1}} {
  v [list event generate .c <ButtonPress-$b> -x $x -y $y]
  v [list event generate .c <ButtonRelease-$b> -x $x -y $y]
}
proc pixelAt {p x0 y0 x1 y1} {
  # The lightest pixel of page index p's photo in the box (x0, y0)-(x1, y1) relative to the photo (a 7x3
  # grid inside it): the paper under a highlight, not a glyph.
  set best none; set bs -1
  foreach fx {0.1 0.25 0.4 0.5 0.6 0.75 0.9} {
    foreach fy {0.2 0.5 0.8} {
      set x [expr {round($x0 + $fx * ($x1 - $x0))}]
      set y [expr {round($y0 + $fy * ($y1 - $y0))}]
      if {[catch {v [list ::safepdf::pg$p get $x $y]} px]} continue
      lassign $px r g b
      if {$r + $g + $b > $bs} { set bs [expr {$r + $g + $b}]; set best $px }
    }
  }
  return $best
}
# yellowish R G B: a highlight on paper (blue clearly below red and green).
proc yellowish {px} {
  if {[llength $px] != 3} { return 0 }
  lassign $px r g b
  expr {$r > 200 && $g > 200 && $b < $r - 60}
}
set ok 1
proc check {name cond detail} {
  rec step $name [expr {$cond ? "ok" : "FAIL"}] $detail
  if {!$cond} { set ::ok 0 }
}
set dt [vopen $file]
set st [status]
lassign [v ::m85::cur] cur n
check open [expr {$n > 0}] "[ms $dt] ms; $st"
# Outline: the entry at about a third of the list whose row is visible; click it.
set panes [v {.pw panes}]
set nOl [llength [v {.ol.t tag names}]]
set jumped 0
set olDetail "no outline"
if {[string match *.ol* $panes]} {
  set ids {}
  foreach t [v {.ol.t tag names}] { if {[regexp {^o(\d+)$} $t -> k]} { lappend ids $k } }
  set ids [lsort -integer $ids]
  set olDetail "[llength $ids] entries"
  set start [expr {[llength $ids] / 3}]
  foreach k [concat [lrange $ids $start end] [lrange $ids 0 [expr {$start - 1}]]] {
    set r [v [list .ol.t tag ranges o$k]]
    if {$r eq ""} continue
    v [list .ol.t see [lindex $r 0]]
    v {update idletasks}
    set bb [v [list .ol.t bbox [lindex $r 0]]]
    if {[llength $bb] != 4} continue
    lassign $bb x y w h
    set title [v [list .ol.t get [lindex $r 0] [lindex $r 1]]]
    set before [lindex [v ::m85::cur] 0]
    set t [now]
    v [list event generate .ol.t <ButtonRelease-1> -x [expr {$x + $w / 2}] -y [expr {$y + $h / 2}]]
    set after [lindex [v ::m85::cur] 0]
    waitPage [expr {$after - 1}] $t 60000000
    if {$after != $before} {
      set jumped 1
      set olDetail "[llength $ids] entries; o$k \"[string trim $title]\": page $before -> $after ([ms [expr {[now] - $t}]] ms)"
      break
    }
  }
}
check outline-jump $jumped $olDetail
# Search: Ctrl+F, the word, Enter; then F3 once (second hit) if there is one.
v {::safepdf::showFind; focus -force .find.e; update}
v [list set ::safepdf::query $word]
set t [now]
# The status is read in the same `send` as the key: a deferred render may replace it later.
set fst [v {event generate .find.e <Key-Return>; .status cget -text}]
if {[regexp {hit 1/(\d+)} $fst -> nh] && $nh > 1} {
  set fst [v {event generate .find.e <Key-F3>; .status cget -text}]
}
set hp [lindex [v ::m85::cur] 0]
regexp {on page (\d+)} $fst -> hp
waitPage [expr {$hp - 1}] $t 60000000
check search [regexp {hit \d+/\d+ on page} $fst] "[ms [expr {[now] - $t}]] ms; $fst"
# The current hit (orange) box; a double click on it selects the word, Ctrl+C copies.
# Let the layout settle (the find bar changes the canvas size) before reading the box; the
# bar stays open until the marks are made.
v update
set hb {}
foreach i [v {.c find withtag hit}] {
  set f [v [list .c itemcget $i -fill]]
  set o [v [list .c itemcget $i -outline]]
  if {$f eq "orange" || $o eq "orange"} { set hb [v [list .c bbox $i]]; break }
}
set copied ""
if {[llength $hb] == 4} {
  lassign $hb x0 y0 x1 y1
  set cx [expr {($x0 + $x1) / 2.0}]; set cy [expr {($y0 + $y1) / 2.0}]
  # A word inside the hit: just right of its left edge (a phrase may span words).
  set wx [expr {$x0 + min(6, ($x1 - $x0) / 2.0)}]
  lassign [winOf $wx $cy] wx wy
  v {focus -force .c}
  set tm 5000000
  v [list event generate .c <ButtonPress-1> -x $wx -y $wy -time $tm]
  v [list event generate .c <ButtonRelease-1> -x $wx -y $wy -time [expr {$tm + 10}]]
  v [list event generate .c <ButtonPress-1> -x $wx -y $wy -time [expr {$tm + 60}]]
  set sst [v "[list event generate .c <ButtonRelease-1> -x $wx -y $wy -time [expr {$tm + 70}]]; .status cget -text"]
  v {clipboard clear}
  v {focus -force .c; update; event generate .c <Control-Key-c>}
  catch {set copied [v {clipboard get}]}
  set w0 [string tolower [lindex [split $word] 0]]
  check select-copy [expr {[string first $w0 [string tolower $copied]] >= 0}] "clipboard \"$copied\"; $sst"
  # Highlight the selection (key h), then a note at a point left of the hit.
  set hst [v {focus -force .c; update; event generate .c <Key-h>; .status cget -text}]
  set marks [v {llength [.c find withtag mark]}]
  # The hit box relative to its page photo (the page may sit elsewhere after reopening).
  lassign [v [list .c coords p[expr {$hp - 1}]]] ix iy
  set rb [list [expr {$x0 - $ix}] [expr {$y0 - $iy}] [expr {$x1 - $ix}] [expr {$y1 - $iy}]]
  set pxBefore [pixelAt [expr {$hp - 1}] {*}$rb]
  check highlight [expr {[string match "*highlighted*" $hst] && [yellowish $pxBefore]}] "$hst; pixel $pxBefore; box $hb on [v [list .c coords p[expr {$hp - 1}]]]"
  lassign [winOf [expr {max(5, $x0 - 40)}] $cy] nx ny
  v [list event generate .c <ButtonPress-3> -x $nx -y $ny]
  # Not in smoke mode the context menu is posted with a grab: unpost it, invoke the entry.
  v {.pop unpost; catch {grab release [grab current]}}
  v {.pop invoke {Add note...}}
  v {update idletasks}
  set noted [v {winfo exists .note.t}]
  if {$noted} {
    v [list .note.t insert end $notetext]
    set nst [v {.note.b.save invoke; .status cget -text}]
  } else {
    set nst [status]
  }
  check note [expr {$noted && [string match "*note saved*" $nst]}] $nst
} else {
  check select-copy 0 "no current hit box"
}
v {::safepdf::hideFind; update}
set title [v {wm title .}]
check unsaved-mark [string match "\\* *" $title] "title \"$title\""
# Save (Ctrl+S): FILE-annotated.pdf, then the viewer opens it.
v {set ::safepdf::lastAsk {}}
set t [now]
set sst [v {focus -force .c; update; event generate .c <Control-Key-s>; .status cget -text}]
set saved [string match "saved *" $sst]
rec save_ms [ms [expr {[now] - $t}]]
check save $saved "$sst; asked \"[v {set ::safepdf::lastAsk}]\""
set target [file rootname $file]-annotated.pdf
# Close (Ctrl+W; unsaved marks are discarded if the save failed), reopen the saved file.
v {set ::safepdf::autoAnswer no}
v {focus -force .c; update; event generate .c <Control-Key-w>}
check close [string equal [v {wm title .}] safe-pdf] "title \"[v {wm title .}]\""
v {set ::safepdf::autoAnswer {}}
if {$saved} {
  set dt [vopen $target]
  set rst [status]
  set nm 0
  regexp {(\d+) saved marks} $rst -> nm
  # The highlight is drawn by the renderer now: go to the hit's page and read the pixel.
  # (Go > Next page until the hit's page: page labels make Ctrl+G ambiguous.)
  set t [now]
  for {set k 1} {$k < $hp} {incr k} { v {.menubar.go invoke {Next page}} }
  waitPage [expr {$hp - 1}] $t 60000000
  set pxAfter [pixelAt [expr {$hp - 1}] {*}$rb]
  check reopen-marks [expr {$nm >= 2 && [yellowish $pxAfter]}] "[ms $dt] ms; $nm saved marks; pixel at the highlight $pxAfter (before save $pxBefore); page at [v [list .c coords p[expr {$hp - 1}]]]; $rst"
  v {focus -force .c; update; event generate .c <Control-Key-w>}
}
rec target $target
dumpLog
rec hwm [hwm]
v {set ::safepdf::autoAnswer no}
catch {send -async $::app {::safepdf::emit quit}}
rec result [expr {$ok ? "ok" : "FAIL"}]
close $fh
exit 0
TCL

# ---------------------------------------------------------------------------------------------
# start_x: starts Xvfb on a free display (sets $disp, $xvfb_pid).
start_x() {
  local n
  for n in $(seq 140 199); do
    if [ ! -e "/tmp/.X11-unix/X$n" ] && [ ! -e "/tmp/.X$n-lock" ]; then
      Xvfb ":$n" -screen 0 1700x1100x24 -nolisten tcp >"$work/xvfb.log" 2>&1 &
      xvfb_pid=$!
      local k
      for k in $(seq 1 100); do
        [ -S "/tmp/.X11-unix/X$n" ] && { disp=":$n"; return 0; }
        kill -0 "$xvfb_pid" 2>/dev/null || break
        sleep 0.05
      done
      kill "$xvfb_pid" 2>/dev/null || true
      wait "$xvfb_pid" 2>/dev/null || true
      xvfb_pid=""
    fi
  done
  echo "viewer-corpus: cannot start Xvfb" >&2
  return 1
}
stop_x() {
  if [ -n "$xvfb_pid" ]; then
    kill "$xvfb_pid" 2>/dev/null || true
    wait "$xvfb_pid" 2>/dev/null || true
    xvfb_pid=""
  fi
}

# run_one MODE FILE LOG [WORD NOTE]: viewer + driver on a fresh Xvfb; writes LOG and LOG.meta
# (viewer exit status, driver exit status, wall time).
run_one() {
  local mode="$1" file="$2" log="$3" word="${4:-}" note="${5:-}"
  local abs
  abs="$(cd "$(dirname "$file")" && pwd)/$(basename "$file")"
  start_x
  local t0 t1 vrc drc
  t0=$(date +%s.%N)
  env -u DISPLAY DISPLAY="$disp" SAFEPDF_VIEWER_DRIVE=1 SAFEPDF_VIEWER_GEOMETRY=1600x1000 \
    SAFEPDF_VIEWER_VIEW=continuous \
    "$viewer" "$abs" >"$log.stdout" 2>"$log.stderr" &
  viewer_pid=$!
  drc=0
  env -u DISPLAY DISPLAY="$disp" timeout -k 5 "$timeout_s" "$wish" "$work/driver.tcl" \
    "$mode" "$log" "$abs" "$viewer_pid" "$word" "$note" >"$log.driver" 2>&1 || drc=$?
  # The driver asked the viewer to close; give it 20 s, then kill it.
  local k
  for k in $(seq 1 200); do
    kill -0 "$viewer_pid" 2>/dev/null || break
    sleep 0.1
  done
  if kill -0 "$viewer_pid" 2>/dev/null; then
    kill -9 "$viewer_pid" 2>/dev/null || true
    echo "killed" >>"$log.stderr.note"
  fi
  vrc=0
  wait "$viewer_pid" 2>/dev/null || vrc=$?
  viewer_pid=""
  t1=$(date +%s.%N)
  stop_x
  printf 'viewer_rc\t%s\ndriver_rc\t%s\nwall_s\t%s\n' "$vrc" "$drc" \
    "$(python3 -I -c 'import sys; print(round(float(sys.argv[2]) - float(sys.argv[1]), 3))' "$t0" "$t1")" \
    >"$log.meta"
}

commit="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
if [ -n "$(git status --porcelain --untracked-files=no 2>/dev/null)" ]; then commit="$commit+dirty"; fi

if [ "$do_corpus" = 1 ]; then
  mkdir -p "$work/corpus"
  : >"$work/corpus/list"
  i=0
  for f in "${files[@]}"; do
    i=$((i + 1))
    name="$(basename "$f" .pdf)"
    printf '[%d/%d] %s ... ' "$i" "${#files[@]}" "$name"
    run_one corpus "$f" "$work/corpus/$name.log"
    printf '%s\t%s\n' "$name" "$f" >>"$work/corpus/list"
    tail -n 3 "$work/corpus/$name.log.meta" | tr '\n' ' '
    echo
  done
fi

# The session: (file, word to search, note text).
session=(
  "corpus/files/arxiv-2201.11903.pdf|arithmetic|Outline paper: note [1] \$x {y} ü"
  "corpus/files/www.ntsb.gov-AIR2201.pdf|airplane|Encrypted NTSB file: note"
  "corpus/files/arxiv-2303.08774.pdf|benchmark|Long paper: note"
)
if [ "$do_session" = 1 ]; then
  mkdir -p "$work/session"
  : >"$work/session/list"
  for entry in "${session[@]}"; do
    IFS='|' read -r f word note <<<"$entry"
    [ -f "$f" ] || { echo "session: $f missing, skipped"; continue; }
    name="$(basename "$f" .pdf)"
    # Work on a copy, so the corpus file and an older -annotated.pdf stay out of it.
    cp "$f" "$work/session/$name.pdf"
    rm -f "$work/session/$name-annotated.pdf"
    echo "session: $name"
    run_one session "$work/session/$name.pdf" "$work/session/$name.log" "$word" "$note"
    saved="$work/session/$name-annotated.pdf"
    {
      if [ -f "$saved" ]; then
        if command -v qpdf >/dev/null; then
          if qpdf --check "$saved" >"$saved.qpdf" 2>&1; then echo -e "qpdf\tok"
          else echo -e "qpdf\tFAIL $(tail -n 2 "$saved.qpdf" | tr '\n' ' ')"; fi
        else echo -e "qpdf\tskipped (no qpdf)"; fi
        osz=$(stat -c %s "$work/session/$name.pdf")
        if cmp -s -n "$osz" "$work/session/$name.pdf" "$saved"; then echo -e "prefix\tok"
        else echo -e "prefix\tFAIL"; fi
        echo -e "saved_bytes\t$(stat -c %s "$saved") (original $osz)"
      else
        echo -e "saved_file\tnone"
      fi
    } >"$work/session/$name.post"
    printf '%s\t%s\n' "$name" "$f" >>"$work/session/list"
  done
fi

python3 -I - "$work" "$commit" "$json" "$timeout_s" <<'PY'
import json, os, statistics, sys

work, commit, json_out, timeout_s = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
HANG_MS = 5000.0


def records(path):
    out = []
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            for line in f:
                out.append(line.rstrip("\n").split("\t"))
    except FileNotFoundError:
        pass
    return out


def meta(path):
    return {r[0]: r[1] for r in records(path) if len(r) >= 2}


def pct(xs, q):
    if not xs:
        return None
    xs = sorted(xs)
    k = max(0, min(len(xs) - 1, int(round(q * (len(xs) - 1)))))
    return xs[k]


def tcl_list(s):
    # The page lists the wrapper logs are plain words ("3", "e4").
    return s.split() if s else []


def parse_corpus(name, log):
    recs = records(log)
    m = meta(log + ".meta")
    r = {"file": name, "opened": False, "pages": 0, "pages_displayed": 0, "render_errors": [],
         "open_ms": None, "connect_ms": None, "page_ms": [], "wait_ms": [], "hangs": [],
         "max_event_ms": 0.0, "max_event": "", "peak_rss_mib": None, "viewer_rc": None,
         "driver_rc": None, "fatal": None, "status_open": "", "wall_s": None, "nav_mismatch": []}
    first = {}      # page index -> (event ms, event)
    hwm = 0
    for rec in recs:
        k = rec[0]
        if k == "connect_ms":
            r["connect_ms"] = float(rec[1])
        elif k == "open_ms":
            r["open_ms"] = float(rec[1])
            r["status_open"] = rec[2] if len(rec) > 2 else ""
        elif k == "pages":
            r["pages"] = int(rec[1])
        elif k == "page":
            p = int(rec[1])
            w = float(rec[2])
            r["wait_ms"].append(w)
            if p > 1 and len(rec) > 3 and rec[3] != str(p):
                r["nav_mismatch"].append(p)
        elif k == "ev":
            dt = float(rec[1])
            new = tcl_list(rec[2])
            ev = rec[3] if len(rec) > 3 else ""
            # Task 8.8: pages shown by a `poll` event carry their time from request to display.
            tw = tcl_list(rec[4]) if len(rec) > 4 else []
            ttd = {int(tw[i]): float(tw[i + 1]) for i in range(0, len(tw) - 1, 2)}
            if dt > r["max_event_ms"]:
                r["max_event_ms"], r["max_event"] = dt, ev
            if dt > HANG_MS:
                r["hangs"].append({"event": ev, "ms": dt, "pages": new})
            for x in new:
                err = x.startswith("e")
                idx = int(x[1:] if err else x)
                if idx not in first:
                    first[idx] = (dt if err else ttd.get(idx, dt), ev, err)
        elif k == "hwm":
            hwm = max(hwm, int(rec[1]))
        elif k == "fatal":
            r["fatal"] = " ".join(rec[1:])
    st = r["status_open"]
    r["opened"] = r["pages"] > 0 and "cannot open" not in st and "cannot read" not in st
    # Page 1 is put on screen by the open event, which also parses the file: its own render
    # time is the one the status line reports.
    import re
    mt = re.search(r"rendered in ([0-9.]+) ms", st)
    for idx, (dt, ev, err) in sorted(first.items()):
        if idx == 0 and mt and ev.startswith("open"):
            dt = float(mt.group(1))
        r["page_ms"].append({"page": idx + 1, "ms": dt, "event": ev.split(" ")[0], "error": err})
        if err:
            r["render_errors"].append(idx + 1)
    r["pages_displayed"] = len(first)
    r["peak_rss_mib"] = round(hwm / 1024, 1) if hwm else None
    r["viewer_rc"] = int(m.get("viewer_rc", "-1"))
    r["driver_rc"] = int(m.get("driver_rc", "-1"))
    r["wall_s"] = float(m["wall_s"]) if "wall_s" in m else None
    try:
        err = open(log + ".stderr", encoding="utf-8", errors="replace").read().strip()
    except FileNotFoundError:
        err = ""
    try:
        err += open(log + ".stderr.note").read().strip()
    except FileNotFoundError:
        pass
    r["stderr"] = err[:2000]
    r["timed_out"] = r["driver_rc"] == 124 or r["driver_rc"] == 137
    r["crashed"] = (r["viewer_rc"] not in (0,)) or r["fatal"] is not None
    return r


result = {"commit": commit, "window": "1600x1000", "view": "continuous",
          "timeout_s": int(timeout_s), "hang_ms": HANG_MS, "files": [], "session": []}

lst = os.path.join(work, "corpus", "list")
for row in records(lst):
    if len(row) >= 1 and row[0]:
        result["files"].append(parse_corpus(row[0], os.path.join(work, "corpus", row[0] + ".log")))

slst = os.path.join(work, "session", "list")
for row in records(slst):
    if not row or not row[0]:
        continue
    name = row[0]
    base = os.path.join(work, "session", name)
    steps, events, hwm, res = [], [], 0, "FAIL"
    for rec in records(base + ".log"):
        if rec[0] == "step":
            steps.append({"step": rec[1], "result": rec[2], "detail": rec[3] if len(rec) > 3 else ""})
        elif rec[0] == "ev":
            events.append(float(rec[1]))
        elif rec[0] == "hwm":
            hwm = max(hwm, int(rec[1]))
        elif rec[0] == "result":
            res = rec[1]
        elif rec[0] == "fatal":
            steps.append({"step": "fatal", "result": "FAIL", "detail": " ".join(rec[1:])})
    post = {r[0]: r[1] for r in records(base + ".post") if len(r) >= 2}
    m = meta(base + ".log.meta")
    ok = res == "ok" and all(v.startswith("ok") or v.startswith("skipped") or k == "saved_bytes"
                             or (k == "saved_file") for k, v in post.items())
    ok = ok and m.get("viewer_rc") == "0"
    result["session"].append({"file": name, "result": "ok" if ok else "FAIL", "steps": steps,
                              "post": post, "viewer_rc": m.get("viewer_rc"),
                              "max_event_ms": max(events) if events else None,
                              "peak_rss_mib": round(hwm / 1024, 1) if hwm else None})

files = result["files"]
all_ms = [p["ms"] for f in files for p in f["page_ms"]]
waits = [w for f in files for w in f["wait_ms"] if w >= 0]
opens = [f["open_ms"] for f in files if f["open_ms"] is not None]
summ = {
    "files": len(files),
    "files_opened": sum(1 for f in files if f["opened"]),
    "pages": sum(f["pages"] for f in files),
    "pages_displayed": sum(f["pages_displayed"] for f in files),
    "render_errors": sum(len(f["render_errors"]) for f in files),
    "ttd_median_ms": statistics.median(all_ms) if all_ms else None,
    "ttd_p95_ms": pct(all_ms, 0.95),
    "ttd_max_ms": max(all_ms) if all_ms else None,
    "pages_over_500ms": sum(1 for x in all_ms if x > 500),
    "wait_median_ms": statistics.median(waits) if waits else None,
    "wait_p95_ms": pct(waits, 0.95),
    "wait_max_ms": max(waits) if waits else None,
    "open_median_ms": statistics.median(opens) if opens else None,
    "open_max_ms": max(opens) if opens else None,
    "hangs": sum(len(f["hangs"]) for f in files),
    "crashes": sum(1 for f in files if f["crashed"]),
    "timeouts": sum(1 for f in files if f["timed_out"]),
    "peak_rss_mib_max": max((f["peak_rss_mib"] or 0) for f in files) if files else None,
    "peak_rss_mib_median": statistics.median([f["peak_rss_mib"] or 0 for f in files]) if files else None,
    "session_ok": sum(1 for s in result["session"] if s["result"] == "ok"),
    "session_runs": len(result["session"]),
}
thr = {"all_open": summ["files_opened"] == summ["files"],
       "all_displayed": summ["pages_displayed"] == summ["pages"],
       "no_crash": summ["crashes"] == 0 and summ["timeouts"] == 0,
       "no_hang": summ["hangs"] == 0 and (summ["ttd_max_ms"] or 0) <= HANG_MS,
       "p95_le_500ms": (summ["ttd_p95_ms"] or 0) <= 500,
       "rss_le_1gib": (summ["peak_rss_mib_max"] or 0) <= 1024,
       "session": summ["session_ok"] == summ["session_runs"]}
result["summary"] = summ
result["thresholds"] = thr
result["m8"] = all(thr.values())


def f1(x):
    return "-" if x is None else f"{x:.0f}" if isinstance(x, float) else str(x)


if files:
    print()
    print(f"{'file':34} {'pages':>5} {'shown':>5} {'open':>7} {'median':>7} {'p95':>7} {'max':>7} "
          f"{'>5s':>3} {'rss':>6} {'rc':>3}  notes")
    for f in files:
        ms = [p["ms"] for p in f["page_ms"]]
        notes = []
        if not f["opened"]:
            notes.append("NOT OPENED: " + f["status_open"][:80])
        if f["render_errors"]:
            notes.append(f"render errors on {f['render_errors'][:8]}")
        if f["fatal"]:
            notes.append("fatal: " + f["fatal"][:80])
        if f["timed_out"]:
            notes.append("TIMEOUT")
        if f["nav_mismatch"]:
            notes.append(f"nav mismatch {f['nav_mismatch'][:5]}")
        if f["stderr"]:
            notes.append("stderr: " + f["stderr"].splitlines()[0][:60])
        print(f"{f['file'][:34]:34} {f['pages']:>5} {f['pages_displayed']:>5} {f1(f['open_ms']):>7} "
              f"{f1(statistics.median(ms) if ms else None):>7} {f1(pct(ms, 0.95)):>7} "
              f"{f1(max(ms) if ms else None):>7} {len(f['hangs']):>3} {f1(f['peak_rss_mib']):>6} "
              f"{f['viewer_rc']:>3}  {'; '.join(notes)}")
for s in result["session"]:
    print()
    print(f"session {s['file']}: {s['result']} (viewer exit {s['viewer_rc']}, "
          f"max event {f1(s['max_event_ms'])} ms, peak RSS {f1(s['peak_rss_mib'])} MiB)")
    for st in s["steps"]:
        print(f"  {st['step']:14} {st['result']:4} {st['detail'][:150]}")
    for k, v in s["post"].items():
        print(f"  {k:14} {v}")
print()
print(f"commit {commit}; window 1600x1000, continuous; times in ms")
print("summary: " + ", ".join(f"{k} {f1(v) if not isinstance(v, float) else f'{v:.1f}'}"
                              for k, v in summ.items()))
print("thresholds: " + ", ".join(f"{k} {'yes' if v else 'NO'}" for k, v in thr.items()))
print(f"M8 (docs/viewer-corpus.md thresholds): {'holds' if result['m8'] else 'does NOT hold'}")
if json_out:
    with open(json_out, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=1, ensure_ascii=False)
        f.write("\n")
sys.exit(0 if result["m8"] else 1)
PY
