#!/usr/bin/env bash
# M8/M9 corpus check of the native macOS app (task 11.5; Plan.md §6 Phases 8, 9, 11; the Tk
# check is scripts/viewer-corpus.sh, docs/viewer-corpus.md; this one docs/macos-smoke.md).
# Run from the repo root:
#
#   scripts/macos-corpus.sh [--no-build] [--json OUT] [--out DIR] [--timeout SEC]
#                           [--no-session] [--no-corpus] [--corpus DIR] [--no-fetch] [FILE.pdf ...]
#
# 1. Corpus pass: every PDF (default: corpus/files/*.pdf; --corpus DIR another copy of the corpus,
#    each file verified against corpus/manifest.json's SHA-256 first) is opened by the app itself
#    in a headless session (macos/App/SmokeSession.swift: activation policy Prohibited, never
#    activated, no window shown) with a 1600x1000 page area in the continuous view at Automatic
#    Zoom (the Tk check's setup); the session goes through every page with Next page, waiting
#    after each step until the new current page has its image and no render is pending. Per
#    file: opened, pages, per-page time to display (the render's request to its delivery on the
#    main thread, through the confined worker), the wait after Next page, render errors, pages
#    never displayed, the longest time the main thread was busy (a hang is > 5 s), exit status,
#    the peak physical footprints of the app and of its worker processes. Hard limit per file
#    --timeout (default 900 s).
# 2. Session on three papers (outline, encrypted NTSB, long), each on a copy: open, outline jump
#    (the page changes), find a word, double click the hit and copy (the word on the pasteboard),
#    highlight (yellow pixels), a note left of it with metacharacters and ü, Save As
#    FILE-annotated.pdf through the first-save question, close, reopen the saved file (the marks
#    saved, the highlight yellow from the renderer), close; the original bytes a prefix of the
#    saved file (C7); qpdf --check and mutool's annotation list when the tools exist.
# The corpus files are git-ignored: when none are there and --corpus is not given, the script
# fetches them (python3 -I scripts/corpus/fetch.py, SHA-256 verified) unless --no-fetch; when that
# fails (no network) it reports "skipped" and exits 0.
# A front-app watcher (lsappinfo, every 0.2 s) fails the run if the app it started ever becomes
# the front app or a Foreground app. Output: a table and a summary against the M8 thresholds of
# docs/viewer-corpus.md; --json OUT writes every number. Exit 0 when M8 holds.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

build=1 json="" outdir="" timeout_s=900 do_session=1 do_corpus=1 corpus="" fetch=1
files=()
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) build=0 ;;
    --json) json="$2"; shift ;;
    --out) outdir="$2"; shift ;;
    --timeout) timeout_s="$2"; shift ;;
    --no-session) do_session=0 ;;
    --no-corpus) do_corpus=0 ;;
    --corpus) corpus="$2"; shift ;;
    --no-fetch) fetch=0 ;;
    -h|--help) sed -n '2,33p' "$0"; exit 0 ;;
    *) files+=("$1") ;;
  esac
  shift
done
if [ "$(uname -s)" != Darwin ]; then echo "macos-corpus: macOS only" >&2; exit 1; fi

if [ -n "$outdir" ]; then
  mkdir -p "$outdir"; work="$(cd "$outdir" && pwd)"
else
  work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
fi

# The corpus: given files, --corpus DIR (verified), corpus/files, or a fetch.
if [ ${#files[@]} -eq 0 ]; then
  dir="${corpus:-corpus/files}"
  if [ -z "$corpus" ] && ! ls corpus/files/*.pdf >/dev/null 2>&1 && [ "$fetch" = 1 ]; then
    echo "macos-corpus: corpus/files is empty; fetching (python3 -I scripts/corpus/fetch.py)"
    python3 -I scripts/corpus/fetch.py || echo "macos-corpus: the fetch failed (network?)" >&2
  fi
  shopt -s nullglob
  files=("$dir"/*.pdf)
  shopt -u nullglob
  if [ ${#files[@]} -eq 0 ]; then
    echo "macos-corpus: skipped: no corpus files in $dir (see docs/corpus.md)"
    exit 0
  fi
  # Every file must match the manifest (SHA-256 and size); the rest is refused.
  python3 -I - "$repo/corpus/manifest.json" "$work/verified.txt" "${files[@]}" <<'PY'
import hashlib, json, os, sys
man = {e["id"]: e for e in json.load(open(sys.argv[1]))["entries"]}
ok, bad = [], []
for f in sys.argv[3:]:
    e = man.get(os.path.basename(f)[:-4])
    h = hashlib.sha256(open(f, "rb").read()).hexdigest() if e else None
    (ok if e and h == e["sha256"] and os.path.getsize(f) == e["size"] else bad).append(f)
open(sys.argv[2], "w").write("".join(f + "\n" for f in ok))
print("macos-corpus: %d files verified against the manifest (SHA-256)%s" % (len(ok), "; refused: " + ", ".join(bad) if bad else ""))
PY
  files=()
  while IFS= read -r f; do files+=("$f"); done < "$work/verified.txt"
fi

if [ "$build" = 1 ]; then macos/build.sh; fi
bin="$repo/macos/build/safepdf-mac"
[ -x "$bin" ] || { echo "macos-corpus: $bin not built (macos/build.sh)" >&2; exit 1; }

samples=0; alerts=0
watchlog="$work/front-app.log"; : > "$watchlog"
# run_app NAME SCRIPT LIMIT: the app on SCRIPT under the front-app watcher; sets `rc` (124: the
# hard limit) and `leaked`.
run_app() {
  local name="$1" script="$2" limit=$(( $3 * 5 )) out="$work/out-$1" pid t=0
  mkdir -p "$out"
  SAFEPDF_MACOS_SESSION="$script" SAFEPDF_MACOS_SESSION_OUT="$out" SAFEPDF_SESSION_IN="$work" \
    "$bin" 2>"$out/stderr.log" &
  pid=$!
  rc=0; leaked=0
  local timed_out=0
  while kill -0 "$pid" 2>/dev/null; do
    local front front_pid
    front="$(lsappinfo front 2>/dev/null || true)"
    front_pid="$(lsappinfo info -only pid "$front" 2>/dev/null | tr -dc '0-9' || true)"
    printf '%s %s front pid %s\n' "$(date +%T)" "$name" "${front_pid:-?}" >> "$watchlog"
    samples=$((samples + 1))
    if [ "$front_pid" = "$pid" ] || lsappinfo list 2>/dev/null | grep -E "pid = $pid[^0-9].*type=\"Foreground\"" >/dev/null; then
      echo "FAIL: $name: the app became the front or a Foreground app; killing PID $pid" >&2
      kill "$pid" 2>/dev/null || true; leaked=1
    fi
    t=$((t + 1))
    if [ "$t" -gt "$limit" ]; then kill -9 "$pid" 2>/dev/null || true; timed_out=1; fi
    sleep 0.2
  done
  wait "$pid" || rc=$?
  if [ "$timed_out" = 1 ]; then rc=124; fi
  if [ "$leaked" = 1 ]; then alerts=$((alerts + 1)); fi
}

# 1. Corpus pass.
results="$work/results.jsonl"; : > "$results"
if [ "$do_corpus" = 1 ]; then
  i=0
  for f in "${files[@]}"; do
    i=$((i + 1))
    name="$(basename "$f" .pdf)"
    abs="$(cd "$(dirname "$f")" && pwd)/$(basename "$f")"
    printf 'size 1600 1000\nopen %s\ncorpus-pass\n' "$abs" > "$work/c-$i.txt"
    run_app "c-$i" "$work/c-$i.txt" "$timeout_s"
    python3 -I - "$work/out-c-$i/corpus.json" "$name" "$rc" "$leaked" "$work/out-c-$i/stderr.log" >> "$results" <<'PY'
import json, os, sys
path, name, rc, leaked, err = sys.argv[1:]
try:
    r = json.load(open(path))
except Exception:
    r = {"opened": False}
r["file"] = name
r["exit"] = int(rc)
r["leaked"] = leaked == "1"
lines = open(err, errors="replace").read().splitlines() if os.path.exists(err) else []
r["failures"] = [l for l in lines if l.startswith("FAIL")][:5]
print(json.dumps(r))
PY
    tail -1 "$results" | python3 -I -c '
import json, sys
r = json.loads(sys.stdin.read())
t = sorted(x for x in r.get("ttd_ms", []) if x >= 0)
med = t[len(t) // 2] if t else -1
print("macos-corpus: %-28s %4s pages  open %7.1f ms  median %6.1f ms  max %7.1f ms  block %6.0f ms  exit %d%s" % (
    r["file"], r.get("pages", "-"), r.get("open_ms", -1), med, t[-1] if t else -1,
    r.get("max_block_ms", -1), r["exit"], "" if r.get("opened") else "  NOT OPENED"))'
  done
fi

# 2. Session on three papers.
session_rows="$work/session.jsonl"; : > "$session_rows"
if [ "$do_session" = 1 ]; then
  n=0
  for spec in "arxiv-2201.11903 arithmetic" "www.ntsb.gov-AIR2201 airplane" "arxiv-2303.08774 benchmark"; do
    set -- $spec
    paper="$1"; word="$2"; src=""
    for f in "${files[@]}"; do [ "$(basename "$f" .pdf)" = "$paper" ] && src="$f"; done
    if [ -z "$src" ]; then echo "macos-corpus: session: $paper not in the corpus, skipped"; continue; fi
    n=$((n + 1))
    sdir="$work/s-$n"; mkdir -p "$sdir"
    cp "$src" "$sdir/$paper.pdf"; cp "$src" "$sdir/$paper-orig.pdf"
    cat > "$work/s-$n.txt" <<EOF
size 1600 1000
open $sdir/$paper.pdf
remember p0 page
outline third
expect page != @p0
find $word
expect find ~ hit
dblclick-hit
key cmd+c
expect clipboard ~ $word
key ctrl+cmd+h
expect pill ~ highlighted
measure-mark
expect mark.b < 0.8
expect mark.g > 0.45
note-left
note-save note [x] {y} \$z \\ ü
expect pill ^ note saved
expect edited = 1
answer saveas
saveurl $sdir/$paper-annotated.pdf
key cmd+s
expect doc = $paper-annotated.pdf
expect pill ^ saved 2 new
remember save_ms last_ms
prefix $sdir/$paper-orig.pdf $sdir/$paper-annotated.pdf
key cmd+w
expect doc =
open $sdir/$paper-annotated.pdf
expect saved >= 2
expect kinds ~ H
measure-mark
expect mark.b < 0.8
expect mark.g > 0.45
key cmd+w
EOF
    run_app "s-$n" "$work/s-$n.txt" 600
    q="-"
    if command -v qpdf >/dev/null 2>&1 && [ -f "$sdir/$paper-annotated.pdf" ]; then
      qr=0; qpdf --check "$sdir/$paper-annotated.pdf" >/dev/null 2>&1 || qr=$?
      if [ "$qr" = 0 ] || [ "$qr" = 3 ]; then q="ok"; else q="exit $qr"; fi
    fi
    python3 -I - "$work/out-s-$n/stderr.log" "$paper" "$rc" "$leaked" "$q" "$sdir/$paper.pdf" "$sdir/$paper-annotated.pdf" >> "$session_rows" <<'PY'
import json, os, re, sys
err, paper, rc, leaked, q, orig, saved = sys.argv[1:]
log = open(err, errors="replace").read() if os.path.exists(err) else ""
fails = [l for l in log.splitlines() if l.startswith("FAIL")]
def grab(pat):
    m = re.search(pat, log)
    return m.group(1) if m else "-"
print(json.dumps({
    "paper": paper, "passed": rc == "0" and leaked == "0" and not fails, "exit": int(rc), "failures": fails[:5],
    "outline": grab(r"outline row \d+ (“[^”]*”: page \d+ -> \d+ \(\d+ ms\))"),
    "find": grab(r"  find: (.*)"), "copied": grab(r"expect clipboard ~ \S+: ok \((.*)\)"),
    "appended": os.path.getsize(saved) - os.path.getsize(orig) if os.path.exists(saved) else -1,
    "save_ms": grab(r"save_ms = (\S+)"), "qpdf": q,
}, ensure_ascii=False))
PY
    tail -1 "$session_rows" | python3 -I -c '
import json, sys
r = json.loads(sys.stdin.read())
print("macos-corpus: session %-22s %s; outline %s; find %s; copied %r; %d bytes appended; save %s ms; qpdf %s" % (
    r["paper"], "passed" if r["passed"] else "FAILED " + " | ".join(r["failures"]), r["outline"], r["find"],
    r["copied"], r["appended"], r["save_ms"], r["qpdf"]))'
  done
fi

# Summary against the M8 thresholds (docs/viewer-corpus.md).
python3 -I - "$results" "$session_rows" "${json:-}" "$samples" "$alerts" <<'PY'
import json, sys
res_path, ses_path, out, samples, alerts = sys.argv[1:]
rs = [json.loads(l) for l in open(res_path) if l.strip()]
ss = [json.loads(l) for l in open(ses_path) if l.strip()]
MiB = 1024 * 1024
ttd = sorted(x for r in rs for x in r.get("ttd_ms", []) if x >= 0)
waits = sorted(x for r in rs for x in r.get("wait_ms", []))
opens = sorted(r.get("open_ms", -1) for r in rs if r.get("opened"))
def pct(xs, p):
    return xs[min(len(xs) - 1, int(p * len(xs)))] if xs else -1
pages = sum(r.get("pages", 0) for r in rs)
errors = sum(len(r.get("errors", {})) for r in rs)
missing = sum(len(r.get("missing", [])) for r in rs)
opened = sum(1 for r in rs if r.get("opened"))
nonzero = [r["file"] for r in rs if r["exit"] != 0]
timeouts = [r["file"] for r in rs if r["exit"] == 124]
block = max((r.get("max_block_ms", 0) for r in rs), default=0)
slow = [x for x in ttd if x > 5000]
app = max((r.get("peak_app_bytes", 0) for r in rs), default=0)
wrk = max((r.get("peak_worker_bytes", 0) for r in rs), default=0)
worst = max(rs, key=lambda r: max(r.get("peak_app_bytes", 0), r.get("peak_worker_bytes", 0)), default={})
if rs:
    print("macos-corpus: files opened %d / %d; pages displayed %d / %d (%d render errors, %d never displayed)" % (
        opened, len(rs), pages - missing, pages, errors, missing))
    print("macos-corpus: time to display: median %.0f ms, p95 %.0f ms, max %.0f ms; over 500 ms / 1 s / 5 s: %d / %d / %d" % (
        pct(ttd, .5), pct(ttd, .95), ttd[-1] if ttd else -1, sum(x > 500 for x in ttd), sum(x > 1000 for x in ttd), len(slow)))
    print("macos-corpus: wait after Next page: median %.1f ms, p95 %.0f ms, max %.0f ms; open (to the first page shown): median %.0f ms, max %.0f ms" % (
        pct(waits, .5), pct(waits, .95), waits[-1] if waits else -1, pct(opens, .5), opens[-1] if opens else -1))
    print("macos-corpus: longest main-thread block %.0f ms; non-zero exits %d, timeouts %d" % (block, len(nonzero), len(timeouts)))
    print("macos-corpus: peak footprint: app %.0f MiB, worker %.0f MiB (worst file %s)" % (app / MiB, wrk / MiB, worst.get("file", "-")))
if ss:
    print("macos-corpus: session: %d / %d passed" % (sum(s["passed"] for s in ss), len(ss)))
checks = [
    ("every file opens", not rs or opened == len(rs)),
    ("every page displayed", not rs or missing == 0),
    ("no crash (exit 0, no timeout)", not nonzero),
    ("no hang (main thread blocked <= 5 s, no page > 5 s)", block <= 5000 and not slow),
    ("p95 time to display <= 500 ms", not ttd or pct(ttd, .95) <= 500),
    ("peak footprint <= 1 GiB (app and worker)", app <= 1024 * MiB and wrk <= 1024 * MiB),
    ("session passes", all(s["passed"] for s in ss)),
    ("front-app watcher: never frontmost or Foreground", alerts == "0"),
]
for name, ok in checks:
    print("macos-corpus: M8 %-52s %s" % (name, "yes" if ok else "NO"))
print("macos-corpus: front-app watcher: %s samples, %s alerts" % (samples, alerts))
held = all(ok for _, ok in checks)
print("macos-corpus: M8 %s" % ("holds" if held else "does NOT hold"))
if out:
    json.dump({"files": rs, "session": ss}, open(out, "w"), indent=1)
sys.exit(0 if held else 1)
PY
