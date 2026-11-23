#!/usr/bin/env bash
# Full text and identifier detection of `viewer --biblean` (task 10.3; Plan.md §6 Phase 10;
# bib-lean docs/READER-CONTRACT.md §3, optional routes /fulltext and /detected). Run from the
# repo root:
#   Tests/biblean/text-test.sh [--no-build] [CORPUS.pdf …]
#
# Uses the stub server (Tests/biblean/stub_server.py) and the fixture
# Tests/biblean/text-pdf.py (page 1: an arXiv stamp and a DOI; page 2: a second DOI; page 3:
# a DOI that must not be detected). Checks through `--probe`: the full text arrives as
# UTF-8 with one form feed between pages, every page equal to `SAFEPDF_PAGE=N inspect --view
# text --json`; the detection body is {"doi", "arxiv"} with the first of each; detection is
# posted for an attachment without a parent and skipped for one with a parent; both POSTs
# carry the token, no Origin, the right content type; and failures of these posts (HTTP 500,
# a dropped connection) never make the viewer fail — neither the probe nor the window
# (Xvfb, smoke mode), whose background posts are also checked to arrive. Every extra
# argument is a PDF probed the same way; its detected identifiers are printed (informational).
# Exit 0 on success.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
cd "$repo"

if [ "${1:-}" = "--no-build" ]; then
  shift
else
  lake build viewer inspect
fi
viewer="$repo/.lake/build/bin/viewer"
inspect="$repo/.lake/build/bin/inspect"
[ -x "$viewer" ] || { echo "text-test: $viewer not built" >&2; exit 1; }
[ -x "$inspect" ] || { echo "text-test: $inspect not built" >&2; exit 1; }
extra=()
for f in "$@"; do extra+=("$(cd "$(dirname "$f")" && pwd)/$(basename "$f")"); done

umask 077
work="$(mktemp -d)"
stub_pid=""
stop_stub() {
  if [ -n "$stub_pid" ]; then kill "$stub_pid" 2>/dev/null || true; wait "$stub_pid" 2>/dev/null || true; fi
  stub_pid=""
}
cleanup() { stop_stub; rm -rf "$work"; }
trap cleanup EXIT

pass=0 fail=0
ok() { echo "ok - $1"; pass=$((pass + 1)); }
bad() { echo "FAIL - $1${2:+: $2}"; fail=$((fail + 1)); }
check() { if [ "$1" = 0 ]; then ok "$2"; else bad "$2" "${3:-}"; fi; }

att=ATT23456 parent=PAR23456
python3 -I "$here/text-pdf.py" "$work/text.pdf"
token="$(python3 -I -c 'import secrets; print(secrets.token_hex(32))')"
printf '%s\n' "$token" >"$work/token"

# start_stub PDF PARENT [STUB-ARGS…]: (re)starts the stub, sets $server; fresh log and outputs.
start_stub() {
  local pdf="$1" par="$2"; shift 2
  stop_stub
  rm -f "$work/port" "$work/log" "$work/fulltext" "$work/detected"
  python3 -I "$here/stub_server.py" --token-file "$work/token" --pdf "$pdf" \
    --att "$att" --parent "$par" --title "Parent title" --port-file "$work/port" \
    --log "$work/log" --fulltext-out "$work/fulltext" --detected-out "$work/detected" "$@" &
  stub_pid=$!
  for _ in $(seq 100); do [ -s "$work/port" ] && break; sleep 0.05; done
  [ -s "$work/port" ] || { echo "text-test: stub server did not start" >&2; exit 1; }
  server="http://127.0.0.1:$(cat "$work/port")"
  touch "$work/log"
}

# probe NAME: runs `viewer --biblean --probe` with the token on fd 3; exit code in $rc.
probe() {
  local name="$1"
  env -u BIBLEAN_PAGE BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" "$viewer" --biblean --probe \
    >"$work/$name.out" 2>"$work/$name.err" 3< <(printf '%s\n' "$token")
  rc=$?
}

# From here on a failing check is counted, not fatal (a failing last command of an `&&` list
# would otherwise end the script under `set -e`).
set +e

# 1. A standalone attachment (no parent): detection and full text are posted.
start_stub "$work/text.pdf" ""
probe a
check "$rc" "T1 probe exits 0" "exit $rc: $(cat "$work/a.err")"
python3 -I - "$work/log" "$att" <<'EOF'
import json, sys
log = [json.loads(l) for l in open(sys.argv[1])]
att = sys.argv[2]
posts = [(r["method"], r["path"], r["status"], r["ctype"]) for r in log if r["method"] == "POST"]
want = [("POST", f"/api/attachments/{att}/detected", 202, "application/json"),
        ("POST", f"/api/attachments/{att}/fulltext", 200, "text/plain; charset=utf-8")]
assert posts == want, posts
assert all(r["auth"] == "ok" and not r["origin"] for r in log), log
EOF
check $? "T2 detected (202) then fulltext (200) were posted, right token, no Origin, right types" \
  "$(cat "$work/log")"
python3 -I - "$work/detected" <<'EOF'
import json, sys
ds = [json.loads(l) for l in open(sys.argv[1])]
assert ds == [{"doi": "10.1234/safe-pdf.5678", "arxiv": "2101.01234v2"}], ds
EOF
check $? "T3 the detection body is the first DOI and the first arXiv id of page 1" \
  "$(cat "$work/detected" 2>/dev/null)"
grep -qxF 'doi: 10.1234/safe-pdf.5678 (page 1), 10.5555/Second-Paper.2 (page 2)' "$work/a.out" &&
  grep -qxF 'arxiv: 2101.01234v2 (page 1)' "$work/a.out" &&
  grep -qxF 'detected: HTTP 202' "$work/a.out"
check $? "T4 the probe lists the identifiers of pages 1-2 (deduplicated, page 3 not read)" \
  "$(cat "$work/a.out")"
python3 -I - "$work/fulltext" "$inspect" "$work/text.pdf" <<'EOF'
import json, os, subprocess, sys
body = open(sys.argv[1], "rb").read()
pages = body.decode("utf-8").split("\f")
assert len(pages) == 3, len(pages)
for n, text in enumerate(pages, start=1):
    out = subprocess.run([sys.argv[2], "--view", "text", "--json", sys.argv[3]], check=True,
                         capture_output=True, env=dict(os.environ, SAFEPDF_PAGE=str(n))).stdout
    want = json.loads(out.decode("utf-8").splitlines()[0])["text"]
    assert text == want, (n, text, want)
assert "arXiv:2101.01234v2" in pages[0] and "10.9999/not-detected" in pages[2]
EOF
check $? "T5 the full text has 3 pages split by form feeds, each equal to inspect --view text" \
  "$(head -c 400 "$work/fulltext" 2>/dev/null)"
grep -qx 'fulltext: HTTP 200 (3 pages, [0-9]* bytes)' "$work/a.out"
check $? "T6 the probe reports the full-text post" "$(cat "$work/a.out")"

# 2. An attachment with a parent item: no detection is posted, the full text still is.
start_stub "$work/text.pdf" "$parent"
probe b
[ "$rc" = 0 ] && grep -qx 'detected: skipped (the attachment has a parent item)' "$work/b.out" &&
  ! grep -q '/detected' "$work/log" && grep -q '"/api/attachments/'"$att"'/fulltext"' "$work/log"
check $? "T7 with a parent item detection is skipped, the full text is posted" \
  "exit $rc: $(cat "$work/b.out" "$work/log")"

# 3. The text posts fail: the probe still succeeds.
start_stub "$work/text.pdf" "" --fail-text 500
probe c
[ "$rc" = 0 ] && grep -qx 'detected: HTTP 500 (ioError)' "$work/c.out" &&
  grep -qx 'fulltext: HTTP 500 (ioError) (3 pages, [0-9]* bytes)' "$work/c.out"
check $? "T8 HTTP 500 from /detected and /fulltext: the probe exits 0 and reports them" \
  "exit $rc: $(cat "$work/c.out" "$work/c.err")"
start_stub "$work/text.pdf" "" --fail-text close
probe d
[ "$rc" = 0 ] && grep -q '^detected: failed: ' "$work/d.out" && grep -q '^fulltext: failed: ' "$work/d.out"
check $? "T9 a dropped connection on the posts: the probe exits 0 and reports them" \
  "exit $rc: $(cat "$work/d.out" "$work/d.err")"
! grep -qF "$token" "$work"/*.out "$work"/*.err
check $? "T10 the token is not in the viewer's output"

# 4. The window (Xvfb, smoke mode): the posts run in the background, failures do not matter.
wrap=()
display=1
if [ -n "${DISPLAY:-}" ] && { command -v xdpyinfo >/dev/null 2>&1 && xdpyinfo >/dev/null 2>&1 \
    || [ -S "/tmp/.X11-unix/X${DISPLAY#*:}" ]; }; then
  :
elif command -v Xvfb >/dev/null 2>&1; then
  # Start Xvfb directly, not through xvfb-run: xvfb-run reuses file descriptor 3 for its own
  # diagnostics (`exec 3>&1`), which would replace the token pipe the viewer reads from fd 3.
  xvfb_dpy=""
  for n in $(seq 120 160); do
    [ -e "/tmp/.X11-unix/X$n" ] || [ -e "/tmp/.X$n-lock" ] && continue
    Xvfb ":$n" -screen 0 1280x1024x24 -nolisten tcp >/dev/null 2>&1 &
    xvfb_pid=$!
    for _ in $(seq 1 50); do [ -S "/tmp/.X11-unix/X$n" ] && break; sleep 0.1; done
    if [ -S "/tmp/.X11-unix/X$n" ]; then xvfb_dpy=":$n"; break; fi
    kill "$xvfb_pid" 2>/dev/null; wait "$xvfb_pid" 2>/dev/null
  done
  if [ -n "$xvfb_dpy" ]; then
    export DISPLAY="$xvfb_dpy"
    trap 'kill "$xvfb_pid" 2>/dev/null; cleanup' EXIT
  else
    display=0
    echo "skip - T11-T15 window checks (Xvfb did not start)"
  fi
else
  display=0
  echo "skip - T11-T15 window checks (no X display and no Xvfb)"
fi
# window NAME: the window in smoke mode; exit code in $rc.
window() {
  local name="$1"
  rm -rf "$work/smoke" "$work/tmp"; mkdir -p "$work/smoke" "$work/tmp"
  start=$(date +%s)
  env -u BIBLEAN_PAGE TMPDIR="$work/tmp" SAFEPDF_VIEWER_SMOKE="$work/smoke" \
    BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" \
    timeout 60 "${wrap[@]}" "$viewer" --biblean >"$work/$name.out" 2>"$work/$name.err" \
    3< <(printf '%s\n' "$token")
  rc=$?
  elapsed=$(( $(date +%s) - start ))
}
if [ "$display" = 1 ]; then
  start_stub "$work/text.pdf" ""
  window w1
  base=$elapsed
  check "$rc" "T11 the window run exits 0" "exit $rc: $(cat "$work/w1.err")"
  grep -q '"/api/attachments/'"$att"'/detected", .*"status": 202' "$work/log" &&
    grep -q '"/api/attachments/'"$att"'/fulltext", .*"status": 200' "$work/log" &&
    [ "$(tr -cd '\f' <"$work/fulltext" | wc -c)" = 2 ]
  check $? "T12 the window's background posts arrived (detection, 3-page full text)" "$(cat "$work/log")"
  start_stub "$work/text.pdf" "" --fail-text close
  window w2
  [ "$rc" = 0 ] && grep -q '^title: Full Text PDF.pdf - page [1-3]/3 - safe-pdf$' "$work/smoke/state.txt"
  check $? "T13 failing posts do not break the window (exit 0, document shown)" \
    "exit $rc: $(cat "$work/w2.err" "$work/smoke/state.txt" 2>/dev/null)"
  grep -q 'fulltext: failed' "$work/w2.err" && ! grep -qF "$token" "$work/w2.err" "$work/w2.out"
  check $? "T14 the window reports the failed posts on stderr, without the token" "$(cat "$work/w2.err")"
  start_stub "$work/text.pdf" "" --fail-text hang
  window w3
  [ "$rc" = 0 ] && [ "$elapsed" -le $((base + 10)) ]
  check $? "T15 a server that never answers the posts does not hold the viewer (exit 0 in ${elapsed}s, normal run ${base}s)" \
    "exit $rc: $(cat "$work/w3.err")"
fi

# 5. Extra PDFs (informational): the identifiers the probe detects.
for f in "${extra[@]}"; do
  start_stub "$f" ""
  probe x
  echo "# $(basename "$f"): exit $rc"
  grep -E '^(pages|doi|arxiv|detected|fulltext):' "$work/x.out" | sed 's/^/#   /'
done

echo "text-test: $pass passed, $fail failed"
[ "$fail" = 0 ]
