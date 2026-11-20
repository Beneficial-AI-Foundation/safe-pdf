#!/usr/bin/env bash
# Launch test of `viewer --biblean` (task 10.1; Plan.md §6 Phase 10; bib-lean
# docs/READER-CONTRACT.md §2, §5). Run from the repo root:
#   Tests/biblean/launch-test.sh [--no-build]
#
# Starts the stub server Tests/biblean/stub_server.py (loopback, random port, checks the
# bearer token) and runs the viewer the way bib-lean does: BIBLEAN_SERVER /
# BIBLEAN_ATTACHMENT / BIBLEAN_PAGE in the environment, the token as one line on fd 3 (a pipe
# fed by the shell builtin printf, so the token is on no command line). Checks, through the
# headless `--probe` mode: the file is fetched with the right token and no Origin header,
# the title comes from the parent item, BIBLEAN_PAGE (and `--page`) select the page, a page
# past the end is ignored, chunked JSON answers decode; and the refusals with the contract's
# exit codes: wrong token (1, the server saw a wrong token), non-loopback server (2, no
# request sent), missing or malformed fd 3 (3), bad attachment key (2), unknown attachment
# (1). The token never appears in the viewer's output. Then the window path under Xvfb
# (smoke mode, SAFEPDF_VIEWER_SMOKE): the window title shows the title, and the private
# temporary copy is removed when the window closes. Exit 0 on success.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
cd "$repo"

if [ "${1:-}" != "--no-build" ]; then
  lake build viewer
fi
viewer="$repo/.lake/build/bin/viewer"
[ -x "$viewer" ] || { echo "launch-test: $viewer not built" >&2; exit 1; }

umask 077
work="$(mktemp -d)"
stub_pid=""
cleanup() {
  if [ -n "$stub_pid" ]; then kill "$stub_pid" 2>/dev/null || true; wait "$stub_pid" 2>/dev/null || true; fi
  rm -rf "$work"
}
trap cleanup EXIT

pass=0 fail=0
ok() { echo "ok - $1"; pass=$((pass + 1)); }
bad() { echo "FAIL - $1${2:+: $2}"; fail=$((fail + 1)); }
check() { if [ "$1" = 0 ]; then ok "$2"; else bad "$2" "${3:-}"; fi; }

att=ATT23456 parent=PAR23456
title='On "Safe" PDFs: a/b $(x) é'
python3 -I "$repo/scripts/viewer-smoke-pdf.py" "$work/two.pdf"
token="$(python3 -I -c 'import secrets; print(secrets.token_hex(32))')"
wrong="$(python3 -I -c 'import secrets; print(secrets.token_hex(32))')"
printf '%s\n' "$token" >"$work/token"

# start_stub [--chunked]: (re)starts the stub, sets $server.
start_stub() {
  if [ -n "$stub_pid" ]; then kill "$stub_pid" 2>/dev/null || true; wait "$stub_pid" 2>/dev/null || true; fi
  rm -f "$work/port" "$work/log"
  python3 -I "$here/stub_server.py" --token-file "$work/token" --pdf "$work/two.pdf" \
    --att "$att" --parent "$parent" --title "$title" --port-file "$work/port" \
    --log "$work/log" "$@" &
  stub_pid=$!
  for _ in $(seq 100); do [ -s "$work/port" ] && break; sleep 0.05; done
  [ -s "$work/port" ] || { echo "launch-test: stub server did not start" >&2; exit 1; }
  server="http://127.0.0.1:$(cat "$work/port")"
}

# run NAME TOKEN-LINE [ENV…] -- [ARGS…]: runs the viewer with the token line on fd 3 (a pipe);
# stdout to $work/NAME.out, stderr to $work/NAME.err, exit code in $rc.
run() {
  local name="$1" tok="$2"; shift 2
  local envs=()
  while [ $# -gt 0 ] && [ "$1" != "--" ]; do envs+=("$1"); shift; done
  shift
  set +e
  env -u BIBLEAN_PAGE "${envs[@]}" "$viewer" --biblean "$@" \
    >"$work/$name.out" 2>"$work/$name.err" 3< <(printf '%s\n' "$tok")
  rc=$?
  set -e
}

start_stub

# 1. The normal launch, page 1 (zero-based) of 2.
run p1 "$token" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" BIBLEAN_PAGE=1 -- --probe
check "$rc" "L1 probe exits 0" "exit $rc: $(cat "$work/p1.err")"
grep -qxF "title: $title" "$work/p1.out"; check $? "L2 the title is the parent's title" "$(cat "$work/p1.out")"
grep -qx 'pages: 2' "$work/p1.out" && grep -qx 'page: 1' "$work/p1.out"
check $? "L3 BIBLEAN_PAGE=1 selects page 1 of 2" "$(cat "$work/p1.out")"
size="$(wc -c <"$work/two.pdf" | tr -d ' ')"
grep -qx "bytes: $size" "$work/p1.out"; check $? "L4 the whole file arrived ($size bytes)"
python3 -I - "$work/log" "$att" "$parent" <<'EOF'
import json, sys
log = [json.loads(l) for l in open(sys.argv[1])]
att, parent = sys.argv[2], sys.argv[3]
want = [("GET", f"/api/attachments/{att}/file"), ("GET", f"/api/items/{att}"),
        ("GET", f"/api/items/{parent}"), ("POST", f"/api/attachments/{att}/fulltext")]
got = [(r["method"], r["path"]) for r in log]
assert got == want, got
assert all(r["auth"] == "ok" and r["status"] == 200 and not r["origin"] for r in log), log
EOF
check $? "L5 the server saw file + item + parent requests (+ the full text, task 10.3), all with the right token, no Origin" \
  "$(cat "$work/log")"
! grep -qF "$token" "$work/p1.out" "$work/p1.err"
check $? "L6 the token is not in the viewer's output"

# 2. Page selection details.
run p7 "$token" BIBLEAN_SERVER="$server/" BIBLEAN_ATTACHMENT="$att" BIBLEAN_PAGE=7 -- --probe
[ "$rc" = 0 ] && grep -qx 'requested: 7' "$work/p7.out" && grep -qx 'page: none' "$work/p7.out"
check $? "L7 a page past the end is ignored (and a trailing / on the server is accepted)" "exit $rc: $(cat "$work/p7.out" "$work/p7.err")"
run pa "$token" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" -- --probe --page 1
[ "$rc" = 0 ] && grep -qx 'page: 1' "$work/pa.out"
check $? "L8 --page 1 without BIBLEAN_PAGE selects page 1" "exit $rc: $(cat "$work/pa.out")"
run pe "$token" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" BIBLEAN_PAGE=0 -- --probe --page=1
[ "$rc" = 0 ] && grep -qx 'page: 0' "$work/pe.out"
check $? "L9 BIBLEAN_PAGE wins over --page" "exit $rc: $(cat "$work/pe.out")"
run pn "$token" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" BIBLEAN_PAGE=-1 -- --probe
[ "$rc" = 0 ] && grep -qx 'requested: none' "$work/pn.out"
check $? "L10 a malformed BIBLEAN_PAGE is ignored" "exit $rc: $(cat "$work/pn.out")"

# 3. Refusals.
: >"$work/log"
run w "$wrong" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" -- --probe
[ "$rc" = 1 ] && grep -q '401' "$work/w.err" && grep -q '"auth": "wrong"' "$work/log"
check $? "L11 a wrong token is refused by the server (401) and the viewer exits 1" "exit $rc: $(cat "$work/w.err")"
! grep -qF "$wrong" "$work/w.out" "$work/w.err"
check $? "L12 the wrong token is not echoed either"

: >"$work/log"
port="${server##*:}"
for host in "http://10.0.0.1:$port" "http://example.com:$port" "https://127.0.0.1:$port" \
    "http://127.0.0.1.example:$port" "http://[::1]:$port" "http://127.0.0.1:$port/api"; do
  run nl "$token" BIBLEAN_SERVER="$host" BIBLEAN_ATTACHMENT="$att" -- --probe
  [ "$rc" = 2 ]; check $? "L13 non-loopback or malformed server $host is a usage error (2)" "exit $rc: $(cat "$work/nl.err")"
done
[ ! -s "$work/log" ]; check $? "L14 no request reached the server for a refused origin"
run ns "$token" BIBLEAN_ATTACHMENT="$att" -- --probe
[ "$rc" = 2 ]; check $? "L15 no BIBLEAN_SERVER is a usage error (2)" "exit $rc"

set +e
env -u BIBLEAN_PAGE BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" "$viewer" --biblean --probe \
  >"$work/n3.out" 2>"$work/n3.err" 3<&-
rc=$?
set -e
[ "$rc" = 3 ] && grep -q 'file descriptor 3' "$work/n3.err"
check $? "L16 no fd 3 exits 3" "exit $rc: $(cat "$work/n3.err")"
run up "$(printf '%s' "$token" | tr a-f A-F)" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" -- --probe
[ "$rc" = 3 ]; check $? "L17 a malformed token (uppercase hex) exits 3" "exit $rc"
run sh "${token:0:63}" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" -- --probe
[ "$rc" = 3 ]; check $? "L18 a short token exits 3" "exit $rc"
run ek "" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" -- --probe
[ "$rc" = 3 ]; check $? "L19 an empty fd 3 exits 3" "exit $rc"

run bk "$token" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="../../x1" -- --probe
[ "$rc" = 2 ]; check $? "L20 a malformed attachment key is a usage error (2)" "exit $rc"
run uk "$token" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="ZZZZ2345" -- --probe
[ "$rc" = 1 ] && grep -q '404' "$work/uk.err"
check $? "L21 an unknown attachment (404) exits 1" "exit $rc: $(cat "$work/uk.err")"
run ua "$token" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" -- --probe --bogus
[ "$rc" = 2 ]; check $? "L22 an unknown argument is a usage error (2)" "exit $rc"
! grep -rqF "$title" "$work"/*.err
check $? "L23 no failure message quotes the title (nothing from the library on stderr)"

# 4. Chunked JSON answers.
start_stub --chunked
run ch "$token" BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" BIBLEAN_PAGE=1 -- --probe
[ "$rc" = 0 ] && grep -qxF "title: $title" "$work/ch.out"
check $? "L24 chunked item answers decode (title found)" "exit $rc: $(cat "$work/ch.out" "$work/ch.err")"

# 5. The window (Xvfb), smoke mode: the title is shown, the temporary copy is removed.
wrap=()
display=1
if [ -n "${DISPLAY:-}" ] && { command -v xdpyinfo >/dev/null 2>&1 && xdpyinfo >/dev/null 2>&1 \
    || [ -S "/tmp/.X11-unix/X${DISPLAY#*:}" ]; }; then
  :
elif command -v xvfb-run >/dev/null 2>&1; then
  wrap=(xvfb-run -a -s "-screen 0 1280x1024x24")
else
  display=0
  echo "skip - L25-L27 window checks (no X display and no xvfb-run)"
fi
if [ "$display" = 1 ]; then
  mkdir -p "$work/smoke" "$work/tmp"
  set +e
  env -u BIBLEAN_PAGE TMPDIR="$work/tmp" SAFEPDF_VIEWER_SMOKE="$work/smoke" \
    BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" \
    timeout 60 "${wrap[@]}" "$viewer" --biblean >"$work/win.out" 2>"$work/win.err" \
    3< <(printf '%s\n' "$token")
  rc=$?
  set -e
  check "$rc" "L25 the window run exits 0" "exit $rc: $(cat "$work/win.err")"
  want="title: On \"Safe\" PDFs: ab \$(x) é.pdf - page 2/2 - safe-pdf"
  grep -qxF "$want" "$work/smoke/state.txt" 2>/dev/null
  check $? "L26 the window title shows the item's title" "$(cat "$work/smoke/state.txt" 2>/dev/null)"
  [ -z "$(ls -A "$work/tmp")" ]
  check $? "L27 the private temporary copy is removed after the window closes" "$(ls -lAR "$work/tmp")"
fi

echo "launch-test: $pass passed, $fail failed"
[ "$fail" = 0 ]
