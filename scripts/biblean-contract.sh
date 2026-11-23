#!/usr/bin/env bash
# bib-lean's reader-contract checks S1–S25 against `viewer --biblean --self-test` (task 10.4;
# Plan.md §6 Phase 10 "Conformance", M10; bib-lean docs/READER-CONTRACT.md §6).
#
#   scripts/biblean-contract.sh [--no-build] [--biblean BIN | --stub] [--pdf FILE]
#
# Run from anywhere; builds `viewer` first unless --no-build.
#
# bib-lean's own `tests/reader/contract.sh` cannot be pointed at another viewer: it launches
# its curl stub viewer (`tests/reader/stub-viewer.sh`) and asserts the stub's own payload
# (ids `stub-1`/`stub-2`, a strike-out, the DOI 10.1038/nature12373) through files the stub
# writes. This script is a faithful re-implementation of its S1–S25 with
# `exec viewer --biblean --self-test` in place of the stub (bib-lean's script is the model,
# same author; every check cites its S-number):
#
# * **bib-lean mode** (`--biblean BIN`, or `$BIBLEAN_BIN`): BIN is a built `biblean`
#   executable (never built or run from here; copy one out of a bib-lean checkout). In fresh
#   temporary libraries, exactly the contract script's sequence: `biblean init`, `add --pdf`,
#   `open --reader 'exec …'` (embedded server), `reader = exec …` in <LIB>/config, a live
#   `serve --api` session, `fsck`, the exit-code and config cases, `--page`. Checks that
#   assert the stub's payload are adapted to the self-test's (S2–S5, S8, S9, S11, S14, S15,
#   S21, S23, S24 — see each check); the others are unchanged. X1 adds: the file bib-lean
#   stored from the self-test's PUT holds the original as a prefix and both marks' /NM.
# * **stub mode** (`--stub`, the default without BIN): the same viewer-side checks against
#   our stub server (`Tests/biblean/stub_server.py`); the checks that test bib-lean itself
#   (S1, S6, S10, S13, S16–S20, S22, S25: its launcher, config, sessions, fsck) are printed
#   as `skip`. Needs no bib-lean checkout.
#
# Both modes add X2–X5: our viewer's own exit codes (no token on fd 3 → 3, a non-loopback
# server → 2, an unknown argument → 2, a wrong token → 1) and that the token never appears
# in its output.
#
# The PDF (--pdf FILE) must have text on page 1 and a DOI on page 1 or 2; the default is
# `Tests/biblean/text-pdf.py`'s (DOI 10.1234/safe-pdf.5678). bib-lean's fixture
# `tests/fixtures/reader-sample.pdf` works too.
# Prints `ok - …`/`FAIL - …`/`skip - …` and `contract: N passed, M failed, K skipped`;
# exit 0 iff nothing failed. Needs python3 (stub mode, fixture), no display.
set -u
umask 077

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/.." && pwd)"

build=1 bin="${BIBLEAN_BIN:-}" pdf="" mode=""
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) build=0 ;;
    --biblean) bin="${2:?--biblean needs a path}"; shift ;;
    --stub) mode=stub ;;
    --pdf) pdf="${2:?--pdf needs a path}"; shift ;;
    *) echo "usage: scripts/biblean-contract.sh [--no-build] [--biblean BIN | --stub] [--pdf FILE]" >&2; exit 2 ;;
  esac
  shift
done
[ -z "$mode" ] && { if [ -n "$bin" ]; then mode=biblean; else mode=stub; fi; }
if [ "$mode" = biblean ]; then
  case "$bin" in /*) ;; *) bin="$PWD/$bin" ;; esac
  [ -x "$bin" ] || { echo "biblean-contract: biblean binary not found: $bin" >&2; exit 1; }
fi
if [ "$build" = 1 ]; then (cd "$repo" && lake build viewer) || exit 1; fi
viewer="$repo/.lake/build/bin/viewer"
[ -x "$viewer" ] || { echo "biblean-contract: $viewer not built" >&2; exit 1; }

tmp="$(mktemp -d "${TMPDIR:-/tmp}/safepdf-contract.XXXXXX")"
srv=""
cleanup() { [ -n "$srv" ] && { kill "$srv" 2>/dev/null; wait "$srv" 2>/dev/null; }; rm -rf "$tmp"; }
trap cleanup EXIT
passed=0 failed=0 skipped=0
ok() { echo "ok - $1"; passed=$((passed + 1)); }
bad() { echo "FAIL - $1${2:+: $2}"; failed=$((failed + 1)); }
skip() { echo "skip - $1"; skipped=$((skipped + 1)); }
check() { if [ "$1" = 0 ]; then ok "$2"; else bad "$2" "${3:-}"; fi; }
flat() { tr '\n' ';' <"$1" 2>/dev/null | cut -c1-600; }

if [ -z "$pdf" ]; then
  pdf="$tmp/fixture.pdf"
  python3 -I "$repo/Tests/biblean/text-pdf.py" "$pdf" || { echo "biblean-contract: no fixture" >&2; exit 1; }
fi
case "$pdf" in /*) ;; *) pdf="$PWD/$pdf" ;; esac
[ -f "$pdf" ] || { echo "biblean-contract: no such PDF: $pdf" >&2; exit 1; }
sha="$(sha256sum "$pdf" | cut -d' ' -f1)"
# The fixture's first DOI, lower case (bib-lean normalises DOIs to lower case).
doi="$(python3 -I - "$viewer" "$pdf" <<'EOF' 2>/dev/null
import re, subprocess, sys
# pdftotext is optional; the default fixture's DOI is known.
try:
    t = subprocess.run(["pdftotext", sys.argv[2], "-"], capture_output=True, timeout=30).stdout.decode()
except Exception:
    t = ""
m = re.search(r"\b(10\.\d{4,9}/[^\s\"<>]+)", t, re.I)
print((m.group(1).rstrip(".,;:)]}>'\"") if m else "10.1234/safe-pdf.5678").lower())
EOF
)"
q='\"'
spec="exec '$viewer' --biblean --self-test"
selftest_ok() { grep -qx 'viewer self-test: ok' "$1"; }
# Whether FILE holds /NM safepdf-mark-1 and -2 (a literal or a hex string, as the writer emits).
has_nms() {
  python3 -I - "$1" <<'EOF'
import sys
b = open(sys.argv[1], "rb").read().upper()
for i in (1, 2):
    nm = b"SAFEPDF-MARK-%d" % i
    assert nm in b or b"<" + nm.lower().hex().upper().encode() + b">" in b, nm
EOF
}
# The answered keys of a self-test output, one per line.
keys_of() { sed -n 's/^annotations: HTTP 200, [0-9]* elements, keys //p' "$1" | tr ',' '\n'; }

# Viewer-side checks of one self-test output OUT (S3–S5 adapted; shared by both modes).
check_payload() {
  local out="$1" n="$2"
  grep -qx "sha256: $sha" "$out" && grep -qx "bytes: $(wc -c <"$pdf" | tr -d ' ')" "$out"
  check $? "S3$n GET …/file gave the attachment's exact bytes (the self-test's sha256 = the fixture's)" "$(flat "$out")"
  grep -qE '^annotations: HTTP 200, 2 elements, keys [0-9A-Z]{8},[0-9A-Z]{8}$' "$out"
  check $? "S4$n POST …/annotations answered two keys" "$(flat "$out")"
  grep -q '^detected: HTTP 202 ' "$out" && grep -i '^detected: ' "$out" | grep -qiF "$doi"
  check $? "S5$n POST …/detected is a pending proposal (202) with the DOI $doi" "$(flat "$out")"
}

# X2–X5: our own exit codes and token hygiene (no bib-lean needed).
own_exit_codes() {
  local server="$1" token="$2" att="$3"
  BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" "$viewer" --biblean --self-test \
    >"$tmp/x2.out" 2>&1 3</dev/null
  rc=$?; [ "$rc" = 3 ]; check $? "X2 no token on file descriptor 3: exit 3 (contract §5)" "exit $rc"
  BIBLEAN_SERVER="http://192.0.2.1:80" BIBLEAN_ATTACHMENT="$att" "$viewer" --biblean --self-test \
    >"$tmp/x3.out" 2>&1 3<"$token"
  rc=$?; [ "$rc" = 2 ]; check $? "X3 a non-loopback BIBLEAN_SERVER is a usage error (2)" "exit $rc"
  BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" "$viewer" --biblean --self-test --bogus \
    >"$tmp/x4.out" 2>&1 3<"$token"
  rc=$?
  BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" "$viewer" --biblean --self-test --probe \
    >"$tmp/x4b.out" 2>&1 3<"$token"
  rc2=$?
  [ "$rc" = 2 ] && [ "$rc2" = 2 ] && grep -q '^usage: viewer --biblean' "$tmp/x4.out" &&
    grep -q '^usage: viewer --biblean' "$tmp/x4b.out"
  check $? "X4 an unknown argument (and --self-test with --probe) is a usage error (2)" "exit $rc"
  printf '%064d\n' 0 >"$tmp/wrong"
  BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" "$viewer" --biblean --self-test \
    >"$tmp/x5.out" 2>&1 3<"$tmp/wrong"
  rc=$?; [ "$rc" = 1 ] && grep -q '^viewer self-test: FAILED' "$tmp/x5.out" && grep -q '401' "$tmp/x5.out"
  check $? "X5 a wrong token: the server answers 401, the self-test fails with exit 1" "exit $rc: $(flat "$tmp/x5.out")"
}

if [ "$mode" = biblean ]; then
  # ---- bib-lean mode: tests/reader/contract.sh's S1–S25 with our viewer ------------------
  mklib() { "$bin" init "$1" >/dev/null && "$bin" --dir "$1" add --pdf "$pdf" | head -n 1; }
  annots() {
    "$bin" --dir "$1" show "$2" | sed -n 's/^child	\([A-Z0-9]*\)	annotation.*/\1/p' | sort >"$3"
    "$bin" --dir "$1" show "$2" --json >"$3.json"
  }
  lib="$tmp/lib"
  att="$(mklib "$lib")"
  [ -n "$att" ] || { echo "biblean-contract: setup failed" >&2; exit 1; }

  "$bin" --dir "$lib" open "$att" --reader "$spec" --print >"$tmp/print" 2>&1
  grep -q '^viewer	exec$' "$tmp/print" && grep -q '^server	embedded$' "$tmp/print"
  check $? "S1 open --reader 'exec viewer --biblean --self-test' --print: viewer exec, embedded server" "$(flat "$tmp/print")"

  "$bin" --dir "$lib" open "$att" --reader "$spec" >"$tmp/s.log" 2>&1
  rc=$?; [ "$rc" = 0 ] && selftest_ok "$tmp/s.log"
  check $? "S2 the self-test (embedded server) exits 0 with verdict ok and open exits 0" "exit $rc: $(flat "$tmp/s.log")"
  check_payload "$tmp/s.log" ""
  [ ! -e "$lib/session" ]; check $? "S6 no session left after the viewer closed"

  annots "$lib" "$att" "$tmp/a1"
  [ "$(wc -l <"$tmp/a1" | tr -d ' ')" = 2 ]; check $? "S7 two annotation items under the attachment" "$(cat "$tmp/a1")"
  j="$tmp/a1.json"
  grep -qF "\"kind\":\"highlight\",\"pageIndex\":0,\"position\":\"{${q}extra${q}:null,${q}id${q}:${q}safepdf-mark-1${q},${q}kind${q}:${q}highlight${q},${q}rects${q}:[[" "$j" &&
    grep -qE '"sortIndex":"00000\|[0-9]{6}\|[0-9]{5}","text":"[^"]+"' "$j"
  check $? "S8 highlight stored: kind, text (the first word), sortIndex; id safepdf-mark-1 and rects kept in position (stub: stub-1)"
  grep -qF "\"color\":\"#ffff98\",\"comment\":\"safe-pdf self-test note\",\"kind\":\"note\",\"pageIndex\":0,\"position\":\"{${q}extra${q}:null,${q}id${q}:${q}safepdf-mark-2${q},${q}kind${q}:${q}note${q},${q}rects${q}:[[" "$j"
  check $? "S9 note stored with its comment and colour, id safepdf-mark-2 in position (stub: strike-out → underline)"
  # X1: the file bib-lean stored from the PUT.
  stored="$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["item"]["file"]["path"])' "$j" 2>/dev/null)"
  sf="$lib/storage/$att/$stored"
  [ -f "$sf" ] && [ "$(wc -c <"$sf")" -gt "$(wc -c <"$pdf")" ] && cmp -s -n "$(wc -c <"$pdf" | tr -d ' ')" "$pdf" "$sf" &&
    has_nms "$sf"
  check $? "X1 PUT …/file: the stored file is the original plus an update holding both marks' /NM" "$stored"

  printf '# viewer for this library\nreader = %s\n' "$spec" >"$lib/config"
  "$bin" --dir "$lib" open "$att" --print >"$tmp/print2" 2>&1
  grep -q '^viewer	exec$' "$tmp/print2"; check $? "S10 reader = exec … in <LIB>/config is used by default"
  "$bin" --dir "$lib" open "$att" >"$tmp/s2.log" 2>&1
  rc=$?; [ "$rc" = 0 ] && selftest_ok "$tmp/s2.log" && grep -q '^marks: 0 added' "$tmp/s2.log" &&
    grep -q '^put: skipped' "$tmp/s2.log"
  check $? "S11 the self-test from the config exits 0 (on the stored file: nothing added, no PUT)" "exit $rc: $(flat "$tmp/s2.log")"
  annots "$lib" "$att" "$tmp/a2"
  cmp -s "$tmp/a1" "$tmp/a2" && [ "$(wc -l <"$tmp/a2" | tr -d ' ')" = 2 ]
  check $? "S12 the same ids keep their item keys (the set replaced, not appended: A2)"

  mkdir -p "$tmp/noweb"
  "$bin" --dir "$lib" serve --api --dir "$tmp/noweb" --port 0 >"$tmp/serve.log" 2>&1 &
  srv=$!
  for _ in $(seq 1 100); do [ -s "$lib/session" ] && break; sleep 0.05; done
  "$bin" --dir "$lib" open "$att" --print >"$tmp/print3" 2>&1
  grep -q '^server	live$' "$tmp/print3"; check $? "S13 with a running server, open uses the live session"
  "$bin" --dir "$lib" open "$att" >"$tmp/s3.log" 2>&1
  rc=$?; [ "$rc" = 0 ] && selftest_ok "$tmp/s3.log"
  check $? "S14 the self-test through the live server exits 0" "exit $rc: $(flat "$tmp/s3.log")"
  grep -q '^detected: HTTP 202 ' "$tmp/s3.log" && grep '^detected: ' "$tmp/s3.log" | grep -qiF "$doi"
  check $? "S15 the live server took the detection as a proposal"
  # X2–X5 against the live server (its port and a token that is not the session's).
  port="$(sed -n 's/.*"port":\([0-9]*\).*/\1/p' "$lib/session")"
  printf '%064d\n' 1 >"$tmp/notoken"
  own_exit_codes "http://127.0.0.1:$port" "$tmp/notoken" "$att"
  # X7: the live session's token (the one the S14 run received) is not in its output.
  if grep -qF "$(sed -n 's/.*"token":"\([0-9a-f]*\)".*/\1/p' "$lib/session")" "$tmp/s3.log"; then
    bad "X7 the token never appears in the viewer's output"
  else ok "X7 the token never appears in the viewer's output"; fi
  kill "$srv"; wait "$srv" 2>/dev/null; srv=""

  "$bin" --dir "$lib" fsck >"$tmp/fsck" 2>&1
  grep -q '^problems	0$' "$tmp/fsck"; check $? "S16 fsck finds no problems after the three viewer runs"

  "$bin" --dir "$lib" open "$att" --reader 'exec false' >/dev/null 2>&1
  rc=$?; [ "$rc" = 1 ]; check $? "S17 a viewer exiting non-zero makes open exit 1" "exit $rc"
  "$bin" --dir "$lib" open "$att" --reader bogus --print >/dev/null 2>&1
  rc=$?; [ "$rc" = 2 ]; check $? "S18 --reader with an unknown viewer is a usage error (2)" "exit $rc"
  "$bin" --dir "$lib" open "$att" --reader "$spec" --self-test >/dev/null 2>&1
  rc=$?; [ "$rc" = 2 ]; check $? "S19 biblean's --self-test with an exec viewer is a usage error (2)" "exit $rc"
  printf 'reader = exec "unterminated\n' >"$lib/config"
  "$bin" --dir "$lib" open "$att" --print >/dev/null 2>"$tmp/cfg.err"
  rc=$?; [ "$rc" = 3 ] && grep -q 'config line 1' "$tmp/cfg.err"
  check $? "S20 a malformed config line is rejected by line number (exit 3)" "exit $rc: $(cat "$tmp/cfg.err")"
  rm -f "$lib/config"
  # S21 adapted: the stub accepts extra words; our viewer refuses unknown arguments (usage,
  # exit 2 → open exits 1). The words must still arrive verbatim: nothing ran in a shell.
  "$bin" --dir "$lib" open "$att" --reader "$spec '\$(touch $tmp/pwned)' \"; touch $tmp/pwned2\"" >"$tmp/s21.log" 2>&1
  rc=$?; [ "$rc" = 1 ] && grep -q '^usage: viewer --biblean' "$tmp/s21.log" && [ ! -e "$tmp/pwned" ] && [ ! -e "$tmp/pwned2" ]
  check $? "S21 viewer arguments reach the viewer verbatim (no shell expansion; refused as usage by our viewer)" "exit $rc"
  printf 'viewer = pdfjs\n' >"$lib/config"
  "$bin" --dir "$lib" open "$att" --print >/dev/null 2>"$tmp/cfg.err"
  rc=$?; [ "$rc" = 3 ] && grep -q "unknown setting 'viewer'" "$tmp/cfg.err"
  check $? "S22 an unknown config setting is rejected (exit 3)" "exit $rc: $(cat "$tmp/cfg.err")"

  rm -f "$lib/config"
  "$bin" --dir "$lib" open "$att" --page 4 --reader "$spec --page {page}" >"$tmp/s4.log" 2>&1
  rc=$?; [ "$rc" = 0 ] && grep -qx 'page-env: 4' "$tmp/s4.log" && grep -qx 'page-arg: 4' "$tmp/s4.log"
  check $? "S23 open --page 4: the viewer receives BIBLEAN_PAGE=4 and {page} = 4" "exit $rc: $(flat "$tmp/s4.log")"
  BIBLEAN_PAGE=9 "$bin" --dir "$lib" open "$att" --reader "$spec --page {page}" >"$tmp/s5.log" 2>&1
  rc=$?; [ "$rc" = 0 ] && grep -qx 'page-env: unset' "$tmp/s5.log" && grep -qx 'page-arg: 0' "$tmp/s5.log"
  check $? "S24 without --page: no BIBLEAN_PAGE (an inherited one is removed), {page} = 0" "exit $rc: $(flat "$tmp/s5.log")"
  "$bin" --dir "$lib" open "$att" --page -1 --reader "$spec" --print >/dev/null 2>&1
  rc=$?; [ "$rc" = 2 ]; check $? "S25 --page with a non-number is a usage error (2)" "exit $rc"
  cat "$tmp"/s*.log "$tmp"/x*.out >"$tmp/all.out" 2>/dev/null
else
  # ---- stub mode: the viewer-side checks against Tests/biblean/stub_server.py ------------
  att=ATT23456
  python3 -I -c 'import secrets; print(secrets.token_hex(32))' >"$tmp/token"
  start_stub() {  # PDF [STUB-ARGS…]
    local p="$1"; shift
    [ -n "$srv" ] && { kill "$srv" 2>/dev/null; wait "$srv" 2>/dev/null; }
    rm -f "$tmp/port" "$tmp/annots" "$tmp/put"
    python3 -I "$repo/Tests/biblean/stub_server.py" --token-file "$tmp/token" --pdf "$p" \
      --att "$att" --parent "" --title "Contract" --port-file "$tmp/port" --log "$tmp/log" \
      --annots-out "$tmp/annots" --put-out "$tmp/put" "$@" &
    srv=$!
    for _ in $(seq 100); do [ -s "$tmp/port" ] && break; sleep 0.05; done
    [ -s "$tmp/port" ] || { echo "biblean-contract: stub server did not start" >&2; exit 1; }
    server="http://127.0.0.1:$(cat "$tmp/port")"
  }
  # selftest NAME [ARGS…]: the self-test with the token on fd 3 (env as bib-lean sets it).
  selftest() {
    local name="$1"; shift
    env -u BIBLEAN_PAGE BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" ${PAGE:+BIBLEAN_PAGE=$PAGE} \
      timeout 120 "$viewer" --biblean --self-test "$@" >"$tmp/$name.log" 2>&1 3<"$tmp/token"
    rc=$?
  }
  for s in S1 S6 S10 S13 S16 S17 S18 S19 S20 S22 S25; do
    skip "$s (tests bib-lean's launcher, config, sessions or fsck: needs --biblean BIN)"
  done
  start_stub "$pdf"
  selftest s
  [ "$rc" = 0 ] && selftest_ok "$tmp/s.log"
  check $? "S2 the self-test exits 0 with verdict ok" "exit $rc: $(flat "$tmp/s.log")"
  check_payload "$tmp/s.log" ""
  python3 -I - "$tmp/annots" <<'EOF'
import json, sys
posts = [json.loads(l) for l in open(sys.argv[1])]
assert len(posts) == 1, len(posts)
body = posts[0]["body"]
assert len(body) == 2, body
EOF
  check $? "S7 two annotations stored under the attachment"
  python3 -I - "$tmp/annots" <<'EOF'
import json, sys
body = json.loads(open(sys.argv[1]).readline())["body"]
h = [e for e in body if e.get("id") == "safepdf-mark-1"][0]
assert h["kind"] == "highlight" and h["pageIndex"] == 0 and h["text"], h
assert len(h["rects"]) >= 1 and all(len(r) == 4 for r in h["rects"]), h
assert h["sortIndex"].startswith("00000|") and h["color"] == "#ffff98", h
EOF
  check $? "S8 highlight posted: kind, text (the first word), sortIndex, id safepdf-mark-1, rects"
  python3 -I - "$tmp/annots" <<'EOF'
import json, sys
body = json.loads(open(sys.argv[1]).readline())["body"]
n = [e for e in body if e.get("id") == "safepdf-mark-2"][0]
assert n["kind"] == "note" and n["comment"] == "safe-pdf self-test note", n
assert n["color"] == "#ffff98" and len(n["rects"]) == 1, n
EOF
  check $? "S9 note posted with its comment and colour, id safepdf-mark-2"
  size="$(wc -c <"$pdf" | tr -d ' ')"
  [ -f "$tmp/put" ] && [ "$(wc -c <"$tmp/put")" -gt "$size" ] && cmp -s -n "$size" "$pdf" "$tmp/put" &&
    has_nms "$tmp/put"
  check $? "X1 PUT …/file: the original plus an update holding both marks' /NM"
  # S11/S12: as bib-lean after the first run — the PUT file served, the posted set stored.
  cp "$tmp/put" "$tmp/put1.pdf"
  python3 -I -c 'import json,sys; json.dump(json.loads(open(sys.argv[1]).readline())["body"], open(sys.argv[2], "w"))' \
    "$tmp/annots" "$tmp/stored1.json"
  keys_of "$tmp/s.log" >"$tmp/k1"
  start_stub "$tmp/put1.pdf" --annots-in "$tmp/stored1.json"
  selftest s2
  [ "$rc" = 0 ] && selftest_ok "$tmp/s2.log" && grep -q '^marks: 0 added' "$tmp/s2.log" &&
    grep -q '^put: skipped' "$tmp/s2.log" && [ ! -e "$tmp/put" ]
  check $? "S11 a second run on the stored file exits 0 (nothing added, no PUT)" "exit $rc: $(flat "$tmp/s2.log")"
  keys_of "$tmp/s2.log" >"$tmp/k2"
  python3 -I - "$tmp/annots" <<'EOF'
import json, sys
p = json.loads(open(sys.argv[1]).readline())
assert len(p["body"]) == 2 and sorted(p["keys"]) == sorted(p["before"].values()), p
EOF
  check $? "S12 the same ids keep their item keys (the set replaced, not appended: A2)" "$(flat "$tmp/k2")"
  skip "S14 S15 (the live bib-lean server: needs --biblean BIN)"
  skip "S21 (bib-lean's exec argv splitting: needs --biblean BIN)"
  start_stub "$pdf"
  PAGE=4 selftest s4 --page 4
  [ "$rc" = 0 ] && grep -qx 'page-env: 4' "$tmp/s4.log" && grep -qx 'page-arg: 4' "$tmp/s4.log"
  check $? "S23 BIBLEAN_PAGE=4 and {page} = 4 reach the viewer" "exit $rc: $(flat "$tmp/s4.log")"
  selftest s5 --page 0
  [ "$rc" = 0 ] && grep -qx 'page-env: unset' "$tmp/s5.log" && grep -qx 'page-arg: 0' "$tmp/s5.log"
  check $? "S24 without a page: no BIBLEAN_PAGE, {page} = 0" "exit $rc: $(flat "$tmp/s5.log")"
  own_exit_codes "$server" "$tmp/token" "$att"
  python3 -I - "$tmp/log" <<'EOF'
import json, sys
reqs = [json.loads(l) for l in open(sys.argv[1])]
assert reqs and all(r["auth"] == "ok" or r["status"] == 401 for r in reqs), reqs
assert not any(r["origin"] for r in reqs), "an Origin header was sent"
EOF
  check $? "X6 every request carried the token as Authorization: Bearer, none sent Origin (contract §2–§3)"
  cat "$tmp"/s*.log "$tmp"/x*.out >"$tmp/all.out" 2>/dev/null
  if grep -qF "$(cat "$tmp/token")" "$tmp/all.out"; then bad "X7 the token never appears in the viewer's output"
  else ok "X7 the token never appears in the viewer's output"; fi
fi

echo "contract: $passed passed, $failed failed, $skipped skipped ($mode mode)"
[ "$failed" = 0 ]
