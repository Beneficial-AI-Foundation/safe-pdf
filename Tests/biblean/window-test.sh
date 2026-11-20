#!/usr/bin/env bash
# The window of `viewer --biblean` (task 10.1b; Plan.md §6 Phase 10; bib-lean
# docs/READER-CONTRACT.md §2–§4). Run from the repo root:
#   Tests/biblean/window-test.sh [--no-build]
#
# Runs the viewer as bib-lean does (environment + token on fd 3) against the stub server
# (Tests/biblean/stub_server.py, seeded with a stored set: one of our highlights with a
# comment, a pdf.js strike-out, an element without id) on the fixture
# Tests/biblean/annots-pdf.py, in the smoke mode `biblean` (SAFEPDF_VIEWER_SMOKE_MODE=biblean,
# `Viewer.smokeBiblean`) under its own Xvfb — started directly, not through xvfb-run, which
# reuses fd 3 (the token pipe). Checks:
#   W1  the window run exits 0;
#   W2  the window title is the library's title (no file name), `* ` for the stored marks;
#   W3  BIBLEAN_PAGE=1 shows page 2 of 2;
#   W4  the document is opened from memory: TMPDIR stays empty while the window is up and
#       after, nothing is written into the working directory;
#   W5  file descriptor 3 (the token pipe) is closed while the window is up;
#   W6  the stored set is loaded into the window (2 marks, unsaved); Save says "Save to library";
#   W7  a highlight made in the window reaches the stub as a POST before any PUT (no save);
#   W8  Save in the window: a PUT (the original bytes a prefix, the marks' /NM inside) then a
#       POST with the new note and the stored elements of other viewers; after it the marks
#       are saved, the title has no `*`, the window stays on the library's document;
#   W9  the token appears nowhere in the output.
# Exit 0 on success; the window checks are skipped (exit 0) without Xvfb.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
cd "$repo"

if [ "${1:-}" != "--no-build" ]; then
  lake build viewer
fi
viewer="$repo/.lake/build/bin/viewer"
[ -x "$viewer" ] || { echo "window-test: $viewer not built" >&2; exit 1; }

umask 077
work="$(mktemp -d)"
stub_pid="" xvfb_pid="" vpid=""
cleanup() {
  if [ -n "$vpid" ]; then kill "$vpid" 2>/dev/null || true; fi
  if [ -n "$stub_pid" ]; then kill "$stub_pid" 2>/dev/null || true; wait "$stub_pid" 2>/dev/null || true; fi
  if [ -n "$xvfb_pid" ]; then kill "$xvfb_pid" 2>/dev/null || true; wait "$xvfb_pid" 2>/dev/null || true; fi
  rm -rf "$work"
}
trap cleanup EXIT

pass=0 fail=0
ok() { echo "ok - $1"; pass=$((pass + 1)); }
bad() { echo "FAIL - $1${2:+: $2}"; fail=$((fail + 1)); }
check() { if [ "$1" = 0 ]; then ok "$2"; else bad "$2" "${3:-}"; fi; }

if ! command -v Xvfb >/dev/null 2>&1; then
  echo "skip - W1-W9 (no Xvfb)"
  exit 0
fi
xvfb_dpy=""
for n in $(seq 201 240); do
  [ -e "/tmp/.X11-unix/X$n" ] || [ -e "/tmp/.X$n-lock" ] && continue
  Xvfb ":$n" -screen 0 1280x1024x24 -nolisten tcp >/dev/null 2>&1 &
  xvfb_pid=$!
  for _ in $(seq 1 50); do [ -S "/tmp/.X11-unix/X$n" ] && break; sleep 0.1; done
  if [ -S "/tmp/.X11-unix/X$n" ]; then xvfb_dpy=":$n"; break; fi
  kill "$xvfb_pid" 2>/dev/null; wait "$xvfb_pid" 2>/dev/null; xvfb_pid=""
done
if [ -z "$xvfb_dpy" ]; then
  echo "skip - W1-W9 (Xvfb did not start)"
  exit 0
fi
export DISPLAY="$xvfb_dpy"

att=ATT23456
title='On "Safe" PDFs: a/b $(x) é'
python3 -I "$here/annots-pdf.py" "$work/a.pdf"
token="$(python3 -I -c 'import secrets; print(secrets.token_hex(32))')"
printf '%s\n' "$token" >"$work/token"
cat >"$work/stored.json" <<'EOF'
[{"id": "safepdf-mark-1", "kind": "highlight", "pageIndex": 0,
  "rects": [[100, 697.6, 128.0, 709.6]], "text": "Hello", "comment": "a comment",
  "color": "#ffff98", "sortIndex": "00000|000000|00082", "extra": null},
 {"id": "12R", "kind": "strikeout", "pageIndex": 1, "rects": [[1.50, 2, 3, 4e0]],
  "text": "Second", "comment": null, "color": "#ff0000", "sortIndex": "00001|000000|00290",
  "extra": {"subtype": "StrikeOut", "rect": [1, 2, 3, 4]}},
 {"kind": "note", "pageIndex": 0, "rects": [], "text": null, "comment": "no id",
  "color": "#ffd400", "sortIndex": "00000|000000|00000"}]
EOF

python3 -I "$here/stub_server.py" --token-file "$work/token" --pdf "$work/a.pdf" \
  --att "$att" --parent PAR23456 --title "$title" --port-file "$work/port" \
  --log "$work/log" --annots-in "$work/stored.json" --annots-out "$work/annots" \
  --put-out "$work/put" &
stub_pid=$!
for _ in $(seq 100); do [ -s "$work/port" ] && break; sleep 0.05; done
[ -s "$work/port" ] || { echo "window-test: stub server did not start" >&2; exit 1; }
server="http://127.0.0.1:$(cat "$work/port")"

mkdir -p "$work/smoke" "$work/tmp" "$work/cwd"
set +e
(cd "$work/cwd" && exec env TMPDIR="$work/tmp" SAFEPDF_VIEWER_SMOKE="$work/smoke" \
  SAFEPDF_VIEWER_SMOKE_MODE=biblean SAFEPDF_SUBST_FONTS=0 \
  BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" BIBLEAN_PAGE=1 \
  "$viewer" --biblean >"$work/win.out" 2>"$work/win.err" 3< <(printf '%s\n' "$token")) &
vpid=$!
# While the window is up (the smoke steps wait 1.5 s after writing `up`).
for _ in $(seq 600); do [ -e "$work/smoke/up" ] && break; kill -0 "$vpid" 2>/dev/null || break; sleep 0.05; done
fd3="$(readlink "/proc/$vpid/fd/3" 2>/dev/null || echo absent)"
tmp_during="$(ls -A "$work/tmp")"
up=0; [ -e "$work/smoke/up" ] || up=1
# Wait for the end (at most 60 s).
for _ in $(seq 1200); do kill -0 "$vpid" 2>/dev/null || break; sleep 0.05; done
if kill -0 "$vpid" 2>/dev/null; then kill "$vpid"; fi
wait "$vpid"
rc=$?
vpid=""
# The checks below run without -e: a failed check is counted, not fatal.
out="$work/smoke/biblean.txt"
[ "$rc" = 0 ] && [ "$up" = 0 ] && grep -qx done "$out"
check $? "W1 the window run exits 0 after the scripted steps" \
  "exit $rc: $(cat "$work/win.err" "$out" 2>/dev/null | tail -20)"
grep -qxF "title: * $title - page 2/2 - safe-pdf" "$out"
check $? "W2 the window title is the library's title (unsaved stored marks: * )" "$(cat "$out" 2>/dev/null)"
grep -qx 'page: 2/2' "$out"
check $? "W3 BIBLEAN_PAGE=1 shows page 2 of 2" "$(cat "$out" 2>/dev/null)"
grep -qx 'in-memory: true library: true' "$out" && [ -z "$tmp_during" ] &&
  [ -z "$(ls -A "$work/tmp")" ] && [ -z "$(ls -A "$work/cwd")" ]
check $? "W4 opened from memory: no temporary file, nothing written to the working directory" \
  "tmp during: $tmp_during; after: $(ls -A "$work/tmp" "$work/cwd")"
case "$fd3" in pipe:*) false ;; *) true ;; esac
check $? "W5 file descriptor 3 (the token pipe) is closed while the window is up ($fd3)"
grep -qx 'marks0: 2 saved 0 dirty true' "$out" &&
  grep -qxF 'save-label: Save to library | Save to library (Ctrl+S)' "$out"
check $? "W6 the stored set is in the window (2 unsaved marks); Save reads \"Save to library\"" \
  "$(cat "$out" 2>/dev/null)"
python3 -I - "$work/log" "$work/annots" <<'EOF'
import json, sys
log = [json.loads(l) for l in open(sys.argv[1])]
writes = [(r["method"], r["path"].rsplit("/", 1)[1], r["status"]) for r in log
          if r["method"] == "PUT" or r["path"].endswith("/annotations")]
assert writes == [("POST", "annotations", 200), ("PUT", "file", 200),
                  ("POST", "annotations", 200)], writes
first = json.loads(open(sys.argv[2]).readline())["body"]
hls = [e for e in first if e.get("kind") == "highlight" and e.get("text") == "Second"]
assert len(hls) == 1 and hls[0]["pageIndex"] == 1, first
assert not any(e.get("comment") == "library note" for e in first), first
EOF
check $? "W7 the highlight made in the window reaches the stub as a POST, before any PUT" \
  "$(cat "$work/log" "$work/annots" 2>/dev/null | tail -20)"
python3 -I - "$work/annots" "$work/put" "$work/a.pdf" <<'EOF'
import json, re, sys
posts = [json.loads(l) for l in open(sys.argv[1])]
body = posts[-1]["body"]
ids = [e.get("id") for e in body]
assert "12R" in ids and None in ids, ids
notes = [e for e in body if e.get("kind") == "note" and e.get("comment") == "library note"]
assert len(notes) == 1, body
mine = {i for i in ids if (i or "").startswith("safepdf-mark-")}
put, orig = open(sys.argv[2], "rb").read(), open(sys.argv[3], "rb").read()
assert put.startswith(orig) and len(put) > len(orig), "prefix"
names = {m.decode() for m in re.findall(rb"/NM\s*\((safepdf-mark-\d+)\)", put)}
for h in re.findall(rb"/NM\s*<([0-9A-Fa-f\s]*)>", put):
    v = bytes.fromhex(re.sub(rb"\s", b"", h).decode())
    if v.startswith(b"safepdf-mark-") and b"-popup-" not in v:
        names.add(v.decode())
assert mine and mine <= names, (mine, names)
EOF
r=$?
grep -qxF "after-save: 4 saved 4 dirty false title $title - page 2/2 - safe-pdf" "$out" &&
  grep -q '^after-save-path: .* in-memory true library true page 2$' "$out"
check $((r + $?)) "W8 Save: PUT (original a prefix, the marks inside) then POST (the note, other viewers' elements); marks saved, window stays on the library's document" \
  "$(cat "$out" "$work/log" 2>/dev/null | tail -20)"
! grep -rqF "$token" "$work/win.out" "$work/win.err" "$work/smoke"
check $? "W9 the token is not in the viewer's output"

echo "window-test: $pass passed, $fail failed"
[ "$fail" = 0 ]
