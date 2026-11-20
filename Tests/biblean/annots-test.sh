#!/usr/bin/env bash
# Annotations both ways between `viewer --biblean` and bib-lean (task 10.2; Plan.md §6 Phase 10
# "Annotations both ways"; bib-lean docs/READER-CONTRACT.md §3–§4). Run from the repo root:
#   Tests/biblean/annots-test.sh [--no-build]
#
# Uses the stub server (Tests/biblean/stub_server.py, seeded with a stored set: one of our
# highlights with a comment, a pdf.js strike-out with an object-reference id, an element
# without id) and the fixture Tests/biblean/annots-pdf.py (`Hello safe world` at (100, 700)).
# Through `--probe`:
#   A1  loading is read-only and converts the set (2 marks, 2 elements kept as they are);
#   A2  `--annots echo` posts the loaded set back unchanged modulo ordering (numbers compared
#       as numbers), keeping every id'ed element's item key;
#   A3  `--annots demo` (six changes 30 ms apart, then a Save): one PUT then one POST — the
#       debounce folds the changes; the POST has the new highlight (text `Hello`, last colour,
#       user-space rectangle, sort key), the note, the stored elements; ids unique;
#   A4  the PUT body is a PDF whose original bytes are a prefix, that `qpdf --check` accepts
#       (when installed) and that holds the marks' /NM;
#   A5  the same on a page with /Rotate 90 and CropBox [50 60 500 760]: identical rectangles
#       (user space), the sort key's distance measured from the CropBox top, the note icon
#       inside the CropBox;
#   A6–A8 failures (HTTP 500, dropped connection, a server that never answers) never fail the
#       probe, are reported on stderr without the token, and a hang costs at most the grace;
#   A9  token never printed, every request authenticated, no Origin, right content types.
# In a window (Xvfb; smoke mode `save` of scripts/viewer-smoke.sh):
#   A10 the marks saved in the window reach bib-lean on exit: the PUT holds the original as a
#       prefix and three marks, the POST lists them with the stored elements;
#   A11 a server that never answers does not hold the window's exit.
# Exit 0 on success.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
cd "$repo"

if [ "${1:-}" = "--no-build" ]; then
  shift
else
  lake build viewer
fi
viewer="$repo/.lake/build/bin/viewer"
[ -x "$viewer" ] || { echo "annots-test: $viewer not built" >&2; exit 1; }

umask 077
work="$(mktemp -d)"
stub_pid=""
xvfb_pid=""
stop_stub() {
  if [ -n "$stub_pid" ]; then kill "$stub_pid" 2>/dev/null || true; wait "$stub_pid" 2>/dev/null || true; fi
  stub_pid=""
}
cleanup() {
  stop_stub
  if [ -n "$xvfb_pid" ]; then kill "$xvfb_pid" 2>/dev/null || true; wait "$xvfb_pid" 2>/dev/null || true; fi
  rm -rf "$work"
}
trap cleanup EXIT

pass=0 fail=0
ok() { echo "ok - $1"; pass=$((pass + 1)); }
bad() { echo "FAIL - $1${2:+: $2}"; fail=$((fail + 1)); }
check() { if [ "$1" = 0 ]; then ok "$2"; else bad "$2" "${3:-}"; fi; }

att=ATT23456
python3 -I "$here/annots-pdf.py" "$work/a.pdf"
python3 -I "$here/annots-pdf.py" "$work/r.pdf" --rotate 90 --crop 50 60 500 760
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

# start_stub PDF [STUB-ARGS…]: (re)starts the stub with the stored set ($stored, default
# stored.json), sets $server.
start_stub() {
  local pdf="$1"; shift
  stop_stub
  rm -f "$work/port" "$work/log" "$work/annots" "$work/put" "$work"/put.*
  python3 -I "$here/stub_server.py" --token-file "$work/token" --pdf "$pdf" \
    --att "$att" --parent PAR23456 --title "Parent title" --port-file "$work/port" \
    --log "$work/log" --annots-in "${stored:-$work/stored.json}" --annots-out "$work/annots" \
    --put-out "$work/put" "$@" &
  stub_pid=$!
  for _ in $(seq 100); do [ -s "$work/port" ] && break; sleep 0.05; done
  [ -s "$work/port" ] || { echo "annots-test: stub server did not start" >&2; exit 1; }
  server="http://127.0.0.1:$(cat "$work/port")"
  touch "$work/log"
}

# probe NAME [ARGS…]: `viewer --biblean --probe ARGS…`, token on fd 3; exit code in $rc,
# wall time in $elapsed.
probe() {
  local name="$1"; shift
  local start; start=$(date +%s)
  env -u BIBLEAN_PAGE BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" \
    timeout 90 "$viewer" --biblean --probe "$@" \
    >"$work/$name.out" 2>"$work/$name.err" 3< <(printf '%s\n' "$token")
  rc=$?
  elapsed=$(( $(date +%s) - start ))
}

set +e

# A1. Loading.
start_stub "$work/a.pdf"
probe a1
[ "$rc" = 0 ] &&
  grep -qxF 'annotations: 3 stored, 2 marks (0 from the file), 2 kept as they are' "$work/a1.out" &&
  ! grep -q '"/api/attachments/'"$att"'/annotations"\|"PUT"' "$work/log"
check $? "A1 the stored set loads into 2 marks (highlight + comment), 2 elements pass through; nothing is posted" \
  "exit $rc: $(cat "$work/a1.out" "$work/a1.err")"

# A2. Echo: the same set comes back.
start_stub "$work/a.pdf"
probe a2 --annots echo
[ "$rc" = 0 ] && grep -qxF 'sync-done: true' "$work/a2.out" &&
  grep -qx "sync: POST /api/attachments/$att/annotations: HTTP 200" "$work/a2.out" &&
python3 -I - "$work/annots" "$work/stored.json" <<'EOF'
import json, sys
posts = [json.loads(l) for l in open(sys.argv[1])]
assert len(posts) == 1, len(posts)
body, keys, before = posts[0]["body"], posts[0]["keys"], posts[0]["before"]
stored = json.load(open(sys.argv[2]))
def canon(e):
    e = dict(e)
    for k in ("id", "text", "comment", "extra"):
        e.setdefault(k, None)
    e["rects"] = [[round(float(x), 3) for x in r] for r in e["rects"]]
    return json.dumps(e, sort_keys=True)
assert sorted(map(canon, body)) == sorted(map(canon, stored)), (body, stored)
for e, k in zip(body, keys):
    if e.get("id") is not None:
        assert before[e["id"]] == k, (e["id"], k, before)
EOF
check $? "A2 --annots echo posts the stored set back unchanged (modulo order), item keys kept" \
  "exit $rc: $(cat "$work/a2.out" "$work/a2.err" "$work/annots" 2>/dev/null)"

# A3/A4. The scripted session: debounced POST, PUT of the annotated file.
# demo_checks OUT PDF: the checks shared by the plain and the rotated/cropped page.
demo_checks() {
  python3 -I - "$work/log" "$work/annots" "$work/put" "$2" "$att" "$1" <<'EOF'
import json, sys
import re
def nm_names(b):
    """The /NM strings of `b` that name our marks (literal or hex strings)."""
    out = {m.decode() for m in re.findall(rb"/NM\s*\((safepdf-mark-\d+)\)", b)}
    for h in re.findall(rb"/NM\s*<([0-9A-Fa-f\s]*)>", b):
        v = bytes.fromhex(re.sub(rb"\s", b"", h).decode())
        # A highlight's comment popup (9.5g, pdf.js form) is named
        # safepdf-mark-ID-popup-CID; it belongs to the highlight and is not a mark.
        if v.startswith(b"safepdf-mark-") and b"-popup-" not in v:
            out.add(v.decode())
    return out
log = [json.loads(l) for l in open(sys.argv[1])]
att = sys.argv[5]
writes = [(r["method"], r["path"].rsplit("/", 1)[1], r["status"]) for r in log
          if r["method"] == "PUT" or r["path"].endswith("/annotations")]
assert writes == [("PUT", "file", 200), ("POST", "annotations", 200)], writes
posts = [json.loads(l) for l in open(sys.argv[2])]
body = posts[0]["body"]
ids = [e.get("id") for e in body if e.get("id") is not None]
assert len(ids) == len(set(ids)), ids
mine = {e["id"]: e for e in body if (e.get("id") or "").startswith("safepdf-mark-")}
assert set(mine) == {"safepdf-mark-1", "safepdf-mark-3", "safepdf-mark-4"}, sorted(mine)
hl = mine["safepdf-mark-3"]
assert hl["kind"] == "highlight" and hl["text"] == "Hello" and hl["color"] == "#ffcbe6", hl
assert hl["comment"] is None and hl["pageIndex"] == 0 and len(hl["rects"]) == 1, hl
x0, y0, x1, y1 = hl["rects"][0]
assert x0 == 100 and abs(y0 - 697.6) < 0.01 and abs(y1 - 709.6) < 0.01 and 127 < x1 < 128, hl
note = mine["safepdf-mark-4"]
assert note["kind"] == "note" and note["comment"] == "demo note" and note["text"] is None, note
assert mine["safepdf-mark-1"]["comment"] == "a comment", mine["safepdf-mark-1"]
assert {e.get("id") for e in body} >= {"12R", None}, body
put = open(sys.argv[3], "rb").read()
orig = open(sys.argv[4], "rb").read()
assert put.startswith(orig) and len(put) > len(orig), (len(put), len(orig))
assert put.rstrip().endswith(b"%%EOF"), put[-40:]
# Mark 2 is the highlight's comment: since 9.5g it is written as highlight 1's
# /Contents + /Popup (pdf.js form), whose popup is named safepdf-mark-1-popup-2.
assert nm_names(put) == {"safepdf-mark-%d" % n for n in (1, 3, 4)}, nm_names(put)
assert b"safepdf-mark-1-popup-2" in put or bytes("safepdf-mark-1-popup-2", "ascii").hex().upper().encode() in put.upper(), "popup of mark 1"
json.dump({"hl": hl, "note": note}, open(sys.argv[6], "w"))
EOF
}
qpdf_ok() {
  if command -v qpdf >/dev/null 2>&1; then qpdf --check "$1" >/dev/null 2>&1; else return 0; fi
}

start_stub "$work/a.pdf"
probe a3 --annots demo
[ "$rc" = 0 ] && grep -qxF 'sync-done: true' "$work/a3.out" &&
  grep -q '^demo: highlight 3 on 5 characters, a note, saved [0-9]* bytes$' "$work/a3.out"
check $? "A3a --annots demo runs the scripted session" "exit $rc: $(cat "$work/a3.out" "$work/a3.err")"
demo_checks "$work/a3.json" "$work/a.pdf"
check $? "A3b six changes and a save give one PUT then one POST; the posted set is right" \
  "$(cat "$work/log" "$work/annots" 2>/dev/null)"
qpdf_ok "$work/put"
check $? "A4 the PUT body passes qpdf --check (original bytes a prefix, the marks' /NM inside: A3b)"

# A5. /Rotate 90 and a CropBox offset: the same user-space rectangles.
start_stub "$work/r.pdf"
probe a5 --annots demo
demo_checks "$work/a5.json" "$work/r.pdf" &&
python3 -I - "$work/a3.json" "$work/a5.json" <<'EOF'
import json, sys
a, r = json.load(open(sys.argv[1])), json.load(open(sys.argv[2]))
assert a["hl"]["rects"] == r["hl"]["rects"], (a["hl"], r["hl"])
assert a["hl"]["sortIndex"] == "00000|000000|00082", a["hl"]["sortIndex"]
assert r["hl"]["sortIndex"] == "00000|000000|00050", r["hl"]["sortIndex"]
# The note was put 20 units inside the CropBox's upper-left corner: its icon is in the CropBox.
assert a["note"]["rects"] == [[20, 752, 40, 772]], a["note"]["rects"]
assert r["note"]["rects"] == [[70, 720, 90, 740]], r["note"]["rects"]
EOF
check $? "A5 /Rotate 90 + CropBox [50 60 500 760]: same rectangles, sort key from the CropBox top, icon inside" \
  "exit $rc: $(cat "$work/a5.out" "$work/a5.err" "$work/a3.json" "$work/a5.json" 2>/dev/null)"

# A6–A8. Failures never break the probe.
start_stub "$work/a.pdf" --fail-annots 500
probe a6 --annots demo
[ "$rc" = 0 ] && grep -qx "sync: PUT /api/attachments/$att/file: HTTP 500 (ioError)" "$work/a6.out" &&
  grep -qx "sync: POST /api/attachments/$att/annotations: HTTP 500 (ioError)" "$work/a6.out" &&
  grep -q "viewer --biblean: POST /api/attachments/$att/annotations: HTTP 500" "$work/a6.err"
check $? "A6 HTTP 500 on PUT and POST: exit 0, both reported (stdout and stderr)" \
  "exit $rc: $(cat "$work/a6.out" "$work/a6.err")"
start_stub "$work/a.pdf" --fail-annots close
probe a7 --annots demo
[ "$rc" = 0 ] && grep -q "^sync: PUT /api/attachments/$att/file: .*" "$work/a7.out" &&
  grep -c '^viewer --biblean: ' "$work/a7.err" | grep -qx 2
check $? "A7 a dropped connection on PUT and POST: exit 0, both reported" \
  "exit $rc: $(cat "$work/a7.out" "$work/a7.err")"
start_stub "$work/a.pdf" --fail-annots hang
probe a8 --annots demo
[ "$rc" = 0 ] && grep -qxF 'sync-done: false' "$work/a8.out" && [ "$elapsed" -le 12 ]
check $? "A8 a server that never answers: exit 0 after the grace (${elapsed}s), reported as pending" \
  "exit $rc: $(cat "$work/a8.out" "$work/a8.err")"

# A9. Token hygiene and request shape (log of the last good runs is in A3/A5; recheck A6's).
start_stub "$work/a.pdf"
probe a9 --annots demo
! grep -qF "$token" "$work"/*.out "$work"/*.err &&
python3 -I - "$work/log" <<'EOF'
import json, sys
log = [json.loads(l) for l in open(sys.argv[1])]
assert all(r["auth"] == "ok" and not r["origin"] for r in log), log
types = {(r["method"], r["path"].rsplit("/", 1)[1]): r["ctype"] for r in log}
assert types[("PUT", "file")] == "application/pdf", types
assert types[("POST", "annotations")] == "application/json", types
EOF
check $? "A9 the token is never printed; every request carries it, no Origin, right content types"

# A10–A11. The window (Xvfb), smoke mode `save`.
display=1
if command -v Xvfb >/dev/null 2>&1; then
  # Started directly, not through xvfb-run (which reuses fd 3, the token pipe).
  xvfb_dpy=""
  for n in $(seq 161 200); do
    [ -e "/tmp/.X11-unix/X$n" ] || [ -e "/tmp/.X$n-lock" ] && continue
    Xvfb ":$n" -screen 0 1280x1024x24 -nolisten tcp >/dev/null 2>&1 &
    xvfb_pid=$!
    for _ in $(seq 1 50); do [ -S "/tmp/.X11-unix/X$n" ] && break; sleep 0.1; done
    if [ -S "/tmp/.X11-unix/X$n" ]; then xvfb_dpy=":$n"; break; fi
    kill "$xvfb_pid" 2>/dev/null; wait "$xvfb_pid" 2>/dev/null; xvfb_pid=""
  done
  if [ -n "$xvfb_dpy" ]; then export DISPLAY="$xvfb_dpy"; else display=0; fi
else
  display=0
fi
window() {
  local name="$1"
  rm -rf "$work/smoke" "$work/tmp"; mkdir -p "$work/smoke" "$work/tmp"
  local start; start=$(date +%s)
  env -u BIBLEAN_PAGE TMPDIR="$work/tmp" SAFEPDF_VIEWER_SMOKE="$work/smoke" \
    SAFEPDF_VIEWER_SMOKE_MODE=save SAFEPDF_SUBST_FONTS=0 \
    BIBLEAN_SERVER="$server" BIBLEAN_ATTACHMENT="$att" \
    timeout 120 "$viewer" --biblean >"$work/$name.out" 2>"$work/$name.err" \
    3< <(printf '%s\n' "$token")
  rc=$?
  elapsed=$(( $(date +%s) - start ))
}
if [ "$display" = 1 ]; then
  # Only other viewers' elements are stored: in the window (until task 10.1b) the viewer does
  # not see the stored set, so the library's own marks must be the file's (see Annots.lean).
  python3 -I -c 'import json, sys; s = json.load(open(sys.argv[1])); json.dump(s[1:], open(sys.argv[2], "w"))' \
    "$work/stored.json" "$work/stored-other.json"
  stored="$work/stored-other.json"
  start_stub "$work/a.pdf"
  window w1
  base=$elapsed
  [ "$rc" = 0 ] &&
  python3 -I - "$work/log" "$work/annots" "$work/put" "$work/a.pdf" <<'EOF'
import json, re, sys
import re
def nm_names(b):
    """The /NM strings of `b` that name our marks (literal or hex strings)."""
    out = {m.decode() for m in re.findall(rb"/NM\s*\((safepdf-mark-\d+)\)", b)}
    for h in re.findall(rb"/NM\s*<([0-9A-Fa-f\s]*)>", b):
        v = bytes.fromhex(re.sub(rb"\s", b"", h).decode())
        # A highlight's comment popup (9.5g, pdf.js form) is named
        # safepdf-mark-ID-popup-CID; it belongs to the highlight and is not a mark.
        if v.startswith(b"safepdf-mark-") and b"-popup-" not in v:
            out.add(v.decode())
    return out
log = [json.loads(l) for l in open(sys.argv[1])]
writes = [(r["method"], r["path"].rsplit("/", 1)[1], r["status"]) for r in log
          if r["method"] == "PUT" or r["path"].endswith("/annotations")]
assert writes == [("PUT", "file", 200), ("POST", "annotations", 200)], writes
put, orig = open(sys.argv[3], "rb").read(), open(sys.argv[4], "rb").read()
assert put.startswith(orig) and len(put) > len(orig), "prefix"
nms = nm_names(put)
assert len(nms) == 3, nms
body = json.loads(open(sys.argv[2]).readline())["body"]
ids = [e.get("id") for e in body]
mine = {i for i in ids if (i or "").startswith("safepdf-mark-")}
# The window's highlight with its comment note travels as one element; every posted mark is in
# the file, and the stored elements of other viewers are kept.
assert mine and mine <= nms, (mine, nms)
assert "12R" in ids and None in ids, ids
assert any(e.get("kind") == "highlight" and e.get("text") == "world" for e in body), body
EOF
  check $? "A10 marks saved in the window reach bib-lean on exit (PUT with 3 marks, then the set)" \
    "exit $rc: $(cat "$work/w1.err" "$work/log" "$work/smoke/save.txt" 2>/dev/null | tail -40)"
  start_stub "$work/a.pdf" --fail-annots hang
  window w2
  [ "$rc" = 0 ] && [ "$elapsed" -le $((base + 10)) ] && ! grep -qF "$token" "$work/w2.err" "$work/w2.out"
  check $? "A11 a server that never answers does not hold the window (exit 0 in ${elapsed}s, normal ${base}s)" \
    "exit $rc: $(cat "$work/w2.err")"
else
  echo "skip - A10-A11 window checks (no Xvfb)"
fi

echo "annots-test: $pass passed, $fail failed"
[ "$fail" = 0 ]
