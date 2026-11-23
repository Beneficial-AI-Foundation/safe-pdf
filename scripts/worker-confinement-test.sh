#!/usr/bin/env bash
# Platform test of the document worker's confinement (task 12.2b; docs/safety.md §2.4).
# Run from the repo root.
#   scripts/worker-confinement-test.sh [--no-build]
#
# Builds `worker` and the test-only `worker-probe` (both default targets), then:
#   1. starts the production `worker` with a non-empty environment: it must refuse to serve
#      (exit status 3) and write nothing to stdout;
#   2. starts it the way the client does (empty environment, cwd /) with empty input: it must
#      confine itself and exit 0 at end of input;
#   3. runs `worker-probe --parent PDF` with SAFEPDF_PROBE_TOKEN set: the parent listens on
#      127.0.0.1 and starts a confined child exactly like the client starts the worker
#      (`Worker.spawn`: empty environment, cwd /) plus an unconfined control child. The
#      confined child must be denied: reading /etc/hosts, re-reading a font file it read at
#      startup, creating a file in /tmp, listing /, connecting to the parent's port, seeing
#      SAFEPDF_PROBE_TOKEN, spawning /bin/echo; and must still run a thread and render page
#      1. The control child must be allowed all of them (the probes can detect access).
# Every probe line is printed. Rendering through the confined worker byte-for-byte against
# in-process rendering is the `worker` suite of `lake exe tests`; the same checks as here
# are the `worker-confinement` suite.
#
# Linux: the seccomp filter in c/worker_sandbox.c has not been run on Linux yet (written on
# macOS); a failure here on Linux is the first real test of it.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

build=1
case "${1:-}" in
  --no-build) build=0 ;;
  "") ;;
  *) echo "usage: $0 [--no-build]" >&2; exit 2 ;;
esac

if [ "$build" = 1 ]; then
  lake build worker worker-probe
fi

worker="$repo/.lake/build/bin/worker"
probe="$repo/.lake/build/bin/worker-probe"
pdf="$repo/Tests/golden/text/latin.pdf"
for f in "$worker" "$probe"; do
  [ -x "$f" ] || { echo "missing $f (run without --no-build)" >&2; exit 2; }
done

status=0
echo "== $(uname -s) $(uname -m)"

echo "== 1. production worker with a non-empty environment"
set +e
out="$(cd / && SAFEPDF_PROBE_TOKEN=secret "$worker" </dev/null 2>/dev/null)"
code=$?
set -e
if [ "$code" = 3 ] && [ -z "$out" ]; then
  echo "refused: exit 3, no output (ok)"
else
  echo "FAIL: expected exit 3 and no output, got exit $code"
  status=1
fi

echo "== 2. production worker as the client starts it (empty environment, cwd /)"
set +e
err="$(cd / && env -i "$worker" </dev/null 2>&1 >/dev/null)"
code=$?
set -e
if [ "$code" = 0 ]; then
  echo "confined and served until end of input: exit 0 (ok)"
else
  echo "FAIL: exit $code: $err"
  status=1
fi

echo "== 3. probes (confined child and unconfined control)"
set +e
SAFEPDF_PROBE_TOKEN="probe-token-$$" "$probe" --parent "$pdf"
code=$?
set -e
[ "$code" = 0 ] || { echo "FAIL: worker-probe exit $code"; status=1; }

if [ "$status" = 0 ]; then
  echo "worker-confinement-test: PASS"
else
  echo "worker-confinement-test: FAIL"
fi
exit $status
