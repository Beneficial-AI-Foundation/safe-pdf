#!/usr/bin/env bash
# Headless self-test of the native macOS shell (task 11.1 spike, 11.3b app). Never shows a
# window or activates:
#   macos/selftest.sh FILE.pdf [OUTDIR]     (OUTDIR defaults to macos/build/selftest)
# Binary: by default macos/build/safepdf-mac. SAFEPDF_SELFTEST_BUNDLE=1 runs the bundle's binary
# macos/build/SafePdf.app/Contents/MacOS/SafePdf instead (the same code, run in place; the
# bundle is executed directly, never opened through LaunchServices).
# Runs `SAFEPDF_MACOS_SELFTEST=OUTDIR <binary> FILE` under a watcher that
# samples the front application every 0.5 s (`lsappinfo`, no Automation permission needed);
# if that PID ever becomes the front app or a Foreground app it is killed (only that PID) and
# the test fails; other processes with the same name (e.g. a copy launched by hand) are ignored.
# The watcher matches by PID, so it covers every name the process can have (safepdf-mac,
# SafePdf, SafePDF, bundle id org.safe-pdf.SafePDF); those names only label the messages.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ "${SAFEPDF_SELFTEST_BUNDLE:-0}" = 1 ]; then
  bin="$here/build/SafePdf.app/Contents/MacOS/SafePdf"
else
  bin="$here/build/safepdf-mac"
fi
pdf="${1:?usage: $0 FILE.pdf [OUTDIR]}"
out="${2:-$here/build/selftest}"
mkdir -p "$out"
watch="$out/front-app.log"
: > "$watch"

# Without a WindowServer session (e.g. a CI runner with no logged-in GUI user) lsappinfo has
# no front application to report: the watcher is then skipped with a printed line (nothing
# could become frontmost) and only the self-test's own exit status counts.
watcher=1
if ! lsappinfo front 2>/dev/null | grep -q '^ASN:'; then
  watcher=0
  echo "selftest: SKIP front-app watcher: lsappinfo reports no front application (no WindowServer session?)"
fi

SAFEPDF_MACOS_SELFTEST="$out" "$bin" "$pdf" &
pid=$!
leaked=0
while [ "$watcher" = 1 ] && kill -0 "$pid" 2>/dev/null; do
  # Only the PID this script started counts: a copy launched by hand is not ours.
  front_pid="$(lsappinfo info -only pid "$(lsappinfo front)" 2>/dev/null | tr -dc '0-9' || true)"
  front="$(lsappinfo info -only name "$(lsappinfo front)" 2>/dev/null || true)"
  printf '%s %s (pid %s)\n' "$(date +%T)" "$front" "$front_pid" >> "$watch"
  if [ "$front_pid" = "$pid" ]; then
    echo "selftest: the app became the front app; killing PID $pid" >&2
    kill "$pid" 2>/dev/null || true
    leaked=1
  fi
  # A Prohibited app never appears in lsappinfo's list as Foreground: look at our PID's entry.
  if lsappinfo list 2>/dev/null | grep -E "pid = $pid[^0-9].*type=\"Foreground\"" >/dev/null; then
    echo "selftest: the app registered as a Foreground app; killing PID $pid" >&2
    kill "$pid" 2>/dev/null || true
    leaked=1
  fi
  sleep 0.5
done
status=0
wait "$pid" || status=$?
if [ "$watcher" = 1 ]; then
  echo "selftest: exit $status; front-app samples: $(wc -l < "$watch" | tr -d ' '), leaks: $leaked"
else
  echo "selftest: exit $status; front-app watcher skipped"
fi
[ "$leaked" = 0 ] && [ "$status" = 0 ]
