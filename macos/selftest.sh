#!/usr/bin/env bash
# Headless self-test of the AppKit spike (task 11.1). Never shows a window or activates:
#   macos/selftest.sh FILE.pdf [OUTDIR]     (OUTDIR defaults to macos/build/selftest)
# Runs `SAFEPDF_MACOS_SELFTEST=OUTDIR macos/build/safepdf-mac FILE` under a watcher that
# samples the front application every 0.5 s (`lsappinfo`, no Automation permission needed);
# if that PID ever becomes the front app or a Foreground app it is killed (only that PID) and
# the test fails; other processes with the same name (e.g. a copy launched by hand) are ignored.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bin="$here/build/safepdf-mac"
pdf="${1:?usage: $0 FILE.pdf [OUTDIR]}"
out="${2:-$here/build/selftest}"
mkdir -p "$out"
watch="$out/front-app.log"
: > "$watch"

SAFEPDF_MACOS_SELFTEST="$out" "$bin" "$pdf" &
pid=$!
leaked=0
while kill -0 "$pid" 2>/dev/null; do
  # Only the PID this script started counts: a copy launched by hand is not ours.
  front_pid="$(lsappinfo info -only pid "$(lsappinfo front)" 2>/dev/null | tr -dc '0-9' || true)"
  front="$(lsappinfo info -only name "$(lsappinfo front)" 2>/dev/null || true)"
  printf '%s %s (pid %s)\n' "$(date +%T)" "$front" "$front_pid" >> "$watch"
  if [ "$front_pid" = "$pid" ]; then
    echo "selftest: the spike became the front app; killing PID $pid" >&2
    kill "$pid" 2>/dev/null || true
    leaked=1
  fi
  # A Prohibited app never appears in lsappinfo's list as Foreground: look at our PID's entry.
  if lsappinfo list 2>/dev/null | grep -E "pid = $pid[^0-9].*type=\"Foreground\"" >/dev/null; then
    echo "selftest: the spike registered as a Foreground app; killing PID $pid" >&2
    kill "$pid" 2>/dev/null || true
    leaked=1
  fi
  sleep 0.5
done
status=0
wait "$pid" || status=$?
echo "selftest: exit $status; front-app samples: $(wc -l < "$watch" | tr -d ' '), leaks: $leaked"
[ "$leaked" = 0 ] && [ "$status" = 0 ]
