#!/usr/bin/env bash
# Headless self-test of the AppKit spike (task 11.1). Never shows a window or activates:
#   macos/selftest.sh FILE.pdf [OUTDIR]     (OUTDIR defaults to macos/build/selftest)
# Runs `SAFEPDF_MACOS_SELFTEST=OUTDIR macos/build/safepdf-mac FILE` under a watcher that
# samples the front application every 0.5 s (`lsappinfo`, no Automation permission needed);
# if the spike ever becomes the front app it is killed (only that PID) and the test fails.
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
  front="$(lsappinfo info -only name "$(lsappinfo front)" 2>/dev/null || true)"
  printf '%s %s\n' "$(date +%T)" "$front" >> "$watch"
  case "$front" in
    *safepdf-mac*|*safe-pdf*)
      echo "selftest: the spike became the front app; killing PID $pid" >&2
      kill "$pid" 2>/dev/null || true
      leaked=1 ;;
  esac
  # A Prohibited app never appears in lsappinfo's list as Foreground.
  if lsappinfo list 2>/dev/null | grep -A3 "safepdf-mac" | grep -q "type=\"Foreground\""; then
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
