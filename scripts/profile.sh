#!/usr/bin/env bash
# Sampling profiler for a running native binary (task 13.17). `perf` does not run in the
# Linux sandbox; this takes N stack samples with gdb instead. Lean runs `main` on its own
# thread, so every sample is `thread apply all bt DEPTH` (all threads, not just thread 1).
#
# Usage: scripts/profile.sh [-n SAMPLES] [-d DEPTH] [-o OUT] [-i INTERVAL_S] -- CMD [ARGS...]
#        scripts/profile.sh [-n SAMPLES] [-d DEPTH] [-o OUT] -p PID
#   -n  samples (default 500)        -d  frames per thread (default 12)
#   -o  raw output file (default profile.<pid>.txt)   -i  sleep between samples (default 0)
#   -r  with CMD: rerun CMD in a loop and sample whichever run is current, so a short CMD
#       (a few seconds) still yields N samples; the loop is killed at the end
# Each sample attaches, prints the backtraces and detaches, so the process runs between
# samples; sampling stops early when the process exits (a CMD that finishes before N samples
# gives fewer; wrap it in a loop or use a larger workload). Aggregate with
#   python3 -I scripts/profile_agg.py OUT
# gdb is a development tool only (sudo apt-get install -y gdb), not a project dependency.
set -uo pipefail
n=500; depth=12; out=""; interval=0; pid=""; rep=""
while getopts "n:d:o:i:p:r" o; do
  case $o in n) n=$OPTARG;; d) depth=$OPTARG;; o) out=$OPTARG;; i) interval=$OPTARG;; p) pid=$OPTARG;; r) rep=1;;
    *) sed -n 2,14p "$0"; exit 2;; esac
done
shift $((OPTIND - 1))
[ "${1:-}" = "--" ] && shift
command -v gdb >/dev/null || { echo "gdb not installed" >&2; exit 2; }
started=""
if [ -z "$pid" ]; then
  [ $# -gt 0 ] || { sed -n 2,14p "$0"; exit 2; }
  if [ -n "$rep" ]; then
    pidfile=$(mktemp)
    ( while :; do "$@" >/dev/null 2>&1 & echo $! >"$pidfile"; wait $!; done ) &
    loop=$!; started=1; sleep 0.2; pid=$(cat "$pidfile")
  else
    "$@" >/dev/null 2>&1 &
    pid=$!; started=1
  fi
fi
[ -n "$out" ] || out="profile.$$.txt"
: >"$out"
got=0
for ((i = 0; i < n; i++)); do
  [ -z "$rep" ] || pid=$(cat "$pidfile")
  if ! kill -0 "$pid" 2>/dev/null; then
    [ -z "$rep" ] && break
    sleep 0.05; continue
  fi
  {
    echo "=== SAMPLE $i"
    gdb -p "$pid" -batch -ex "thread apply all bt $depth" 2>/dev/null
  } >>"$out"
  got=$((got + 1))
  [ "$interval" = 0 ] || sleep "$interval"
done
if [ -n "$started" ]; then
  [ -z "$rep" ] || { kill "$loop" 2>/dev/null; pid=$(cat "$pidfile"); rm -f "$pidfile"; }
  kill "$pid" 2>/dev/null; wait 2>/dev/null
fi
echo "profile.sh: $got samples -> $out" >&2
