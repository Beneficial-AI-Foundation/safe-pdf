#!/usr/bin/env bash
# Flate throughput benchmark (task 3.11): compile scripts/bench-flate.lean natively and run it.
# Usage: scripts/bench-flate.sh [--reps N] file.z …
# Builds the SafePdf static library, compiles the benchmark with `lean -c` and links it with
# `leanc`; no lakefile target is needed. Artifacts go to .lake/bench/ (git-ignored via .lake).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
out=.lake/bench
mkdir -p "$out"
lake build SafePdf:static >/dev/null
lake env lean -c "$out/bench-flate.c" scripts/bench-flate.lean
lib=$(ls .lake/build/lib/lib*SafePdf.a)
leanc -O3 -o "$out/bench-flate" "$out/bench-flate.c" "$lib"
exec "$out/bench-flate" "$@"
