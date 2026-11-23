#!/usr/bin/env bash
# Raster benchmark (task 7.2d): compile scripts/bench-raster.lean natively and run it.
# Usage: scripts/bench-raster.sh [--reps N]
# Builds the SafePdf static library, compiles the benchmark with `lean -c` and links it with
# `leanc`; no lakefile target is needed. Artifacts go to .lake/bench/ (git-ignored via .lake).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
out=.lake/bench
mkdir -p "$out"
lake build SafePdf:static >/dev/null
lake env lean -c "$out/bench-raster.c" scripts/bench-raster.lean
lib=$(ls .lake/build/lib/lib*SafePdf.a)
leanc -O3 -o "$out/bench-raster" "$out/bench-raster.c" "$lib"
exec "$out/bench-raster" "$@"
