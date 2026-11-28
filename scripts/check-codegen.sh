#!/usr/bin/env bash
# Guard (task 13.18): no big-number constant is rebuilt per call in the raster and content
# interpreter code.
#
# A Nat or Int literal of 2^32 or more in a function body compiles to
# `lean_cstr_to_nat("...")`, a decimal parse through GMP on every call, unless the compiler
# lifts it into a closed term (an `_init_` function, evaluated once at start-up). This script
# fails when the generated C of `SafePdf/Core/Raster` or `SafePdf/Core/Content` contains
# `lean_cstr_to_nat(` outside an `_init_` function. Run it after `lake build` (it reads the C
# that the build leaves under `.lake/build/ir/`; it builds nothing).
#
# Usage: scripts/check-codegen.sh [IR_DIR]   (default .lake/build/ir/SafePdf/Core)
# Fix a hit by naming the constant at a type that does not take the bignum path (`UInt64`,
# `Int64`), by computing it with a shift of a run-time value, or by moving it into a `def`
# that is not inlined; then rebuild and re-run.
set -uo pipefail
cd "$(dirname "$0")/.."
ir=${1:-.lake/build/ir/SafePdf/Core}
fail=0
checked=0
for dir in Raster Content; do
  if [ ! -d "$ir/$dir" ]; then
    echo "check-codegen: $ir/$dir not found (run lake build first)" >&2
    exit 2
  fi
  while IFS= read -r f; do
    checked=$((checked + 1))
    # fn = name of the C function whose header was seen last (headers start at column 0 and
    # do not end in ';'; declarations do). Hits inside `_init_` functions run once.
    hits=$(awk '
      /^(LEAN_EXPORT|static|lean_object\* initialize|uint8_t initialize)/ && !/;$/ {
        fn = $0; sub(/\(.*/, "", fn); sub(/.*[ *]/, "", fn) }
      /lean_cstr_to_nat\(/ && fn !~ /^_init_/ {
        lit = $0; sub(/.*lean_cstr_to_nat\("/, "", lit); sub(/".*/, "", lit)
        print "  " fn ": " lit }' "$f")
    if [ -n "$hits" ]; then
      echo "check-codegen: $f: lean_cstr_to_nat outside an _init_ function:" >&2
      echo "$hits" >&2
      fail=1
    fi
  done < <(find "$ir/$dir" -name '*.c' | sort)
done
if [ "$checked" -eq 0 ]; then
  echo "check-codegen: no generated C files found under $ir" >&2
  exit 2
fi
if [ "$fail" -ne 0 ]; then
  echo "check-codegen: FAILED (a bignum literal is parsed on every call)" >&2
  exit 1
fi
echo "check-codegen: OK ($checked files, no lean_cstr_to_nat outside _init_)"
