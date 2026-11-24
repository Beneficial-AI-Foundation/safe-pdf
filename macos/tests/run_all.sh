#!/usr/bin/env bash
# Task 11.3a5: every C API v2 check in one go, headless (no window, no AppKit).
#   macos/tests/run_all.sh
# (a) compiles all_headers.c (all four headers) with -Wall -Wextra -Werror,
# (b) runs run.sh, run_view.sh, run_marks.sh and run_select.sh in turn,
# (c) lists the global symbols the four safepdf_*.o objects define (nm -g -U) and fails on a
#     duplicate, since the app links all four together.
# Exits non-zero on any failure and prints one summary line.
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
macos="$(dirname "$here")"
repo="$(dirname "$macos")"
out="$macos/build/all-headers"
failed=()

if [ "$(uname)" != Darwin ]; then
  echo "run_all.sh: macOS only" >&2
  exit 1
fi
mkdir -p "$out"
prefix="$(cd "$repo" && lean --print-prefix)"

# (a) the combined header test
if clang -O2 -Wall -Wextra -Werror -I "$prefix/include" -I "$macos" \
     -c "$here/all_headers.c" -o "$out/all_headers.o"; then
  echo "run_all.sh: all_headers.c compiled"
else
  failed+=(all_headers)
fi

# (b) the four suites
for s in run.sh run_view.sh run_marks.sh run_select.sh; do
  if "$here/$s"; then
    echo "run_all.sh: $s passed"
  else
    echo "run_all.sh: $s FAILED" >&2
    failed+=("$s")
  fi
done

# (c) duplicate global symbols across the four objects (the ones the suites above built)
objs=(
  "$macos/build/safepdf_core.o"
  "$macos/build/tests/safepdf_view.o"
  "$macos/build/marks-test/safepdf_marks.o"
  "$macos/build/select-test/safepdf_select.o"
)
syms="$out/symbols.txt"
: > "$syms"
missing=0
for o in "${objs[@]}"; do
  if [ -f "$o" ]; then
    nm -g -U "$o" | awk 'NF >= 3 {print $3}' | sort -u >> "$syms"
  else
    echo "run_all.sh: missing object $o" >&2
    missing=1
  fi
done
dups="$(sort "$syms" | uniq -d)"
if [ "$missing" != 0 ]; then
  failed+=(symbols-missing)
elif [ -n "$dups" ]; then
  echo "run_all.sh: duplicate global symbols:" >&2
  echo "$dups" >&2
  failed+=(duplicate-symbols)
else
  echo "run_all.sh: no duplicate global symbols ($(wc -l < "$syms" | tr -d ' ') defined in 4 objects)"
fi

if [ "${#failed[@]}" = 0 ]; then
  echo "run_all.sh: ok (all_headers, run.sh, run_view.sh, run_marks.sh, run_select.sh, symbols)"
else
  echo "run_all.sh: FAILED: ${failed[*]}"
  exit 1
fi
