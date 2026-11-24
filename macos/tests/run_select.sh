#!/usr/bin/env bash
# Builds and runs the selection/search C API test (task 11.3a4): macos/tests/select_test.c
# against macos/safepdf_select.c, macos/safepdf_core.c and libsafepdfffi.a, over the real
# confined worker on Tests/golden/text/latin.pdf.
#   macos/tests/run_select.sh        (run from anywhere; macOS only; no GUI)
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mac="$(dirname "$here")"
repo="$(dirname "$mac")"
out="$mac/build/select-test"
mkdir -p "$out"

if [ "$(uname)" != Darwin ]; then
  echo "run_select.sh: macOS only" >&2
  exit 1
fi

# `lake build macosFfi` does not build the worker executable: build it explicitly.
(cd "$repo" && lake build macosFfi worker)
ffi="$repo/.lake/build/lib/libsafepdfffi.a"
prefix="$(cd "$repo" && lean --print-prefix)"

cflags=(-O2 -Wall -Wextra -Werror -I "$prefix/include" -I "$mac")
clang "${cflags[@]}" -c "$mac/safepdf_core.c" -o "$out/safepdf_core.o"
clang "${cflags[@]}" -c "$mac/safepdf_select.c" -o "$out/safepdf_select.o"
clang "${cflags[@]}" -c "$here/select_test.c" -o "$out/select_test.o"
clang -o "$out/select_test" "$out/select_test.o" "$out/safepdf_select.o" "$out/safepdf_core.o" "$ffi" \
  -L "$prefix/lib/lean" -L "$prefix/lib" \
  -lleancpp -lInit -lStd -lleanrt -lcadical -lc++ -lgmp -luv \
  -Wl,-dead_strip
"$out/select_test" "$repo/.lake/build/bin/worker" "$repo/Tests/golden"
