#!/usr/bin/env bash
# Builds and runs the view/chrome C API test (task 11.3a2): macos/tests/view_test.c against
# macos/safepdf_view.c, macos/safepdf_core.c (for safepdf_init) and libsafepdfffi.a.
#   macos/tests/run_view.sh        (run from anywhere; macOS only; no GUI)
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mac="$(dirname "$here")"
repo="$(dirname "$mac")"
out="$mac/build/tests"
mkdir -p "$out"

if [ "$(uname)" != Darwin ]; then
  echo "run_view.sh: macOS only" >&2
  exit 1
fi

(cd "$repo" && lake build macosFfi)
ffi="$repo/.lake/build/lib/libsafepdfffi.a"
prefix="$(cd "$repo" && lean --print-prefix)"

cflags=(-O2 -Wall -Wextra -Werror -I "$prefix/include" -I "$mac")
clang "${cflags[@]}" -c "$mac/safepdf_core.c" -o "$out/safepdf_core.o"
clang "${cflags[@]}" -c "$mac/safepdf_view.c" -o "$out/safepdf_view.o"
clang "${cflags[@]}" -c "$here/view_test.c" -o "$out/view_test.o"
clang -o "$out/view_test" "$out/view_test.o" "$out/safepdf_view.o" "$out/safepdf_core.o" "$ffi" \
  -L "$prefix/lib/lean" -L "$prefix/lib" \
  -lleancpp -lInit -lStd -lleanrt -lcadical -lc++ -lgmp -luv \
  -Wl,-dead_strip
"$out/view_test"
