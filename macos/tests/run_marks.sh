#!/usr/bin/env bash
# Builds and runs the C test of the marks/save/XFDF API (task 11.3a3, macos/safepdf_marks.h):
#   macos/tests/run_marks.sh        (run from anywhere; uses the repository's Lake project)
# Needs the Lean toolchain (elan) and the system clang. Never launches a GUI. The saved file is
# opened with the project's inspector; when `qpdf` is
# installed, the saved file is also checked with `qpdf --check` (skipped otherwise).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
macos="$(dirname "$here")"
repo="$(dirname "$macos")"
out="$macos/build/marks-test"
mkdir -p "$out"

(cd "$repo" && lake build macosFfi)
ffi="$repo/.lake/build/lib/libsafepdfffi.a"
prefix="$(cd "$repo" && lean --print-prefix)"

cflags=(-O2 -Wall -Wextra -I "$prefix/include")
clang "${cflags[@]}" -c "$macos/safepdf_core.c" -o "$out/safepdf_core.o"
clang "${cflags[@]}" -c "$macos/safepdf_marks.c" -o "$out/safepdf_marks.o"
clang "${cflags[@]}" -c "$here/marks_test.c" -o "$out/marks_test.o"
# Link line of macos/build.sh, without AppKit.
clang -o "$out/marks_test" "$out/marks_test.o" "$out/safepdf_marks.o" "$out/safepdf_core.o" "$ffi" \
  -L "$prefix/lib/lean" -L "$prefix/lib" \
  -lleancpp -lInit -lStd -lleanrt -lcadical -lc++ -lgmp -luv \
  -Wl,-dead_strip

golden="$repo/Tests/golden/text"
"$out/marks_test" "$golden/latin.pdf" "$golden/enc-aes-128.pdf" "$golden/enc-rc4-128.pdf" "$out"

# The saved file opens in the project's own inspector (strict and lenient paths, exit 0).
(cd "$repo" && lake build inspect >/dev/null)
"$repo/.lake/build/bin/inspect" "$out/saved.pdf" >"$out/saved.inspect.txt"
echo "run_marks.sh: inspect saved.pdf: ok ($(head -n 1 "$out/saved.inspect.txt"))"

if command -v qpdf >/dev/null 2>&1; then
  qpdf --check "$out/saved.pdf"
else
  echo "run_marks.sh: qpdf not installed; skipping qpdf --check"
fi
echo "run_marks.sh: ok"
