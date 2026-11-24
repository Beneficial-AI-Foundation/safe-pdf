#!/usr/bin/env bash
# Builds and runs the C API v2 test (task 11.3a1): macos/tests/core_test.c over the real
# confined worker, on the goldens under Tests/golden/. Headless (no window, no AppKit).
#   macos/tests/run.sh
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
macos="$(dirname "$here")"
repo="$(dirname "$macos")"

if [ "$(uname)" != Darwin ]; then
  echo "macos/tests/run.sh: macOS only" >&2
  exit 1
fi

"$macos/build.sh"
# `lake build macosFfi` does not build the worker executable: build it explicitly.
(cd "$repo" && lake build worker)
"$macos/build/core_test" "$repo/.lake/build/bin/worker" "$repo/Tests/golden"
