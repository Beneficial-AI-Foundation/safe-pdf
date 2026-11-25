#!/usr/bin/env bash
# Builds the native macOS shell (task 11.3b; docs/macos-design.md §3 decision 6, no Xcode
# project):
#   macos/build/safepdf-mac       the app binary (unbundled; with macos/build/worker beside it)
#   macos/build/SafePdf.app       the bundle: Contents/MacOS/SafePdf, Contents/Helpers/worker,
#                                 Contents/Resources/SafePdf.icns, Info.plist; ad-hoc signed
#   macos/build/core_test         the C API v2 test program (macos/tests/run.sh runs it)
#   macos/build.sh                (run from anywhere; uses the repository's Lake project;
#                                 `lake build macosApp` runs it too)
# Needs: the Lean toolchain (elan), the Xcode command line tools (clang, swiftc, iconutil,
# codesign; macOS SDK). No other dependency. Never launches the app.
#
# Swift sees the C API through macos/module.modulemap (module SafePdfC: the four headers).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
out="$here/build"
mkdir -p "$out"

if [ "$(uname)" != Darwin ]; then
  echo "macos/build.sh: macOS only" >&2
  exit 1
fi

# 1. The Lean side: SafePdf.Shell.Ffi and its import closure as one static library, and the
#    confined document worker (not built by macosFfi). `lake build macosApp` (lakefile.lean)
#    builds both itself and then runs this script with SAFEPDF_MACOS_LAKE_DONE=1, so that no
#    `lake build` runs inside a running one.
if [ "${SAFEPDF_MACOS_LAKE_DONE:-0}" != 1 ]; then
  (cd "$repo" && lake build macosFfi worker)
fi
ffi="$repo/.lake/build/lib/libsafepdfffi.a"
worker="$repo/.lake/build/bin/worker"
prefix="$(cd "$repo" && lean --print-prefix)"
leanlibs=(-L "$prefix/lib/lean" -L "$prefix/lib"
  -lleancpp -lInit -lStd -lleanrt -lcadical -lc++ -lgmp -luv)

# 2. The C API shims with the system clang (it has the macOS SDK), at the app's deployment
#    target: macOS 15 (task 11.6a, the human's decision; the Lean toolchain's libgmp.a and
#    libuv.a are built for 15.0, so nothing older can be promised).
min=15.0
cflags=(-O2 -Wall -Wextra -I "$prefix/include" -I "$here")
for m in core view marks select; do
  clang "${cflags[@]}" -mmacosx-version-min="$min" -c "$here/safepdf_$m.c" -o "$out/safepdf_$m.o"
done

# 3. The Swift app (Swift 6 language mode, strict concurrency), linked by swiftc against the
#    shims, the Lean library and Lean's runtime: Lake's executable link line minus the
#    libraries the core's closure does not use (Lean, Lake, LeanExport, ssl).
#    Objects marked for a newer macOS than $min make the linker warn once per object: since
#    the minimum is 15.0 the toolchain's libgmp.a / libuv.a (15.0) no longer do; the C that
#    Lake compiles for libsafepdfffi.a carries the build machine's macOS (Lake passes no
#    deployment target). Those warnings are counted, not repeated (the full text stays in
#    build/swift-link.log); any other diagnostic is shown.
log="$out/swift-link.log"
if ! swiftc -swift-version 6 -O -target "$(uname -m)-apple-macos$min" -module-name SafePdfApp \
  -I "$here" "$here"/App/*.swift \
  "$out/safepdf_core.o" "$out/safepdf_view.o" "$out/safepdf_marks.o" "$out/safepdf_select.o" \
  "$ffi" "${leanlibs[@]}" \
  -framework AppKit -framework CoreGraphics -framework UniformTypeIdentifiers \
  -Xlinker -dead_strip \
  -o "$out/safepdf-mac" 2>"$log"; then
  cat "$log" >&2
  exit 1
fi
newer="than being linked ($min)"
grep -v -F "$newer" "$log" >&2 || true
n="$(grep -c -F "$newer" "$log" || true)"
if [ "$n" != 0 ]; then
  echo "macos/build.sh: note: $n linked objects are built for a newer macOS than $min (Lake's C objects carry the build machine's version; see $log)" >&2
fi
cp "$worker" "$out/worker"

# 3b. The C API v2 test program (task 11.3a1; run it with macos/tests/run.sh): plain C over
#     the same library, no AppKit (built as before 11.3b: no deployment target).
clang -O2 -Wall -Wextra -I "$prefix/include" -c "$here/safepdf_core.c" -o "$out/core_test_core.o"
clang -O2 -Wall -Wextra -I "$prefix/include" -c "$here/tests/core_test.c" -o "$out/core_test.o"
clang -o "$out/core_test" "$out/core_test.o" "$out/core_test_core.o" "$ffi" "${leanlibs[@]}" \
  -Wl,-dead_strip

# 4. The bundle (for Finder/Dock; never opened by scripts).
app="$out/SafePdf.app"
rm -rf "$app"
mkdir -p "$app/Contents/MacOS" "$app/Contents/Helpers" "$app/Contents/Resources"
cp "$out/safepdf-mac" "$app/Contents/MacOS/SafePdf"
cp "$worker" "$app/Contents/Helpers/worker"
cp "$here/Info.plist" "$app/Contents/Info.plist"
printf 'APPL????' > "$app/Contents/PkgInfo"

# 4a. The icon from docs/branding (iconutil wants icon_WxH[@2x].png; 1024 px is absent, so the
#     512@2x slot is left out).
iconset="$out/SafePdf.iconset"
rm -rf "$iconset"
mkdir -p "$iconset"
brand="$repo/docs/branding"
cp "$brand/icon-16.png" "$iconset/icon_16x16.png"
cp "$brand/icon-32.png" "$iconset/icon_16x16@2x.png"
cp "$brand/icon-32.png" "$iconset/icon_32x32.png"
cp "$brand/icon-64.png" "$iconset/icon_32x32@2x.png"
cp "$brand/icon-128.png" "$iconset/icon_128x128.png"
cp "$brand/icon-256.png" "$iconset/icon_128x128@2x.png"
cp "$brand/icon-256.png" "$iconset/icon_256x256.png"
cp "$brand/icon-512.png" "$iconset/icon_256x256@2x.png"
cp "$brand/icon-512.png" "$iconset/icon_512x512.png"
iconutil -c icns "$iconset" -o "$app/Contents/Resources/SafePdf.icns"

# 4b. Ad-hoc signing (distribution signing and notarisation are deferred, design §3.5): the
#     helper first, then the bundle.
codesign --force --sign - "$app/Contents/Helpers/worker"
codesign --force --sign - "$app"
plutil -lint "$app/Contents/Info.plist" >/dev/null

echo "built $out/safepdf-mac, $app and $out/core_test"
