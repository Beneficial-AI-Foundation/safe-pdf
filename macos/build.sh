#!/usr/bin/env bash
# Builds the AppKit spike (task 11.1): macos/build/safepdf-mac and macos/build/SafePdf.app.
#   macos/build.sh            (run from anywhere; uses the repository's Lake project)
# Needs: the Lean toolchain (elan), Xcode command line tools (clang, AppKit SDK). No other
# dependency. Never launches the app.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
out="$here/build"
mkdir -p "$out"

if [ "$(uname)" != Darwin ]; then
  echo "macos/build.sh: macOS only" >&2
  exit 1
fi

# 1. The Lean side: SafePdf.Shell.Ffi and its import closure as one static library.
(cd "$repo" && lake build macosFfi)
ffi="$repo/.lake/build/lib/libsafepdfffi.a"
prefix="$(cd "$repo" && lean --print-prefix)"

# 2. The C API shim and the AppKit app, with the system clang (it has the macOS SDK).
cflags=(-O2 -Wall -Wextra -I "$prefix/include")
clang "${cflags[@]}" -c "$here/safepdf_core.c" -o "$out/safepdf_core.o"
clang "${cflags[@]}" -fobjc-arc -Wno-deprecated-declarations -c "$here/main.m" -o "$out/main.o"

# 3. Link: the Lean runtime as Lake links an executable (`lake build viewer -v`), minus the
#    libraries the core's closure does not use (Lean, Lake, LeanExport, ssl).
clang -o "$out/safepdf-mac" "$out/main.o" "$out/safepdf_core.o" "$ffi" \
  -L "$prefix/lib/lean" -L "$prefix/lib" \
  -lleancpp -lInit -lStd -lleanrt -lcadical -lc++ -lgmp -luv \
  -framework AppKit -framework CoreGraphics \
  -Wl,-dead_strip

# 4. A minimal bundle around the same binary (for Finder/Dock; never opened by scripts).
app="$out/SafePdf.app/Contents"
mkdir -p "$app/MacOS"
cp "$out/safepdf-mac" "$app/MacOS/safepdf-mac"
cat > "$app/Info.plist" <<'PLIST'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>CFBundleExecutable</key><string>safepdf-mac</string>
  <key>CFBundleIdentifier</key><string>org.safe-pdf.spike</string>
  <key>CFBundleName</key><string>safe-pdf</string>
  <key>CFBundlePackageType</key><string>APPL</string>
  <key>CFBundleShortVersionString</key><string>0.1</string>
  <key>NSHighResolutionCapable</key><true/>
</dict>
</plist>
PLIST
echo "built $out/safepdf-mac and $out/SafePdf.app"
