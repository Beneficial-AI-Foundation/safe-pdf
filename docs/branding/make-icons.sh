#!/usr/bin/env bash
# Generates the viewer's application/window icons (task 9.r3) from the logo
# docs/branding/safe-pdf.png (1086x1448, transparent background): the document mark without
# the "safe-pdf" wordmark (illegible at icon sizes), its inside filled white (so the dark
# outline stays visible on dark panels and Docks), centred on a transparent square, at
# 16, 32, 64, 128, 256 and 512 px. 16 and 32 px are drawn from copies whose strokes are
# thickened first (they would otherwise fade to grey).
#
# A one-time generation: the PNGs (docs/branding/icon-N.png) and the Lean module that embeds
# them as base64 (SafePdf/Shell/App/Icons.lean, read by Tk's `image create photo -data`) are
# committed. Re-run only when the logo changes (needs ImageMagick 7 `magick`, coreutils
# `base64`):
#   docs/branding/make-icons.sh [PNG-OUTDIR [LEAN-FILE]]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
out=${1:-$here}
lean=${2:-$repo/SafePdf/Shell/App/Icons.lean}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# The document mark: rows 144..1086, columns 197..882 of the logo (alpha bounding box above
# the gap before the wordmark), padded to a 1024 square.
magick "$here/safe-pdf.png" -crop 686x943+197+144 +repage -background none \
  -gravity center -extent 1024x1024 "$tmp/mark.png"
# Silhouette: everything not reachable from the corner through transparent pixels.
magick "$tmp/mark.png" -alpha extract -threshold 50% -bordercolor black -border 1 \
  -fill red -draw "color 0,0 floodfill" -shave 1x1 \
  -fill white +opaque red -fill black -opaque red -alpha off "$tmp/sil.png"
magick -size 1024x1024 xc:white "$tmp/mark.png" -composite "$tmp/onwhite.png"
magick "$tmp/onwhite.png" "$tmp/sil.png" -alpha off -compose CopyOpacity -composite \
  "$tmp/master.png"
png='-strip -depth 8 -define png:compression-level=9'
# Thickened copies for the small sizes: dark strokes and the dot grow by R px of 1024
# (16 px: 28, 32 px: 14), the silhouette with them.
for sr in 16:28 32:14; do
  s=${sr%:*} r=${sr#*:}
  magick "$tmp/onwhite.png" -morphology Erode "Disk:$r" \
    \( "$tmp/sil.png" -morphology Dilate "Disk:$r" \) -alpha off -compose CopyOpacity \
    -composite -filter Lanczos -resize "${s}x${s}" $png "$out/icon-$s.png"
done
for s in 64 128 256 512; do
  magick "$tmp/master.png" -filter Lanczos -resize "${s}x${s}" $png "$out/icon-$s.png"
done
# The Lean module. `all` lists the largest first: Tk on macOS uses only the first image of
# `wm iconphoto` (for the Dock).
{
  cat <<'EOF'
/-!
# Application icon (task 9.r3; Plan.md §8 native app, §10 `SafePdf/Shell/`)

**Generated** by `docs/branding/make-icons.sh` from the logo `docs/branding/safe-pdf.png`;
do not edit. The PNG icons `docs/branding/icon-N.png` as base64 text, embedded so that the
installed `viewer` does not depend on the source tree. `Viewer.setIcon` loads them with
`image create photo -format png -data` and sets them with `wm iconphoto . -default`.
-/

namespace SafePdf.Shell.App.Icons

EOF
  for s in 16 32 64 128 256 512; do
    printf '/-- The %s×%s px icon, PNG in base64. -/\ndef png%s : String :=\n  "%s"\n\n' \
      "$s" "$s" "$s" "$(base64 -w0 "$out/icon-$s.png")"
  done
  cat <<'EOF'
/-- Every size as (pixels, base64 PNG), largest first. -/
def all : List (Nat × String) :=
  [(512, png512), (256, png256), (128, png128), (64, png64), (32, png32), (16, png16)]

-- Base64 of a PNG: the signature 89 50 4E 47 0D 0A 1A 0A encodes as "iVBORw0KGgo".
#guard all.all fun (_, d) => d.startsWith "iVBORw0KGgo" && d.all fun c =>
  c.isAlphanum || c == '+' || c == '/' || c == '='

end SafePdf.Shell.App.Icons
EOF
} > "$lean"
