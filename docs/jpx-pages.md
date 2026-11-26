# JPX source-PDF page comparisons

The M10.2c gate renders the original, SHA-256-verified PDFs through safe-pdf's confined
worker. The two pikepdf PDFs exercise the same image behind different filter chains.
Their 90 × 33 pages expose the old worker's solid gray placeholder over 2,764 of
2,970 pixels by the existing safe-pdf metric.

## Running the gate

From the safe-pdf root, build the worker and its client. Set `JPX_CACHE` to an existing
decoder corpus `files` directory or a new cache outside either checkout. The clean fetch
below downloads only the pinned source PDFs. It verifies an existing cache offline when
all files are present. The gate independently checks size and SHA-256 before opening each
PDF. Third-party PDFs, extracted images and rendered pages stay out of Git.

```sh
lake build worker SafePdf.Shell.Worker.Client
pkg=.lake/packages/jpeg2000
python3 -I "$pkg/scripts/fetch-corpus.py" --only pdf-sources/ --root "$JPX_CACHE"
JPX_TOOLS=$(mktemp -d)
python3 -m venv "$JPX_TOOLS/venv"
"$JPX_TOOLS/venv/bin/pip" install --only-binary=:all: pypdfium2==5.15.2
npm install --prefix "$JPX_TOOLS" --ignore-scripts --save-exact pdfjs-dist@6.5.438 @napi-rs/canvas@1.2.1
PDFJS_DIST="$JPX_TOOLS/node_modules/pdfjs-dist"
"$JPX_TOOLS/venv/bin/python" -IB Tests/differential/jpx/pages.py --cache "$JPX_CACHE" \
  --pdfjs-dir "$PDFJS_DIST" --json /tmp/jpx-pages.json
```

Install qpdf with JSON v2 support and MuPDF with `mutool draw` PNM and trace output.
Only the map reference subprocess imports pypdfium2. PDF.js and its canvas backend
render the colour-channel grid and embedded-opacity page (tested on Node 22.23.5). Each renderer's
version is recorded with its evidence. A missing tool, PDF, placement or usable reference
keeps the full gate red. The two thumbnail streams have no page-content pixels to compare.

```sh
python3 -I Tests/differential/jpx/pages.py --selftest
python3 -I Tests/differential/jpx/pages.py --cache "$JPX_CACHE" \
  --only pike-jp2 --only pike-flate-jp2 --json /tmp/jpx-pike.json
```

`--only` takes exact PDF stems and labels the result `focused`. An existing Lean build
with the same Lake manifest can be used from a reference-only checkout via
`--build-root /path/to/built/safe-pdf`. The default worker in that build is
`.lake/build/bin/worker`. Use `--worker /absolute/path/to/worker` to measure an earlier
binary against the same references. The JSON includes the worker binary and catalog hashes,
page RGB hashes, image dictionaries, actual filter chains, object numbers and the two
region colour counts (exact up to 4,095). Temporary rasters and traces are removed after
each page.

## Placements and comparisons

The decoder manifest at `9a8880a` has **20 source PDFs, 46 object occurrences and
42 distinct JPX streams**. Counting only the primary `source_pdf` values gives 19 PDFs.
The twentieth, `pike-flate-jp2.pdf`, occurs in `also_in`. The adapter expands every alias,
scans the actual qpdf dictionaries and verifies each stream hash after undoing its filter
prefix. It uses the pinned package's extraction helpers without writing extracted streams.

`Tests/differential/jpx/placements.json` records only the placement audit. Page lists
are one-based in reading order. Each pair identifies the painted image object and its
half-open rectangle in top-left device coordinates. `page` means the transformed image
fills the view. Coordinates were derived from the hashed sources' image `Do` operators,
resource dictionaries, clipping and CropBox transforms. MuPDF's live trace checks the
paint count, source dimensions, device-space extent and external mask clips. One pixel
of rounding at a fractional clip edge is allowed in the trace check. The actual raster
comparison always uses the audited rectangle. For the grid and embedded-opacity page, PDF.js reports each image
paint's native dimensions and device rectangle. The gate requires one matching paint
and the reviewed RGB digest separately for each crop. A missing paint or changed crop
leaves its own mandatory reference gap. A page-wide diagnostic or dimension mismatch
invalidates the page.

| Source | What the gate measures |
| --- | --- |
| `pike-jp2`, `pike-flate-jp2` | Object 6 uses `/JPXDecode` and object 7 uses `[/FlateDecode /JPXDecode]`. Each comparison starts from its own source PDF. |
| `jpx_numcomps` | Six separate 100 × 100 placements. Objects 10, 11, 12 and 15 share bytes and have different colour/opacity dictionaries. Each gets its own row. |
| `issue5481` | Object 43 on pages 1 and 2 gets two comparisons. Page 3 paints object 5. |
| `S2` | Objects 17–22 each paint through a JPX soft mask (29–34). JPX object 35 masks the Flate image 24 in a 5 × 47 region. Two other Flate image paints are outside the JPX gate. Mask and base rows share one measured composite where appropriate. |
| `red_stamp` | Stamp annotation 14's normal appearance executes form 16, then form 17, then JPX image 18. The stamp covers the CropBox. At 36 dpi both renderers give 152 × 158. At 72 dpi they round the bottom edge differently. |
| `issue19326`, `issue19517` | Image 8 has an external RunLength soft mask in each document. Their 1 × 1 JPX objects 11 and 13, respectively, are page `/Thumb` entries. The gate checks those links and lists both as unpainted. |
| `jpx_smaskindata`, `jpx_subsampling`, PDFBox and remaining PDFs | Each direct paint has its own rectangle. The JSON includes `SMaskInData`, `Matte`, `ColorSpace`, and external `/SMask` references when present. |

The worker receives the document bytes with the production client, default decoder limits,
default layers, zero additional rotation and font substitution disabled. Both sides render
the CropBox on opaque white at 72 dpi, except the stamp at 36 dpi and the large map at
4.5 dpi. Width and height must agree exactly before any crop. Every placement must meet
the existing symmetric 3 × 3 neighbourhood tolerance of 32/255 per channel with at most
1% of **placement** pixels differing. A uniformly blank or placeholder-gray worker crop
fails against a distinguishable reference. A reference crop indistinguishable from blank
or placeholder gray is a coverage gap. [Metric implementation](../Tests/differential/pixels.py)

`outside_rgb_changed` flags exact RGB differences outside the union of audited rectangles.
For example, `S2` has additional page differences there. These do not affect the placement
score. A mismatch inside a rectangle can involve positioning, clipping, colour conversion
or opacity. The mask and base are evaluated together as the reader sees them. A flat gray
worker crop against a multicoloured reference provides direct evidence of a placeholder
regression. Diagnosing its pipeline stage requires the focused consumer tests.

## Baseline and reference coverage

On consumer `87bae91`, MuPDF 1.25.1 and PDF.js 4.10.38 (Node 22.23.5), the full gate
exited 1. Across 22 pages it reported 37 measured object/page rows covering 31 distinct
painted placements, eight rows with reference gaps, and two unpainted thumbnails.
Twenty-four measured rows produced a blank or placeholder region and 13 exceeded the
placement tolerance with several colours. The Debian MuPDF build reported unavailable ICC
support. Reference logs preserve this and the marked-content nesting warning on some PDFs.

References now cover all 45 painted object/page rows (39 distinct placements).
The map and six grid placements were measured against the pre-renderer worker with SHA-256
`d24cf255b3d8130adfc6e4e5875bbe52342373c365b719c8e28fe277d91627c2`.
The focused gate exited 1 with seven placeholder failures, zero reference gaps, and one
unpainted thumbnail. For `bug_jpx` object 15, the eighth historical gap, the
reference renderer receives a freshly constructed PDF containing the recorded 128 × 64
raw gray plane. A second reference changes the sample value to verify the placement.
The gate checks both RGB hashes and requires the worker to match the entire reference
page exactly. The baseline worker painted all 8,385 placement pixels gray. [Recorded-plane evidence](../Tests/differential/jpx/bug_jpx_recorded_plane.md)

Repeat the map and grid checks after a worker change with

```sh
"$JPX_TOOLS/venv/bin/python" -IB Tests/differential/jpx/pages.py --cache "$JPX_CACHE" \
  --pdfjs-dir "$PDFJS_DIST" --only issue19517 --only jpx_numcomps --json /tmp/jpx-focused.json
```

### Map at 4.5 dpi

PDFium 159.0.8149.0, from the pypdfium2 5.15.2 Linux AArch64 wheel (SHA-256
`dd46e93c0c3a73f6cea8489baff6d77a5d0759dd53fbbce0aeb49c91830176fc`), painted the
original one-image page at 1/16 scale on white. The source and image both span
12,608 × 16,806. The output was **788 × 1051, 21 colours**, RGB SHA-256
`685a011f41bdbbb15f28d60ff95ee989ee5937b98327879a491684648cf8ac1c`.
The bounded capacity probe started with 2,297,664 KiB of available memory and used
302,800 KiB peak RSS. It exited **0 in 0.20 s** with empty stderr. The gate uses a
1,024 MiB address-space limit, 45 CPU seconds, a 60-second wall timeout and an 8 MiB
file limit. Its JSON records the process result. The worker painted all 828,188 pixels
RGB (128,128,128), differing on 100%.

The orange palette has little variation, so nonwhite output alone gives weak evidence.
Object 8 uses an sRGB ICC profile and external mask 17. Independently expanding the
mask's RunLength packet counts gives 211,890,048 opaque samples. OpenJPEG 2.5.3
decoded the hash-verified image stream at reduction 4 into four unsigned 788 × 1051
PGX planes. The fourth was uniformly 255. At every display coordinate the absolute
difference between PDFium RGB and the first three independent planes was at most
(3,4,3) by channel. The gate checks the whole reviewed RGB digest and rejects a
flat worker map even within channel tolerance.

With the same 1 GiB address-space cap, MuPDF 1.25.1 exited 1 in 0.01 s with a tile
allocation diagnostic and a white 788 × 1051 image. Poppler 25.03.0 exited 0 with a
decode warning and a two-colour image. Ghostscript 10.05.1 exited 0 with a white
788 × 1050 image. All three outputs failed reference review.

### Colour-channel grid at 72 dpi

This PDF was introduced with PDF.js's handling of missing and nonstandard component
counts. PDF.js 6.5.438 with canvas 1.2.1 and Node 22.23.5 rendered the original at
**320 × 220**, with six image paints, empty stderr and no warnings. Page RGB SHA-256
was `84621961ad39f732a5da31c68acb613e571de58401d13efb6101f1cb7b4af1ba`.
ISO 32000-1 §7.4.9 requires the declared colour component count to agree with
the JPX colour data. Its default device spaces cover one, three or four channels.
Rows 11, 12 and 14 exercise the fixture author's reader recovery behaviour. Their
expected colours below describe that compatibility target. [PDF.js fixture change](https://github.com/mozilla/pdf.js/commit/a72eb1599fb7712ffd31c96656fc79464aaf9ba9) · [ISO 32000-1 §7.4.9](https://opensource.adobe.com/dc-acrobat-sdk-docs/pdfstandards/PDF32000_2008.pdf)

| Object | Expected RGB from the source's native sample planes | Reference colours | Gray worker pixels differing (of 10,000) |
| --- | --- | ---: | ---: |
| 10 | Two DeviceN tints A,B. Function 20 returns (A,B,0). | 1,024 | 10,000 |
| 11 | Bare two-channel stream, absent colour space. PDF.js displays A as opaque gray. | 32 | 7,500 |
| 12 | Four DeviceN tints requested, only A,B supplied. PDF.js pads C,D with zero. Function 21 returns (A,B,255−C). | 1,024 | 10,000 |
| 13 | Five DeviceN tints. Function 22 returns (A,B,E). | 1,024 | 10,000 |
| 14 | DeviceRGB with `SMaskInData 1` but only three samples. PDF.js uses opaque (A,B,C) over the blue rectangle. | 1,024 | 10,000 |
| 15 | DeviceGray A, straight opacity B, over blue. Output is (A·b,A·b,A·b+255·(1−b)), rounded to bytes, where b=B/255. | 948 | 9,640 |

For an independent check, OpenJPEG 2.5.3 decoded the three verified bare streams for
objects 10, 13 and 14 to PGX (`opj_decompress -i source.j2k -o native.pgx -threads 1`).
Each header was unsigned 8-bit, 32 × 32. Objects 11, 12 and 15 have the same stream
hash as 10. At the centre of **every** native sample cell in each audited 100 × 100
rectangle, all RGB bytes matched the table exactly (6 × 1,024 checks). For a native
coordinate i, the local display pixel is floor((i+0.5)·100/32), independently in x and
y. The gate pins the full 10,000-pixel digest for each object in `placements.json`.
In a control with the reviewed page on both sides, all six passed. Removing only
object 13's live paint record produced one mandatory gap and five passing comparisons.

MuPDF 1.25.1 omitted three grid paints. PDF.js 4.10.38 reported four undecodable
images. Ghostscript 10.05.1 emitted component warnings, left object 11 white,
and left objects 14 and 15 backdrop blue. Poppler 25.03.0 emitted JP2-header warnings
and produced colours inconsistent with the native-channel check. None supplied a
complete, warning-free grid reference.

### Embedded opacity and matte

The four images on `jpx_smaskindata` each contain two native RGBA samples. Page 1
paints them over a 50% gray background, enlarging each sample to a 15 × 30 rectangle.
The source omits `/Interpolate`. For mode 2, remove the PDF matte contribution from
the stored colour before compositing with the background. The default matte is black.
Mode 1 supplies straight colour. [PDF.js fixture and decoder change](https://github.com/mozilla/pdf.js/commit/f554d0c9c89b8e4bb837f2193c767f63ea8869a0)

| Object | Stored RGBA, left and right | Mode and matte | Expected RGB over gray, left and right |
| --- | --- | --- | --- |
| 5 | (128,255,128,128), (0,255,0,0) | 2, green | (192,192,192), (128,128,128) |
| 6 | (128,0,0,128), (0,0,200,255) | 2, black | (192,64,64), (0,0,200) |
| 7 | (128,128,255,128), (0,0,255,0) | 2, blue | (192,192,192), (128,128,128) |
| 8 | (255,0,0,128), (0,255,0,255) | 1 | (192,64,64), (0,255,0) |

Each recorded crop digest is the SHA-256 of 30 identical RGB rows, with each of the
two expected colours repeated 15 times. The pinned PDF.js renderer matches these
four digests and reports four 2 × 1 image paints. MuPDF 1.25.1 interpolates between
the samples and retains a visible matte tint on objects 5 and 7. It differs from the
analytic placements on 50%, 63.33%, 50% and 33.33% of pixels respectively under
the placement metric.

### Pikepdf control

The direct and Flate-prefixed pikepdf references had identical RGB SHA-256
`75e307fd8131df1986e26aed467476910fa8925b2e96da8b3e9e14d17016a0e6` and 1,220 colours.
Both worker outputs were solid RGB (128,128,128). Each comparison differed on 93.064% of
its region. As a positive reference control, PDF.js 4.10.38 and MuPDF 1.25.1 rendered the
direct PDF within tolerance, with zero differing pixels under the neighbourhood metric.
The following commands repeat that control using temporary files.

```sh
pdf="$JPX_CACHE/pdf-sources/pikepdf/pike-jp2.pdf"
tmp=$(mktemp -d)
mutool draw -q -b CropBox -r 72 -c rgb -F pnm -o "$tmp/mu.ppm" "$pdf" 1
node Tests/differential/jpx/pdfjs-page.mjs "$PDFJS_DIST" "$pdf" 1 1 "$tmp/js.png" 1
python3 -I Tests/differential/pixels.py --a "$tmp/js.png" --b "$tmp/mu.ppm"
rm -r "$tmp"
```

The built-in self-check rejects a 36-pixel placeholder on a 10,000-pixel white page and
accepts the correct placement when a pixel elsewhere changes. Both controls exercise the
comparator. Production JPX integration still needs a new full worker run.
