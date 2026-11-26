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
python3 -I Tests/differential/jpx/pages.py --cache "$JPX_CACHE" \
  --pdfjs-dir "$PDFJS_DIST" --json /tmp/jpx-pages.json
```

The Python scripts use the standard library. Install qpdf with JSON v2 support and MuPDF
with `mutool draw` PNM and trace output. For the DeviceN comparison, `PDFJS_DIST`
is an installed Node `pdfjs-dist` directory with its canvas backend. Each renderer's
version is recorded with its evidence. A missing tool, PDF, placement or usable reference
keeps the full gate red. The two thumbnail streams have no page-content pixels to compare.

```sh
python3 -I Tests/differential/jpx/pages.py --selftest
python3 -I Tests/differential/jpx/pages.py --cache "$JPX_CACHE" \
  --only pike-jp2 --only pike-flate-jp2 --json /tmp/jpx-pike.json
```

`--only` takes exact PDF stems and labels the result `focused`. The default worker is
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
comparison always uses the audited rectangle. PDF.js checks the image paint count and
renders its fixed DeviceN grid. Reference diagnostics that indicate a skipped or failed
decode invalidate the reference.

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

## Baseline and outstanding references

On consumer `87bae91`, MuPDF 1.25.1 and PDF.js 4.10.38 (Node 22.23.5), the full gate
exited 1. Across 22 pages it reported 37 measured object/page rows covering 31 distinct
painted placements, eight rows with reference gaps, and two unpainted thumbnails.
Twenty-four measured rows produced a blank or placeholder region and 13 exceeded the
placement tolerance with several colours. The Debian MuPDF build reported unavailable ICC
support. Reference logs preserve this and the marked-content nesting warning on some PDFs.

| Unmeasured placement | Evidence and next check |
| --- | --- |
| `bug_jpx` p1 obj 15 | The upstream corpus documents a native reference crash case. The gate verifies the source, stream identity and page resource, and records a mandatory gap before rendering. A separately vetted source-page reference and review are needed to extend coverage. |
| `issue19517` p1 obj 8 | Worker view is 788 × 1051. MuPDF cannot produce this reduced view of the 212 MP source within the default 1 GiB reference-process address space. On a suitably provisioned reference host, set `--map-reference-mib` to the available reference budget and repeat at the same view. |
| `jpx_numcomps` p1 objs 10–15 | MuPDF 1.25.1 omits three of six paints. PDF.js 4.10.38 reports four undecodable images. The gate rejects its partial page. Supply a PDF.js distribution that renders all six and review its output at 320 × 220. |

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
