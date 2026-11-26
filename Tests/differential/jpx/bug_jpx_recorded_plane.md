# Recorded-plane reference for `bug_jpx` page 1

The pinned decoder manifest at `9a8880a` identifies object 15 and records one
128 × 64 unsigned 8-bit plane of zeros. The package's `docs/corpus.md` records
exact agreement for all 8,192 samples through its raw and consumer APIs. This
reference uses that existing observation. Only safe-pdf's worker renders the
original source. The reference path uses qpdf JSON v2 with stream decoding off.

The page has a 612 × 792 point CropBox and MediaBox, zero rotation, default
graphics state, and one unmasked DeviceGray image. Its content saves state,
applies `[128 0 0 64 269.6739197 527.7081909]`, paints `/Im0`, and restores
state. The helper matches the source and encoded image hashes and checks the
catalog, page tree, resources, image dictionary and every content byte. It
serializes five fresh objects with the same page semantics, omitting the
catalog's outlines and metadata. Before rendering each temporary PDF it
reparses the entire object table and verifies every dictionary and both raw
streams. It also checks the serialized file for the original encoded payload.

At 72 dpi using MuPDF 1.25.1, the half-open rectangle `[269, 200, 398, 265]`
contains 8,385 black pixels on a white page. Changing the raw samples to 192
changes exactly those 8,385 pixels to RGB (192,192,192). Both full-page RGB
hashes are pinned in the helper. The baseline worker
`d24cf255b3d8130adfc6e4e5875bbe52342373c365b719c8e28fe277d91627c2`
painted all 8,385 pixels RGB (128,128,128), with zero differences outside.
The crop failed with 100% differing pixels. This measures one document, page,
image object, stream and placement.

## Consumer call

The harness selects this reference by verified source SHA-256. The report records the
source, stream, plane, content, verified PDF and RGB digests in `reference_provenance`.
It requires exact full-page agreement for this flat image because a one-pixel translation
can fit within the ordinary crop tolerance. Any reference error keeps the case red.

Run the focused tests with the source cache and package manifest available.

```sh
JPX_CACHE=/path/to/corpus/files JPX_MANIFEST=.lake/packages/jpeg2000/corpus/manifest.json \
  python3 -I Tests/differential/jpx/test_bug_jpx_recorded_plane.py -v
```
