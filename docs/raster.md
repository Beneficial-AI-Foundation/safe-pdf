# Raster output, pixel differential and page timing (task 7.4)

Plan.md §6 Phase 7 — exit M7: "≥ 95% of corpus pages within perceptual threshold; median
page < 100 ms compiled"; "Faithfulness: pixel-differential vs MuPDF/pdf.js (perceptual
diff)".

## Inspector view `raster`

    inspect --view raster [--json] FILE
    SAFEPDF_PAGE=N  SAFEPDF_DPI=D  SAFEPDF_RASTER_DIR=dir  SAFEPDF_RASTER_FORMAT=png

`SafePdf/Shell/Views/Raster.lean`. Every page (or page `N`) is rendered by the verified
full-page renderer `Core.Raster.Glyph.renderDocPage` at zoom `D/72` (default 72 dpi, as
`mutool draw`), CropBox as the visible area, the page's `/Rotate` applied, opaque white
background. Each page gets a fresh decoded-bytes budget (pages are independent, as in a
viewer). With `SAFEPDF_RASTER_DIR` each page is written as `page-N.ppm` (binary `P6`) or,
with `SAFEPDF_RASTER_FORMAT=png`, `page-N.png` (8-bit RGB, stored DEFLATE through
`Core.Filter.Deflate.zlibStored`, CRC-32 in the shell). `--json` prints per page
`{"page","width","height","dpi","ms","nanos","status","error","file"}` and a summary with
`medianMs`, `maxMs`, `totalMs`, `parseMs`.

**Timing.** `ms`/`nanos` is wall-clock time around the pure `renderDocPage` call (content
decode, display list with font advances, font programs, images, shadings, rasterisation,
compositing), evaluated in `IO.lazyPure` and matched in `IO` before the clock is read again.
File writing is excluded. The inspector is compiled (`leanc -O3`), so these are compiled
times. Process start-up is not included (see "Issues" below: it is ~1 s today).

## Comparator `pixels`

    python3 -I Tests/differential/run.py --comparator pixels [--files GLOB] [--dpi D]
        [--exclude GLOB] [--min-within P] [--json OUT]        # JSON key "pixels"
    python3 -I Tests/differential/pixels.py --selftest
    python3 -I Tests/differential/pixels.py --a OURS.ppm --b REF.pnm [--tol T] [--tau PCT]

Reference: `mutool draw -s t -r D -c rgb -F pnm -o ref-%d.pnm FILE` (MuPDF 1.25.1); `-s t`
gives MuPDF's per-page time (integer ms). Images are read by a stdlib PNM (P5/P6) and PNG
(8-bit, filters 0–4, zlib) decoder. Skips cleanly without `mutool`, or when mutool renders
no page (wrong password, unrecoverable file) or times out.

**Metric.** A pixel *differs* when, in some RGB channel, its value in one image lies
outside `[min − T, max + T]` of the 3×3 neighbourhood at the same position in the other
image, checked both ways; `T = 32` (of 255). The page metric is the percentage of differing
pixels; the page is **within** the perceptual threshold when it is `≤ τ = 1%`.

Why: the neighbourhood range absorbs what a reader does not perceive — anti-aliasing
differences on edges (an edge pixel's coverage lies between its neighbours' values in both
renderers), sub-pixel and 1-px placement differences (MuPDF quantises glyph origins in its
glyph cache), page-size rounding — and `T` absorbs smooth colour differences (gradient
steps, image resampling filters, colour conversion rounding). What remains are content
differences: missing/extra glyphs, wrong fills or colours, missing images, clips, offsets of
2 px or more (the self-test checks that a 1-px shift is absorbed and a 3-px shift is not).
`τ = 1%` of the page area: one missing 12 pt word at 72 dpi is ≈ 0.05%, a missing text
line ≈ 0.3%, a page of missing text 3–10%, a missing picture or background tens of percent;
measured CM/Times text pages that render correctly sit at 0.28–0.32% (residual glyph-edge
differences), missing Type 3 text at 8–9%. So "within" = looks the same at a glance; a page
above τ has a block-level defect. `pixels.py --tol/--tau` re-evaluate other choices;
`identical` (byte-equal) pages are counted too.

Size mismatches (rounding of the scaled CropBox) are handled by padding both images with
white to the larger size (top-left aligned); a difference of more than 1 px is counted as
`size_mismatch`. Pages are paired by number; a page only one side renders counts as not
within (`ours_failed` / `ref_missing`). Documents the core refuses to open are `known` and
their pages are reported separately ("of the pages of documents we open").

Corpus report: % pages within (all, and of opened documents), identical, failures, size
mismatches; page time ours (median / p95 / max) vs MuPDF (median / p95); the worst pages.

## Measurements (2026-11-20, this sandbox, aarch64, 72 dpi)

The corpus is not reachable from the sandbox (firewall); measured on every PDF under
`Tests/` and on generated pdfTeX pages (`Tests/differential/fixtures/gen_tex_pages.py`).

**`Tests/**/*.pdf`** (71 files, `Tests/adversarial/xobject-fanout.pdf` excluded: mutool
explodes on it; 15 skipped because mutool renders nothing — wrong password, no startxref,
no version marker, …): 65 pages compared, **42 within (64.6%)**, 16 byte-identical; of the
57 pages of documents we open, 73.7%. **Every page we render is within τ** (worst 0.59%,
`Tests/golden/text/latin.pdf`, non-embedded Helvetica drawn by MuPDF only); all 23 pages
outside are pages we deliberately refuse: decompression bombs (`limitExceeded`), reference
cycles (`/Length`, `/Prev`, object stream, `/Kids`), `Tests/golden/pages/shared.pdf`
(shared `/Kids` treated as a cycle), `Tests/golden/pages/tree.pdf` p5 (a dangling kid: we
have 4 pages, MuPDF 6), `Tests/golden/text/unicode.pdf` p3 (deliberately broken zlib).
Page time ours: **median 3.1 ms**, p95 9.8 ms, max 12.3 ms.

**pdfTeX pages** (7 files, 23 pages): **21 within (91.3%)**, at 144 dpi also 91.3%.

| file (pages) | worst % differing | our time per page (72 dpi) | MuPDF |
|---|---|---|---|
| text, CM Type 1 (8) | 0.31 | 205–226 ms (last, short page 18 ms) | 1–3 ms |
| type3, T1 fontenc bitmap fonts (2) | **9.1 (outside)** | 12–15 ms | 1 ms |
| times, Nimbus Type 1 (6) | 0.32 | 202–222 ms | 1–3 ms |
| math, CM (2) | 0.19 | 118–125 ms | 1 ms |
| vector, 400 paths (1) | 0.00 | 128 ms | 3 ms |
| image, PNG Flate (2) | 0.06 | 13–52 ms | 1 ms |
| mixed (2) | 0.20 | 73–90 ms | 1 ms |

Median page 205 ms (72 dpi) / 230 ms (144 dpi): the time hardly depends on the resolution,
it is per-glyph / per-segment geometry, not pixels.

**M7 status from these samples**: the faithfulness half holds wherever the content is
supported (every rendered page within τ); the failures are Type 3 fonts and deliberate
refusals. The timing half (**median < 100 ms**) is **not met on text-heavy pages**
(≈ 210 ms); see issue 1.

## Issues found (Core; not fixed here — other tasks own the files)

1. **Glyph geometry in `Rat` dominates text pages.** gdb stack sampling of `inspect --view
   raster` on the CM text page: 19 of 30 samples in `Glyph.outlineToD` → `segToD` →
   `Geom.Aff.apply` → `Rat.mul` / `Nat.gcd` / bignum `mpz` (the glyph matrix
   `gs.matrix g * glyphPlacement r tx * rm` has denominators ~10¹²+, every outline point
   is a `Rat` multiply-add with gcd normalisation), ~6 in `Fill.fillEdgesCounted`.
   Suggested fix (owner of `Core/Raster/Glyph.lean`): convert the per-glyph matrix once to
   fixed-point integers (as `Fill.ofContentPath` does for page paths) and transform outline
   points with `Int`/`Int64` arithmetic; or cache device paths per (glyph, matrix-without-
   translation) and add the translation in integers. Expected: text page ≈ 70 ms.
2. **Inspector start-up ≈ 1.0 s** (`inspect --help` takes 1.04 s): gdb shows the time in
   `initialize_…SafePdf_Core_Filter_LZW` → `LZW.pack` — the test constants `longCodes`,
   `bomb`, `wideCodes` (private top-level defs used by `#guard`s) are closed terms the
   compiler evaluates at module initialisation, on every program start (inspector, tests,
   fuzz). Fix: make them functions of `Unit`, or move them into `Tests/`.
3. **Type 3 fonts draw nothing** (known: charprocs are not run). pdfTeX with `T1` fontenc and
   no cm-super produces bitmap Type 3 fonts: 8–9% of the page differs.
4. Stroking dominates the vector page (`Stroke.strokeSubs`/`solidSub`/`quadPts`), 128 ms for
   400 paths — in budget, but the next hot spot after 1.
5. Known, by design: non-embedded fonts draw nothing (MuPDF substitutes base-14 fonts), DCT
   images are placeholders, shared `/Kids` are a cycle, page numbering differs from MuPDF
   after a dangling kid.
