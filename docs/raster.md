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

## Substitute fonts for non-embedded fonts (task 7.7)

A font without an embedded program (the standard 14, `/Arial`, `/TimesNewRoman`, any other
non-embedded simple font, the "hail mary" font of a `Tf` naming no font) is painted with the
substitute MuPDF 1.25.1 would use, **when a substitute program is found on the system**.
Nothing is committed: the repository is MIT, the fonts are not (URW base-35: AGPL-3.0 with a
font exception; TeX Gyre: GUST font licence). Ledger Decisions 2026-11-20 (7.7).

**Where they come from** (`SafePdf/Shell/Fonts.lean`, first readable candidate per face wins;
every path is fixed or one level of a sorted directory listing — nothing is searched
recursively):

1. `SAFEPDF_FONT_DIR` (a directory, or several separated by `:`), with the URW file names
   (`NimbusSans-Regular`, `NimbusSans-Bold`, `NimbusSans-Italic`, `NimbusSans-BoldItalic`,
   `NimbusRoman-*`, `NimbusMonoPS-*`, `StandardSymbolsPS`, `D050000L`) or the TeX Gyre names
   (`texgyreheros-regular`, …, `texgyretermes-*`, `texgyrecursor-*`), extension `.t1`,
   `.pfb`, `.pfa`, `.otf` or none;
2. URW base-35 — Debian/Ubuntu package **`fonts-urw-base35`**:
   `/usr/share/fonts/type1/urw-base35/*.t1`, `/usr/share/fonts/X11/Type1/*.pfb`,
   `/usr/share/fonts/opentype/urw-base35/*.otf`; then Ghostscript's `Resource/Font` (URW
   names, no extension) under `/opt/homebrew/share/ghostscript` (Homebrew, Apple silicon),
   `/usr/local/share/ghostscript` (Homebrew on Intel, source builds) and
   `/usr/share/ghostscript`: first the unversioned `Resource/Font`, then each version
   directory `<ver>/Resource/Font` (Homebrew's layout), newest version first (`10.05.1`
   before `10.04.0` before `9.56.1`);
3. TeX Gyre (Heros, Termes, Cursor `.otf`; no Symbol or Dingbats) — `fonts-texgyre`:
   `/usr/share/texmf/fonts/opentype/public/tex-gyre`, `/usr/share/fonts/opentype/texgyre`;
   Homebrew `/opt/homebrew/share/fonts`, `/usr/local/share/fonts`; MacTeX
   `/Library/TeX/Root/texmf-dist/fonts/opentype/public/tex-gyre`, then
   `/usr/local/texlive/<year>/texmf-dist/fonts/opentype/public/tex-gyre` (newest year first);
4. the macOS font folders `~/Library/Fonts` then `/Library/Fonts` (where Font Book installs):
   the URW names (`.otf`, `.t1`, `.pfb`, `.ttf`), then the TeX Gyre names (`.otf`);
5. **the macOS system fonts** (task 9.r7) — always present on a stock Mac, so this is what
   the human's Mac uses unless one of the above is installed:

   | Standard 14 | First choice (face by PostScript name) | Then (single `.ttf`) |
   |---|---|---|
   | Helvetica, -Bold, -Oblique, -BoldOblique | `/System/Library/Fonts/Helvetica.ttc` faces `Helvetica`, `Helvetica-Bold`, `Helvetica-Oblique`, `Helvetica-BoldOblique` | `Arial.ttf`, `Arial Bold.ttf`, `Arial Italic.ttf`, `Arial Bold Italic.ttf` |
   | Times-Roman, -Bold, -Italic, -BoldItalic | `/System/Library/Fonts/Times.ttc` faces `Times-Roman`, `Times-Bold`, `Times-Italic`, `Times-BoldItalic` | `Times New Roman.ttf`, `… Bold.ttf`, `… Italic.ttf`, `… Bold Italic.ttf` |
   | Courier, -Bold, -Oblique, -BoldOblique | `/System/Library/Fonts/Courier.ttc` faces `Courier`, `Courier-Bold`, `Courier-Oblique`, `Courier-BoldOblique` | `Courier New.ttf`, `… Bold.ttf`, `… Italic.ttf`, `… Bold Italic.ttf` |
   | Symbol | — | `Symbol.ttf`, then `Apple Symbols.ttf` |
   | ZapfDingbats | — | `ZapfDingbats.ttf` |

   A single `.ttf` is looked for in `/System/Library/Fonts/Supplemental/` (macOS 10.15+),
   `/Library/Fonts/` (older macOS, Office installs) and `/System/Library/Fonts/`, in that
   order. In a collection the face is the one whose `name` table PostScript name (name ID 6)
   is exactly the standard name (`Core.Font.TrueType.faceByPsName?`); a collection without it
   is skipped, never guessed by index.

`SAFEPDF_SUBST_FONTS=0` disables substitutes (the behaviour before 7.7; used for before/after
comparisons). **`SAFEPDF_SUBST_FONTS=report`** prints on stderr, when the inspector or the
viewer loads the table, one line per standard-14 name: `subst: Helvetica-Bold <-
/System/Library/Fonts/Helvetica.ttc #1`, `… (does not parse)` when the chosen face fails to
parse, or `subst: Symbol <- none (unpainted)`. A face that is missing, unreadable (or over
32 MB) or does not parse is absent: its text stays unpainted, nothing fails. The inspector's
`raster` view and the viewer both load the table once per process (a collection file is read
once for all its faces); each face is parsed (Type 1 parser, the CFF parser on an OpenType
file's `CFF ` table, or — task 9.r7 — the TrueType parser on a `.ttf` or on one face of a
`.ttc`, `Font.TrueType.parseAt`) the first time a page needs it, inside that page's timed
render (≈ 10 ms per face). CI needs `apt-get install fonts-urw-base35` for the painting checks
of suite `raster-subst` against MuPDF (without it they skip); the collection and macOS-search
checks of task 9.r7 always run (generated fixtures, below).

**TrueType substitutes and collections** (task 9.r7). A collection (`'ttcf'` header: version,
`numFonts`, one offset per face; at most 64 faces read) is parsed face by face: each face's
offset table lies inside the file and its table offsets are absolute, so `parseAt bytes dir`
is the ordinary TrueType parser started at that face's offset table (`parse` = `parseAt … 0`
still refuses a collection as an embedded program). A face with CFF outlines (`'OTTO'`) inside
a collection goes to the CFF parser. Glyph choice for a TrueType substitute: the encoding's
glyph name in `post` (format 2), else its Unicode value (Adobe Glyph List, then the
ZapfDingbats list) in a Unicode `cmap`; a code without a usable name: its name in the face's
standard-14 built-in encoding (`StandardEncoding`, Symbol's, ZapfDingbats'), else the raw code
in the symbolic `cmap`s ((3,0) with `0xF000`… offsets, (1,0)). Widths are never taken from the
substitute: standard-14 fonts keep their AFM widths, `/Widths` win as before, and only MuPDF's
`ft_stretch` case scales glyphs (by the TrueType advance).

**Caveats of the macOS faces** (measured on macOS 26, MuPDF 1.28.6, task 10.15).
Apple's `Helvetica.ttc`, `Times.ttc` and `Courier.ttc` are licensed versions of the designs
the standard 14 are named after, so their advances should agree with the AFM widths we
position by — and positions never come from the substitute anyway (AFM widths or `/Widths`),
so lines, columns and table cells stay where they are on Linux. Outlines differ in detail from
URW Nimbus (MuPDF's bundled clones), so a pixel diff against MuPDF on a Mac is not 0% as it is
with URW. Apple's Courier is a much *heavier* stroke than Nimbus Mono PS: on the fixture
`Tests/fixtures-subst/subst.pdf` the Courier line (baseline y = 160) has ink 791 px with
`Courier.ttc` against MuPDF's 556 px with its bundled Nimbus Mono PS, same column extent;
MuPDF itself, given `Courier.ttc` embedded (`mutool create`, `%%Font F4
/System/Library/Fonts/Courier.ttc`), paints 801 px — so the difference is the face, not our
rasteriser. Helvetica / Times lines are within 0–3% (893 vs 871, 643 vs 649). Suite
`raster-subst` therefore compares with `mutool` only when every needed face is a URW base-35
file (file name `NimbusSans-Regular…`, `isUrwFile`), and otherwise prints which faces are not
and skips that comparison. Arial / Times New Roman /
Courier New (fallbacks) are metric-compatible but differently drawn. Symbol: Apple's
`Symbol.ttf` is reached by `post` name, Unicode (Glyph List) or raw code; `Apple Symbols.ttf`
(last resort) is Unicode-only and may lack some Symbol glyphs (e.g. bracket pieces).
ZapfDingbats: by Unicode value (`a1` → U+2701, …) or raw code. If a system face uses `post`
format 2.5/3.0 (no names) the Unicode path still finds the glyphs. Hinting is never run (as
for every TrueType font here).

**Checking it on a Mac** (source build, Homebrew Tk; no Ghostscript or TeX installed):

1. `SAFEPDF_SUBST_FONTS=report .lake/build/bin/inspect --view raster --json receipts.pdf
   > /dev/null` — the stderr lines should name `Helvetica.ttc #0…#3`, `Times.ttc`,
   `Courier.ttc`, and none should say `(does not parse)`; Symbol / ZapfDingbats show which
   file was taken or `none`. (The same lines appear when starting the viewer with
   `SAFEPDF_SUBST_FONTS=report`.)
2. Reopen the receipts PDF in the viewer: the page-1 table text (non-embedded Helvetica and
   Helvetica-Bold) must be painted, bold headers visibly bolder, columns aligned.
3. Reopen the M9 paper saved with a FreeText ("Add text") mark: the "M9 text" must be painted
   by the renderer from its appearance stream (since 9.r5 the canvas draws it itself only when
   no Helvetica substitute loads, so with a substitute it must still show — before any click,
   at every zoom and rotation).
4. Optionally `SAFEPDF_RASTER_DIR=/tmp/r SAFEPDF_RASTER_FORMAT=png …inspect --view raster
   receipts.pdf` and look at `/tmp/r/page-1.png`; and `SAFEPDF_SUBST_FONTS=0` to confirm the
   text disappears without substitutes (the old behaviour).
5. Report the `subst:` lines if any face is `none` or `(does not parse)`.

The fixtures for this (nothing of Apple's is committed): `python3 -I
Tests/fixtures-subst/make_ttc.py synthetic` writes `Tests/fixtures-subst/mini.ttc` (four box
faces named Helvetica, Helvetica-Bold — that one with a Macintosh-platform name record —
Times-Roman, Times-Bold; face `i`'s box `100·(i+1)` units wide) and `mini.ttf`
(`CourierNewPSMT`); `make_ttc.py merge OUT A.ttf B.ttf …` builds a collection from real
fonts. Suite `raster-subst` (`runMac`) checks the header, the PostScript names, face parsing,
the search below a temporary root (`SearchConfig.root`: `System/Library/Fonts/*.ttc`,
`Supplemental/Courier New.ttf`, a collection without `Courier` skipped; Ghostscript version
directories newest first; `~/Library/Fonts` before the system fonts), the fixture page painted
with the macOS faces (Helvetica-Bold darker than Helvetica: the right face), and, when python3
and DejaVu Sans are installed, the page painted from a collection of DejaVu Sans + Bold.

**Which substitute** (`SafePdf/Core/Raster/Subst.lean`, MuPDF `pdf-font.c`):
`pdf_clean_font_name`'s exact table (standard names; `Arial`, `ArialMT`, `Arial,Bold`,
`TimesNewRoman…`, `CourierNew…`, `SymbolMT…`; spaces ignored, no subset-tag stripping) gives
a built-in face; a font without `/FontDescriptor` and an unknown name gets Times-Roman; a
descriptor without an embedded program and an unknown name gets `pdf_load_substitute_font`'s
face from `/Flags` (FixedPitch → Courier, Serif → Times, else Helvetica; Italic flag or
`Italic`/`Oblique` in the name; ForceBold flag or `Bold` in the name — MuPDF 1.25.1 ignores
`/FontWeight` and `/StemV`). Glyphs by name through the font's encoding (implicit base: the
substitute's built-in encoding), else the code's glyph in the built-in encoding. Advances stay
the PDF's (`/Widths` or the standard-14 AFM widths, as before); only for the last case
(MuPDF's `ft_stretch`) each glyph is scaled horizontally to its PDF width
(`fz_adjust_ft_glyph_width`). Not substituted: non-embedded CIDFonts (`/Type0`: MuPDF uses CJK
fonts or a Unicode-mapped substitute), embedded programs our parsers reject.

Measured (72 dpi, `pixels.py`): the human's receipts page (non-embedded Helvetica,
Helvetica-Bold, WinAnsi) 4.70% → 0.0002% differing pixels; the 7-font fixture
`Tests/fixtures-subst/subst.pdf` 0.0000% with URW (`.t1` and `.otf`), 0.08% with TeX Gyre.

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

## Render-time tail (task 7.9)

    python3 -I scripts/corpus/timing.py [--files GLOB] [--dpi D] [--top N] [--jobs J]
        [--file-timeout S] [--page-timeout S] [--json OUT] [--compare OLD.json]

One `inspect --view raster --json` process per file (the view times every page); a file run
over the timeout is killed and its remaining pages are run one process per page; a page
still over the page timeout counts as `timeout` with the timeout as its time (a lower
bound). Prints median / p95 / p99 / max, the pages over 500 ms and 5 s, and the slowest pages
(`--compare`: with their earlier time).

**Measured** (2026-11-20, aarch64 sandbox, 72 dpi, all 81 corpus files, 2,450 pages,
`--jobs 2` on a shared machine: ±10% noise):

| build | median | p95 | p99 | max | > 500 ms | > 5 s |
|---|---|---|---|---|---|---|
| d575fd9 (before) | 81 ms | 4,115 ms | 6,449 ms | 44,525 ms | 357 | 59 |
| 7.9 (this branch) | 77 ms | 2,927 ms | 4,386 ms | 5,967 ms | 349 | 7 |
| 7.9 + `Text.lean` width-table patch (below) | 64 ms | **262 ms** | 826 ms | **4,417 ms** | 54 | 0 |

The rendered pixels are byte-identical before and after (every page's PPM hashed, all three
builds). The target (p95 ≤ 500 ms, max ≤ 5 s) is met only with the `Text.lean` patch, which
belongs to task 6.8e's file in wave 44.

**What the tail was** (perf on the compiled inspector; `perf` needs
`LD_PRELOAD=/lib/aarch64-linux-gnu/libtinfo.so.6` in this sandbox):

1. **TrueType advance table recomputed per glyph** (`Text.buildFontDict`): `let tbl :=
   ttWidthTable …; fun code => tbl.getD code 0` inside a function-typed `match` is
   eta-expanded by the compiler, so every `codeAdvance` rebuilt the 256-code table (256 cmap
   look-ups + AGL linear searches, ~1 ms). Simple TrueType fonts whose `/Widths` leave codes
   unknown (Word-made NTSB reports, several arXiv papers): 300 pages of 2–11 s. Fix
   (`Text.lean`, not in this branch): make the table a data value (`Option (Array Fixed)`)
   and match on it in `width`; 1409.0003 p14 4,022 → 72 ms. This branch tabulates the
   one-byte advances once per page for the renderer's own layout (`Glyph.tabulateWidths`),
   which halves those pages; text extraction still pays per glyph.
2. **Knockout groups copied page buffers per pixel and per element** (matplotlib scatter
   plots: every `B` with `CA < 1` is a knockout group, 21,878 on 2307.09288 p25):
   `knockPx` read `dest` after writing it (three page copies per pixel; fixed by reading
   first), `fillBuf` appended rows to an unreserved buffer (quadratic), and each element made
   three page-size buffers. Now: lazy knockout frames (`Transparency.knockL`: patches instead
   of a page copy; elements shaped and merged over their bound in reused scratch buffers),
   stroke bounds from the pen's reach (`Clip.strokeBound`, so a stroke's bound is no longer
   its clip), the last stroke mask reused (`Clip.RState.smemo`: the element is painted
   three times), the clip cache evicts the least recently used entry (the axes clip shared by
   every marker was evicted every 16 markers). p25 44.5 s → 4.4 s, p64 6.6 s → 0.7 s,
   1807.06209 p61 9.9 s → 0.16 s.
3. **Pen geometry per stroke** (`Stroke.Geo.make` over `Rat`, ~20 µs; 1303.5076 p21–23 have
   200,000 strokes): the chord count in integers (`arcCountGoI`, `arcCount_eq`), the pen's
   circle table rounded in integers (`circleTableI`, `#guard` = the `Rat` table for every
   `m ≤ 64`; the `Rat` table only for the reference stroker), and a per-page table of
   geometries by CTM linear part and width (`Stroke.GeoTable`, `Clip.tableStroke`).
   6.5 s → 1.8 s.

**What remains above 500 ms** (54 pages with the patch; none above 5 s):

* 2307.09288 p25 (4.4 s): half is text extraction of 21,879 form XObjects, each `Do`
  decoding the same Flate stream again (`Content/Run`: a per-page cache of decoded form
  streams would remove ~2 s); the rest is three stroke renders per marker (`Stroke.mkSeg`).
* Long polylines and dense strokes (2210.00002 p30/31/36 1.5–2.7 s, 1303.5076 p21–23
  1.4–1.8 s): `Stroke.mkSeg` per chord (`sqrtQ` and grid divisions on bignum common
  denominators) and the scanline fill. Task 7.9c (below) moved `mkSeg` to 64 bits.

### 64-bit chord geometry (task 7.9c)

`Stroke.mkSeg` now tries `mkSegW` first: the same formulas as the exact path
(`mkSegExact`, the 7.2i code) in `UInt64`/`Int64`: `|u|²` from the pen's 64-bit inverse map
(`IMatW`), its normalisation by `gcd64`, the 128-bit radicand `mul128`, the digit-by-digit
root `isqrtW` (`⌊√(Y·2⁴⁰)⌋` for `Y < 2⁸²`), the length as a `Rat` built from a 64-bit gcd
(`ratW`), and the six grid values as `roundDivI(±A·2³⁶, B)` by chunked long division
(`rdiv36`). 64-bit arithmetic wraps; every operation sits under a run-time range guard that
is the hypothesis of a kernel theorem (`mulW_toNat`, `mul128_eq`, `isqrtW_eq`, `gcd64_eq`,
`rdiv36_eq`, `lin64_toInt`, `abs64_toNat`, `IMatW.of_ok`, `ratW_eq`), so within the guards
nothing wraps; outside them (large denominators, huge chords) it falls back to
`mkSegExact`. The composition is tested: `raster-stroke-spec` compares `mkSeg`,
`mkSegExact` and `mkSegSpec` on 16,000 chords (≥ 5,000 on the 64-bit path; 0 mismatches)
plus 3,000 kernel cases. On the slow pages 76–89% of chords take the 64-bit path
(fallback: `|u|²` radicand ≥ 2⁸² or divisors ≥ 2⁶²); `mkSeg` went from ~31% of
2210.00002 p31's time to ~8%.

| page (72 dpi, sequential) | before | after |
|---|---|---|
| 2210.00002 p30 | 1,384 ms | 1,046 ms |
| 2210.00002 p31 | 2,241 ms | 1,658 ms |
| 2210.00002 p36 | 2,418 ms | 1,702 ms |
| 1303.5076 p21 | 1,227 ms | 1,014 ms |
| 1303.5076 p22 | 1,624 ms | 1,316 ms |
| 1303.5076 p23 | 1,784 ms | 1,587 ms |

Full corpus (`timing.py --jobs 2`): median 64.8 → 66.2 ms, p95 247 → 246 ms, max 3.9 → 4.2 s
(2307.09288 p25, unchanged code path: noise), 41 → 44 pages over 500 ms (noise on the other
pages); all 2,450 page PPMs byte-identical before and after. What remains on these pages is
the scanline fill (`Fill.fillEdgesCounted`, ~50% of 2210.00002 p31) and text extraction
inside `renderDocPage` (`Text.extractDocPage`, 26–39%).
* Image decoding at full resolution (2112.10752, 2006.11239, 2501.12948, 2005.14165:
  0.7–1.4 s): JPEG (`Quarantine/DCT`, MuPDF decodes at reduced size, task 7.6d), Flate
  (Adler-32, `Filter`), and per-sample `ByteArray.push` in `Image.samplesLoop`/`blockRow`.

## Reduced-size JPEG decoding (task 7.10)

`arxiv-2501.12948` p16 differed 26.2% from MuPDF (the only corpus page above 1.81%): its
figure is one 11881 × 7646 RGB `/DCTDecode` image drawn 453 × 292 pt. The full decode needs
272.5 MB of output (and ≈ 136 MB of planes), above `Limits.maxDecodedStreamBytes` (256 MiB),
so `decodeDCT` failed and the figure was the grey placeholder; the failed attempt still peaked
at ≈ 1.2 GB RSS. MuPDF never decodes it at full size: `fz_get_pixmap_from_image` picks
`l2factor` = the largest `l ≤ 6` with `w >> l ≥ ⌊device width⌋ + 2` (same for heights; here
4), and for JPEG passes up to 3 of it to libjpeg (`scale_num = 8 / 2^l`), which decodes at
1/8 through its scaled IDCTs.

* `Quarantine/DCT.lean`: `decode … (scale := k)` is libjpeg's reduced decode: output
  `⌈w / 2^k⌉ × ⌈h / 2^k⌉`, per-component scaled block sizes as `jpeg_calc_output_dimensions`
  (`scaledSize`: 4:2:0 chroma needs no upsampling at a reduced scale), the `jidctred.c`
  transforms (`idctScaled`: 4 × 4, 2 × 2, 1 × 1), no fancy upsampling at 1/8. Bit-exact
  against `djpeg -dct int -scale 1/2^k` on 17 fixtures × 3 scales (suite `dct`). A progressive
  frame kept its full-size coefficient buffer (8 bytes per coefficient) until task 8.6.
* `Raster/Image.lean`: `imageExtents` (largest squared device extents of each image XObject
  over its page/annotation uses at the render's zoom; images also used in tiling cells or
  Type 3 glyphs are excluded), `l2Factor` (MuPDF's rule in exact arithmetic), `dctScale`;
  `Glyph.renderDocPage` passes the extents to `loadImages`. Not reduced (until 8.6, below): soft masks, images
  whose soft mask has a `/Matte` (MuPDF), inline images.
* **One step less than MuPDF** (`dctScale l = min 3 (l − 1)`): with MuPDF's own factor, 15 of
  the 21 other changed pages of the sample got slightly worse (`arxiv-1105.2345` p8, a
  noise-like sky map drawn at 0.36 of its size: 0.78% → 1.08%, outside τ), because MuPDF
  finishes the reduction with a tent filter and our placement with an area-averaging box
  filter, which barely smooths below two samples per device pixel. With one step less the
  box filter always averages ≥ 2 samples per pixel; the corpus image still decodes at 1/8.

Measured (72 dpi; 11 corpus files, 316 pages; before = 29b1a74):

| | before | after |
|---|---|---|
| 2501.12948 p16 | 26.24% | **0.36%** |
| 2501.12948 (86 pages) | 85 within, worst 26.24% | 86 within, worst 0.67% |
| p16 render time | 1,041 ms | 393 ms |
| p16 peak RSS, 72 / 150 dpi | 1,220 / 1,213 MiB | 81 / 123 MiB |

Every page PPM of the 10 other files (2010.11929, 1810.04805, cond-mat_0410550, 1602.03837,
1105.2345, ntsb MIR2301, ntsb AAR1201, 2412.19437, 1512.03385, 1706.00001) was hashed before
and after: 8 pages changed, all with downscaled JPEGs, all within τ, each by at most
+0.03 points (`pixels.py`: 1105.2345 p5 0.193 → 0.205%, 1602.03837 p3 0.393 → 0.394%,
p4 0.427 → 0.429%, p2 identical %, 2010.11929 p21 0.226 → 0.219%, 2412.19437 p47
0.243 → 0.256%, 2501.12948 p43 0.364 → 0.389%, p44 0.244 → 0.246%).

## Memory bound for huge images (task 8.6)

M8 (`docs/viewer-corpus.md`) bounds the peak RSS at 1 GiB per file. After 7.10 the remaining
risks were: a progressive JPEG's full-size coefficient buffer, Flate/LZW/raw images decoded and
converted at full size (decoded stream + sample buffer + RGBA ≈ 3.3 bytes per RGB sample), the
images 7.10 did not reduce, and the grey placeholder whenever a full-size decode was over
`maxDecodedStreamBytes`.

* **Progressive coefficients** (`Quarantine/DCT.lean`, `CLay`): stored as 16-bit values in a
  `ByteArray`, and only the positions the component's (scaled) IDCT reads keep their value —
  64 at full size, 49 at 1/2, 25 at 1/4, the DC at 1/8; every other position keeps one
  nonzero bit, which is all AC refinement needs (a correction never zeroes a nonzero
  coefficient for `Al ≤ 13`). Bytes per block: 128 / 106 / 58 / 10 (was 512 at every scale).
  Bit-exact on every progressive fixture of suite `dct` (incl. the scaled references).
  The plane and coefficient buffers are no longer built with `ByteArray.mk (Array.replicate
  n v)`, which first allocates a boxed `Array UInt8` (8 bytes per byte).
* **Row-by-row conversion, decoded at the drawn size** (`Raster/Image.lean`, `Src`, `fused`):
  no image-size sample or RGBA buffer; an image drawn smaller than its size is box-filtered
  while decoding to exactly the size, blocks and rounding the placement's `boxDown` would use
  (`Extent.t`: `⌈√…⌉` of the grid-fitted device extents of the largest use, computed by
  `imageExtents` through the page → device matrix), with colour key, masks (on `withMask`'s
  grid) and `/Matte` applied per pixel in the old order. One output row needs one source row
  of the image and of its mask plus `tw` running sums. The placement then finds the pixmap at
  its target and paints the same pixels. JPEGs keep 7.10's reduced libjpeg decode before
  that. Soft masks and `/Mask` stencils take part in the same pass; inline images use the
  target of their one use.
* **Retry instead of the placeholder**: a JPEG over the limit (planes, coefficients or output,
  checked at the frame header) is decoded again at the next scale, up to 1/8; a pixmap whose
  RGBA would exceed `maxDecodedStreamBytes` is decoded at the first `⌈n / 2^j⌉` that fits
  (`fitTarget`). The page's image budget `maxPageImagePixels` is now 2²⁶ pixels (256 MiB of
  RGBA, was 1 GiB) and each image is decoded under what is left of it (reduced to fit).
* **Not reduced** (full size, as before; the retry still applies): images also drawn in tiling
  cells or Type 3 glyphs (cell/glyph matrices, not page matrices; Type 3 images go through
  MuPDF's stencil scaler). **Still full size in memory**: the decoded filter output of an
  XObject and of its soft mask (`Source.decode`; the byte filters are not streaming, and
  Flate's output grew by doubling, so a 144 MB stream peaked near 2× — reserved once since
  task 8.10, below).

Pixels (72 dpi, all 81 corpus files, 2,450 page PPMs hashed before = eb78544 and after):
**2,445 pages byte-identical**; the 5 others (1810.04805 p3, p15; 2112.10752 p1; 2412.19437
p16; cs_0410012 p3) draw one image at two sizes — the smaller use is now box-filtered twice —
and change by at most +0.004 points (`pixels.py`: worst 2412.19437 p16 0.395 → 0.399%), all
within τ. (A first version that averaged `2^k × 2^k` blocks while decoding, as MuPDF's
`fz_subsample_pixmap`, changed 70 pages, 49 of them worse by up to +0.19 points and
ntsb-AAR0701 p157 to 1.02%, outside τ: the double box filter blurs; it was dropped.)

Peak RSS of `inspect --view raster` (whole file, 72 dpi, `Tests/differential/peak_rss.py`;
the five corpus files with the largest images):

| file (largest image) | before | after |
|---|---|---|
| arxiv-2501.12948 (11881 × 7646 JPEG) | 87 MiB | 73 MiB |
| ntsb AAR0501 (5464 × 5050 Indexed Flate) | 207 MiB | 98 MiB |
| arxiv-2005.14165 (4568 × 4248 RGB Flate) | 323 MiB | 197 MiB |
| arxiv-2307.09288 (5215 × 2605 JPEG, 4096 × 1644 Flate) | 172 MiB | 126 MiB |
| arxiv-2401.00001 (4592 × 2250 RGB Flate) | 195 MiB | 116 MiB |

Render times unchanged (same totals within noise). Generated stress files (scratch, not
committed): an 8192 × 6144 4:2:0 progressive JPEG drawn 400 × 300 pt — before: the grey
placeholder (coefficients over the limit), 26 MiB; after: decoded at 1/8, 65 MiB, 1.3 s; an
8000 × 6000 RGB Flate image drawn 400 × 300 pt — 515 → 413 MiB (what remains is the 144 MB
decoded stream and its growth).

## Remaining memory peaks (task 8.10)

* **Filter output reserved once.** `Flate.inflateAt`/`zlibDecode`/`flateDecode` take an
  optional `cap`, the capacity of the output buffer (`ByteArray.emptyWithCapacity`); before,
  the output grew by doubling from empty, and each reallocation copied it while the old buffer
  was still alive (a 144 MB stream peaked near 2×). `Filter.decodeStream`/`decodeStreamB`
  read the stream's `/DL` (ISO 32000-2 Table 5, the decoded length, a hint;
  `declaredLength`) and hand it to every stage; a Flate stage reserves `flateCap`: `/DL` plus
  one tag byte per row when a PNG predictor follows, at most the stage's (budget-capped)
  limit and `2048 · input + 4096` bytes. `Image.loadXObject`/`loadMask` decode image data
  with `/DL` set to `dataSize` (`h · ⌈w · nc · bpc / 8⌉`, `withDL`). The reservation is not
  observable: `inflateAt_cap`, `flateDecode_cap`, `decodeOne_cap`, `applyStages_cap`,
  `applyStagesB_cap`, `decodeStream_eq` are `rfl`/induction equalities, so every Phase 3
  bound (`decodeStream_size_le`, `flateDecodeW_steps_le`, `decodeAllB_total`, the bomb
  suite) holds unchanged — and the reservation never exceeds what B2 already charges a
  failing stage. Streaming filter output row by row into the image decoder was not needed for
  the measured peaks (the decoded stream itself, 1× its size, remains).
* **Filled buffers without the boxed array.** `ByteArray.mk (Array.replicate n v)` first
  builds an `Array UInt8` (8 bytes per element) — a transient 9× peak. `Clip.filledBuf w h v`
  pushes one row and appends `h` copies into a buffer reserved at `w · h` bytes
  (`filledBuf_eq`: same bytes as the replicate form). Used by `Clip.whiteBuf` (every page and
  tiling cell), `Type3.fullMask`, the `View` cache test helper. `Transparency.fillBufSpec`
  keeps the replicate form: it is the 7.3c reference that the test drivers compare against
  (the renderer uses `fillBuf`, row copies since 7.9). LZW output still grows from empty
  (LZW images are rare in the corpus).

Peak RSS (`python3 -I Tests/differential/peak_rss.py`, 72 dpi, whole file):

| file | before (b631f27) | after |
|---|---|---|
| arxiv-2005.14165 | 197 MiB | 142 MiB |
| arxiv-2307.09288 | 128 MiB | 103 MiB |
| arxiv-2401.00001 | 117 MiB | 73 MiB |
| arxiv-2501.12948 | 73 MiB | 56 MiB |
| ntsb AAR0501 | 99 MiB | 60 MiB |
| 8000 × 6000 RGB Flate stress file (scratch, drawn 400 × 300 pt) | 285 MiB | 157 MiB |

Pixels: all 375 page PPMs of these six files byte-identical before/after (SHA-256). Times
unchanged within noise.

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
5. Known, by design: non-embedded fonts draw nothing without substitute fonts on the system
   (task 7.7; on macOS the system's Helvetica/Times/Courier are used since 9.r7; non-embedded
   CIDFonts always), DCT
   images are placeholders, shared `/Kids` are a cycle, page numbering differs from MuPDF
   after a dangling kid.

## Error bounds (task 12.8)

Plan.md §6 Phase 12 "Proof gaps". **There is no IEEE `Float` in `SafePdf/Core`, `Spec` or
`Repair`** (grep: the only hit is the `Object.lean` doc saying reals are never `Float`), so
Lean's lack of a `Float` semantics is not an obstacle: every "float surface" is a rounding
fixed-point or integer approximation of an exact `Rat` quantity. Theorems in
`SafePdf/Spec/RasterError.lean`; all bounds two-sided (`Near x y ε := −ε ≤ x − y ≤ ε`), no
saturation/clamping assumed where stated.

| Surface | Representation | ℚ model | Bound |
|---|---|---|---|
| Operand `Decimal → Fixed` (`Fixed.ofDecimal`) | `raw·10⁻⁶`, half up | `decimalToRat` | **proved** `ofDecimal_err`: `≤ δ = ½·10⁻⁶` |
| One `cm` product (`Content.Matrix.mul`) | `Fixed`, exact at 10¹², rounded once | `Geom.Aff.mul` | **proved** `mul_err`: every entry `≤ δ` |
| CTM after `k` `cm`s (not associative) | chain of rounded products | exact product chain | **proved** `ctm_err`: `δ·Σⱼ rowNorm(Pⱼ)`; `ctm_err_linear`: `≤ k·K·δ` if every later partial product `Pⱼ` has `rowNorm ≤ K` |
| Point through the CTM (`Content.Matrix.apply`) | `Fixed`, rounded once | `Aff.apply` | 7.1: `Matrix.apply_{x,y}_err` `≤ δ`; **new** `apply_err`/`ctm_apply_err`: `δ + (|x|+|y|+1)·k·K·δ` end to end |
| Page → device map (`Fill.ofContentPath`) | exact `Rat` (or exact `Int64` `IAff`, tested equal) | `Aff.apply` | exact; then `toSub` rounding **proved** `toSub_err`: `≤ ½` subpixel (`ofPt_near` without clamping) |
| Curve flattening (`segCount`, `bezAt`, `cubicLoop`) | integer vertices `roundDivI(bezNum, n³)` | `Fill.bez` | 7.2a: `flatten_err` (exact chords `3M/(4n²)`), `segCount_tol_of_cap`; **new** `vertex_err` (`½`), `polyline_err` (`3M/(4n²)+½`), `polyline_tol` (`tol+½` under the cap condition), `bez_near`, `device_curve_err`: exact device curve vs implemented polyline `≤ tol + 1` subpixel units per coordinate |
| Forward-difference flattener (`cubicFD`) | integer additions | `cubicLoop` | 7.2f: equal (`cubicFD_eq`), so the bounds above carry over |
| Shading/function arithmetic (`Shading.qd`, `Fn.eval`) | `Rat` rounded to `2⁻²⁴`, saturated `±2⁴⁰` | exact `Rat` ops | **proved** one step `qd_err`: `≤ 2⁻²⁵`; whole evaluations, `log2Q`/`exp2Q` (30-bit, ≈2⁻²⁵ relative, measured), 256-entry LUTs: **open** |
| Axial/radial shading per pixel | `Int64` fixed point `2²⁴`/`2¹⁶`, integer Newton `isqrtFrom` | exact start per row | **open** (row start exact; per-pixel step drift not bounded) |
| Stroke frame (`gridQ`, `circleTableI`, `isqrtW`, dash centres) | multiples of `2⁻¹⁶`, 64-bit roots | `Rat` reference stroker | 7.2i: `gridQ_err` (`½` grid unit), `isqrtW_eq`, `circleTableI` = `Rat` table (`#guard`, `m ≤ 64`); outline-vs-exact-offset-curve distance **open** |
| Arc segment count (`arcCount`) | integer search | `Rat` (`arcCount_eq`) | exact equality; chord error of the pen polygon **open** |
| Image resampling (`resample`, `boxDown`, bilinear 12-bit weights, 32-bit fixed-point stepping) | `Int64` fixed point | exact device→image map per row start | **open** (tested only) |
| Type 3 / glyph bitmap weights (`weightsAtI`) | `2⁻²⁰` grid, `2⁻²⁴` filter | `weightsAt` (exact `Rat`) | **open**: differs by ≤ 1 only near ties (measured, `Tests/RasterGlyph.lean`) |
| Glyph matrices fixed point (`Glyph` §3b, 7.2h) | `2ᴷ`-scaled `Int64` | `Rat` path | tested equal (suite `raster-fill-spec`); no bound needed where equal |
| Fill coverage, compositing | integers | — | exact by construction (`Fill`, `Clip`) |

The chain bound needs a magnitude hypothesis: an error made at step `j` is carried to the
end by the exact product of the matrices concatenated after it, so a large later scale
magnifies it. `PartialNormLe K` states that hypothesis; no unconditional linear bound exists.

### More error bounds (task 12.8b, `SafePdf/Spec/RasterError2.lean`)

| Surface | Proved | Open |
|---|---|---|
| Type 3 weights | `weightI_near`: `wR ≤ wI ≤ wR+1`, unequal only within 17/2¹⁸ of a tie; `weightsAtI_eq`, `dist_down`/`dist_up` link the kernel to both formulas; `sum_near` (sums differ by at most the index count), `checkWeightsB_sum` (= 256 when adjusted) | list-level `l`/`r` range identity |
| Axial/radial per pixel | `step_near`: after k steps within (−1−k/2, k/2] units (2⁻²⁴ axial, 2⁻¹⁸ radial); `stepI_toInt_clamped`: no Int64 wrap under the clamps for k ≤ 2³²; `isqrtFrom_bound`: ≥ ⌊√n⌋, exact when converged | — |
| Shading functions | `powNat_near` (≤ n·2⁻²⁵ for \|x\| ≤ 1); `exp_component_near` (type 2, natural exponent: 2⁻²⁵ + n·2⁻²⁵·\|c₁−c₀\|) | `log2Q`/`exp2Q`, types 0/3, 256-entry LUTs |
| Image resampling | `bil_near`: 12-bit bilinear within (E−2, E] of the exact bilinear value at the 12-bit weights (`lerpU_toNat`: no wrap) | 12-bit fraction truncation, 32-bit stepping, `boxDown` (tested only) |
| Stroke pen / arcs | — | outline vs exact offset curve and pen chord error: needs a rational cos/sin bound model (core `Rat` has no cos) |


## Phase 13 start baseline and profiling (task 13.17)

**Baseline commit `abfb5b97c004`** (`lake build inspect`, aarch64 sandbox, 8 cores).
**Noisy: re-run on a quiet machine before M13's speed comparison.** Three other agents were
building Lean in parallel; load average (`uptime`) was 12.6-14.1 at the profiling runs and
5.8-8.3 around the corpus timing run. Corpus timing ran as `taskset -c 6 nice -n 10`, one
process at a time (`--jobs 1`).

    python3 -I scripts/corpus/timing.py --corpus <corpus/files> --json OUT   # 72 dpi

| figure | value | load |
|---|---|---|
| corpus, 81 files, 2,450 pages, 72 dpi: median / p95 / p99 / max | **62.1 ms / 241.9 ms / 655.6 ms / 2,880 ms** (36 pages > 500 ms, none > 5 s, 0 errors, 0 timeouts; total 235.6 s) | 5.8-8.3 |
| `arxiv-2307.09288` p25, 125 dpi | 2,789 ms (one run) | 14.1 |
| `arxiv-0704.0001`, 37 pages, 72 dpi | 4.5 s whole file (timing.py) | 5.8 |

The M13 part (5) comparison is median and p95 of the first row, on the same machine, quiet.
The older figures quoted in the 13.17 row (2.7 s, 4.1 s, median 106 ms) came from 031d779
with 109 and 54 samples; the corpus figures above also supersede the 7.9 table (the tree has
moved on since).

### Profiling without `perf`

`perf` does not run in the Linux sandbox. `scripts/profile.sh` samples with gdb
(`gdb -p PID -batch -ex "thread apply all bt 12"`; Lean runs `main` on its own thread, so
thread 1 is idle and all threads are dumped); `scripts/profile_agg.py` aggregates.

    SAFEPDF_DPI=125 SAFEPDF_PAGE=25 scripts/profile.sh -n 600 -r -o OUT -- \
        .lake/build/bin/inspect --view raster --json corpus/files/arxiv-2307.09288.pdf
    python3 -I scripts/profile_agg.py OUT [--top N]

`-r` reruns a short command in a loop and samples whichever run is current (a run of 3 s
gives about 30 samples otherwise); `-p PID` attaches to a running process. `gdb` is a dev
tool (`sudo apt-get install -y gdb`), not a project dependency; it was already installed
here. Each sample stops the process briefly, so wall times while profiling mean nothing; the
shares do. The aggregator ignores threads whose innermost frame is a wait, picks the active
thread with a project frame, and reports the share of samples with a bignum frame
(`lean_int_big_*`, `lean_nat_pow`, `__gmpz_*`, `lean_cstr_to_nat`, `lean_nat_gcd`, ...) or
an allocator frame (`malloc`/`free`/`realloc`, `lean_alloc*`, `lean_dec_ref_cold`, ...),
the leaf functions, inclusive `SafePdf.*` functions and the innermost project function above
a bignum frame. Stacks are cut short where gdb cannot unwind Lean-compiled code (a few
percent have no project frame within 12 frames).

**Profile 1: `arxiv-2307.09288` p25, 125 dpi**, 600 samples (596 usable):
bignum frame on the stack **44.0%**; allocator frame on the stack 25.5%, allocator as the
leaf 17.1%. Leaves: `free` 5.5%, `mi_free` 4.2%, `lean_dec_ref_cold` 3.9%, `Fill.emitB`
3.0%, `malloc` 2.9%, `lean_alloc_small_object_core` 2.7%, `__gmpz_realloc` 2.3%,
`__gmpz_set_str` 2.2%. Innermost project caller of a bignum frame: `Stroke.sqrtQ` 8.6%,
`Fill.roundDivI` 8.1%, `Matrix.apply` 5.0%, `Fill.IAff.ofAff?` 5.0%, `Stroke.mkSegExact`
4.7%, `Content.roundDiv` 2.7%. Inclusive: `Clip.renderItem` 45.5%, `Stroke.strokePathT`
39.6%, `Glyph.renderItemWith` 39.4%, `Stroke.mkSegs` 28.4%, `Stroke.mkSegExact` 24.7%.

**Profile 2: `arxiv-0704.0001`, 37 pages, 72 dpi**, 600 samples (599 usable):
bignum frame **53.6%**; allocator frame 24.7%, allocator as the leaf 19.2%. Leaves: `free`
6.8%, `malloc` 5.0%, `tcache_free` 4.3%, `__gmpz_add` 4.0%, `lean_dec_ref_cold` 3.8%,
`__gmpz_realloc` 3.2%. Innermost project caller of a bignum frame: `Image.sampleAt` 10.5%,
`Geom.Aff.mul` 9.8%, `Content.roundDiv` 9.5%, `Matrix.apply` 3.2%, `Fixed.mul` 2.8%.
Inclusive: `Type3.glyphStep` 20.9%, `Glyph.renderItemWith` 20.4%, `Image.rowRGBA` 15.5%,
`Image.decodeCCITTOr` 15.0%.

Compared with the row's earlier few-sample figures the bignum share is similar (44% vs 38%,
54% vs 52%) and the same functions lead (`roundDiv*`, `sqrtQ`, `mkSegExact`, `ofAff?`,
`sampleAt`, `Aff.mul`). The allocator share on the stack is 25%, leaf share 17-19% (the
row had 37% of leaf samples for page 25, with 109 samples). The raw sample files were not
kept in the repository.
