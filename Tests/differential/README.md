# Differential testing

`run.py` compares our inspector against independent reference tools over the
corpus (Plan.md section 7, item 1). Stdlib only; run with `python3 -I`.

    python3 -I Tests/differential/run.py [--comparator NAME]... [--corpus DIR]
                                         [--files GLOB] [--limit N] [--json OUT]
                                         [--min-compared N] [--min-similarity X] [--no-fold]
                                         [--min-within P] [--dpi D] [--exclude GLOB]...

Defaults: all comparators, `corpus/files` (git-ignored; a missing or empty
directory reports 0 files and exits 0). `--files` overrides `--corpus`.

## Comparators

A comparator = name + required external tools + reference-dump function +
our dump (`.lake/build/bin/inspect <file> <view>`) + normalizer + compare.

| name      | reference tool           | inspector view | status      |
|-----------|--------------------------|----------------|-------------|
| `size`    | `os.path.getsize`        | default        | working     |
| `objects` | `qpdf --json=2` (>= 11)  | `objects`      | working (needs qpdf; see below) |
| `pages`   | `qpdf --json=2` (>= 11)  | `pages`        | working (needs qpdf; see below) |
| `streams` | Python `zlib`            | `streams`      | working     |
| `text`    | `pdftotext` (poppler)    | `text`         | working (needs pdftotext; see below) |
| `text-mupdf` | `mutool draw -F txt` (MuPDF) | `text`    | working (needs mutool; see below) |
| `positions` | `mutool draw -F stext` (MuPDF) | `text` (`SAFEPDF_TEXT_GLYPHS=1`) | working (needs mutool; see `positions.py` docstring) |
| `pixels` | `mutool draw -F pnm` (MuPDF) | `raster` (`SAFEPDF_RASTER_DIR`) | working (needs mutool; metric and numbers in `docs/raster.md`; `pixels.py --selftest`) |

Add one by appending a `Comparator(...)` to `COMPARATORS` in `run.py` (pdf.js
later).

Outcomes per file: agree, known (a documented divergence, never a failure),
disagree, `skipped (tool missing: qpdf)`,
`skipped (view not implemented)`, error. Missing tools and unimplemented views
are never failures. Exit status is 1 only for disagreements or errors in
comparators that actually ran, or when `--min-compared N` (default 0) is given
and fewer than N files had at least one object (page) compared by each selected
`objects` / `pages` comparator (guards CI against a run that silently compared
nothing).

Note: `size` currently extracts the first `<N> bytes` from the inspector's
default view; it will move to a dedicated view once the inspector CLI settles.
Unknown-view detection is heuristic (an "unknown view" message, or the default
`path: N bytes` line coming back for a non-default view) and should be replaced
by a proper exit code/message when views land.

## Triage

Every disagreement is classified as one of: our bug (fix it), their bug
(reference tool is wrong; document), or spec ambiguity (Plan.md section 7.1).
Non-bug outcomes are recorded in `docs/deviations-from-spec.md`.

## `objects` comparator (`objects.py`)

Compares `inspect --view objects --json FILE` (linear `N G obj` scan) with
`qpdf --json=2 --json-key=qpdf` object dumps. Offline mode for fixtures/debugging:

    python3 -I Tests/differential/objects.py --ours OURS.jsonl --qpdf QPDF.json

Fixtures: `fixtures/ours.jsonl` + `fixtures/qpdf.json` (one deliberate
disagreement, one qpdf-only, one ours-only, `u:`/`b:` string equality; exit 1),
`fixtures/ours_agree.jsonl` + `fixtures/qpdf_agree.json` (exit 0).

Normalization: strings to bytes (qpdf `u:` text matches if our bytes equal its
UTF-8 / PDFDocEncoding / UTF-16BE / UTF-8-BOM encoding); names to bytes;
numbers to Decimal (int vs real compare numerically, spelling mismatch is a
warning); dict key order ignored; null dict entries == absent; `/Length`
dropped on both sides (qpdf omits it); streams compare dicts only; trailer
ignored. Counts: compared, agree, disagree, ours-only, qpdf-only (expected:
compressed object-stream members until Phase 2/3), our-errors. Exit 1 only on
disagreement. qpdf >= 11 required (JSON v2); the comparator is skipped when
qpdf is missing, the view is not implemented, or qpdf fails on the file.
Unverified qpdf-format assumptions are listed in the `objects.py` docstring.

CI: job `differential-objects` in `.github/workflows/ci.yml` (ubuntu-24.04,
apt qpdf >= 11) fetches/verifies the corpus, prints qpdf and inspector output
heads for one file (debug), runs `objects` over the corpus with
`--min-compared 20` and over `Tests/adversarial/minimal-valid.pdf` with
`--min-compared 1`, and uploads the JSON results and logs as the artifact
`differential-objects`.

## `streams` comparator (`streams.py`)

Compares our FlateDecode output with Python `zlib` (no external tool needed).
Per PDF: `inspect --view streams --json FILE` lists streams; those whose chain is
exactly `[FlateDecode]` with no `/DecodeParms` are compared (predictor, other
filters, resolved indirect `/Filter` are skipped and counted). The script locates
raw bytes itself (the view has no offset): scan for `N G obj` (newest match
first), find `>> stream` EOL, take exactly the view's `raw` byte count, accept
only if `endstream` follows. Every located stream gets a size check (zlib's
length vs the view's `decoded`); a sample (`--per-file N`, default 20, evenly
spread, 0 = all; all streams when `--files` is given without `--per-file`) is
byte-compared using `SAFEPDF_STREAM=N SAFEPDF_STREAM_OUT=tmp inspect --view
streams FILE`. Categories: agree (sub-count `trailing`), disagree, ours-error
(we reject, zlib decodes), zlib-error (zlib rejects, e.g. bad Adler-32, or sees
truncation, we decode), both-error, skipped. Any disagree / ours-error /
zlib-error / size mismatch makes the file `disagree`.

    python3 -I Tests/differential/run.py --comparator streams [--per-file N] [--files GLOB]
    python3 -I Tests/differential/streams.py --ours OURS.bin --raw RAW.bin   # offline

Fixtures: `fixtures/streams_ok.{raw,ours}` (agree, exit 0),
`fixtures/streams_diff.ours` + `streams_ok.raw` (last byte differs, exit 1),
`fixtures/streams_adler.{raw,ours}` (corrupt Adler-32: zlib-error, exit 1).

## `pages` comparator (`pages.py`)

Compares `inspect --view pages --json FILE` (task 4.4: the core page tree,
`Core.Doc.openDoc`) with `qpdf --json=2 --json-key=pages --json-key=qpdf
--decode-level=none FILE`. qpdf's `pages` array gives the page count and order
(object references); qpdf reports no effective boxes, so the script computes
them from qpdf's raw objects with the core's rules (Core/Doc.lean A1–A6) but by
walking each page's `/Parent` chain upwards (the core walks `/Kids` downwards):
one-level resolution of references, a box must be 4 numbers (else absent and
inheritance continues), corners normalized, missing MediaBox = US Letter (our
`mediaBoxDefaulted` must then be true), Rotate modulo 360 with non-multiples of
90 as 0. Our CropBox is already clipped to the MediaBox; qpdf's raw CropBox is
clipped the same way before comparing (empty intersection = MediaBox).
Numbers: exact `Decimal`s, tolerance 0 for integers and 1e-9 for reals.

Per file: agree; known (we reject the tree with `reference cycle`: a page shared
by two parents, which qpdf duplicates, or a `/Kids` cycle — D-002 in
`docs/deviations-from-spec.md`); disagree with categories `ours-failed`, `count`,
`ref`, `mediabox`, `cropbox`, `rotate`, `defaulted-flag`; skipped when qpdf is
missing or fails. Stats: `compared` (pages), `our_pages`, `qpdf_pages`,
`defaulted`, `known`, `cat_<category>`.

    python3 -I Tests/differential/run.py --comparator pages --min-compared 20
    python3 -I Tests/differential/pages.py --ours OURS.jsonl --qpdf QPDF.json   # offline

Fixtures (qpdf JSON hand-written from the qpdf 11 manual: qpdf is not installed
locally; `ours` files are real inspector output for `Tests/golden/pages/*.pdf`):
`fixtures/pages_tree.{ours.jsonl,qpdf.json}` (inheritance, swapped corners,
`595.2760` vs `595.276`, clipping, Rotate -90/450/45, defaulted MediaBox; agree,
exit 0), `pages_tree.ours.jsonl` + `pages_diff.qpdf.json` (count, cropbox and
rotate disagreements, exit 1), `pages_shared.{ours.jsonl,qpdf.json}` (known,
exit 0). CI: step "Pages comparison on the corpus" in job `differential-objects`
(`--min-compared 20`), results in the `differential-objects` artifact as
`differential-pages.{json,log}`.

## `text` comparator (`text.py`)

Compares `inspect --view text --json FILE` (task 6.6: `Core.Text.extractDocPage`,
all pages under one document budget) with poppler's `pdftotext -enc UTF-8 FILE -`
(reading-order mode, not `-layout`), split into pages on form feeds. Pages are
paired by index; a page present on one side only is compared with the empty
string (note `page-count`). Comparator `text-mupdf` is the same with MuPDF as the
reference (`mutool draw -q -F txt -o - FILE`, which also ends every page with a form
feed); Plan.md names pdfium/MuPDF as the M6 reference, so both are reported.
Phase 6 exit M6 asks for >= 98% similarity; this
comparator **reports** the numbers, the threshold is evaluated by the
orchestrator.

Normalization (both sides; full list in the `text.py` docstring): Unicode NFKC
(ligatures, NBSP, compatibility forms); soft hyphen, zero-width characters, BOM
and other non-whitespace control characters dropped; dashes U+2010–2015 and
U+2212 folded to `-`, curly single/double quotes and primes to `'` / `"`
(`--no-fold` disables this step); every whitespace run collapsed to one space,
ends stripped. U+FFFD is kept (an edit against the reference).

Similarity per page: `1 - lev(a, b) / max(len(a), len(b))` (1 when both are
empty), Levenshtein over code points after stripping the common prefix and
suffix, computed exactly with the bit-parallel Myers/Hyyrö algorithm on Python
ints (checked against the O(n·m) DP by `text.py --selftest`; ~3 s for a
100 000-character page). Size guard: a remainder above 100 000 code points is
compared at word-token level (same algorithm over tokens, character distance
estimated as `(1 - sim_tok) · max len`), above 200 000 tokens by bag-of-words F1;
both counted in `fallback_pages`. Per file: character-weighted similarity
`1 - Σ lev / Σ max len`, page mean / median / min. Corpus (printed by `run.py`):
character-weighted similarity over all pages, and the 10 worst pages with an
excerpt around the first difference (50 in the JSON under `"text"`).

Status: agree (compared), disagree (never by default), known (the core rejects
the document — open failures are the `objects` / `pages` comparators' concern;
counted as similarity 0), error (inspector crash, timeout, non-JSON output),
skipped (`pdftotext` missing or failing on the file). `--min-similarity X`
fails the run when the corpus similarity is below X. Stats: `compared`/`pages`,
`pages_exact`, `page_count_mismatch`, `chars_ours`, `chars_ref`, `dist`,
`maxlen`, `fallback_pages`, `ours_replacement`, `ours_failed`.

    python3 -I Tests/differential/run.py --comparator text --json differential-text.json
    python3 -I Tests/differential/text.py --ours OURS.jsonl --ref REF.txt [--min-similarity X]
    python3 -I Tests/differential/text.py --selftest

Fixtures (`ours` is real inspector output for `Tests/golden/text/latin.pdf`; the
pdftotext side is hand-written, since pdftotext is not installed locally):
`fixtures/text_ours.jsonl` + `text_ref.txt` (ligature, en dash, one missing word
space: similarity 0.9863, exit 0 even with `--min-similarity 0.9`),
`text_ours.jsonl` + `text_diff.ref.txt` (different text and a page-count mismatch:
0.1561, exit 1 with `--min-similarity 0.9`), `text_failed.ours.jsonl` +
`text_ref.txt` (our open failure: known, exit 0). CI: step "Text comparison on
the corpus" in job `differential-objects` (apt `poppler-utils`), results in the
`differential-objects` artifact as `differential-text.{json,log}`.

## Glyph positions (`positions`)

Comparator `positions` (`Tests/differential/positions.py`, task 6.10) compares our per-glyph origins with MuPDF's `stext` character origins after converting MuPDF's device space back to PDF user space (page transform printed by `mutool run`). A pair is within tolerance when the distance is ≤ max(1 pt, 0.1 × font size). The conversions, matching and tolerance are documented in the module docstring; `python3 -I Tests/differential/positions.py --selftest` checks the offline fixtures.
