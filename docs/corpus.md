# Test corpus

The JPX source-PDF placement gate uses the decoder dependency's pinned PDF collection.
For fetch, worker comparisons and per-object coverage, see [JPX page comparisons](jpx-pages.md).

## Purpose

Plan.md §1 ("Target corpus") names academic and office PDFs: LaTeX output (pdfTeX, LuaTeX,
XeTeX), Word/LibreOffice exports, publisher PDFs, matplotlib/R figures, scanned papers.
Plan.md §7 makes success a measured quantity against a real corpus (dashboard per
milestone: % opens, % text-accurate, % pixel-accurate, parse/render time; regressions block
merge), because proofs only show we meet *our* spec. The corpus also feeds differential
testing and fuzzer seeds.

## Fetching

```
python3 -I scripts/corpus/fetch.py            # download missing, verify all (SHA-256 + size)
python3 -I scripts/corpus/fetch.py --summary  # counts per engine / year / producer
python3 -I scripts/corpus/fetch.py --add URL [URL...] [--category engine=XeTeX] [--source S] [--license L]
python3 -I scripts/corpus/fetch.py --reindex  # recompute producer/engine from present files (offline)
```

Stdlib only. Files go to git-ignored `corpus/files/<id>.pdf` (temp name `.part`, verified,
then renamed; a mismatch is reported and the file deleted, exit status 1). Requests use the
User-Agent `safe-pdf-corpus-fetch/0.1`, >= 3.5 s apart on arxiv.org. A second run with
everything present makes no network requests. `corpus/manifest.json` is the committed
catalogue: `id, url, sha256, size, source, license, category{engine, year, producer,
embedded}, creator`. `producer` and `creator` are read from the trailer's Info dictionary
by regex (falling back to inflated streams when the Info dict sits in an object stream).
`engine` is a coarse class derived from Producer (Creator only if Producer is unrecognised).
`embedded` lists engines of other `/Producer` strings found inside (embedded figures,
e.g. matplotlib), which is not the document's own producer.

## Current contents (first slice)

74 arXiv PDFs, 183.8 MB, 1995-2026 (2005-2026 well covered; 1995-2004 has 8 files), plus 7
encrypted US government PDFs (6.5 MB, see "Encrypted subset" below): 81 entries, 190.3 MB.
The tables below cover the arXiv files.

| engine (document Producer) | files | notes |
|---|---|---|
| pdfTeX | 32 | dominant, 2007-2025; many embed matplotlib/Quartz figures |
| dvips + Ghostscript | 14 | arXiv's PS->PDF conversion of old TeX sources |
| Ghostscript (alone) | 11 | likewise |
| Word | 4 | Word 2013/2016/365, Adobe PDF Library (Creator Word) |
| Acrobat Distiller/Pro | 4 | author-supplied PDFs |
| Chrome/Skia (Google Docs) | 2 | |
| other | 6 | pikepdf (arXiv post-processing), iText, 3-Heights |
| unknown | 1 | Info dict without Producer (edge case kept on purpose) |

By 5-year bucket of arXiv ID: 1995-99: 4, 2000-04: 4, 2005-09: 9, 2010-14: 14,
2015-19: 14, 2020-24: 20, 2025-26: 9.

Gaps: no LuaTeX/XeTeX/LibreOffice document-producer sample yet (arXiv usually rebuilds from
source with pdfTeX; those engines appear only in author-supplied PDFs), no scanned papers,
no publisher PDFs (Elsevier/Springer/ACM/IEEE). Add them with `--add ... --category`.
Pre-2007 files are mostly Ghostscript conversions, so "year" here is submission year, not
producer vintage. arXiv URLs are unversioned (latest version); the SHA-256 pin makes a
regenerated PDF show up as a mismatch to be triaged (re-add under a versioned URL, e.g.
`.../pdf/1706.03762v7`, if that happens).

## Encrypted subset (task 4.7, M4 "encrypted publisher PDFs open")

7 real (not generated) encrypted PDFs, all US federal government works, which are public
domain under 17 U.S.C. 105 (no copyright, so redistribution is unrestricted; the `license`
field says so). All use the Standard security handler with an owner password and an empty
user password (they open in any reader without a prompt). Cipher read from the `/Encrypt`
dictionary (V, R, `/CF /StdCF /CFM`).

| id | source | pages | cipher | notes |
|---|---|---|---|---|
| `www.ntsb.gov-AAR0501` | NTSB aircraft accident report AAR-05/01 | 120 | RC4-40 (V1 R2) | classic xref table |
| `www.ntsb.gov-AAR0701` | NTSB AAR-07/01 | 173 | RC4-128 (V2 R3) | classic xref table |
| `www.ntsb.gov-RAR0801` | NTSB railroad accident report RAR-08/01 | 36 | RC4-128 (V2 R3) | classic xref table |
| `www.ntsb.gov-AAR1201` | NTSB AAR-12/01 | 74 | AES-128 (V4 R4, AESV2) | object streams |
| `www.ntsb.gov-AIR2201` | NTSB aviation investigation report AIR-22/01 | 11 | AES-256 (V5 R6, AESV3) | object streams |
| `www.ntsb.gov-MIR2301` | NTSB marine investigation report MIR-23/01 | 12 | AES-256 (V5 R6, AESV3) | object streams |
| `www.uscis.gov-g-1145` | USCIS form G-1145 | (1) | AES-128 (V4 R4, AESV2) | linearized, xref streams only; opens *repaired* and undecrypted (0 pages) as of 554a909, see below |

NTSB URLs (`https://www.ntsb.gov/investigations/AccidentReports/Reports/<ID>.pdf`) name a
fixed, published report and are stable. The USCIS URL is unversioned (it serves the current
form edition), so a hash mismatch there means a new edition: re-add or drop it.

Observations from screening (useful for adding more): NTSB switched ciphers over time
(2005 RC4-40, 2006-2008 RC4-128, 2012-2020 AES-128, 2021+ AES-256 for AAR/AIR/MIR; some
years are unencrypted) and all current USCIS forms are AES-128. IRS prior-year forms,
VA/CMS/GSA/OPM/SEC forms, NIST SP 800-53 and Census reports checked were not encrypted.

The Info dictionary strings of these files are encrypted, so `fetch.py`'s regex cannot read
`/Producer`; their manifest entries carry `engine: unknown`, `producer: "encrypted Info (not
decrypted by fetch.py)"` and an extra `category.encryption` field. `--reindex` would put the
undecrypted bytes back into `producer`; re-apply that normalisation after a reindex.

Inspector results at 554a909 (summary, `resolve`, `pages`, `streams`, `outline`): the six
NTSB files open strict with `encrypted: true`, resolve all objects with 0 errors, page count
equals `/Count`, streams decode with 0 errors (only image placeholders), and outline titles
decrypt to readable text. `g-1145` strict xref parses (`--view xref`: `strict: ok`,
`encrypted true`) yet the summary reports `open: repaired`, `encrypted: false`, 0 pages and 4
Flate errors on still-encrypted streams: the "repaired encrypted xref-stream-only file opens
undecrypted" case (task 4.6), plus an unexplained rejection of the strict open.
`dashboard.py --files 'www.*'`: 7/7 open (6 strict, 1 repaired), all objects resolve. The
qpdf pages comparator (`Tests/differential/pages.py`) was not run locally (qpdf not
installed); CI's qpdf decrypts these with the empty user password.

## Known reference defects (task 6.8c)

Sometimes the *reference* tool is the one that is wrong. Such pages would otherwise drag
the corpus-wide M6 numbers (text similarity vs MuPDF, glyph positions within tolerance)
with errors that are not ours. They are recorded, with evidence, in
`Tests/differential/known-reference-defects.json` and handled by
`Tests/differential/run.py`:

* Each entry names a corpus file (basename **and** SHA-256), the pages, the comparators
  it applies to (`text-mupdf`, `positions`), the reference version, a `signature`, the
  `reason` and the `evidence` (how it was decided: rendering, fonts, a second reference).
* An entry applies only when the file's SHA-256 matches, and only to listed pages whose
  reference output (`mutool draw -q -F txt`, that page) still matches `signature` (a
  regular expression). A page that no longer shows it -- e.g. after a MuPDF upgrade
  fixed the bug -- is printed as `STALE known-defect entry ...` and compared normally;
  a hash mismatch ignores the entry the same way. So an entry can never hide a page whose
  reference output is healthy.
* Matching pages are removed from the corpus-wide similarity, the worst-pages list, the
  positions totals (`compared`, `within`, distances, worst glyphs) and the `--min-similarity`
  / `--min-within` gates. They are **printed separately** ("known reference defects
  (EXCLUDED ...)" with per-page similarity / measured pairs and outliers) and counted in
  the stats `known_pages`, `known_dist`, `known_maxlen` (text) and `known_pages`,
  `known_compared`, `known_within` (positions). The file's status becomes `known` with the
  reason (`KNOWN ...` line) unless it disagrees on its other pages. Tolerances and
  thresholds are never changed; `--no-known` reproduces the raw numbers.
* Self-tests: `python3 -I Tests/differential/run.py --selftest` (data file, hash and
  signature gates, text split) and `python3 -I Tests/differential/positions.py
  --selftest` (known-page split, anchoring).

Adding an entry needs the same standard of evidence as the first one: look at the
rendered page, inspect the font / content, and compare with a second reference.

### arxiv-astro-ph_9805201 p51, p60-p72 (MuPDF drops digits)

The tables at the end of this 1998 Ghostscript conversion use Type 3 fonts whose
`/Encoding /Differences` name the digit glyphs `/0` ... `/9` and whose ToUnicode CMap maps
only the letters. MuPDF 1.25.1 turns the glyph names `/1` ... `/9` into the code points
U+0001 ... U+0009 (`mutool draw -F stext` prints `c="&#x2;"` for a '2'; `/0` stays '0'),
so its text loses the digits: `{ { T able . SN Ia Imaging JD a UT Date B V B V` where the
page shows "- 2 -  Table 2.  SN Ia Imaging  JD^a UT Date B45 V45 B35 V35". The rendering
(`mutool draw -o p61.png FILE 61`) and `pdftotext -f 61 -l 61` both have the digits, as
we do. (MuPDF also splits words in these fonts -- "T able", "Con tin ued" -- which neither
pdftotext nor we do.) Exactly pages 51 and 60-72 contain U+0001-U+0008 in MuPDF's text,
which is the entry's signature.

The 844 glyph pairs outside tolerance on this file (e.g. '.' size 0.24 ours (520.564,
405.360) vs MuPDF (90.961, 436.560) on p64) were all on these pages: with the digits gone,
a table row like `22.30(0.09)` is `..(0.)` on MuPDF's side, and the order-preserving
alignment paired leftover '.', '0', '(' and ')' of different table cells. Numbers
(a0f4718, one file):

| comparator | before | after |
|---|---|---|
| `text-mupdf` | 0.9466 over 72 pages; p61-p72 0.47-0.67 | 0.9984 over 58 pages; 14 known pages 0.5786 (printed separately) |
| `positions` | 99.2287% of 109,420 pairs within (844 out) | 100.0000% of 103,100 pairs; 14 known pages 6,067 pairs, 760 out (printed separately) |

Whole corpus (81 files, 2,450 pages, a0f4718 inspector; `run.py --comparator text-mupdf
--comparator positions`), before -> after this mechanism and the matcher fixes below:
text vs MuPDF 0.9926 over 2,450 pages -> 0.9936 over 2,436 pages (+ 14 known pages at
0.5786, printed separately); positions 99.9471% of 5,724,449 pairs within (3,030 out, 76/81
files at 100%) -> 5,718,110 of 5,718,112 within (2 out: arxiv-2010.11929 p18 and
arxiv-1706.00001 p4, 79/81 files at 100%; + 6,067 known-page pairs, 760 out, printed
separately). `--no-known` gives the numbers with the known pages included.

## Positions matcher: anchoring and runs (task 6.8c)

Two matcher flaws paired characters that do not correspond, so they showed up as large
"position errors"; both fixes only change *which* characters are paired, never the
tolerance:

* **Anchoring.** A matching block shorter than 3 characters counts only when it lies on
  the alignment diagonal of the nearest long block before or after it (or of the page
  start / end), or between those two diagonals within 4 characters of one of them (a
  piece between two one-sided deletions, "c[al]c" vs "[al]"); otherwise its characters
  are unmatched (stat `unanchored`). This removed the 17 outliers of arxiv-2501.12948 p52
  (our Caesar-shifted text matched stray 'R', 'K', '9' of MuPDF's) and drops no pair that
  was within tolerance on the healthy files checked (0704.0001, 0905.0002, 2006.11239,
  2303.08774).
* **Runs of identical characters.** difflib pairs a run of equal characters leftmost. On
  www.ntsb.gov-RAR0801 p5 the TOC leaders are `/Span<</ActualText<feff002e>>> BDC ( )Tj
  EMC` + 104 dots: MuPDF honours the ActualText ('.' at the space) and has 105 dots, we
  have a space + 104 dots at exactly MuPDF's other 104 positions, so every dot was paired
  one advance (3 pt) off. A run whose pairs are out of tolerance is now re-paired by
  shifting it up to 2 slots onto identical reference characters that are unmatched (or
  its own), when that puts more of its pairs within tolerance (stat `slid`; one-to-one
  and order kept). RAR0801: 2,167 -> 0 pairs out of tolerance. (ActualText support in our
  extraction is a separate Core task.)

Details in the `positions.py` docstring (`anchored_blocks`, `slide_runs`).

## Licensing

arXiv PDFs are copyrighted by their authors under varying licenses. They are fetched by URL
and **never committed or redistributed**; only URL, hash and metadata live in git. Anything
added from other sources must have a redistribution-friendly license recorded in the
`license` field before it may ever be committed. (PDF Association / SafeDocs / pdf.js
samples were not added in this slice: stable URLs and per-file licenses not yet verified.)

## Planned growth

1. Towards ~2k arXiv PDFs, sampled by year x engine x size (add a sampler script that emits
   `--add` batches; at 3.5 s/request that is ~2 h, run unattended).
2. SafeDocs / PDF Association samples and the pdf.js test PDFs, license-checked per file.
3. Targeted additions: LuaTeX/XeTeX, LibreOffice, publisher PDFs, scanned papers, encrypted
   and linearized files, and known-malformed files (feeds the adversarial suite).
4. A size cap per file (currently 64 MiB at download) and a `corpus/files/` disk budget.
