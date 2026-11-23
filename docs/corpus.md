# Test corpus

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
