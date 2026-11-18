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

74 arXiv PDFs, 183.8 MB, 1995-2026 (2005-2026 well covered; 1995-2004 has 8 files).

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
