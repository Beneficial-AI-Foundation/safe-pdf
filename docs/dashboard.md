# Corpus dashboard

- Generated: 2026-11-18 20:11 UTC
- Git commit: `55119cb`
- Inspector milestone: M0
- Corpus: `corpus`

> **Honesty note.** M0: the inspector's parse is a header check only (`%PDF-x.y` found near the start), so '% opens' is trivially high and says nothing about real parsing ability. Later milestones diff against this file's JSON.

## Headline

| metric | value |
|---|---|
| files | 74 |
| opens | 74 (100.0%) |
| parse time, median (inspector `parseMs`) | 0.006 ms |
| parse time, p95 | 0.007 ms |
| wall time per process, median | 3.3 ms |
| wall time per process, p95 | 4.8 ms |
| total size | 183.8 MB |

## By engine

| group | files | opens | % opens | median parse ms | MB |
|---|---|---|---|---|---|
| pdfTeX | 32 | 32 | 100.0% | 0.006 | 151.5 |
| dvips+ghostscript | 14 | 14 | 100.0% | 0.006 | 8.8 |
| Ghostscript | 11 | 11 | 100.0% | 0.006 | 6.4 |
| other | 6 | 6 | 100.0% | 0.006 | 7.7 |
| Acrobat | 4 | 4 | 100.0% | 0.006 | 2.4 |
| Word | 4 | 4 | 100.0% | 0.006 | 3.8 |
| Chrome/Skia | 2 | 2 | 100.0% | 0.006 | 2.8 |
| unknown | 1 | 1 | 100.0% | 0.006 | 0.4 |

## By year bucket

| group | files | opens | % opens | median parse ms | MB |
|---|---|---|---|---|---|
| <2005 | 8 | 8 | 100.0% | 0.006 | 3.4 |
| 2005-2009 | 9 | 9 | 100.0% | 0.006 | 7.0 |
| 2010-2014 | 14 | 14 | 100.0% | 0.006 | 27.3 |
| 2015-2019 | 14 | 14 | 100.0% | 0.006 | 25.4 |
| 2020+ | 29 | 29 | 100.0% | 0.006 | 120.7 |

## Failures

None. (Expected at M0: only the header is checked.)
