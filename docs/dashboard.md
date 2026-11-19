# Corpus dashboard

- Generated: 2026-11-19 16:36 UTC
- Git commit: `c556319`
- Inspector milestone: M2
- Corpus: `corpus`

> **Honesty note.** M2 (task 2.11): 'opens' means the xref chain loads (strict) or the repair scan rebuilds it (repaired), and /Root resolves to a dictionary. 'Objects resolve' fetches every in-use xref entry (classic offsets and object-stream members) with getObject; it does not decode content streams, fonts or images; encrypted files are decrypted with the empty user password (task 4.3b).

## Headline

| metric | value |
|---|---|
| files | 81 |
| opens (strict or repaired) | 81 (100.0%) |
| open: strict | 81 (100.0%) |
| open: repaired | 0 (0.0%) |
| open: failed | 0 (0.0%) |
| encrypted (opened and decrypted, empty user password; task 4.3b) | 7 |
| in-use objects resolved (`--view resolve`) | 78597 / 78598 (99.999%) |
| files whose in-use objects all resolve | 80 / 81 |
| parse time, median (inspector `parseMs`) | 0.140 ms |
| parse time, p95 | 0.881 ms |
| wall time per process, median | 1016.4 ms |
| wall time per process, p95 | 1030.1 ms |
| wall time per process, max (summary / resolve) | 1360.8 / 1081.7 ms |
| total size | 190.3 MB |

## By engine

| group | files | opens | % opens | strict | repaired | failed | objects resolved | median parse ms | MB |
|---|---|---|---|---|---|---|---|---|---|
| pdfTeX | 32 | 32 | 100.0% | 32 | 0 | 0 | 100.0% | 0.172 | 151.5 |
| dvips+ghostscript | 14 | 14 | 100.0% | 14 | 0 | 0 | 100.0% | 0.111 | 8.8 |
| Ghostscript | 11 | 11 | 100.0% | 11 | 0 | 0 | 100.0% | 0.087 | 6.4 |
| unknown | 8 | 8 | 100.0% | 8 | 0 | 0 | 100.0% | 0.445 | 6.9 |
| other | 6 | 6 | 100.0% | 6 | 0 | 0 | 100.0% | 0.126 | 7.7 |
| Acrobat | 4 | 4 | 100.0% | 4 | 0 | 0 | 100.0% | 0.098 | 2.4 |
| Word | 4 | 4 | 100.0% | 4 | 0 | 0 | 100.0% | 0.152 | 3.8 |
| Chrome/Skia | 2 | 2 | 100.0% | 2 | 0 | 0 | 99.9% | 0.169 | 2.8 |

## By year bucket

| group | files | opens | % opens | strict | repaired | failed | objects resolved | median parse ms | MB |
|---|---|---|---|---|---|---|---|---|---|
| <2005 | 8 | 8 | 100.0% | 8 | 0 | 0 | 100.0% | 0.078 | 3.4 |
| 2005-2009 | 9 | 9 | 100.0% | 9 | 0 | 0 | 100.0% | 0.111 | 7.0 |
| 2010-2014 | 14 | 14 | 100.0% | 14 | 0 | 0 | 100.0% | 0.099 | 27.3 |
| 2015-2019 | 14 | 14 | 100.0% | 14 | 0 | 0 | 100.0% | 0.146 | 25.4 |
| 2020+ | 29 | 29 | 100.0% | 29 | 0 | 0 | 100.0% | 0.173 | 120.7 |
| unknown | 7 | 7 | 100.0% | 7 | 0 | 0 | 100.0% | 0.469 | 6.5 |

## Failures

None.

## Repaired files

None.

## Object-resolution failures

| file | errors / fetched | first errors |
|---|---|---|
| arxiv-2512.00001 | 1 / 180 | 37 0: malformed input at byte 158350: duplicate dictionary key |
