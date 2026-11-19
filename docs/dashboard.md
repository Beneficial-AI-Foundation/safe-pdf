# Corpus dashboard

- Generated: 2026-11-19 12:03 UTC
- Git commit: `1130a99`
- Inspector milestone: M2
- Corpus: `corpus`

> **Honesty note.** M2 (task 2.11): 'opens' means the xref chain loads (strict) or the repair scan rebuilds it (repaired), and /Root resolves to a dictionary. 'Objects resolve' fetches every in-use xref entry (classic offsets and object-stream members) with getObject; it does not decode content streams, fonts or images, and encrypted files' strings and streams are not decrypted (Phase 4).

## Headline

| metric | value |
|---|---|
| files | 74 |
| opens (strict or repaired) | 74 (100.0%) |
| open: strict | 74 (100.0%) |
| open: repaired | 0 (0.0%) |
| open: failed | 0 (0.0%) |
| encrypted (opened; strings/streams not decrypted) | 0 |
| in-use objects resolved (`--view resolve`) | 68573 / 68574 (99.999%) |
| files whose in-use objects all resolve | 73 / 74 |
| parse time, median (inspector `parseMs`) | 0.122 ms |
| parse time, p95 | 0.570 ms |
| wall time per process, median | 8.1 ms |
| wall time per process, p95 | 10.5 ms |
| wall time per process, max (summary / resolve) | 330.6 / 603.0 ms |
| total size | 183.8 MB |

## By engine

| group | files | opens | % opens | strict | repaired | failed | objects resolved | median parse ms | MB |
|---|---|---|---|---|---|---|---|---|---|
| pdfTeX | 32 | 32 | 100.0% | 32 | 0 | 0 | 100.0% | 0.170 | 151.5 |
| dvips+ghostscript | 14 | 14 | 100.0% | 14 | 0 | 0 | 100.0% | 0.110 | 8.8 |
| Ghostscript | 11 | 11 | 100.0% | 11 | 0 | 0 | 100.0% | 0.072 | 6.4 |
| other | 6 | 6 | 100.0% | 6 | 0 | 0 | 100.0% | 0.111 | 7.7 |
| Acrobat | 4 | 4 | 100.0% | 4 | 0 | 0 | 100.0% | 0.083 | 2.4 |
| Word | 4 | 4 | 100.0% | 4 | 0 | 0 | 100.0% | 0.391 | 3.8 |
| Chrome/Skia | 2 | 2 | 100.0% | 2 | 0 | 0 | 99.9% | 0.308 | 2.8 |
| unknown | 1 | 1 | 100.0% | 1 | 0 | 0 | 100.0% | 0.045 | 0.4 |

## By year bucket

| group | files | opens | % opens | strict | repaired | failed | objects resolved | median parse ms | MB |
|---|---|---|---|---|---|---|---|---|---|
| <2005 | 8 | 8 | 100.0% | 8 | 0 | 0 | 100.0% | 0.062 | 3.4 |
| 2005-2009 | 9 | 9 | 100.0% | 9 | 0 | 0 | 100.0% | 0.113 | 7.0 |
| 2010-2014 | 14 | 14 | 100.0% | 14 | 0 | 0 | 100.0% | 0.083 | 27.3 |
| 2015-2019 | 14 | 14 | 100.0% | 14 | 0 | 0 | 100.0% | 0.129 | 25.4 |
| 2020+ | 29 | 29 | 100.0% | 29 | 0 | 0 | 100.0% | 0.216 | 120.7 |

## Failures

None.

## Repaired files

None.

## Object-resolution failures

| file | errors / fetched | first errors |
|---|---|---|
| arxiv-2512.00001 | 1 / 180 | 37 0: malformed input at byte 158350: duplicate dictionary key |
