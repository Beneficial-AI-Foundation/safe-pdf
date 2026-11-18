# Differential testing

`run.py` compares our inspector against independent reference tools over the
corpus (Plan.md section 7, item 1). Stdlib only; run with `python3 -I`.

    python3 -I Tests/differential/run.py [--comparator NAME]... [--corpus DIR]
                                         [--files GLOB] [--limit N] [--json OUT]
                                         [--min-compared N]

Defaults: all comparators, `corpus/files` (git-ignored; a missing or empty
directory reports 0 files and exits 0). `--files` overrides `--corpus`.

## Comparators

A comparator = name + required external tools + reference-dump function +
our dump (`.lake/build/bin/inspect <file> <view>`) + normalizer + compare.

| name      | reference tool           | inspector view | status      |
|-----------|--------------------------|----------------|-------------|
| `size`    | `os.path.getsize`        | default        | working     |
| `objects` | `qpdf --json=2` (>= 11)  | `objects`      | working (needs qpdf; see below) |
| `pages`   | `mutool info` / qpdf     | `pages`        | placeholder |
| `text`    | `pdftotext`              | `text`         | placeholder |

Add one by appending a `Comparator(...)` to `COMPARATORS` in `run.py` (pdf.js
later).

Outcomes per file: agree, disagree, `skipped (tool missing: qpdf)`,
`skipped (view not implemented)`, error. Missing tools and unimplemented views
are never failures. Exit status is 1 only for disagreements or errors in
comparators that actually ran, or when `--min-compared N` (default 0) is given
and fewer than N files had at least one object compared by `objects` (guards
CI against a run that silently compared nothing).

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
