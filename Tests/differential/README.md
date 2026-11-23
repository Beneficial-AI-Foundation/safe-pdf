# Differential testing

`run.py` compares our inspector against independent reference tools over the
corpus (Plan.md section 7, item 1). Stdlib only; run with `python3 -I`.

    python3 -I Tests/differential/run.py [--comparator NAME]... [--corpus DIR]
                                         [--files GLOB] [--limit N] [--json OUT]

Defaults: all comparators, `corpus/files` (git-ignored; a missing or empty
directory reports 0 files and exits 0). `--files` overrides `--corpus`.

## Comparators

A comparator = name + required external tools + reference-dump function +
our dump (`.lake/build/bin/inspect <file> <view>`) + normalizer + compare.

| name      | reference tool           | inspector view | status      |
|-----------|--------------------------|----------------|-------------|
| `size`    | `os.path.getsize`        | default        | working     |
| `objects` | `qpdf --json`            | `objects`      | placeholder |
| `pages`   | `mutool info` / qpdf     | `pages`        | placeholder |
| `text`    | `pdftotext`              | `text`         | placeholder |

Add one by appending a `Comparator(...)` to `COMPARATORS` in `run.py` (pdf.js
later).

Outcomes per file: agree, disagree, `skipped (tool missing: qpdf)`,
`skipped (view not implemented)`, error. Missing tools and unimplemented views
are never failures. Exit status is 1 only for disagreements or errors in
comparators that actually ran.

Note: `size` currently extracts the first `<N> bytes` from the inspector's
default view; it will move to a dedicated view once the inspector CLI settles.
Unknown-view detection is heuristic (an "unknown view" message, or the default
`path: N bytes` line coming back for a non-default view) and should be replaced
by a proper exit code/message when views land.

## Triage

Every disagreement is classified as one of: our bug (fix it), their bug
(reference tool is wrong; document), or spec ambiguity (Plan.md section 7.1).
Non-bug outcomes are recorded in `docs/deviations-from-spec.md`.
