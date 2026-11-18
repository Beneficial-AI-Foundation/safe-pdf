# Deviations from spec

## Purpose

Differential testing (Plan.md §7, item 1) compares our inspector with reference tools
(currently `qpdf --json=2` via `Tests/differential/objects.py`, run in the CI job
`differential-objects`). Plan.md §7.1 requires every disagreement to be triaged as one of:

- **our bug**: fix it in the code (and add a regression test). Not recorded here once
  fixed; the fix commit is the record.
- **their bug**: the reference tool is wrong per ISO 32000. Recorded here, and the
  comparator gets a narrowly scoped, commented exception that cites the entry.
- **spec ambiguity**: ISO 32000 permits more than one reading. Recorded here with the
  reading we chose and why.

Also recorded here: deliberate differences in normalization or scope (for example a
reference tool repairing a file we reject) that make a comparator ignore something.
Each comparator exception must point to an entry in this file; an exception without an
entry is a bug in the comparator.

## Entry template

```
### D-NNN: <short title>

- Classification: their bug | spec ambiguity | deliberate difference
- Found by: <comparator> on <corpus id or fixture>, <date>, CI run <link or id>
- Reference tool and version: <e.g. qpdf 11.9.0>
- Spec reference: ISO 32000-2:2020 §<section> (and -1:2008 §<section> if different)
- Observed: ours <value>, reference <value> (minimal reproduction if possible)
- Reading chosen and rationale: <...>
- Comparator handling: <none | exception in Tests/differential/<file>:<function>>
- Status: open | accepted | resolved (<commit>)
```

## Entries

None yet. To be filled after the first CI run of `differential-objects`.
