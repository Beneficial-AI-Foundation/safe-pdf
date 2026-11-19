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

### D-001: dangling-ref-null — reference to a free object

- Classification: deliberate difference (normalization of an object-level dump)
- Found by: `objects` comparator on arxiv-1303.5076, arxiv-1412.6980, arxiv-2010.11929
  (32 objects), 2026-11-18, CI run 44402582274
- Reference tool and version: qpdf from ubuntu-24.04 apt (11.x)
- Spec reference: ISO 32000-2:2020 §7.3.10 ("An indirect reference to an undefined
  object shall not be considered an error … it shall be treated as a reference to the
  null object")
- Observed: page dictionaries contain `/Group N 0 R` where object N is marked free in the
  cross-reference stream (e.g. arxiv-1412.6980: object 342 is xref type 0; page objects
  340, 375, … reference it). Ours prints `"/Group": "342 0 R"` (the syntactic value);
  qpdf resolves the reference to null and drops the key.
- Reading chosen and rationale: the object-level dump (Phase 1) reports syntax, not
  resolved values; resolution to null belongs to the document layer (Phase 4), which
  will treat such references as null per §7.3.10.
- Comparator handling: `Tests/differential/objects.py:diff` — a dictionary entry whose
  value on our side is a reference `N G R`, absent on the qpdf side, where qpdf has no
  object `N G` or lists it with value `null` (qpdf keeps free objects as `null` in its
  JSON — seen in CI run 44410513896), counts as a warning `dangling-ref-null`, not a disagreement.
- Status: accepted

### D-002: shared-or-cyclic-page-tree — a page-tree node reached twice

- Classification: deliberate difference (we reject what the reference tool repairs)
- Found by: `pages` comparator design (task 4.4) on the fixture
  `Tests/golden/pages/shared.pdf` / `Tests/differential/fixtures/pages_shared.*`,
  2026-11-19. Not observed on the 74-file corpus (every corpus file opens: 0 page-tree
  errors in a local run of the `pages` view).
- Reference tool and version: qpdf 11.x (behaviour from its documentation and source:
  a page object reached a second time in `/Kids` is replaced by a copy). Not yet
  confirmed by a CI run.
- Spec reference: ISO 32000-2:2020 §7.7.3.2 (the page tree is a tree: every page and
  intermediate node has exactly one `/Parent`).
- Observed: ours `reference cycle … page tree /Kids cycle` (`Core.Doc` rule W2: the page
  list must consist of distinct objects, which is what `ofOpen_pages_nodup` proves);
  qpdf lists the shared page twice (the second time as a new object).
- Reading chosen and rationale: a node with two parents violates §7.7.3.2; duplicating it
  would make two pages share one object (and its annotations, by identity), so the core
  rejects the file instead, the same way as a true `/Kids` cycle.
- Comparator handling: `Tests/differential/pages.py:compare` — when our `pages` view
  reports an error containing `reference cycle`, the file is classified `known` (not a
  disagreement), whatever qpdf lists; `run.py` counts it separately and prints it as
  `KNOWN`.
- Status: accepted
