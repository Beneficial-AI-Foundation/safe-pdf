<p align="center"><img src="docs/branding/safe-pdf.png" alt="safe-pdf logo" width="200"></p>

# safe-pdf

**A formally verified, read-only PDF viewer, written in Lean 4.**

Formally verified work on PDF has so far covered parsers only, usually for restricted subsets.
safe-pdf goes further: parsing, cross-reference resolution, decompression, the
content-stream interpreter, fonts, text extraction and rasterization form a **pure, total,
resource-bounded core** with machine-checked properties. A thin, unverified shell (window,
scrolling, clipboard) drives it.

```
bytes → Except Error Document            -- parse (untrusted input)
Document → PageIndex → DisplayList       -- interpret content streams
DisplayList → Bitmap                     -- rasterize
Document → PageIndex → PositionedText    -- text extraction with glyph positions
```

The core's types contain no `IO`, so it cannot touch the network, the file system or other
processes. The design is in [Plan.md](Plan.md); progress, decisions and known gaps are in
[progress.md](progress.md).

## What "verified" means here

The full list, with what is proven and what is only tested, is in [Plan.md §4](Plan.md#4-the-properties-what-verified-means-here).
In short:

* **Security (proven):** memory safety (no `unsafe`, no FFI in the core); **totality** — every
  core function terminates on every byte string, including xref cycles, self-referencing
  `/Length`, cyclic page trees and recursive XObjects; **bounded resources** — exceeding an
  explicit limit returns `Error.limitExceeded` instead of slowing down; no ambient authority;
  unambiguous interpretation across incremental updates; local, visible failure (a bad page
  never breaks another, repaired files are flagged).
* **Correctness (proven):** coordinate round-trips, text ↔ glyph-position correspondence,
  repair conservativity on strictly valid files, efficient parser ≡ executable spec, extracted
  text = displayed text, and saved annotations as a conservative incremental update (the
  original bytes stay a prefix).
* **Tested, not proven:** rendering faithfulness (pixel comparison against pdf.js, MuPDF and
  others), font rasterization quality, and float-level behaviour of the rasterizer.

Top-level theorems depend only on `propext`, `Classical.choice` and `Quot.sound`; the hygiene
guard (`scripts/check-hygiene.sh`) checks this and the core's coding rules on every commit.
[docs/safety.md](docs/safety.md) gives the safety account and its limits.

### Deliberately left out

JavaScript, interactive forms (AcroForm/XFA), launch actions and links to other files,
embedded-file execution, multimedia and 3D, and any network access. The viewer never modifies
the opened file in place; annotations are saved as an incremental update.

## Status

Phases 0–10 of the roadmap (lexer and objects through the rasterizer, the viewer with
annotations, and viewer polish) are complete and merged. Work in progress on PR #16: a native
macOS shell (Phase 11; the Tk viewer stays on Linux) and hardening from an independent
security review (Phase 12: a confined document worker, capped reads, per-operation memory
budgets). See [progress.md](progress.md) for the per-task record.

## Requirements

* [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain`
  (`leanprover/lean4:v4.36.0`). There are no Lake dependencies (no Mathlib, no Batteries).
* For the GUI viewer only: Tcl/Tk development files (Debian/Ubuntu `tk-dev`, Tk 8.6 or 9.0;
  macOS `brew install tcl-tk`).
* Python 3 (standard library only) for the corpus and differential scripts.

## Build, test, run

```sh
lake build                          # library, inspector, example client
lake build tests fuzz && lake exe tests
scripts/check-hygiene.sh            # proof hygiene and axiom audit

lake exe inspect FILE.pdf           # inspector CLI (lake exe inspect --help)
lake exe extract FILE.pdf [PAGE]    # example client of the library API (text)
lake exe extract --render FILE.pdf [PAGE]

lake build viewer                   # GUI viewer (not a default target; needs Tk)
lake exe viewer FILE.pdf
```

The inspector prints views of a file (summary, objects, xref, revisions, repair, streams,
pages, outline, ops, svg, text, raster; `--list-views`), with `--json` for machine-readable
output. The viewer is described in [docs/viewer.md](docs/viewer.md):
continuous and spread view modes, zoom, rotation, outline and thumbnails, selection, search,
links, highlights, notes, free text and ink, saving marks into the PDF, and XFDF
import/export.

## Using the core as a library

`SafePdf.Api` is a small, pure facade over the verified core: open a file or bytes, pages,
text with glyph positions, page rendering to RGBA, outline, links and annotations. From
another Lake project on the same toolchain:

```lean
require «safe-pdf» from git
  "https://github.com/Beneficial-AI-Foundation/safe-pdf.git" @ "main"
```

then `import SafePdf.Api`. See [docs/api.md](docs/api.md) for the reference, guarantees and
limits.

## Repository layout

| Path | Contents |
|---|---|
| `SafePdf/Core/` | The verified core: pure, no `IO`, no `partial`, no `unsafe`, no `sorry` |
| `SafePdf/Spec/` | Denotational specifications and the theorems |
| `SafePdf/Repair.lean` | The lenient path for damaged files (total, bounded, conservative) |
| `SafePdf/Api.lean` | The library API (`safe-pdf-core`) |
| `SafePdf/Shell/` | Unverified shell: inspector CLI and the Tk viewer |
| `Tests/` | Unit and property suites, golden files, fuzzing, adversarial inputs |
| `scripts/` | Guards, benchmarks, corpus and differential tooling, viewer smoke tests |
| `docs/` | API, viewer, safety account, comparisons, proof patterns, deviations from the spec |
| `corpus/` | Manifest of the evaluation corpus (the PDFs themselves are downloaded, not committed) |

## Further reading

* [Plan.md](Plan.md) — vision, architecture, properties, roadmap
* [docs/safety.md](docs/safety.md) — threat model and what the proofs do and do not cover
* [docs/comparison.md](docs/comparison.md), [docs/safedocs-comparison.md](docs/safedocs-comparison.md) — comparison with other projects
* [docs/proof-patterns.md](docs/proof-patterns.md) — reusable proof techniques
* [docs/deviations-from-spec.md](docs/deviations-from-spec.md) — where the implementation knowingly differs from ISO 32000

## License

MIT — see [LICENSE](LICENSE). Copyright (c) 2026 Beneficial AI Foundation.
