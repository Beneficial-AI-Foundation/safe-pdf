# Contributing to safe-pdf

Thanks for your interest in contributing. safe-pdf is a formally verified, read-only
PDF viewer and inspector written in Lean 4: parsing, cross-reference resolution,
decompression, the content-stream interpreter, fonts, text extraction and
rasterization form a pure, total, resource-bounded core with machine-checked
properties, driven by a thin unverified shell (the inspector CLI, the Tcl/Tk viewer
and the native macOS app). This guide covers how to build it, the standards we hold
code to, and how to send a change. It follows the shared contribution standard used
across the [Beneficial AI Foundation](https://github.com/Beneficial-AI-Foundation)
Lean projects.

## Prerequisites

Install [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager.
It reads `lean-toolchain` and fetches the exact Lean/Lake version this project
uses, so you don't install Lean by hand:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

There are no Lake dependencies (no Mathlib, no Batteries). Python 3 (standard library
only) is used by the corpus and differential scripts. The core and the inspector CLI
build on **macOS and Linux**. The viewers are optional and need extra tools: the Tk
viewer needs Tcl/Tk development files (`tk-dev` on Debian/Ubuntu, `brew install
tcl-tk` on macOS); the native macOS app needs macOS 15 or later and the Xcode command
line tools. Neither viewer is a default target.

## Building

```sh
lake build                          # the library, the inspector and the example client
lake exe inspect FILE.pdf           # the inspector CLI (lake exe inspect --help)
lake exe extract FILE.pdf [PAGE]    # example client of the library API

lake build viewer worker            # Tk viewer (Linux or macOS; needs Tk)
lake build macosApp                 # macOS: the native app -> macos/build/SafePdf.app
```

`lake build` and the tests never compile Tk or Swift.

## Testing

```sh
lake build tests fuzz && lake exe tests   # the unit and property suites
scripts/check-hygiene.sh                   # proof hygiene and the axiom audit
scripts/fuzz.sh                            # fuzz smoke test
```

Continuous integration runs the build, the test suites, the hygiene guard, a fuzz
smoke test, the native macOS job, an independent kernel re-check (lean4lean) and
differential comparisons against qpdf/MuPDF/poppler on every push and pull request
(see `.github/workflows/ci.yml`). Please make sure the build, the tests and
`scripts/check-hygiene.sh` pass locally before opening a PR.

## Proof discipline

Correctness and safety come from machine-checked proofs, so the verified core
(`SafePdf/Core/`, `SafePdf/Spec/`, `SafePdf/Api.lean`) must stay free of escape
hatches. `scripts/check-hygiene.sh` enforces this and the build fails on a hit:

- **No `sorry`, `partial`, `unsafe`, `panic!` or `!`-indexing (`get!`, `xs[i]!`)** in
  the core. Recursion uses `termination_by` with an explicit measure, never
  `partial def`. The unverified shell may use `IO`, but still no `sorry`.
- The axiom audit (`scripts/axioms.lean`, via `#print axioms`) pins the top-level
  theorems to `propext`, `Classical.choice` and `Quot.sound` — which rules out
  `native_decide` (`Lean.ofReduceBool`). A change that makes a theorem depend on
  anything else fails the guard.

See `CLAUDE.md` for the full house rules and [docs/safety.md](docs/safety.md) for the
safety account and its limits.

## Submitting a change

1. **Branch** off `main` (or fork the repository).
2. Keep each pull request focused, and add or update a spec/theorem or test for
   behaviour you change.
3. Make sure `lake build`, `lake exe tests` and `scripts/check-hygiene.sh` pass, and
   that CI is green.
4. Write a clear PR description: what changed, why, and how you verified it.
5. By contributing, you agree your contribution is licensed under this repository's
   license (MIT; see `LICENSE`), and you certify the
   [Developer Certificate of Origin](https://developercertificate.org/) — add a
   `Signed-off-by: Your Name <you@example.com>` line to your commits (`git commit -s`).

## Reporting issues

Open a GitHub issue with a clear title, what you expected, what happened, and the
smallest PDF that reproduces it. Since safe-pdf parses untrusted input, please report
security-relevant findings privately to **support@beneficialaifoundation.org**
instead of a public issue.

## Code of conduct

Be respectful and constructive. Harassment or abuse is not tolerated. Maintainers may
remove comments, commits or contributions that don't meet this standard.
