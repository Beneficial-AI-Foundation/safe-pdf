# safe-pdf — instructions for Claude

A formally verified, read-only PDF viewer in Lean 4. The design document is
[Plan.md](Plan.md); progress, tasks, gotchas and decisions live in [progress.md](progress.md)
(the ledger, maintained by `/next-wave`).

## Commands

| What | Command |
|---|---|
| Build (library + inspector) | `lake build` |
| Build test and fuzz executables | `lake build tests fuzz` |
| Tests | `lake exe tests` |
| Fuzz smoke run | `lake exe fuzz` (arguments defined by task 0.6; see `scripts/fuzz.sh` once it exists) |
| Guard: proof hygiene | `scripts/check-hygiene.sh` (once task 0.3 lands) |
| Single-file check | `lake env lean <path/to/File.lean>` |

The gate for every commit is: `lake build && lake build tests fuzz && lake exe tests`, plus
every guard listed above that exists.

The single-file check compiles one file against the **already built** `.olean`s of its
imports. It does not write to `.lake/`, so it is safe to run in the shared checkout while
nothing else builds. It can only import modules that are already built in the main
checkout; a new file importing another new, unbuilt file must say so in its report instead.

## Concurrent builds

**Concurrent builds in one checkout are NOT safe.** Only the orchestrator runs `lake build`,
`lake exe …` or any executable in the main checkout. A subagent in the shared checkout uses
only the single-file check. A subagent in its own git worktree may build and test freely
there; the project has no Lake dependencies, so a fresh worktree builds from scratch in
well under a minute and needs no cache sharing.

## Shared registries (subagents never edit these; report the lines to add)

* `SafePdf.lean` — umbrella imports of every module under `SafePdf/` (except `Shell/`).
* `Tests/Main.lean` — the `suites` list of test suites.
* `lakefile.toml` — targets and options. Every module under `Tests/` belongs to lib `Tests` via `globs = ["Tests.+"]`, so new test modules need no lakefile line.
* `progress.md` — the ledger (orchestrator only).

## Layout (Plan.md §10)

* `SafePdf/Core/` — verified core: pure, no `IO`, no `partial`, no `unsafe`, no `panic!`,
  no `!` indexing (`get!`, `xs[i]!`), no `sorry`.
* `SafePdf/Spec/` — denotational specs and theorems; same rules as `Core/`.
* `SafePdf/Repair.lean` — lenient path; same rules (proven total and bounded).
* `SafePdf/Quarantine/` — FFI decoders + revalidation.
* `SafePdf/Shell/` — unverified shell and inspector; `IO` allowed, but still no `sorry`.
* `Tests/` — `golden/`, `fuzz/` (`Fuzz/`), `adversarial/`, `differential/`.
* `scripts/` — guards, corpus tooling. `corpus/` holds downloaded PDFs and is git-ignored
  except for `corpus/manifest.json`.
* `docs/` — `proof-patterns.md`, `deviations-from-spec.md`, `corpus.md`.

## Conventions

* Toolchain `leanprover/lean4:v4.36.0`, no Lake dependencies (no Mathlib, no Batteries);
  adding one needs a ledger Decisions entry. `autoImplicit = false`.
* Every recursive structure in the format carries a fuel/measure argument or a visited set,
  justified by a proof (Plan.md §3 rule 2, §5.2). Prefer structural recursion or
  `termination_by` with an explicit measure; never `partial def`.
* Errors are values of `SafePdf.Error` (`SafePdf/Core/Error.lean`); limits come from
  `SafePdf.Limits` (`SafePdf/Core/Limits.lean`). Exceeding a limit returns
  `Error.limitExceeded`, never slows down unboundedly.
* Spec first: for each layer write the denotational spec in `Spec/`, the efficient
  implementation in `Core/`, then the equivalence theorem (Plan.md §5.1).
* Top-level theorems must depend only on `propext`, `Classical.choice`, `Quot.sound`
  (`#print axioms`); list them in `scripts/axioms.lean` once task 0.3 lands.
* A requirement or theorem that cannot be met as stated is never weakened silently: record
  the obstacle in the ledger and split the task.
* Every public `def`/`structure`/`theorem` gets a docstring; each file starts with a `/-! -/`
  module doc citing the Plan.md section it implements.
* Tests: unit/property suites in `Tests/*.lean` registered in `Tests/Main.lean`; golden
  files under `Tests/golden/`; adversarial inputs under `Tests/adversarial/`.
* Python scripts (corpus, differential) use only the standard library, run with
  `python3 -I`, and skip cleanly when an external tool (`qpdf`, `mutool`, `pdftotext`) is
  missing. Downloaded files go into `corpus/` and are verified by SHA-256.
* Reusable lessons go into the ledger's Gotchas; design changes into its Decisions (and into
  Plan.md only with the human's agreement).

## Attribution

Commits end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` (or the line the
session gives); PR bodies end with
`🤖 Generated with [Claude Code](https://claude.com/claude-code)`.
