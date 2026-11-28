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
there. A fresh worktree resolves the pinned decoder from the Lake manifest.

**Lean MCP server (`lean-lsp`, configured in `.mcp.json`).** It runs `lake serve` in the main
checkout and can build on demand. Use its read-only tools (`lean_goal`,
`lean_diagnostic_messages`, `lean_hover_info`, `lean_multi_attempt`, `lean_run_code`, search
tools) only while no `lake build` runs in the main checkout, and never call `lean_build` there;
builds stay with the orchestrator. In a worktree the server's `LEAN_PROJECT_PATH` still points
at the main checkout, so worktree subagents keep using `lake build` / `lake env lean` locally.

**Every agent working on Lean code uses the Lean MCP tools as its primary proof loop** (load
them with ToolSearch `lean_` when they are deferred). Required working pattern:

* **Shared checkout (`new` tasks):** develop proofs interactively with `lean_goal` (goal state
  at a line), `lean_diagnostic_messages` (errors for your file), `lean_multi_attempt` (try
  several tactics at one position before editing) and `lean_hover_info`, instead of repeated
  whole-file `lake env lean` runs. Use `lake env lean <file>` once at the end as the final
  check, and quote it in the report.
* **Worktree (`wt` tasks):** the server sees the main checkout, not your worktree, so build and
  check with `lake` locally; still use the MCP *search* tools and `lean_run_code` (scratch
  snippets against the main checkout's modules) to find lemmas and test tactics.
* **Finding lemmas (everyone):** before proving a helper, search for it — `lean_local_search`
  (project and core), `lean_loogle` (by type shape), `lean_leansearch` / `lean_leanfinder`
  (natural language), `lean_hammer_premise` (premises for the current goal). There is no Mathlib: a hit that lives only in Mathlib is not
  usable.
* If the `lean_*` tools are missing in a session, say so in the report and fall back to
  `lake env lean`; do not stop.

Setup per machine: `.mcp.json` names the macOS path (`/opt/homebrew/bin/uvx`). Elsewhere,
override it once in local scope, e.g. in the Linux sandbox
`claude mcp add --scope local lean-lsp -e LEAN_PROJECT_PATH=$PWD -- /usr/bin/uvx lean-lsp-mcp`
(run in the main checkout; local scope wins over the project entry). MCP servers load at
session start, so start Claude Code from the main checkout after adding it.

## Shared registries (subagents never edit these; report the lines to add)

* `SafePdf.lean` — umbrella imports of every module under `SafePdf/` (except `Shell/`).
* `Tests/Main.lean` — the `suites` list of test suites.
* `lakefile.lean` — targets and options (was `lakefile.toml` until 8.2a). Every module under `Tests/` belongs to lib `Tests` via ``globs := #[.submodules `Tests]``, so new test modules need no lakefile line. The `viewer` exe (Tk) is not a default target; see `docs/viewer.md`.
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

* Toolchain `leanprover/lean4:v4.36.0`. The sole Lake dependency is the pinned pure Lean
  `jpeg2000` decoder. Adding a dependency needs a ledger Decisions entry. `autoImplicit = false`.
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
