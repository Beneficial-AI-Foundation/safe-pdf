# safe-pdf progress ledger

Maintained by `/next-wave`. The orchestrator is the only writer of this file.
Parallel limit: 4
Usage gate: 95%
Design document: Plan.md

## How to read this file
* Status: `todo` · `doing (date)` · `done (date)` · `blocked (why)` · `split (into …)`.
* Needs: task IDs that must be `done` before this one starts.
* Owns: the files or directories this task may create or modify. Tasks whose Owns
  overlap never run in the same wave unless both are `wt`.
* Par: `new` (creates only new files; shared checkout; single-file checks only) ·
  `wt` (edits existing files; own git worktree; builds and tests there) ·
  `solo` (the orchestrator does it alone).
* Phases 2–8 are deliberately coarse; each task there is split (size check) when its
  phase becomes current.

## Current wave

## Branches and PRs
| Phase | Branch | Base | PR | State |
|---|---|---|---|---|
| 0 | `phase-0-infra` | `origin/main` | [#1](https://github.com/Beneficial-AI-Foundation/safe-pdf/pull/1) | ready (2026-11-18) |
| 1 | `phase-1-lexer-objects` | `phase-0-infra` | [#2](https://github.com/Beneficial-AI-Foundation/safe-pdf/pull/2) | draft |
| 2 | `phase-2-xref` | `phase-1-lexer-objects` | — | none |
| 3 | `phase-3-filters` | `phase-2-xref` | — | none |
| 4 | `phase-4-document` | `phase-3-filters` | — | none |
| 5 | `phase-5-content` | `phase-4-document` | — | none |
| 6 | `phase-6-fonts-text` | `phase-5-content` | — | none |
| 7 | `phase-7-raster` | `phase-6-fonts-text` | — | none |
| 8 | `phase-8-shell` | `phase-7-raster` | — | none |
States: none · draft · awaiting-ci · ready (<date>) · changes-requested · merged · closed.

## Phase 0 — Infrastructure
Plan.md §6 Phase 0, §3 rule 3, §7, §10. Exit: **M0**: CI green; fuzzer runs; corpus catalogued.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 0.1 | Lake scaffold: `lean-toolchain` (pin `leanprover/lean4:v4.36.0`), `lakefile.toml` declaring lib `SafePdf`, exes `inspect`, `tests`, `fuzz`; stub roots `SafePdf.lean`, `SafePdf/Core/Limits.lean` (limit record, §10), `SafePdf/Core/Error.lean`, `SafePdf/Shell/Inspect.lean` + `Main` stubs, `Tests/Main.lean`, `Tests/Fuzz/Main.lean`; record dependency decision (no Mathlib to start) | — | `lean-toolchain`, `lakefile.toml`, `SafePdf.lean`, `SafePdf/`, `Tests/Main.lean`, `Tests/Fuzz/Main.lean` | solo | done (2026-11-18) |
| 0.2 | `CLAUDE.md`: build/test/guard/single-file-check commands, concurrent-build rule, shared registries, conventions (§3 rules, §7.5), attribution | 0.1 | `CLAUDE.md` | solo | done (2026-11-18) |
| 0.3 | Proof-hygiene guard `scripts/check-hygiene.sh`: grep `Core/` (and `Spec/`) for `partial`, `unsafe`, `panic!`, `get!`/`!` indexing, `sorry`; `#print axioms` check over top-level theorems listed in `scripts/axioms.lean` allowing only `propext`/`Classical.choice`/`Quot.sound` | 0.1 | `scripts/check-hygiene.sh`, `scripts/axioms.lean` | new | done (2026-11-18) |
| 0.4 | CI `.github/workflows/ci.yml`: elan install, cache `.lake`, `lake build`, `lake exe tests`, hygiene guard, short fuzz smoke run | 0.1, 0.3 | `.github/workflows/ci.yml` | new | done (2026-11-18) |
| 0.5 | Golden-file test harness: `Tests/Golden.lean` runner (input → expected output files under `Tests/golden/`), wired into `Tests/Main.lean` | 0.1 | `Tests/Golden.lean`, `Tests/golden/`, `Tests/Main.lean` | wt | done (2026-11-18) |
| 0.6 | Fuzz entry point: `SafePdf/Core/Parse.lean` stub `parse : ByteArray → Except Error Document` (placeholder `Document`), `Tests/Fuzz/Main.lean` driver (random + mutated seed inputs, deterministic seed, iteration count arg), `scripts/fuzz.sh` | 0.1 | `SafePdf/Core/Parse.lean`, `Tests/Fuzz/`, `scripts/fuzz.sh` | wt | done (2026-11-18) |
| 0.7 | Differential-test runner skeleton `Tests/differential/run.py` (+ README): compares our structure/text dumps vs `qpdf --json`/`mutool`/`pdftotext` when present, skips cleanly when absent | 0.1 | `Tests/differential/` | new | done (2026-11-18) |
| 0.8 | Corpus acquisition: `scripts/corpus/fetch.py` (manifest of URLs + SHA-256, downloads into git-ignored `corpus/`, hash-verified), first slice (~50 arXiv PDFs across years/engines + pdf-association/SafeDocs samples where licensable), `docs/corpus.md` catalogue | — | `scripts/corpus/`, `docs/corpus.md`, `corpus/manifest.json` | new | done (2026-11-18) |
| 0.9 | Adversarial seed: reconstruct Bogk & Schöpl-style cyclic-xref file(s) (`/Prev` cycle, self-referential `/Length`, `/Kids` cycle) as small hand-written PDFs + README describing each | — | `Tests/adversarial/` | new | done (2026-11-18) |
| 0.10 | Inspector skeleton `SafePdf/Shell/Inspect.lean`: CLI `inspect <file> [view]`, reads bytes, calls `parse`, prints size/header/result; view registry for later phases | 0.1, 0.6 | `SafePdf/Shell/Inspect.lean`, `SafePdf/Shell/Main.lean` | wt | done (2026-11-18) |
| 0.11 | Corpus dashboard (§7.4, §6 MVP table M0): `scripts/corpus/dashboard.py` runs `inspect` over the corpus → `docs/dashboard.md` (% opens, timing) | 0.8, 0.10 | `scripts/corpus/dashboard.py`, `docs/dashboard.md` | new | done (2026-11-18) |
Exit criterion checked: [x] (2026-11-18: CI `build` passed on PR #1 at 55119cb; `scripts/fuzz.sh` 2000 iters, 0 slow, 0 crashes; corpus catalogued in `docs/corpus.md` + `docs/dashboard.md`, 74/74 files, 0 regressions)

## Phase 1 — Lexer and object model
Plan.md §6 Phase 1, §5.1. Exit: **M1**: object-level round-trip `parse (print o) = o`; fuzzer finds no panics; property tests vs `qpdf --json` object dumps on corpus.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 1.1 | Object model `SafePdf/Core/Object.lean`: the 8 object types (null, bool, int, real, string, name, array, dict, stream, ref) as an inductive with well-founded size | 0.1 | `SafePdf/Core/Object.lean` | new | done (2026-11-18) |
| 1.2 | Denotational lexer spec `SafePdf/Spec/Lex.lean`: tokens, whitespace/EOL/comments, literal strings with escapes + balanced parens, hex strings, names with `#xx`, numbers in spec ranges | 1.1 | `SafePdf/Spec/Lex.lean` | new | done (2026-11-18) |
| 1.3 | Efficient tokenizer `SafePdf/Core/Lex.lean` over `ByteArray`, total (structural/termination on position), no backtracking | 1.1 | `SafePdf/Core/Lex.lean` | new | done (2026-11-18) |
| 1.4 | Object grammar spec `SafePdf/Spec/Object.lean` (`ObjSpec : List Token → PdfObject → Prop` + executable spec) and unambiguity lemma | 1.2 | `SafePdf/Spec/Object.lean` | new | done (2026-11-18) |
| 1.5 | Efficient object parser `SafePdf/Core/ObjParse.lean` (arrays, dicts, refs `n g R`, nesting depth limit from `Limits`) | 1.3 | `SafePdf/Core/ObjParse.lean` | new | done (2026-11-18) |
| 1.6 | Lexer equivalence proof `SafePdf/Spec/LexEquiv.lean`: `Core.lex bytes = Spec.lex bytes` (C5) | 1.2, 1.3 | `SafePdf/Spec/LexEquiv.lean` | new | done (2026-11-18) |
| 1.7 | Printer `SafePdf/Core/Print.lean` + round-trip theorem `parse (print o) = o` in `SafePdf/Spec/RoundTrip.lean` | 1.4, 1.5 | `SafePdf/Core/Print.lean`, `SafePdf/Spec/RoundTrip.lean` | new | done (2026-11-18) |
| 1.8 | Parser equivalence proof `SafePdf/Spec/ObjEquiv.lean`: impl ≡ spec (C5) | 1.4, 1.5, 1.6 | `SafePdf/Spec/ObjEquiv.lean` | new | done (2026-11-18) |
| 1.9 | `docs/proof-patterns.md`: the spec/impl/equivalence pattern as established by 1.6/1.8 (§9 bus-factor mitigation) | 1.6 | `docs/proof-patterns.md` | new | done (2026-11-18) |
| 1.10 | Wire `parse` (object level) into fuzz driver and golden tests; seed golden files for each object type | 1.5, 0.5, 0.6 | `SafePdf/Core/Parse.lean`, `Tests/golden/objects/`, `Tests/Fuzz/` | wt | done (2026-11-18) |
| 1.11 | Property tests vs `qpdf --json` object dumps on corpus (extends `Tests/differential/`) | 1.5, 0.7, 0.8 | `Tests/differential/objects.py` | new | done (2026-11-18) |
| 1.12 | Inspector view `objects`: pretty-printed object tree, diffable against `qpdf --json` | 1.7, 0.10 | `SafePdf/Shell/Views/Objects.lean`, `SafePdf/Shell/Inspect.lean` | wt | done (2026-11-18) |
| 1.13 | M1 evidence in CI: job `differential-objects` on `ubuntu-24.04` (qpdf ≥ 11 for JSON v2; pin/assert version), build `inspect`, restore the corpus from an Actions cache keyed on `corpus/manifest.json` (fetch once with `scripts/corpus/fetch.py` when missing), run `Tests/differential/run.py --comparator objects` over corpus + `Tests/adversarial/minimal-valid.pdf`; triage every disagreement (our bug / their bug / spec ambiguity → `docs/deviations-from-spec.md`) | 1.11, 1.12 | `.github/workflows/ci.yml`, `docs/deviations-from-spec.md`, `Tests/differential/` | wt | done (2026-11-18) |
| 1.14 | Fix CI `differential-objects` failure: `inspect --view objects --json` timed out (> 60 s) on `corpus/files/arxiv-2307.09288.pdf` (13.7 MB). Profile with a short time budget (find whether the Shell scan, the lexer re-lexing, `parseIndirect`, or the O(n²) dict duplicate check dominates), fix the hot spot without weakening any theorem (Core changes must keep their proofs), re-run the corpus locally with per-file times ≤ 10 s | 1.13 | `SafePdf/Shell/Views/Objects.lean`, `SafePdf/Core/ObjParse.lean`, `SafePdf/Core/Lex.lean` | wt | done (2026-11-18) |
Exit criterion checked: [ ]

## Phase 2 — File structure: xref, trailer, revisions ★
Plan.md §6 Phase 2, §5.2, §5.4. Exit: **M2**: 99% of corpus opens (strict or repaired); Bogk-style cyclic files all rejected in bounded time; first machine-checked proof that PDF xref resolution terminates on arbitrary input.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 2.1 | Classic xref tables + trailer parsing `SafePdf/Core/Xref.lean` | 1.8 | `SafePdf/Core/Xref.lean` | new | done (2026-11-18) |
| 2.2 | `/Prev` chain resolution with visited-offset measure + termination proof (§5.2) | 2.1 | `SafePdf/Core/Xref/Chain.lean`, `SafePdf/Spec/XrefTerm.lean` | new | done (2026-11-18) |
| 2.3 | Indirect `/Length` resolution with fuel = object count; self-dependency is an error | 2.1 | `SafePdf/Core/Xref/Length.lean` | new | done (2026-11-18) |
| 2.4 | Xref streams + object streams (needs Flate + PNG predictors — co-develop with 3.1/3.2); rank argument for containers | 2.2, 3.1, 3.2 | `SafePdf/Core/Xref/Stream.lean` | new | split (into 2.4a, 2.4b) — done |
| 2.4a | Xref streams: `parseXrefStream` (`/Type /XRef` stream object, `/W`, `/Index`, `/Size`, `/Prev`; Flate + predictor via `Core.Filter`; entries type 0/1/2 into `XrefSection` incl. `compressed`), and wire into the chain walk: a `/Prev` or `startxref` offset may point at an xref stream; hybrid `/XRefStm` followed with the same visited-set discipline; keep every 2.2 theorem (termination, cycle rejection, call bound) | 2.2, 3.1, 3.2 | `SafePdf/Core/Xref/Stream.lean`, `SafePdf/Core/Xref/Chain.lean`, `SafePdf/Spec/XrefTerm.lean` | wt | done (2026-11-18) |
| 2.4b | Object streams: `getFromObjStm` — decode `/Type /ObjStm` (`/N`, `/First`, Flate), parse the header pairs, extract object k; rank argument: an object stream may not contain itself or be fetched through itself (container chain checked with a visited set); bounds on `/N`, `/First` | 3.1 | `SafePdf/Core/Xref/ObjStm.lean` | new | done (2026-11-18) |
| 2.5 | Unambiguity S6: newest-revision-wins, one winner per object id; hybrid `/XRefStm` | 2.2, 2.4 | `SafePdf/Spec/Unambiguous.lean` | new | done (2026-11-18) |
| 2.6 | Repair path `SafePdf/Repair.lean` (offset-tolerant `N 0 obj` scan), totality + bound proofs | 2.1 | `SafePdf/Repair.lean` | new | done (2026-11-18) |
| 2.7 | Adversarial regression: all `Tests/adversarial/` files rejected in bounded time | 2.2, 2.3, 0.9 | `Tests/Adversarial.lean` | wt | done (2026-11-18) |
| 2.8 | Inspector views: xref trace, revision history, repair report | 2.5, 2.6 | `SafePdf/Shell/Views/Xref.lean` | wt | todo |
| 2.9 | Move local limits into `SafePdf/Core/Limits.lean`: `maxRevisions` (2.2, 4096) with new `LimitKind.revisions`, repair `failBudget` (2.6, 256) as `maxRepairFailures`; update Chain/Repair/theorems to use them | 2.2, 2.6 | `SafePdf/Core/Limits.lean`, `SafePdf/Core/Error.lean`, `SafePdf/Core/Xref/Chain.lean`, `SafePdf/Spec/XrefTerm.lean`, `SafePdf/Repair.lean` | wt | done (2026-11-18) |
| 2.10 | Refactor duplication: split `ObjParse.parseIndirect` into public `parseHeader` + body taking a `Dict → Except Error Nat` length resolver; move `tokenAt_pos` into `Core/Lex.lean`, `parseStreamBody_ok`/`expectKeyword_pos` into ObjParse; make `Xref/Length.lean` and `Repair.lean` use them (Repair jumps over indirect-/Length streams via 2.3 resolution) | 2.3, 2.6, 2.9 | `SafePdf/Core/ObjParse.lean`, `SafePdf/Core/Lex.lean`, `SafePdf/Core/Xref/Length.lean`, `SafePdf/Repair.lean` | wt | done (2026-11-18) |
| 2.11 | Document opening for M2: `openFile limits bytes : Except Error OpenDoc` in `SafePdf/Core/Open.lean` — strict: `Chain.loadChain` + `mergeChain`; on failure `Repair.repair` with `repaired := true` (S7, Plan §5.4); `OpenDoc.getObject n` resolves `inUse` via `Length.parseIndirectResolved` and `compressed` via `ObjStm.fetchCompressed`; validate `/Root` resolves to a dict; replace the stub `Document` in `Core/Parse.lean` so `parse` opens the file (keep `parseObjectAt`/`parseIndirectAt`); inspector `summary` shows strict/repaired/failed + revision count; dashboard columns % strict, % repaired, % failed, and a per-file 'all in-use objects resolve' count | 2.4a, 2.4b, 2.6 | `SafePdf/Core/Open.lean`, `SafePdf/Core/Parse.lean`, `SafePdf/Shell/Views/Summary.lean`, `scripts/corpus/dashboard.py`, `Tests/golden/header/` | wt | done (2026-11-19) |
| 2.12 | Compose `Unambiguous.checkSize` (object numbers < newest `/Size`) into `Open.openFile` strict validation (failure → repair path), and discharge 2.5's `SameAt` hypothesis with a prefix-stability lemma for `parseSection`/`matchAt`/`parseXrefStream` (parsers read `bytes.size` in range checks: state stability for successful parses when bytes are appended), plus the hybrid-update case of `loadChain_update` | 2.5, 2.11 | `SafePdf/Core/Open.lean`, `SafePdf/Spec/Unambiguous.lean`, `SafePdf/Spec/PrefixStable.lean` | wt | todo |
| 2.13 | M2 clause "Bogk-style cyclic files all rejected in bounded time": add a structured cycle error (e.g. `Error.cycle (offset) (what)` or a `malformed` kind tag) produced by `Chain.loadChain` (`/Prev`, `/XRefStm` cycles), `ObjStm` (object in its own stream) and `Length.resolveLength` (cyclic `/Length`); `Open.openFile` returns it without trying repair; prove `openFile_cycle` (a cycle error from strict ⇒ `openFile` returns that error); adversarial expectations for `xref-prev-cycle`, `xref-prev-self`, `objstm-self-container` become `open: error` | 2.11 | `SafePdf/Core/Error.lean`, `SafePdf/Core/Xref/Chain.lean`, `SafePdf/Core/Xref/ObjStm.lean`, `SafePdf/Core/Xref/Length.lean`, `SafePdf/Core/Open.lean`, `Tests/Adversarial.lean` | wt | todo |
Exit criterion checked: [ ]

## Phase 3 — Filters
Plan.md §6 Phase 3. Exit: **M3**: decompression-bomb suite (nested streams, 10⁶:1 ratios) all rejected within limits.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 3.1 | FlateDecode (inflate) in Lean, output ≤ limit or error, totality | 1.1 | `SafePdf/Core/Filter/Flate.lean` | new | done (2026-11-18) |
| 3.2 | PNG predictors with output-length law | 1.1 | `SafePdf/Core/Filter/Predictor.lean` | new | done (2026-11-18) |
| 3.3 | ASCIIHex, ASCII85, RunLength (fully proven) | 1.1 | `SafePdf/Core/Filter/Ascii.lean`, `SafePdf/Core/Filter/RunLength.lean` | new | todo |
| 3.4 | LZW (totality + bounds) | 1.1 | `SafePdf/Core/Filter/LZW.lean` | new | todo |
| 3.5 | Filter pipeline + DCT/JPX/JBIG2 placeholder (S7) | 3.1, 3.2, 3.3, 3.4 | `SafePdf/Core/Filter.lean` | new | todo |
| 3.6 | Decompression-bomb suite + differential vs zlib | 3.5 | `Tests/adversarial/bombs/`, `Tests/Bombs.lean` | wt | todo |
| 3.7 | Inspector view: decoded-stream viewer | 3.5 | `SafePdf/Shell/Views/Streams.lean` | wt | todo |
Exit criterion checked: [ ]

## Phase 4 — Document structure
Plan.md §6 Phase 4. Exit: **M4**: page count + page boxes match `qpdf` on corpus; encrypted publisher PDFs open.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 4.1 | Catalog + page tree with inheritance, acyclicity proof, total `getPage` | 2.5 | `SafePdf/Core/Doc.lean` | new | todo |
| 4.2 | Outline, named destinations, links, page labels (visited-set) | 4.1 | `SafePdf/Core/Doc/Nav.lean` | new | todo |
| 4.3 | Standard security handler (RC4, AES-128/256, empty user password) | 2.5 | `SafePdf/Core/Crypt.lean` | new | todo |
| 4.4 | Differential page count/boxes vs qpdf; inspector page-tree + outline browser | 4.1, 4.2 | `Tests/differential/pages.py`, `SafePdf/Shell/Views/Pages.lean` | wt | todo |
Exit criterion checked: [ ]

## Phase 5 — Content-stream interpreter
Plan.md §6 Phase 5. Exit: **M5**: operator coverage report ≥ 99% of corpus ops; interpreter never fails on corpus; inspector exports pages as SVG rendered from the DisplayList.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 5.1 | `DisplayList` type + graphics state | 4.1 | `SafePdf/Core/Content/DisplayList.lean`, `SafePdf/Core/Content/GState.lean` | new | todo |
| 5.2 | Interpreter: q/Q bounded stack, cm, color, paths, clipping, text ops, XObjects with fuel, inline images | 5.1, 3.5 | `SafePdf/Core/Content/Interp.lean` | new | todo |
| 5.3 | Inductive transition spec + impl proof | 5.2 | `SafePdf/Spec/Content.lean` | new | todo |
| 5.4 | Operator coverage report + SVG export view | 5.2 | `SafePdf/Shell/Views/Svg.lean`, `scripts/corpus/opcoverage.py` | wt | todo |
Exit criterion checked: [ ]

## Phase 6 — Fonts and text extraction
Plan.md §6 Phase 6. Exit: **M6**: text extraction ≥ 98% similarity vs pdfium/MuPDF on corpus; all glyph positions within tolerance.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 6.1 | TrueType (glyf + cmap) | 5.1 | `SafePdf/Core/Font/TrueType.lean` | new | todo |
| 6.2 | CFF | 5.1 | `SafePdf/Core/Font/CFF.lean` | new | todo |
| 6.3 | Type 1 | 5.1 | `SafePdf/Core/Font/Type1.lean` | new | todo |
| 6.4 | Type0/CIDFont Identity-H, `/Differences`, standard-14 metrics | 5.1 | `SafePdf/Core/Font/Encoding.lean`, `SafePdf/Core/Font/Std14.lean` | new | todo |
| 6.5 | ToUnicode CMaps + text extraction from DisplayList (C3, C6) | 6.4, 5.2 | `SafePdf/Core/Text.lean`, `SafePdf/Core/Font/CMap.lean` | new | todo |
| 6.6 | Text differential vs pdftotext; inspector text browser + overlay | 6.5 | `Tests/differential/text.py`, `SafePdf/Shell/Views/Text.lean` | wt | todo |
Exit criterion checked: [ ]

## Phase 7 — Rasterizer
Plan.md §6 Phase 7. Exit: **M7**: ≥ 95% of corpus pages within perceptual threshold; median page < 100 ms compiled.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 7.1 | ℚ geometric model + C2 coordinate round-trips | 5.1 | `SafePdf/Core/Raster/Geom.lean` | new | todo |
| 7.2 | Scanline fill (nonzero/even-odd), Bézier flattening with error bound, stroking, clipping, AA | 7.1 | `SafePdf/Core/Raster/Fill.lean`, `SafePdf/Core/Raster/Stroke.lean` | new | todo |
| 7.3 | Glyph outlines, images, soft masks, transparency groups, shadings | 7.2, 6.1 | `SafePdf/Core/Raster/Composite.lean` | new | todo |
| 7.4 | Pixel differential + timing budget; inspector raster output | 7.3 | `Tests/differential/pixels.py`, `SafePdf/Shell/Views/Raster.lean` | wt | todo |
Exit criterion checked: [ ]

## Phase 8 — Viewer shell + annotations
Plan.md §6 Phase 8, §8. Exit: **M8**: daily-drivable viewer on the corpus.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 8.1 | GUI toolkit decision (open question §8) | 7.4 | Decisions entry | solo | todo |
| 8.2 | Native shell: open/render/scroll/zoom/rotate, selection & copy, search, outline, links | 8.1 | `SafePdf/Shell/App/` | new | todo |
| 8.3 | Annotation appearance streams (`/AP`) | 5.2 | `SafePdf/Core/Annot.lean` | new | todo |
| 8.4 | Library packaging `safe-pdf-core` | 8.2 | `lakefile.toml` | wt | todo |
Exit criterion checked: [ ]

## Gotchas (append-only; read before every wave, pasted into every brief)
* `qpdf`, `mutool`, `pdftotext` are not installed on the dev machine (2026-11-18); differential scripts must skip cleanly when absent.
* Installed Lean toolchains: v4.31.0, v4.35.0, v4.36.0 (elan 4.2.4).
* Lake layout (0.1): exes `inspect` (root `SafePdf.Shell.Main`), `tests` (`Tests.Main`), `fuzz` (`Tests.Fuzz.Main`); `lake build` builds lib `SafePdf` + `inspect`; tests/fuzz need `lake build tests fuzz`. Shared registries: `SafePdf.lean` (umbrella imports), `Tests/Main.lean` (`suites` list), `lakefile.toml`.
* Single-file check `lake env lean <file>` (0.2) takes ~0.2 s and only sees modules already built in the main checkout; new files importing other unbuilt new files cannot be checked this way.
* Worktree subagents may be branched from `main`, not the phase branch: briefs must say to check `git log` first and `git reset --hard <phase-branch>` if the branch is empty (0.6).
* Forbidden-construct greps that don't strip comments trip on Core module docs naming `partial`/`sorry`; `scripts/check-hygiene.sh` strips comments/strings, so use it as the authority (0.3, 0.6).
* `scripts/check-hygiene.sh` needs `lake build` first (the axioms step imports built modules); options `--root DIR`, `--no-axioms`. Every phase adds `#print axioms` lines for its top-level theorems to `scripts/axioms.lean` (0.3).
* `!` rule in the hygiene guard is a broad `ident!` match in Core/Spec/Repair; an identifier legitimately ending in `!` needs an allowlist entry in `scripts/hygiene.py` (0.3).
* ByteArray in v4.36: `emptyWithCapacity`, `extract`, `++`, `foldl`, `push`, `bytes[i]?` work; set a byte with no `!`/proof via `⟨b.data.modify i f⟩` (no-op out of range) (0.6).
* Timing a pure call in IO: `match` on its result before re-reading `IO.monoNanosNow`, else the computation may float past the clock read (0.6).
* `SafePdf.Core.Parse`: `parseWith (limits) (bytes)` / `parse`; `Document` is a placeholder (`headerOffset`, `version`, `byteLength`) to be replaced in Phase 1/2 (0.6).
* Fuzz driver reads seeds from `Tests/adversarial` and `corpus` by default, so `scripts/fuzz.sh` results (input-hash) change as the corpus grows; determinism holds for a fixed seed set (0.6).
* Corpus: `python3 -I scripts/corpus/fetch.py` (≈4 min first run, 74 arXiv PDFs, 184 MB, into git-ignored `corpus/files/`); `--add URL`, `--summary`, `--reindex`. Unversioned arXiv URLs serve the latest version — use `…/pdf/<id>vN` for new entries (0.8).
* arXiv `/Producer` reflects arXiv's rebuild (pdfTeX recent, Ghostscript/dvips pre-2012, pikepdf on 2025+ IDs); read Producer via the trailer's `/Info`, not the last `/Producer` in the file (embedded figures) (0.8).
* Corpus gaps (0.8): no LuaTeX/XeTeX/LibreOffice document producers, no scanned or publisher PDFs, no SafeDocs/PDF Association samples (license/URL unverified).
* Adversarial files (0.9): `python3 -I Tests/adversarial/generate.py [--check]` is deterministic; never open them in a viewer. Not yet consumed by any Lean test (that is 2.7); Bogk mutations not generated yet.

* Lake v4.36 only builds modules that belong to a `lean_lib`; an exe's local imports outside any lib fail with "object file … does not exist". Lib `Tests` now uses `globs = ["Tests.+"]` (0.5).
* Golden tests: `Tests/golden/<suite>/<input>` + `<input>.expected`; renderers registered in `Tests/Golden.lean` (`renderers`); regenerate with `SAFEPDF_GOLDEN_UPDATE=1 lake exe tests` then review `git diff Tests/golden` (0.5).
* Inspector (0.10): `inspect [--json] [--view NAME] [--list-views] <file>...`; views are `SafePdf/Shell/Views/<Name>.lean` modules registered in `views` in `SafePdf/Shell/Inspect.lean`; shared types in `Views/Common.lean` (`Config`, `Input`, `View`, `jsonString`/`jsonObject`). A trailing bare word is a view only if it's not an existing path — prefer `--view`. Exit: 0 ok, 1 parse error, 2 usage/IO.
* Don't import `Lean` (e.g. `Lean.Json`) in Shell/Core: it links the compiler library into the exe; JSON is hand-rolled in `Views/Common.lean` (0.10).
* v4.36: `String.mk` deprecated → `String.ofList`; no `List.forM'` → `forM` (0.10).
* Differential runner (0.7): `python3 -I Tests/differential/run.py [--comparator N] [--files 'GLOB'] [--limit N] [--json OUT]`; comparators skip on missing tool; non-`size` comparators skip until the inspector has `objects`/`pages`/`text` views — update its unknown-view heuristic to use inspector exit code 2 (0.7, 0.10).
* CI (0.4): `.github/workflows/ci.yml`, actions pinned by SHA (checkout v4.2.2, cache v4.2.0), `elan-init.sh` at elan v4.4.0 commit (elan binary itself not hash-pinned); `.lake` cache key includes all `*.lean` hashes — bump the `lean-` prefix on stale-cache trouble.
* Subagent Bash in worktrees: complex compound heredoc commands may be refused by the permission check; tell subagents to use the Write tool for new files (0.10).
* Object model (1.1): `PdfObject` = direct objects only; streams only in `IndirectBody.stream` of `IndirectObject {num, gen, body}`. Strings/names are decoded `List UInt8`; stream data `ByteArray`. Reals are `Decimal {mantissa, scale}`, canonical via `Decimal.normalize`; printer must print scale-0 reals with a `.` (e.g. `5.0`). `Dict := List (Name × PdfObject)`, `Dict.lookup` first match, `Dict.get?` treats null as absent. State round-trip over `PdfObject.Canonical` (decidable `isCanonical`).
* v4.36: `deriving DecidableEq` fails on nested inductives (`List T` fields) — hand-write from a mutual Boolean `beq` + soundness/reflexivity proofs (as in `Core/Object.lean`). `deriving BEq`/`Repr` work. `ByteArray` has `DecidableEq` but no `Repr`. Mutual structural recursion through `List`/`List (A × T)` needs no `termination_by` (1.1).
* v4.36: `decide` gets stuck on `String.toUTF8` — use `#guard` or literal byte lists; `if_false` deprecated → `ite_false`; `simp [f]` in case branches may leave `x ≤ max x y` → `Nat.le_max_left` (1.1).
* Dashboard (0.11): `python3 -I scripts/corpus/dashboard.py [--compare docs/dashboard.json [--write]]`; compare re-runs the inspector and exits 1 on regressions; `docs/dashboard.json` changes every run (timings/date), so use `--compare`, not diff. Regenerate `docs/dashboard.md` at each milestone.
* Lexer contract (wave 6): `SafePdf/Core/Token.lean` (orchestrator-owned) fixes `Token`, `LexError {offset, kind}` and the `next` signatures; Spec `Spec.Lex.next : List UInt8 → Except LexError (Option (Token × List UInt8))` (offsets relative), Core `Core.Lex.next : ByteArray → Nat → …(Token × Nat)` (offsets absolute). Name errors: leftmost problem decides the kind. A randomized differential check (61,500 input/position pairs, 0 disagreements) ran at integration; 1.6 should keep it as a test.
* Spec lexer structure (1.2): `next l = nextAt (l.length - (skipWs l).length) (skipWs l)`; helpers `skipWs/skipComment` (mutual structural), `regularRun`, `lexNumber` (decides the whole run after the fact), `litBody` (well-founded, `termination_by l.length`, depth counts extra opens from 0), `hexBody` + `packNibbles`, `decodeName`. Spec `lexAll` offsets are relative to its input.
* Core lexer structure (1.3): `next bytes pos = tokenAt bytes (skipWs bytes pos false)`; scanners `readRun`, `litStr` (depth from 1, ends on `)` at depth ≤ 1, escapes via `escapeAt`/`octalAt`), `hexStr` (pending high nibble), `nameRun`; all accumulators are reversed lists; `next_pos` gives progress. `lexAll` ≈ 1.9 MB/s interpreted (#eval).
* v4.36 proofs: nested `match bs with | c :: cs => match cs …` breaks structural recursion → `termination_by` + named matches (`match h : …`, name `_h` if unused); `if_pos/if_neg/dif_pos/dif_neg` deprecated (use `simp`, `dite_eq_left/right`); `split at h` fails behind `let` — pass the scrutinee as a function parameter; `getElem?_neg` works for `ByteArray`; `fun_induction` IH names unreliable → `rename_i` (1.2, 1.3).
* **C5 for the lexer is proved** (1.6): `SafePdf.Spec.LexEquiv.next_eq` (no hypothesis on `pos`) and `lexAll_eq` (plain equality). Proof pattern (seed for 1.9): one `restAt` bridge (`restAt_cons`, `restAt_nil`, `length_restAt`), one lemma per scanner via `fun_induction` with generalized accumulators (`acc.reverse ++ ·`, position = `size - rest.length`), unfold well-founded spec functions one step with `conv => lhs; rw [f.eq_def]`, `generalize` before dependent matches, `decide` over all 256 bytes for byte-class facts, dispatch by `by_cases` on first byte, suffix lemmas for iteration.
* Object grammar spec (1.4): `Spec.Object.Parses/ParsesItems/ParsesEntries` (fuel, input, object, rest) + executable `parse/parseItems/parseEntries` (well-founded on `(ts.length, 0|1)`); `parse_eq_ok_iff`, `parse_isError_iff`, `Parses.unique` (S6), `Parses.depth_le`, `Parses.length_lt`, `Parses.canonical` (needs canonical real tokens + NUL-free name tokens) — all proved. `rw [parseItems] at h` leaves a side goal → `rotate_left`.
* Object parser (1.5): `Core.ObjParse.parseObj fuel bytes pos` → `parseObjTok` (mutual with `parseArray`/`parseDict`, reversed acc, measure `(fuel, size - pos)`); loops guard recursion with `if _hr : pos < r` (else branch unreachable — 1.8 discharges it via `parseObjTok_pos`); ref lookahead `parseIntTail` re-lexes (≤3 lexes per int); dict duplicate check `hasKey` is O(n²) (10k keys: 4 s interpreted). `parseIndirect` handles `n g obj … endobj` and streams with direct `/Length`; indirect `/Length` → `Error.unsupported`.
* **For 1.8**: the core parser lexes lazily and never sees lexer errors after the object's last token (`1 0 R )` succeeds), and a lexer error inside the ref lookahead (`5 )`) is an error. So the equivalence must be stated against the spec run on the tokens actually lexed (a lazily produced token prefix), not on `Spec.Lex.lexAll` of the whole input; compare successes exactly and failures only as "both fail".
* Hygiene guard: `s!`/`m!`/`f!` interpolation macros are exempt from the `ident!` rule (fixed at wave 7 integration); `get!`/`head!` etc. still flagged.
* v4.36: `conv_lhs`, `swap`, `on_goal` are Mathlib-only — use `conv => lhs; …`, `case neg => …`, `rotate_left`; `show` is a keyword (can't name a helper `show`); `Except` has no `BEq` (compare via `Sum` in tests); no `List.nodup_reverse` (use `List.pairwise_reverse`); `simp` equation lemmas don't fire on functions with overlapping patterns → `rw [f.eq_def]`; mutual theorem blocks need every member recursive (else "unused termination_by"); `↓reduceDIte`/`↓reduceIte` in `simp only` reduce termination guards (1.4–1.6).
* **M1 round trip proved** (wave 8): `SafePdf.Spec.RoundTripCore.parseObject_print : o.Canonical → RefsInRange o → o.depth ≤ limits.maxObjectDepth → ∃ r, Core.ObjParse.parseObject limits (print o) 0 = .ok (o, r)` — composes 1.7 (`lexAll_print`, `parse_printTokens`) with 1.8 (`parseObj_of_spec_full`). Exact end position (`r = (print o).size`) would need `dropToks (printTokens o).length (printObj o) = some []` + `ObjEquiv.parseObj_of_spec_full_size` — optional strengthening.
* Printer (1.7): `printObj o = render (printTokens o)`, tokens joined by one SP, no leading/trailing whitespace; ints via own `natDigits`; reals always with `.` (`5.`, `-3.5`, `0.005`); strings always hex `<…>` uppercase; names keep 0x21–0x7E non-delimiter non-`#`, else `#XX`. `RefsInRange` (n ≥ 1, g ≤ 65535) lives in `Core/Print.lean` — `Canonical` does not cover ref ranges.
* Parser equivalence (1.8): `ObjEquiv.LexFrom bytes p ps` (lazy token stream with end positions), `parseObj_ok_iff`/`parseObj_error_iff` (given `LexFrom`), `_lexAll` variants (whole remainder lexes), `parseObj_of_spec_full(_size)`, `dropToks`. Proof: one induction on token count replaces the mutual well-founded recursion; unfolding lemmas for the impl loops (`parseArray_none/_some`, `parseDict_*`) via `rw [f]; split`. `Core.ObjParse.keywordObj`/`kwR` are `rfl`-equal to the spec's.
* Golden suites (1.10): `objects` (24) and `indirect` (9) via test-only renderer `Tests/ObjRender.lean`; `Core/Parse.lean` gains `parseObjectAt`/`parseIndirectAt`. Fuzz driver runs 6 entry points per iteration with per-entry summaries; slowest-call timings on a separate `fuzz: timing` line (not deterministic). 220k iterations: 0 slow, 0 crashes, slowest 6 ms.
* `decode`/`unfold` pitfalls (1.7): `unfold f` also rewrites inside `flatMap` and breaks IHs — use small `rw` lemmas; `rw [← h]` with `h : f x = x` rewrites every occurrence; ambiguous dotted constructors (`.int`) → write `PdfObject.int` (1.8).
* `docs/proof-patterns.md` (1.9) documents the spec/impl/equivalence pattern with cited snippets; its "TODO (after 1.7/1.8)" section is still to be filled (fold into 1.12 or later doc pass).
* Inspector `objects` view (1.12): `inspect --view objects [--json] [--all] FILE` — Shell-level linear scan for `int int obj`, `parseIndirectAt` each, last (num, gen) wins unless `--all`. JSON lines per the 1.11 contract + `{"summary": …}`; K = successfully parsed objects. Exit code still comes from the header check (header-less inputs exit 1 with valid output). ~1 MB in 30 ms.
* qpdf comparator (1.11): `Tests/differential/objects.py` (`--ours F --qpdf F` offline mode; fixtures in `Tests/differential/fixtures/`), plugged into `run.py` as `objects`. Uses `qpdf --json=2 --json-key=qpdf --decode-level=none` — **needs qpdf ≥ 11 (JSON v2)**: ubuntu-22.04 has 10.6, use ubuntu-24.04. qpdf exit 3 (warnings) = success; other failures → skip (watch the skipped count). Normalizes strings/names to bytes, numbers to Decimal (int vs real = warning), drops `/Length` and null dict entries, ignores trailer. Never run against real qpdf yet; unverified assumptions listed in its docstring.
* Classic xref (2.1): `Core.Xref` — `XrefEntry` (free/inUse/compressed), `XrefSection {entries : List (Nat × XrefEntry), sorted}` (strictly ascending ⇒ one entry per object, merge-friendly for 2.2/2.5), `Trailer.ofDict` (`size`, `prev?`, `root?`, `xrefStm?`, `encrypted`; null = absent), `findStartxref` (last `startxref` in final 1024 bytes, strict `%%EOF`), `parseXrefTable`; `entryAt_eq` bridges the 20-byte reader to `entrySpec`. Not checked here: object numbers vs `/Size`, `/Prev`/`/XRefStm` offsets (2.2 must range-check before following). No acceptance-completeness theorem.
* v4.36: `simp` can't rewrite a dependent `match hh : f x` after `rw [f]` — use the dead-guard trick (proof-patterns §3.2); `simp only [f]` unfolds recursively, `rw [f]` unfolds one step; core has `List.mergeSort`, `mem_mergeSort`, `length_mergeSort` (2.1).
* **xref `/Prev` termination proved** (2.2): `Core.Xref.Chain.walk` carries a Nodup visited list of offsets < size, measure `bytes.size - visited.length`, heart lemma `length_lt_of_fresh` (via core `List.Nodup.length_le_of_subset` into `List.range n`). `Spec.XrefTerm.loadChain_cycle_rejected` covers cycles of every length (error kind not pinned: a >4096-revision tail hits the limit first); `loadChainCounted_calls_le` (parses ≤ size and ≤ 4096); `mergeChain_lookup` (newest revision wins). Adversarial `xref-prev-self`/`xref-prev-cycle` rejected with "xref /Prev cycle" (#guard, byte-exact embeds). `/XRefStm` not followed; `/Prev` to an xref stream errors (2.4).
* Indirect `/Length` (2.3): `Core.Xref.Length.resolveLengthAux` (count × result, structural on fuel, visiting check first), `parseIndirectResolved lookup limits bytes fuel pos` (keeps the original dict, data = resolved length); `length-self-ref.pdf` → "cyclic /Length"; `length-mutual.pdf` only "unsupported" until xref streams (2.4) — replace its hand-built lookup then. Duplicates `parseHeader`/`parseIndirectBody`/`tokenAt_pos` from ObjParse/Lex (task 2.10).
* Repair (2.6): `Repair.scanObjects` byte-level `headerAt` at boundaries + `parseIndirect` jump-past, newest wins (`mergeSort keyLe` + `keepAsc`), cap `maxObjects`; `scanSection` builds a sorted `XrefSection` with `(0, free 0 65535)`; `repair` errors only on no objects / no root. Failure budget 256: after it, headers are recorded but not parsed (bounds attempts but not bytes read per attempt; adversarial 1 MB of `1 0 obj (` = 60 s interpreted). Indirect-/Length streams fail fast and are not jumped over (fake headers inside can be reported) — fix in 2.10. Xref-stream trailers aren't candidates (loses `/Encrypt`) until 2.4.
* CI job `differential-objects` (1.13) on ubuntu-24.04 with apt qpdf (asserts ≥ 11), corpus cached on manifest hash, debug step printing qpdf/inspector heads, `run.py --min-compared 20`; artifact via upload-artifact v4.6.2 `ea165f8d65b6e75b540449e92b4886f43607fa02`. **First run not yet seen** — the next wave must read it, fix comparator assumptions, triage into `docs/deviations-from-spec.md`, then check M1.
* Permission: a subagent brief asking to push/delete temporary remote branches to iterate on CI was refused by the permission classifier (wave 10). Keep subagents local; the orchestrator pushes only phase branches and reads CI in the next wave.
* v4.36: no `List.Nodup.subperm` (use `List.Nodup.length_le_of_subset`); `Option.noConfusion` on `none = some _` fails → `cases`; `<+` not available unqualified → `List.Sublist`; `(d, ·)` inside `.map` doesn't parse → `fun r => (d, r)`; `parseStreamBody` has a `let` → `dsimp only at h` before `split` (2.2, 2.3, 2.6).
* **First qpdf comparison run** (CI run 44402582274, wave 11): 74 files, 73 with objects compared; 55,870 / 55,902 objects agree; 9,912 qpdf-only (object streams); 287 our errors (not yet triaged — mostly indirect `/Length` streams, expected until the resolved parser is wired into the view); 32 disagreements, all `/Group N 0 R` → free object N ⇒ D-001 `dangling-ref-null` in `docs/deviations-from-spec.md` (comparator now warns instead); 1 error: inspector timeout on arxiv-2307.09288 (13.7 MB) → task 1.14.
* Flate (3.1): `Core.Filter.Flate` — output buffer `Out limit := {b : ByteArray // b.size ≤ limit}` makes the bound structural; puff-style canonical Huffman (`counts`/`symbols`, bit-by-bit `decodeGo`, fuel 15); `inflate`, `inflateAt` (returns bit pos), `zlibDecode … (checkAdler := true)`, `flateDecode limits`; `set_option maxRecDepth 4000 in` needed for `codes`. Interpreted speed: ~0.34 MB/s Huffman-heavy, ~2.9 MB/s back-ref-heavy, ~5 MB/s stored — compiled speed unmeasured (Plan §8 open question). Work-bound theorem (c) NOT proved (follow-up). 40 KB hex vectors live in the Core file (move to Tests later). Use zlib's 32-code fixed distance table (puff's 30 is incomplete and `build` rejects it).
* Predictors (3.2): `Core.Filter.Predictor` — `Params.ofDict` (Table 10 defaults, `/Colors` ≤ 32, `/Columns` ≤ 2^24), shared `unfilterByte` for spec and impl, `decodePng_size` (exact length law), `decode_size_le` (output ≤ input, so no new limit); partial rows are strict errors; TIFF 2 for bpc 8/16 only.
* Adversarial suite (2.7): `Tests/Adversarial.lean` (suite `adversarial`) with an expectations table + 141 deterministic mutations of the cyclic files; `SAFEPDF_ADV_VERBOSE=1` prints every result; all calls < 5 ms compiled. Tighten `length-mutual`/`objstm-*` rows to real cycle errors when 2.4 lands.
* Limits (2.9): `Limits.maxRevisions := 4096` (→ `limitExceeded .revisions`), `Limits.maxRepairFailures := 256`; theorems restated over the fields.
* v4.36 (wave 11): `Subtype.property _` fails higher-order unification on subtype-valued results — wrap in an `Except` helper and project; a `let i := …` inside a termination-checked body yields copies `omega` treats as unrelated — inline it; `bs[k]? = bs.data[k]?` for ByteArray isn't closed by `simp` — use `getElem?_pos`/`getElem?_neg`; `ite_eq_left_of_eq_true` replaces deprecated `if_pos`.
* Usage gate: the loop checks `mcp__ccd_session_mgmt__get_usage` before each wave (gate 95%); at 100% of the 5-hour window it waits for the reset (wave 11 integration was deferred across one reset).
* Inspector timeout root cause (1.14): after a failed stream parse the Shell scan lexed binary stream data; each unbalanced `(` made `Core.Lex.litStr` run to EOF ⇒ O(#`(` × size). Fix (Shell only): resume after the next `endstream` for failed streams, and re-parse indirect-`/Length` streams via `Core.Xref.Length.parseIndirectResolved` with a lookup from scanned headers. Corpus: max 0.12 s/file (was > 20 s), 67,474 objects (was 54,678), 1 error (`arxiv-2512.00001` obj 37 duplicate key — genuine). **Residual risk:** any caller that retries the lexer byte-by-byte over garbage is quadratic (Core is linear per call; repair is capped by `maxRepairFailures`).
* Xref streams (2.4a): `Core.Xref.Stream.parseXrefStream`; `Chain.parseSection` dispatches table vs stream; `walk` recurses through a non-recursive `step` returning a proof-carrying `StepOk` record (fresh, distinct, in-bounds offsets) — `fun_induction walk` stays clean. Hybrid `/XRefStm` parsed in the same step (visited, counts toward `maxRevisions`; cycle → "xref /XRefStm cycle"); lookup order table → its XRefStm → older. Unknown entry types → `free 0 0` (§7.5.8.3). `PrevStep`/`Terminal` now mean "`parseSection` ok" (`PrevStep.of_table` shows the old relation is contained — cycle theorem strengthened). All 74 corpus files `loadChain` in 2–27 ms (66 single table, 4 two tables, 2 pure xref streams, 2 hybrid).
* Object streams (2.4b): `Core.Xref.ObjStm` — `ObjStm` structure carries proof fields (sorted offsets, bounds, nums ≥ 1, distinct via mergeSort-neighbour check, not O(n²)); `fetchCompressed lookup limits bytes fuel num` does ≤ 1 container parse + ≤ 1 decode (`fetchCompressed_work`), container must be `inUse … 0` (nested/self → error; `fetchCompressed_rank` is the Plan §5.2 rank argument). Strict: extra header tokens and non-whitespace after the last object are errors (may cost corpus files — watch the qpdf comparison).
* Adversarial expectations updated at wave 12 integration: `length-mutual.pdf` `loadChain` now `.ok` (its attack is the `/Length` cycle at resolution time, still asserted as an error); `objstm-self-container.pdf` now asserts "own object stream". A subagent may not edit `Tests/` expectations; the orchestrator does it at integration with a comment explaining why.
* v4.36 (wave 12): `omega` ignores list equalities like `h : os.entries = entries` — `rw` first; after `split at h` prefer `next a b hn =>` to `rename_i`; `simp only [h, ↓reduceIte]` replaces `if_pos/if_neg`.
* Unambiguity (2.5): `Spec.Unambiguous.resolveEntry limits bytes n`; `resolveEntry_eq_some_iff` (newest revision wins, index form), `resolveEntry_winner_unique`, `mergeChain_keys_nodup`/`mergeChain_mem_unique`, `resolveEntry_hybrid_table`/`_stream`, `checkSize` + `resolveEntry_lt_size`; `loadChain_update` (incremental update prepends one revision) holds under a `SameAt` hypothesis at old offsets — not yet discharged (task 2.12); update must not itself be hybrid. `/Size` is NOT enforced by `loadChain` for classic tables (only by xref streams) — `checkSize` composes in 2.12.
* Refactor (2.10): `ObjParse.parseHeader`, `parseIndirectBodyWith`/`parseStreamBodyWith` take `LengthResolver := Dict → Nat → Except Error Nat` (Nat = error offset); `Length.parseIndirectResolved` = header + body with `lengthOf`; `Lex.tokenAt_pos` (`next` unfolds to `tokenAt (skipWs …)`). Repair retries indirect-/Length streams once via a lazily built header table (`headerTable`, binary-search `tableLookup`), charged to the failed attempt (`scanAttempts_le` unchanged). Unproven cost: a successful retry may do up to 1 + t length-object parses (documented in Repair "Bounds"). Error order changed in `parseIndirectResolved` (EOL check before /Length resolution).
* qpdf lists free objects in its JSON as `{"value": null}` — the D-001 rule now also accepts a dangling target present on the qpdf side with value null (CI run 44410513896: timeout gone, 67,441/67,473 agree, all 32 disagreements were this case).
* v4.36 (2.5): `dite_eq_left_of_eq_true`, `dite_eq_right_of_eq_false`, `ite_eq_right_of_eq_false` take `eq_true h`/`eq_false h`; `unfold` of a match-defined function doesn't reduce on cons — add a `f_cons := rfl` lemma.
* Open (2.11): `Core.Open.openFile limits bytes : Except Error OpenDoc` (strict `loadChain`+`mergeChain`, else `Repair.repair`; both fail → strict error); `OpenDoc.getObject d limits n g` (binary search on `index`, free/absent/gen-mismatch → `.obj .null`); `openFile_strict`, `openFile_repaired`, `openFile_root`, `getObject_depth`, `getObject_work`; `Document` = header fields + `doc : OpenDoc` + `root`.
* Depth after 2.10: use `Core.Open.parseIndirectBodyWith_depth` (any `LengthResolver`; stream dict via `ObjParse.parseStreamBodyWith_ok`'s `s.dict = d`) — `Length.parseBodyResolved` no longer exists.
* Repair scans only classic `N G obj` headers: a repaired file whose `/Root` lives in an object stream fails validation. Hybrid merge puts the table first, so a table `free` entry hides an XRefStm `compressed` one (not seen in the corpus).
* Core unit checks: `#guard` (not `native_decide`) so no extra axiom appears.
* `.gitignore`'s `corpus/files/` does not match a symlink `corpus/files` — never symlink it in a worktree, it gets committed.

## Decisions and deviations from the design document
* 2026-11-18 (0.1) — Toolchain pinned to `leanprover/lean4:v4.36.0`; **no Lake dependencies** (no Mathlib, no Batteries) to start, for build speed and a small trusted base. Termination measures that Plan.md §5.2 sketches with `Finset ℕ` use core-Lean structures (e.g. `List Nat`/bitmaps with explicit size measures) instead. Adding Mathlib later needs a new Decisions entry.
* 2026-11-18 (0.1) — `autoImplicit = false` project-wide.
* 2026-11-18 (1.1) — Object model decisions: direct/indirect split (streams never nested); exact decimal reals, never Float (round-trip); decoded `List UInt8` strings/names for proof ergonomics; strict parser **rejects duplicate dictionary keys** (S6; ISO 32000-2 §7.3.7 leaves them undefined), repair path may keep the last occurrence; integer/ref range checks live in the lexer/parser, not the model.
* 2026-11-18 (wave 5) — Task 1.1 (phase 1) was pulled into the last phase-0 wave per the next-phase fill rule; it landed on `phase-0-infra` and ships in PR #1.
* 2026-11-18 (1.4/1.5) — A reference `n g R` with out-of-range numbers (n < 1 or g > 65535) is an error in the strict path, never a fallback to integers (lenient readers differ; repair path may relax). A lexer error inside the 2-token reference lookahead is an error.
* 2026-11-18 (2.2/2.6) — Local resource constants pending move into `Limits` (task 2.9): `maxRevisions := 4096` (revision-chain cap, reported as `limitExceeded .objects` for now) and repair `failBudget := 256` (failed parse attempts before the repair scan stops parsing). Accepted provisionally: they keep S3 bounds explicit and proven; the budget bounds attempts, not bytes per attempt.
* 2026-11-18 (1.13) — New CI dependency: apt `qpdf` on `ubuntu-24.04` (11.x, version asserted ≥ 11, not hash-pinned) for the differential job only; plus `actions/upload-artifact` v4.6.2 pinned by SHA. The trusted build job is unchanged.
* 2026-11-18 (wave 11) — Pulled 3.1 (Flate) and 3.2 (PNG predictors) from phase 3 ahead of the next-phase rule: they block 2.4 (xref streams), and Plan.md §6 Phase 2 says xref streams "need Flate + PNG predictors from Phase 3 — co-develop". They land on the current phase branch.
* 2026-11-18 (2.4a) — Hybrid files (§7.5.8.4): the classic table's entries take precedence; its `/XRefStm` stream fills the gaps (same as pdf.js/MuPDF). The XRefStm's own `/Prev`/`/XRefStm` are ignored. Unknown xref-stream entry types are treated as free (§7.5.8.3: references to them are null).
* 2026-11-19 (2.11) — `openFile` falls back to repair when strict fails, so Bogk `/Prev` cycles currently open as `repaired`. That contradicts M2 ("cyclic files all rejected") and Plan §10 item 3 ("fail fast and cleanly"); not weakened — M2 stays unticked until 2.13 makes cycle errors final. Corpus result on 91d9031: 74/74 open strict, 68,573/68,574 objects resolve (the 1 failure is a real duplicate key, rejected by the strict object parser per the 1.1 decision).

## Blocked / questions for the human
* 2026-11-18 (1.11) — **`qpdf` is not installed** on the dev machine, and M1's third clause needs "property tests vs `qpdf --json` object dumps on corpus". Options: (a) the human runs `brew install qpdf` locally (adds a system tool — your call); (b) run the qpdf comparison in CI (`apt-get install qpdf` on ubuntu-latest, pinned version) on a corpus slice fetched in CI or on `Tests/adversarial` + golden inputs only. The loop will implement the comparator so it works in either setup and pick (b) for evidence unless told otherwise.

## Log (append-only; one line per integrated wave)
* 2026-11-18 — wave 0 (phase 0, PR #1): ledger bootstrapped from Plan.md; draft PR opened; commit "wave 0: ledger"
* 2026-11-18 — wave 1 (phase 0, PR #1): 0.1 done (Lake scaffold, builds; `lake exe tests` passes smoke suite); commit "wave 1: 0.1 — Lake scaffold"
* 2026-11-18 — wave 2 (phase 0, PR #1): 0.2 done (CLAUDE.md: commands, build-isolation rule, registries, conventions); commit "wave 2: 0.2 — CLAUDE.md"
* 2026-11-18 — wave 3 (phase 0, PR #1): 0.3, 0.6, 0.8, 0.9 done (hygiene guard; parse stub + fuzz driver; 74-PDF arXiv corpus; 9 adversarial PDFs); none returned; commit "wave 3: 0.3 0.6 0.8 0.9 — hygiene guard, fuzzer, corpus, adversarial seeds"
* 2026-11-18 — wave 4 (phase 0, PR #1): 0.4, 0.5, 0.7, 0.10 done (CI workflow; golden harness + `Tests` lib in lakefile; differential runner; inspector with view registry); none returned; commit "wave 4: 0.4 0.5 0.7 0.10 — CI, golden tests, differential runner, inspector"
* 2026-11-18 — wave 5 (phase 0, PR #1): 0.11, 1.1 done (corpus dashboard; object model with 30 theorems); none returned; phase 0 exit criterion ticked; commit "wave 5: 0.11 1.1 — corpus dashboard, object model"
* 2026-11-18 — phase 0 milestone: PR #1 marked ready for review (CI green on cf2daba)
* 2026-11-18 — wave 6 (phase 1, PR #2): 1.2, 1.3 done (lexer spec, 13 theorems; tokenizer, `next_pos` progress); shared `Core/Token.lean` written by orchestrator; Core vs Spec agree on 61,500 random cases; commit "wave 6: 1.2 1.3 — lexer spec and tokenizer"
* 2026-11-18 — wave 7 (phase 1, PR #2): 1.4, 1.5, 1.6 done (object grammar spec + unambiguity; object/indirect parser; **lexer impl ≡ spec proved**); hygiene guard fixed for `s!`; 72 theorems axiom-checked; commit "wave 7: 1.4 1.5 1.6 — object grammar spec, object parser, lexer equivalence proof"
* 2026-11-18 — wave 8 (phase 1, PR #2): 1.7, 1.8, 1.9, 1.10 done (printer + spec round trip; object parser ≡ spec; proof-patterns doc; fuzz/golden wiring) + orchestrator `Spec/RoundTripCore.lean` (**M1 `parseObject (print o) = o` proved**); 86 theorems axiom-checked; commit "wave 8: 1.7 1.8 1.9 1.10 — printer, round trip, parser equivalence, proof patterns, fuzz/golden wiring"
* 2026-11-18 — wave 9 (phase 1, PR #2): 1.11, 1.12, 2.1 done (qpdf object comparator, offline-tested only; inspector `objects` view; classic xref table + trailer, pulled from phase 2); added 1.13 (run the qpdf comparison in CI on the corpus) as the remaining M1 step; 97 theorems axiom-checked; commit "wave 9: 1.11 1.12 2.1 — qpdf comparator, objects view, classic xref"
* 2026-11-18 — wave 10 (phase 1, PR #2): 1.13 done (qpdf CI job written; first run pending), 2.2 (**`/Prev` chain termination + cycle rejection proved**), 2.3 (indirect /Length), 2.6 (repair) done; first 1.13 brief refused by the permission classifier (remote temp branches) and re-scoped to local-only; added 2.9 (limits into `Limits`) and 2.10 (ObjParse refactor); 123 theorems axiom-checked; commit "wave 10: 1.13 2.2 2.3 2.6 — qpdf CI job, /Prev termination, indirect /Length, repair"
* 2026-11-18 — wave 11 (phase 1, PR #2): 2.7, 2.9, 3.1, 3.2 done (adversarial suite + 141 mutations; limits into `Limits`; Flate decoder with output-bound proof; PNG/TIFF predictors with length law; 3.1/3.2 pulled from phase 3 for xref streams); first qpdf CI run triaged (D-001 dangling-ref-null; comparator rule added); added 1.14 (inspector timeout on a 13.7 MB file); 137 theorems axiom-checked; commit "wave 11: 2.7 2.9 3.1 3.2 — adversarial suite, limits, Flate, predictors"
* 2026-11-18 — wave 12 (phase 1, PR #2): 1.14 (inspector timeout fixed: 13.7 MB file 0.10 s), 2.4a (xref streams + hybrid in the chain walk, all 2.2 theorems kept), 2.4b (object streams, no-recursion rank lemma) done; adversarial expectations tightened for xref-stream files; 2.10 deferred (overlap with 1.14); 158 theorems axiom-checked; commit "wave 12: 1.14 2.4a 2.4b — inspector perf, xref streams, object streams"
* 2026-11-18 — wave 13 part 1 (phase 1, PR #2): 2.5 (S6 unambiguity, `SameAt` hypothesis open → 2.12), 2.10 (shared indirect-object parsing; repair skips indirect-/Length streams) done; qpdf comparator D-001 rule extended to null-valued targets; added 2.12; 173 theorems axiom-checked; commit "wave 13 (part 1): 2.5 2.10 — S6 unambiguity, parser refactor, comparator null-target rule"
* 2026-11-19 — wave 13 part 2 (phase 1, PR #2): 2.11 done (`openFile`, real `Document`, `--view resolve`, dashboard M2 columns; depth proof re-done against the 2.10 API at merge); corpus 74/74 open, 99.999% objects resolve; added 2.13 (cycle errors must not be repaired, M2 clause 2); commit "wave 13 (part 2): 2.11 — document opening"
