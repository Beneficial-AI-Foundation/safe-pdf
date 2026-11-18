# safe-pdf progress ledger

Maintained by `/next-wave`. The orchestrator is the only writer of this file.
Parallel limit: 4
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
(empty)

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
| 1.4 | Object grammar spec `SafePdf/Spec/Object.lean` (`ObjSpec : List Token → PdfObject → Prop` + executable spec) and unambiguity lemma | 1.2 | `SafePdf/Spec/Object.lean` | new | todo |
| 1.5 | Efficient object parser `SafePdf/Core/ObjParse.lean` (arrays, dicts, refs `n g R`, nesting depth limit from `Limits`) | 1.3 | `SafePdf/Core/ObjParse.lean` | new | todo |
| 1.6 | Lexer equivalence proof `SafePdf/Spec/LexEquiv.lean`: `Core.lex bytes = Spec.lex bytes` (C5) | 1.2, 1.3 | `SafePdf/Spec/LexEquiv.lean` | new | todo |
| 1.7 | Printer `SafePdf/Core/Print.lean` + round-trip theorem `parse (print o) = o` in `SafePdf/Spec/RoundTrip.lean` | 1.4, 1.5 | `SafePdf/Core/Print.lean`, `SafePdf/Spec/RoundTrip.lean` | new | todo |
| 1.8 | Parser equivalence proof `SafePdf/Spec/ObjEquiv.lean`: impl ≡ spec (C5) | 1.4, 1.5, 1.6 | `SafePdf/Spec/ObjEquiv.lean` | new | todo |
| 1.9 | `docs/proof-patterns.md`: the spec/impl/equivalence pattern as established by 1.6/1.8 (§9 bus-factor mitigation) | 1.6 | `docs/proof-patterns.md` | new | todo |
| 1.10 | Wire `parse` (object level) into fuzz driver and golden tests; seed golden files for each object type | 1.5, 0.5, 0.6 | `SafePdf/Core/Parse.lean`, `Tests/golden/objects/`, `Tests/Fuzz/` | wt | todo |
| 1.11 | Property tests vs `qpdf --json` object dumps on corpus (extends `Tests/differential/`) | 1.5, 0.7, 0.8 | `Tests/differential/objects.py` | new | todo |
| 1.12 | Inspector view `objects`: pretty-printed object tree, diffable against `qpdf --json` | 1.7, 0.10 | `SafePdf/Shell/Views/Objects.lean`, `SafePdf/Shell/Inspect.lean` | wt | todo |
Exit criterion checked: [ ]

## Phase 2 — File structure: xref, trailer, revisions ★
Plan.md §6 Phase 2, §5.2, §5.4. Exit: **M2**: 99% of corpus opens (strict or repaired); Bogk-style cyclic files all rejected in bounded time; first machine-checked proof that PDF xref resolution terminates on arbitrary input.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 2.1 | Classic xref tables + trailer parsing `SafePdf/Core/Xref.lean` | 1.8 | `SafePdf/Core/Xref.lean` | new | todo |
| 2.2 | `/Prev` chain resolution with visited-offset measure + termination proof (§5.2) | 2.1 | `SafePdf/Core/Xref/Chain.lean`, `SafePdf/Spec/XrefTerm.lean` | new | todo |
| 2.3 | Indirect `/Length` resolution with fuel = object count; self-dependency is an error | 2.1 | `SafePdf/Core/Xref/Length.lean` | new | todo |
| 2.4 | Xref streams + object streams (needs Flate + PNG predictors — co-develop with 3.1/3.2); rank argument for containers | 2.2, 3.1, 3.2 | `SafePdf/Core/Xref/Stream.lean` | new | todo |
| 2.5 | Unambiguity S6: newest-revision-wins, one winner per object id; hybrid `/XRefStm` | 2.2, 2.4 | `SafePdf/Spec/Unambiguous.lean` | new | todo |
| 2.6 | Repair path `SafePdf/Repair.lean` (offset-tolerant `N 0 obj` scan), totality + bound proofs | 2.1 | `SafePdf/Repair.lean` | new | todo |
| 2.7 | Adversarial regression: all `Tests/adversarial/` files rejected in bounded time | 2.2, 2.3, 0.9 | `Tests/Adversarial.lean` | wt | todo |
| 2.8 | Inspector views: xref trace, revision history, repair report | 2.5, 2.6 | `SafePdf/Shell/Views/Xref.lean` | wt | todo |
Exit criterion checked: [ ]

## Phase 3 — Filters
Plan.md §6 Phase 3. Exit: **M3**: decompression-bomb suite (nested streams, 10⁶:1 ratios) all rejected within limits.
| ID | Task | Needs | Owns | Par | Status |
|---|---|---|---|---|---|
| 3.1 | FlateDecode (inflate) in Lean, output ≤ limit or error, totality | 1.1 | `SafePdf/Core/Filter/Flate.lean` | new | todo |
| 3.2 | PNG predictors with output-length law | 1.1 | `SafePdf/Core/Filter/Predictor.lean` | new | todo |
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

## Decisions and deviations from the design document
* 2026-11-18 (0.1) — Toolchain pinned to `leanprover/lean4:v4.36.0`; **no Lake dependencies** (no Mathlib, no Batteries) to start, for build speed and a small trusted base. Termination measures that Plan.md §5.2 sketches with `Finset ℕ` use core-Lean structures (e.g. `List Nat`/bitmaps with explicit size measures) instead. Adding Mathlib later needs a new Decisions entry.
* 2026-11-18 (0.1) — `autoImplicit = false` project-wide.
* 2026-11-18 (1.1) — Object model decisions: direct/indirect split (streams never nested); exact decimal reals, never Float (round-trip); decoded `List UInt8` strings/names for proof ergonomics; strict parser **rejects duplicate dictionary keys** (S6; ISO 32000-2 §7.3.7 leaves them undefined), repair path may keep the last occurrence; integer/ref range checks live in the lexer/parser, not the model.
* 2026-11-18 (wave 5) — Task 1.1 (phase 1) was pulled into the last phase-0 wave per the next-phase fill rule; it landed on `phase-0-infra` and ships in PR #1.

## Blocked / questions for the human

## Log (append-only; one line per integrated wave)
* 2026-11-18 — wave 0 (phase 0, PR #1): ledger bootstrapped from Plan.md; draft PR opened; commit "wave 0: ledger"
* 2026-11-18 — wave 1 (phase 0, PR #1): 0.1 done (Lake scaffold, builds; `lake exe tests` passes smoke suite); commit "wave 1: 0.1 — Lake scaffold"
* 2026-11-18 — wave 2 (phase 0, PR #1): 0.2 done (CLAUDE.md: commands, build-isolation rule, registries, conventions); commit "wave 2: 0.2 — CLAUDE.md"
* 2026-11-18 — wave 3 (phase 0, PR #1): 0.3, 0.6, 0.8, 0.9 done (hygiene guard; parse stub + fuzz driver; 74-PDF arXiv corpus; 9 adversarial PDFs); none returned; commit "wave 3: 0.3 0.6 0.8 0.9 — hygiene guard, fuzzer, corpus, adversarial seeds"
* 2026-11-18 — wave 4 (phase 0, PR #1): 0.4, 0.5, 0.7, 0.10 done (CI workflow; golden harness + `Tests` lib in lakefile; differential runner; inspector with view registry); none returned; commit "wave 4: 0.4 0.5 0.7 0.10 — CI, golden tests, differential runner, inspector"
* 2026-11-18 — wave 5 (phase 0, PR #1): 0.11, 1.1 done (corpus dashboard; object model with 30 theorems); none returned; phase 0 exit criterion ticked; commit "wave 5: 0.11 1.1 — corpus dashboard, object model"
* 2026-11-18 — phase 0 milestone: PR #1 marked ready for review (CI green on cf2daba)
* 2026-11-18 — wave 6 (phase 1, PR #2): 1.2, 1.3 done (lexer spec, 13 theorems; tokenizer, `next_pos` progress); shared `Core/Token.lean` written by orchestrator; Core vs Spec agree on 61,500 random cases; commit "wave 6: 1.2 1.3 — lexer spec and tokenizer"
