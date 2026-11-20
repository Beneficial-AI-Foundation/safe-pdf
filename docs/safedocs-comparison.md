# safe-pdf vs. DARPA SafeDocs — the guarantees, side by side

What each effort guarantees, and on what evidence. safe-pdf status as of 2026-11-20
(milestones M0–M5 ticked in [progress.md](../progress.md); M6–M8 in progress).
[Plan.md](../Plan.md) §2 already credits SafeDocs for the subset-first strategy and the
format-description starting point; this compares the *guarantees*.

SafeDocs ([DARPA program](https://www.darpa.mil/research/programs/safe-documents)) produced,
among other tools, [DaeDaLus](https://www.galois.com/project/daedalus) (Galois): a
data-description language whose compiler generates memory-safe parsers in conventional
languages, applied to ~20 formats. With the
[PDF Association](https://www.pdfa.org/safedocs-darpa-does-pdf) it built a PDF reference
parser that was the only parser found free of defects in the program's red-team exercise
(zero defects in the generated parser; the five defects found were in the hand-written C++
wrapper driving it — [PLDI 2024](https://dl.acm.org/doi/10.1145/3656410)),
and the [Arlington PDF Model](https://pdfa.org/safedocs-latest-research-into-securing-pdf/),
a machine-readable model of PDF 2.0 objects.

## Scope

| | SafeDocs (DaeDaLus + PDF Association) | safe-pdf |
|---|---|---|
| Artifact | Spec language + generated parsers/validators (bytes → DOM); Arlington model; ~20 formats | One format, the whole viewer: bytes → objects → xref/revisions → filters → document → DisplayList → raster + positioned text; library API (`SafePdf.Api`) + Tk shell |
| Rendering, text extraction, viewer | Out of scope | In scope (C2/C3/C6 proven; rasterizer tested against MuPDF) |

## Guarantees

Legend: ✓ held today (with the evidence named) · ◐ partial / in progress · — not claimed.

| Guarantee | SafeDocs | safe-pdf | safe-pdf evidence today |
|---|---|---|---|
| Memory safety | ✓-by-construction: generated code in memory-safe style; trusts the DaeDaLus compiler + host-language runtime; no machine-checked proof | Machine-checked by Lean's type system; no `unsafe`, no FFI, no `partial`, no panics in the core | ✓ CI hygiene guard + `#print axioms` audit (only `propext`/`Classical.choice`/`Quot.sound`) |
| Termination on **arbitrary** input | — (the xref/object-stream driver around the generated parsers is hand-written; the language's semantics are paper semantics) | Machine-checked: every core function total; xref `/Prev` chains, object streams, page tree, form recursion all carry proven measures | ✓ `Spec.XrefTerm.loadChain_terminates` (no fuel), `openFile_cycle`; Bogk-style cyclic files rejected in < 0.01 ms (M2) — first machine-checked proof that PDF xref resolution terminates |
| Resource bounds (decompression bombs, DoS) | — | Proven output and work bounds; document-wide decode budget; exceeding a limit returns `Error.limitExceeded` | ✓ `decodeStream_size_le`, `flateDecodeW_steps_le`, `lzwDecode_size_le`, `loadChainB_cost`; 37-bomb suite, all rejected within limits (M3) |
| Unambiguous interpretation | Addressed at the *format* level: deterministic spec language, Arlington model, safe-subset definition | Proven at the *file* level: one winner per object id across incremental updates, newest-revision-wins | ✓ `Spec/Unambiguous.lean` (tasks 2.5, 2.12) |
| Spec ↔ implementation | Parser *generated from* the spec; the generator is trusted, not verified | Denotational spec and efficient implementation are separate artifacts with machine-checked equivalence per layer (C5) | ✓ lexer + objects (`LexEquiv`, `ObjEquiv`, round-trip `parse (print o) = o`, M1); interpreter (`step_iff_exec`, `steps_iff_runOps`, M5) |
| Functional correctness evidence | Empirical: red team found zero defects (only PDF parser so) | Theorems plus fuzzing plus differential testing | ✓ objects 71,854/71,854 agree with qpdf; page count/boxes 2,450/2,450 pages agree (M4); text similarity 0.974 vs MuPDF (M6 target 0.98, open) |
| No ambient authority / read-only | — (ordinary programs in a host language) | The core's type contains no `IO`: cannot touch network, filesystem, processes; read-only by construction (user notes go to an XFDF sidecar, the PDF is never written) | ✓ compiler-checked (S4, S8) |
| Failure behavior | Parse errors reported | Structured `Error` values, page-local failure, `repaired := true` flag, proven structured cycle errors | ✓ S7; `Error.cycle` theorems (2.13) |
| Broken-file repair | — | Lenient path proven total and bounded; conservativity on valid files (C4) still to be proven | ◐ totality + bounds proven (2.6) |
| Coordinates, text ↔ position, extracted = displayed | Out of scope | C2 zoom/rotate round-trips, C3 glyph provenance, C6 one interpreter pass feeds both raster and text | ✓ `toPage_toScreen`/`toScreen_toPage`, `glyph_provenance`, `pageText_glyphs` (`SafePdf.Api`) |
| Rendering faithfulness | Out of scope | Tested, not proven: pixel differential vs MuPDF, perceptual threshold | ◐ M7 open (target ≥ 95% of corpus pages within threshold) |

## Trusted computing base

* **SafeDocs:** the DaeDaLus compiler/interpreter, the host language's compiler and runtime,
  and the hand-written driver code around the generated parsers.
* **safe-pdf:** the Lean kernel (axioms audited per theorem), the Lean compiler/runtime, the
  unverified shell (which makes no document-data decisions), and our spec itself — the
  spec-vs-world gap is covered by differential testing (Plan.md §7), not by proof.

## Where SafeDocs is ahead

* **Breadth:** one toolchain over ~20 formats; safe-pdf is PDF only.
* **Independent adversarial validation:** a DARPA-run red team; safe-pdf's fuzzing and
  adversarial suites are self-run so far.
* **Standards impact:** the Arlington model and safe-subset work shaped the format itself.

## The headline difference

SafeDocs makes *parsers* that are memory-safe by construction and empirically defect-free.
safe-pdf makes a *whole viewer* whose core properties — totality on arbitrary input,
resource bounds, unambiguity, spec equivalence, text/position correctness — are theorems
checked by a proof assistant, rather than properties of a trusted generator; that includes
the first machine-checked termination proof of PDF xref resolution, which no SafeDocs
artifact claims.

Sources: [DARPA SafeDocs](https://www.darpa.mil/research/programs/safe-documents) ·
[Galois DaeDaLus](https://www.galois.com/project/daedalus) ·
[DaeDaLus: Safer Document Parsing (PLDI 2024)](https://dl.acm.org/doi/10.1145/3656410) ·
[PDF Association on SafeDocs](https://www.pdfa.org/safedocs-darpa-does-pdf) ·
[Arlington PDF Model](https://pdfa.org/safedocs-latest-research-into-securing-pdf/)
