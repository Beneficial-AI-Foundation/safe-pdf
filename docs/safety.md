# safe-pdf — the safety account

What safe-pdf does for safety, how that compares with other projects attacking the same
problem, and what would raise the degree of safety further. Status date: 2026-11-23 —
milestones **M0–M8 are proven and measured** (see [progress.md](../progress.md) exit
criteria for theorem names and numbers); M9 is verified except one external-reader check.
Companion documents: [comparison.md](comparison.md) (the full side-by-side tables against
other projects) and [safedocs-comparison.md](safedocs-comparison.md) (the SafeDocs/DaeDaLus
deep dive).

## 1. The threat

A PDF reader executes a complex, attacker-chosen program: tokenizers, a cross-reference
graph, compression filters, font interpreters, a graphics language. Historical exploits
cover every layer: FORCEDENTRY entered iMessage through a JBIG2 decoder, Duqu through a
TrueType font parser, countless CVEs through Flate/JPEG/XFA parsing in C engines; crafted
xref cycles hang mainstream readers (Bogk & Schöpl 2014); decompression bombs exhaust
memory; shadow attacks exploit ambiguous incremental updates; JavaScript and launch actions
turn documents into droppers. The defender's problem is not one bug but a *class* of them.

## 2. What safe-pdf does

### 2.1 Remove the attack surface that cannot be made safe

No JavaScript, no AcroForm/XFA forms, no launch actions or `GoToR`, no embedded-file
execution, no multimedia/3D, no network access ([Plan.md](../Plan.md) §1). Most historical
PDF exploit chains need one of these; here there is nothing to exploit.

### 2.2 Prove the rest

The core (`SafePdf/Core/`, `Spec/`) is pure Lean 4 — no `IO`, no `partial`, no `unsafe`,
no panics, no `sorry` — and the properties are machine-checked theorems, not goals:

| Property | Status today | Key evidence |
|---|---|---|
| S1 memory safety | holds | Lean type system; CI hygiene guard; axiom audit (`propext`/`Classical.choice`/`Quot.sound` only) |
| S2 totality on **any** input | **proven** | `loadChain_terminates` (no fuel); xref `/Prev` cycles, cyclic `/Length`, self-containing object streams, `/Kids` cycles all rejected with `Error.cycle` in < 0.01 ms (M2) |
| S3 resource bounds | **proven** | decode output + work bounds (`decodeStream_size_le`, `flateDecodeW_steps_le`), document-wide decode budget, ops/page bounds; 74 decompression-bomb cases rejected with `limitExceeded` (M3) |
| S4 no ambient authority | holds | the core's type contains no `IO` — compiler-checked |
| S5 unverified-code isolation | holds (vacuously strong) | no FFI decoders at all: even JPEG is pure Lean in `Quarantine/`, held to core hygiene rules |
| S6 unambiguity | **proven** | one winner per object id across incremental updates, newest-revision-wins (`Spec.Unambiguous`) — the anti-shadow-attack property |
| S7 local, visible failure | holds | structured `Error` values; page-local failure; `repaired` flag |
| S8 never modify in place | holds | explicit save emits `bytes ++ update` to a new file (or atomic temp+rename after the user confirms); the original bytes are a prefix |
| C2/C3/C6 text & geometry | **proven** | coordinate round-trips, glyph provenance, extracted text = displayed text (one interpreter pass) |
| C5 spec ↔ implementation | **proven** | lexer, object parser (round-trip `parseObject_print`), interpreter (`step_iff_exec`) each proven ≡ their denotational spec |
| C7 conservative writes | **proven** | `writeAnnots doc marks = bytes ++ update`; strict re-parse yields every original object unchanged (xref-entry *and* value level: `c7`, `c7Update`, `c7Value'`), annotations = marks; validated by re-opening before anything is written |
| Raster faithfulness | tested, not proven (by design) | pixel differential vs MuPDF: 2,435/2,450 corpus pages within threshold (99.39%, M7) |

### 2.3 Architecture that keeps the proofs meaningful

* **Typed boundaries**: once xref resolution produces an object, downstream layers receive
  Lean structures, never raw byte offsets — parsing bugs cannot be re-triggered.
* **Every recursion is measured**: `/Prev` chains, object streams, page tree, form
  XObjects, Type 3 glyphs, patterns, CMap chains — visited sets or proven fuel (§5.2).
* **Repair is quarantined**: the lenient path (proven total and bounded) runs only when the
  strict parser fails, and its output must pass the same strict validation, flagged
  `repaired := true`.
* **The shell is thin and outside the TCB for document data**: Tk UI code makes no parsing
  decisions; its Tk-free logic modules carry `#guard`s and theorems (e.g. the proven
  injection-free `Tcl.quote`, so no document data is ever spliced into script text; URI
  links are never auto-opened and are displayed as proven-printable ASCII).
* **The write path is held to the same bar**: the annotation writer is a core function with
  C7; encrypted files are annotated with the document's own handler; the result is strictly
  re-parsed before a byte reaches disk.

### 2.4 Evidence beyond the proofs

Proofs show we meet *our* spec; testing ties the spec to the world (§7): differential
testing against qpdf (71,854/71,854 objects, 2,450/2,450 pages agree), MuPDF and pdftotext
(text similarity 0.9949; 5.7 M glyph positions within tolerance), pixel diffs, continuous
fuzzing (no panics — as the totality proofs predict), the adversarial suite (Bogk cycles,
bombs, hostile names), a corpus dashboard where regressions block merge, and CI that greps
the core for forbidden constructs and audits axioms on every build.

## 3. How this compares

Four groups attack the "hostile PDF" problem (full tables in [comparison.md](comparison.md)):

1. **Formal PDF work** (Bogk & Schöpl, Li et al., Caradoc, SafeDocs/DaeDaLus): parsers or
   validators only, none proving resource bounds, none touching rendering or text. SafeDocs
   is the strongest: generated memory-safe parsers, and its PDF parser was the only one
   defect-free in red-teaming — but its five red-team defects were in the *hand-written
   wrapper*, exactly the layer (xref walking, drivers) where our theorems live
   ([safedocs-comparison.md](safedocs-comparison.md)).
2. **Memory-safe implementations** (pdf.js): inherits safety from the JS runtime, but no
   totality or bounds (cyclic-xref hangs are ad hoc), and its text layer is a separate pass
   from rendering — text poisoning is possible by construction; our C6 excludes it.
3. **Hardened native engines** (MuPDF, pdfium, Poppler): decades of CVEs mitigated by
   fuzzing and process sandboxes; guarantees are empirical only.
4. **Containment** (Dangerzone, Chrome's pdfium sandbox): assume compromise and contain it.
   Strong, but lossy (pixels + OCR) and it trusts kernels/containers. We have nothing to
   contain — the core cannot do IO by type — yet containment composes with our approach
   (see §5).

What no other project provides: machine-checked termination of full xref resolution,
proven decompression-bomb rejection, proven unambiguity across revisions, extracted text =
rendered text, a proven-conservative repair path — and now a proven-conservative
*annotation writer* (C7), where every other editor appends updates on faith.

## 4. Residual trust (what a honest attacker model still includes)

* **The Lean kernel and compiler.** Theorems are checked by Lean's kernel (small, but
  trusted); the Lean→C compiler and runtime are entirely unverified — a miscompilation
  could break a "proven" property at runtime.
* **The C shim and Tk.** `c/tk_shim.c` and the Tcl/Tk libraries are C in the shell process.
  They never parse document bytes, but they share the address space with everything else.
* **Our spec of ISO 32000.** Proofs are against our reading of a loose spec; differential
  testing and `deviations-from-spec.md` are the mitigation, not a proof.
* **Floats in the rasterizer.** The ℚ model is the proven reference; the compiled float
  path is tested (by design).
* **Crypto primitives** (RC4, AES, MD5/SHA-2): tested against published vectors, not proven.
* **Limits configuration**: the S3 theorems are relative to `Limits`; absurd limits would
  weaken them (defaults are measured, e.g. 256 MiB decode budget).
* **Process**: one project's self-run tests; no independent red team or audit yet.

## 5. Raising the degree of safety

Ordered roughly by value per effort.

### Close the stated proof gaps
1. **C4 conservativity as a theorem** — today repair-path conservativity holds by
   construction (repair runs only on strict failure); state and prove it.
2. **Float error bound for the rasterizer** vs the ℚ model (Plan §4 "if feasible") — turns
   the largest tested-not-proven area into a bounded one.
3. **Crypto functional correctness** — prove RC4/AES/SHA-2 against executable specs
   (HACL*-style); they are small, pure Lean already. Alternatively adopt a verified
   implementation as differential oracle in CI.
4. **Reading-order heuristic**: keep tested (there is no spec for "reading order"), but pin
   it with property tests (monotonicity lemmas partly exist via C3).

### Shrink the trusted computing base
5. **External proof checking in CI**: re-check the whole development with an independent
   checker (lean4lean) so the trusted base is the small kernel algorithm, not the Lean
   implementation.
6. **Probe the unverified compiler**: run the test suites both interpreted and compiled and
   diff results (cheap, catches Lean→C codegen bugs in our hot paths); track verified-
   codegen work in the Lean ecosystem.
7. **Process-isolate the shell**: run the viewer under an OS sandbox profile — no network,
   read access to the opened file, write access only to the chosen save target (macOS App
   Sandbox / Landlock + seccomp on Linux). This is Dangerzone-style defense in depth *on
   top of* the proofs: it contains Tk/C-shim compromise, which the proofs do not cover.
8. **Audit the C shim**: it is small by design; keep it reviewable, consider generating the
   event-dispatch tables from Lean.

### Strengthen the evidence
9. **Independent adversarial review**: an external red team or audit of core + writer + 
   shell (SafeDocs had DARPA's red team; we have only self-run suites), and a public bug
   bounty once released.
10. **Fuzzing at scale**: OSS-Fuzz onboarding; structure-aware fuzzers for fonts, filters
    and now the *writer* (fuzz marks and documents, assert C7's runtime counterpart);
    add veraPDF and Arlington PDF Model cross-checks of both parsed and written files to
    catch spec misreadings our differential trio shares.
11. **Hostile corpus**: extend the adversarial suite with in-the-wild exploit samples
    (FORCEDENTRY-class JBIG2, shadow-attack suites, polyglots) — all should die on the
    excluded-feature or limit paths; document each.

### Guard the growth edges
12. **The write path is the newest surface**: keep every new annotation kind behind C7
    restatements (done so far: W9–W15 rules each re-prove it); never add an in-place write;
    keep strict-reparse-before-write mandatory.
13. **Supply chain**: toolchain pinned (done); keep the no-dependencies policy for the core
    (Batteries enters only via the bib-lean pairing — keep it out of `Core/` proofs);
    reproducible builds and signed releases before distribution.
14. **Process discipline** (already policy, worth stating): never widen the grammar without
    extending the proofs; every spec deviation recorded; limits changes need a theorem
    re-check; proof patterns documented against the bus factor.

## Sources

[Plan.md](../Plan.md) §1–§5 (threat model, properties, architecture) ·
[progress.md](../progress.md) exit criteria (theorem names, measurements) ·
[comparison.md](comparison.md) and [safedocs-comparison.md](safedocs-comparison.md)
(project-by-project tables and references: Bogk & Schöpl 2014, Li et al. 2021, Caradoc,
SafeDocs/DaeDaLus PLDI 2024, EverParse/EverCBOR, pdf.js, MuPDF/pdfium, Dangerzone).
