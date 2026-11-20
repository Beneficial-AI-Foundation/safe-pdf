# safe-pdf guarantees, side by side

How safe-pdf's guarantees (Plan.md §4: S1–S8 security, C1–C6 correctness) compare with the
other formal-methods work on PDF and with the deployed defenses that share our threat model
(reading a hostile PDF safely). Status date: 2026-11-20 — milestones M0–M5 are proven and
measured (see progress.md exit criteria for the theorem names); M6 (text similarity), M7
(pixel faithfulness) and M8 (daily-drivable viewer) are in progress, with the viewer shell
functional (zoom, selection, search, outline, links, annotations).

Legend: **proven** = machine-checked proof; **by construction** = follows from the
architecture or language, no separate proof artifact; **tested** = empirical evidence
(fuzzing, differential testing, red-teaming); **—** = not provided / out of scope.

## Table 1 — formal-methods work on PDF

| | **safe-pdf** (Lean 4) | **Bogk & Schöpl 2014** (Coq) | **Li et al. 2021** (ACL2) | **Caradoc** (ANSSI, OCaml) | **SafeDocs / DaeDaLus** (Galois) |
|---|---|---|---|---|---|
| Scope | Full read path: parse → document → interpret → rasterize → positioned text; viewer shell | Subset parser only | Reference parser + semantic validator (proof of concept) | Strict/relaxed parser, formal grammar for a restricted syntax, object type checker | Declarative format spec → generated parsers; PDF reference implementation + Arlington object model |
| Memory safety (S1) | Proven environment: Lean type system; CI forbids `unsafe`/`partial`/`panic!`/`!`-indexing in `Core/`, axioms audited | By construction (Coq) | By construction (ACL2/Lisp) | By construction (OCaml) | By construction: generated "safe-by-construction" parsers (C++/Haskell) |
| Termination on **any** input (S2) | **Proven**, incl. xref `/Prev` cycles (`loadChain_terminates`, no fuel), cyclic `/Length`, self-containing object streams, `/Kids` cycles — all rejected via `Error.cycle` in < 0.01 ms | **Proven** for their subset (the result that showed xref cycles hang real readers) | Proven (ACL2 admits only terminating functions) | — (engineered, not proven) | — (language has formal semantics, but termination of the PDF driver's xref walk is hand-written Haskell, not proven) |
| Resource bounds (S3) | **Proven**: decode bounds (`decodeStream_size_le`), document-wide decode budget, Flate work bound, ops/page bound; 74 decompression-bomb cases rejected with `limitExceeded` | — | — | — | — |
| No ambient authority (S4) | Core has no `IO` in its type; checked by compiler | n/a (parser study) | n/a | n/a (CLI validator) | n/a (parser library) |
| Unambiguity (S6) | **Proven**: one winner per object id across incremental updates, newest-revision-wins (`Spec.Unambiguous`, prefix-stability) | — | Validator checks semantics, no unambiguity theorem | Restricted grammar reduces ambiguity (paper argument) | Core program goal — deterministic parsing is a language design property, not a machine-checked theorem about PDF |
| Malformed files (S7, C4) | Strict path first; repair path proven total + bounded; conservativity by construction (repair runs only when strict fails); result flagged `repaired` | Rejects | Rejects | Strict + relaxed pair (the architecture we adopted), no proofs | Strictness profiles in the driver |
| Spec conformance (C5) | **Proven**: impl ≡ denotational spec for lexer (`LexEquiv`), objects (`ObjEquiv`, round-trip `parseObject_print`), interpreter (`step_iff_exec`, `steps_iff_runOps`) | Spec is the implementation | Spec is the implementation (reference-level) | — | By construction: parser generated from the spec; the *generator* is trusted, not verified |
| Rendering + text (C2, C3, C6) | C2 coordinate round-trips proven (`toPage_toScreen`); C3 glyph provenance/positions proven (`glyph_provenance`); C6 extracted text = displayed text, one interpreter pass (`pageText_glyphs`); raster faithfulness **tested** vs MuPDF (by design) | — | — | — | — |
| Scripting/forms surface | Excluded by design (no JS, no AcroForm/XFA, no launch actions) | n/a | n/a | Detects/reports | n/a |
| Encryption | RC4-40/128, AES-128/256 open and decrypt (M4, tested against gov't corpus) | — | — | Partial (detects) | In the driver |
| Evidence | Machine-checked proofs (axioms: `propext`/`Classical.choice`/`Quot.sound` only) + fuzzing + differential vs qpdf/MuPDF/pdftotext + adversarial suite + corpus dashboard | Coq proofs | ACL2 proofs | Formal grammar on paper, corpus testing | Formal language semantics + red team: the only PDF parser found **free of defects** in SafeDocs red-teaming |
| Trusted base | Lean kernel + Lean→C compiler + limits config; shell/Tk outside the core | Coq kernel + extraction | ACL2 | OCaml toolchain | DaeDaLus compiler + host toolchain (C++/Haskell) |

## Table 2 — deployed readers and isolation defenses

| | **safe-pdf** | **pdf.js** (Mozilla) | **MuPDF / pdfium / Poppler** | **Dangerzone** (FPF) |
|---|---|---|---|---|
| Approach | Prove the core correct and total | Memory-safe language (JS/WASM) inside the browser sandbox | Native C/C++ engines, hardened by fuzzing; pdfium sandboxed in Chrome | Don't trust the parser at all: convert to pixels inside a disposable sandbox, rebuild a clean file |
| Memory safety | Proven environment (Lean, hygiene CI) | Inherited from the JS runtime | — (decades of parser CVEs; mitigated by OSS-Fuzz + process sandbox) | Inherited from containment |
| Termination / DoS | Proven total; cyclic files rejected in bounded time | — (ad hoc; hangs historically possible — the 2014 cyclic-xref file class) | — (ad hoc limits) | Bounded by sandbox timeouts |
| Resource bounds | Proven limits, structured `limitExceeded` | Ad hoc | Ad hoc | Sandbox quotas |
| Compromise containment | Nothing to contain: core cannot do IO by type | Browser origin sandbox | OS process sandbox (Chrome) or none (library use) | **The** guarantee: compromise stays in the container/VM; trusts kernel/container runtime |
| Fidelity & text | Extracted text provably = displayed text (C6); positions proven (C3) | Text layer is a separate pass from rendering (poisoning mismatch possible) | High fidelity, no guarantees | Lossy: pixels only; text restored by OCR ≠ original text |
| Scripting/forms | Excluded by design | AcroForm JS executed (sandboxed interpreter) — surface present | Optional JS engines (V8/mujs) — surface present | Stripped by reconstruction |
| Features | Read-only academic/office corpus (target); no JS/forms/multimedia | Full-featured | Full-featured, fastest | Read-only output |
| Evidence | Proofs + tests (above) | Massive deployment, fuzzing | Massive deployment, OSS-Fuzz | Audits of the sandbox |

## Methodology relatives (no table column — different formats)

* **EverParse / EverCBOR** (F\*, Microsoft): the strongest verified-parser guarantees in
  production (memory safety, functional correctness, non-malleability; deployed in Hyper-V).
  Our C5 spec/impl discipline follows their pattern; they never faced PDF's cross-reference
  graphs, filters or rendering.
* **Narcissus** (Coq) and **RecordFlux** (SPARK): correct-by-construction encoder/decoder
  derivation for simpler binary formats.
* **Verified parser generators** — CompCert's validated LR(1) frontend, CoStar (verified
  ALL(\*)): grammar-level guarantees; PDF is not context-free, which is why our termination
  arguments (§5.2) are bespoke measures, not grammar theorems.
* **Yardsticks** — CompCert, seL4, CakeML set the scale for "verified system" claims and the
  TCB framing (trust a proof kernel, not a hypervisor). **HACL\* / Project Everest** verified
  crypto is a pointed contrast: our RC4/AES/SHA are *tested against vectors, not proven*
  (Plan.md §8 open question).

## What no other project provides (the gap safe-pdf fills)

1. Machine-checked **termination of xref resolution on arbitrary input** — full model
   (classic tables, xref streams, object streams, hybrids, incremental updates), not a subset.
2. **Proven resource bounds** through the filter stack (decompression bombs rejected by
   theorem, not by luck).
3. **Proven unambiguity** across incremental updates (anti shadow-attack property).
4. **Extracted text = rendered text by construction** (C6) — both derive from one interpreter
   pass; no other viewer offers an anti-text-poisoning guarantee.
5. A **proven-conservative repair path** — lenient reading without giving up the strict
   semantics on valid files.

## Honest gaps (ours)

* Raster pixel faithfulness and font quality are **tested** (differential vs MuPDF), not
  proven — deliberate (Plan.md §4 "Tested, not proven").
* Crypto primitives tested against vectors, not proven.
* Reading-order heuristic for text extraction is tested, not proven; M6 similarity is 0.97
  vs MuPDF against a 0.98 target (task 6.8 open).
* M7/M8 milestones not yet ticked; the viewer shell and inspector are unverified by design.
* Proofs are against *our* spec of ISO 32000; differential testing is what ties that spec to
  the world (deviations recorded in `docs/deviations-from-spec.md`).

## Sources

* Plan.md §2 (prior-art table) and progress.md exit criteria (theorem names, measurements).
* [Galois — DaeDaLus project](https://www.galois.com/project/daedalus);
  [DaeDaLus: Safer Document Parsing (paper)](https://researchconnect.buffalo.edu/en/publications/daedalus-safer-document-parsing/)
  — generated memory-safe parsers; PDF reference implementation "the only parser … found free
  of defects" in red-teaming.
* [DARPA SafeDocs program](https://www.darpa.mil/research/programs/safe-documents);
  [DARPA formal-methods spotlight](https://www.darpa.mil/research/research-spotlights/formal-methods/examples).
* [PDF Association — SafeDocs research](https://pdfa.org/safedocs-latest-research-into-securing-pdf/)
  (Arlington PDF Model validation), [SafeDocs: DARPA does PDF](https://www.pdfa.org/safedocs-darpa-does-pdf).
* [Bogk & Schöpl 2014](https://ieee-security.org/TC/SPW2014/papers/5103a198.PDF) (Coq subset
  parser, cyclic-xref DoS); [Li et al. 2021](https://conferences.computer.org/sp/pdfs/spw/2021/893400a142.pdf)
  (ACL2 reference parser + validator); [Caradoc](https://github.com/ANSSI-FR/caradoc) (ANSSI).
* [EverCBOR / EverParse](https://www.microsoft.com/en-us/research/wp-content/uploads/2025/10/evercbor.pdf);
  [pdf.js](https://mozilla.github.io/pdf.js/); [MuPDF](https://mupdf.com);
  [pdfium](https://pdfium.googlesource.com/pdfium/); [Dangerzone](https://dangerzone.rocks).
