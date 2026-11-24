# safe-pdf — the safety account

What safe-pdf does for safety, how that compares with other projects attacking the same
problem, and what would raise the degree of safety further. Status date: 2026-11-23 —
milestones **M0–M8 met their recorded exit criteria** — a mix of machine-checked proofs and
measurements (see [progress.md](../progress.md) for which is which); M9's remaining clause
(Acrobat/Okular validation) is unchecked.
Companion documents: [comparison.md](comparison.md) (the full side-by-side tables against
other projects) and [safedocs-comparison.md](safedocs-comparison.md) (the SafeDocs/DaeDaLus
deep dive). Revised 2026-11-23 to incorporate corrections from an independent security
review of commit `1c7927a`.

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
| S3 resource bounds | **proven**, per operation | decode output + work bounds (`decodeStream_size_le`, `flateDecodeW_steps_le`), a decode budget threaded through the open, ops/page bounds; 74 decompression-bomb cases rejected with `limitExceeded` (M3). Each per-page API call starts a **fresh** budget, so repeated calls (concurrent renders, thumbnails) multiply it; since 12.3 the viewer's work in flight is reserved in one pool and a search shares one allowance, and the worker has OS memory/CPU fences (§5 item 0c) |
| S4 no ambient authority | holds | the core's type contains no `IO` — compiler-checked |
| S5 unverified-code isolation | holds (vacuously strong) | no FFI decoders at all: even JPEG is pure Lean in `Quarantine/`, held to core hygiene rules — a source-code boundary, not a process one: everything runs in the viewer process (§5) |
| S6 unambiguity | **proven** | one winner per object id across incremental updates, newest-revision-wins (`Spec.Unambiguous`) — the *ambiguity* half of shadow attacks: it settles which revision we display; signatures and other viewers' precedence rules are out of scope |
| S7 local, visible failure | holds | structured `Error` values; page-local failure; `repaired` flag |
| S8 never modify in place | holds | explicit save emits `bytes ++ update` to a new file (or atomic temp+rename after the user confirms); the original bytes are a prefix |
| C2/C3/C6 text & geometry | **proven**, scoped | coordinate round-trips, glyph provenance; C6 (`pageText_glyphs`, stated for page content with annotations off) ties extracted glyphs to the same interpreter pass that renders — a *provenance* theorem: invisible text (`Tr 3`, OCR layers) is kept by default (`includeInvisible`), so search and copy can surface text not visible on the page |
| C5 spec ↔ implementation | **proven** | lexer, object parser (round-trip `parseObject_print`), interpreter (`step_iff_exec`) each proven ≡ their denotational spec |
| C7 conservative writes | **proven**, per rule | `writeAnnots doc marks = bytes ++ update`; for the add-only writer the strict re-parse yields every original object unchanged (xref-entry *and* value level: `c7`, `c7Value'`); edit/delete (`c7Update`) supersedes objects by design, and the preserved prefix means a deleted note's text stays recoverable in the file (§4); validated by re-opening before anything is written |
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

### 2.4 The confined document worker (tasks 12.2a, 12.2b)

The `worker` executable (`SafePdf/Shell/Worker/`) receives a document as **bytes** over
stdin and answers render, text, outline and link requests over stdout; the client starts it
with an empty environment and `/` as working directory, and can kill it at any time. Since
12.2b it confines itself before it reads its first request (`Sandbox.prepare`,
`c/worker_sandbox.c`):

1. **Environment**: a non-empty environment makes it refuse to serve (exit 3). The client
   passes none (`inheritEnv := false`), so `$HOME`, bib-lean's token and any credential of
   the GUI never reach the process that parses untrusted bytes.
2. **Fonts first**: the substitute fonts are read from the fixed system font directories,
   every file in full, *before* confinement (measured: worker startup 7.8 → 13.0 ms median
   on an M-series Mac, i.e. ~5 ms for 14 faces plus the sandbox; the first `openDoc` no longer
   reads them). Parsing them stays lazy and pure.
3. **Sandbox**, irreversible, before any request:
   * **macOS**: `sandbox_init` with the SBPL profile `(version 1) (deny default)` — nothing
     is allowed: no file read or write (not even of the font files already read), no
     directory listing, no network, no process exec/fork, no Mach/XPC lookup, no POSIX IPC,
     no IOKit, no sysctl. Reading and writing the descriptors it already holds
     (stdin/stdout/stderr), allocating memory and starting threads are not sandbox
     operations and keep working. `sandbox_init` is deprecated API but works on macOS 26
     (Chromium's renderer sandbox uses the same mechanism).
   * **Linux** (**untested**: written on macOS, never run on Linux yet): `PR_SET_NO_NEW_PRIVS`
     and a seccomp-bpf allowlist applied to every thread (`SECCOMP_FILTER_FLAG_TSYNC`):
     read/write/readv/writev/close/lseek/fstat on existing descriptors, memory
     (mmap/munmap/mremap/mprotect/madvise/brk), threads (futex, `clone` only with
     `CLONE_THREAD`, `clone3` → ENOSYS so glibc falls back), signals to itself only,
     clocks/sleep/getrandom, exit. Everything else — `open`/`openat`/`openat2`, `socket`,
     `connect`, `execve`, `fork`, `ptrace`, `kill`, `ioctl`, `pipe` … — fails with EPERM;
     a foreign architecture or an x32 call kills the process. `newfstatat`/`statx` are
     allowed because glibc implements `fstat` with them, so a compromised worker can learn a
     path's *metadata* (existence, size, times), never its contents. Landlock and `bwrap`
     are not used: seccomp already removes every call that opens a path, and Landlock
     cannot be applied to the runtime's existing threads.
   * **Anything else** (another OS, a Linux build without the kernel headers or on an
     architecture other than x86-64/arm64): confinement fails.
4. **No unconfined fallback**: if any step fails the worker exits (3: environment, 4:
   sandbox) without reading a request. There is **no debug escape** in `worker` — no flag
   and no environment variable (the environment is empty anyway). The unconfined *control*
   mode exists only in the separate test executable `worker-probe`.

**Evidence** (`scripts/worker-confinement-test.sh`, suite `worker-confinement`): a probe
child started exactly as the client starts the worker is denied reading `/etc/hosts`,
re-reading a font file it read at startup, creating a file in `/tmp`, listing `/`,
connecting to a listening socket on 127.0.0.1, seeing the parent's `SAFEPDF_PROBE_TOKEN`
and spawning `/bin/echo`, while a thread and a render still work; an unconfined control
child is allowed all of these, so the probes detect access. The `worker` suite renders
byte-equal to in-process rendering through the confined worker.

**What is not confined, or not yet**:
* Font files on disk are parsed after confinement but were *read* before it: a malicious
  file planted in a system font directory is still parsed — by the verified font code, in
  the confined process.
* The confined worker can still burn CPU and memory up to the core's limits, write
  anything to its stdout (the client caps and decodes every frame) and to stderr; the
  client's deadline kill is the bound on time.
* Descriptors inherited from the parent stay usable; the client passes only
  stdin/stdout/stderr.
* The GUI process itself (Tk, the C shim, clipboard, saves, bib-lean's token) is not
  sandboxed (item 7 below), and until task 12.2c the Tk viewer still renders in-process.
* Running the worker inside an already sandboxed app (e.g. a future App-Sandboxed macOS
  shell) may make `sandbox_init` fail; the worker then refuses to serve (task 11.x decides).

### 2.5 Evidence beyond the proofs

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
   found defect-free in red-teaming. The hand-written driver code around generated parsers
   (xref walking, object streams) is where generation-based guarantees stop — and where our
   theorems live ([safedocs-comparison.md](safedocs-comparison.md)).
2. **Memory-safe implementations** (pdf.js): inherits safety from the JS runtime, but no
   totality or bounds (cyclic-xref hangs are ad hoc), and its text layer is a separate pass
   from rendering, so displayed and extracted text can diverge silently; our C6 ties them to
   one pass — provenance, though not visibility (§2.2).
3. **Hardened native engines** (MuPDF, pdfium, Poppler): decades of CVEs mitigated by
   fuzzing and process sandboxes; guarantees are empirical only.
4. **Containment** (Dangerzone, Chrome's pdfium sandbox): assume compromise and contain it.
   Chromium's sandbox keeps a full interactive viewer; only Dangerzone's pixel
   reconstruction is lossy — containment itself is not. Our *core* has nothing to contain
   (no IO by type), but the viewer process — Tk, the C shim, clipboard, saves, bib-lean's
   token — does, which is why process isolation composes with our approach (§5).

What no other project provides: machine-checked termination of full xref resolution,
proven decompression-bomb rejection, proven unambiguity across revisions, same-pass text
provenance (C6), a repair path proven total and bounded that never overrides a strict parse
— and an *annotation writer* with machine-checked conservativity theorems (C7).

## 4. Residual trust (what a honest attacker model still includes)

* **The Lean kernel and compiler.** Theorems are checked by Lean's kernel (small, but
  trusted); the Lean→C compiler and runtime are entirely unverified — a miscompilation
  could break a "proven" property at runtime.
* **The C shim and Tk.** `c/tk_shim.c` and the Tcl/Tk libraries are C in the shell process.
  They never parse document bytes, but they share the address space with everything else.
* **The OS sandboxes.** The worker's confinement (§2.4) trusts the macOS seatbelt (a
  deprecated, undocumented profile language) and Linux seccomp, plus the small
  `c/worker_sandbox.c` that installs them; the Linux filter has not been run yet.
* **Our spec of ISO 32000.** Proofs are against our reading of a loose spec; differential
  testing and `deviations-from-spec.md` are the mitigation, not a proof.
* **Floats in the rasterizer.** The ℚ model is the proven reference; the compiled float
  path is tested (by design).
* **Crypto primitives** (RC4, AES, MD5/SHA-2): tested against published vectors, not proven;
  encrypted updates derive AES IVs deterministically (the pure core has no randomness), so
  identical plaintext at the same object position can repeat ciphertext across updates.
* **Invisible text is text**: extraction keeps invisible runs (OCR layers) by default; a
  search hit can have valid provenance yet be invisible on the rendered page.
* **Deleted annotations persist**: the C7 byte prefix means prior revisions — a removed
  note's text included — stay recoverable in the saved file.
* **Limits configuration**: the S3 theorems are relative to `Limits`; absurd limits would
  weaken them (defaults are measured, e.g. 256 MiB decode budget).
* **Process**: one project's self-run tests; no independent red team or audit yet.

## 5. Raising the degree of safety

Ordered roughly by value per effort. The first group is adopted from the independent
security review; those items protect the user even if every current theorem is correct.

### Fix the boundary gaps first (adopted from the independent review)
0a. **Capped reads and true strict mode**: `Api.openFile` stats the file and then reads it
    whole (`readBinFile`), so a growing file allocates before rejection — share the
    inspector's capped read with the API, XFDF import and the overwrite comparison; and make
    `allowRepair := false` *skip* repair work instead of rejecting a repaired result after
    parsing (`repairRefused` rejects post-parse today).
0b. **A stoppable, restricted document worker**: run the core plus document-derived font and
    image processing in a child process the GUI can kill; broker file, clipboard, save and
    bib-lean access in the GUI; keep the library token out of the child. *Status:* the
    worker exists and confines itself (macOS tested, Linux untested; §2.4); the viewer moves
    onto it in task 12.2c.
0c. **Budget a whole user operation**: reserve memory for concurrent page buffers, thumbnails
    and caches before dispatch, and carry one shared work allowance through a search, export
    or render — per-call budgets reset today, so concurrency multiplies them.
    *Status (task 12.3):* the viewer reserves every render, thumbnail and text request in one
    pool (512 MiB, proven never exceeded, releases proven idempotent) before dispatch; a search
    shares one allowance (400 pages, 60 s); the worker has a memory ceiling (Linux rlimits;
    macOS, where `RLIMIT_AS`/`RLIMIT_DATA` are refused, a footprint watchdog) and a per-request
    `RLIMIT_CPU` next to the 20 s deadline; a CI scenario checks the published RSS ceilings
    (`docs/viewer.md`, "Budgets and ceilings"). Still open: Tk photos, Save/export and the
    per-page decode budget inside the worker are outside the pool.
0d. **Fresh IVs for encrypted updates**: supply OS randomness at the shell boundary and pass
    it into the pure writer; set an explicit policy for legacy RC4 writes.

### Close the stated proof gaps
1. **C4 conservativity as a theorem** — proven today is *precedence* (a successful strict
   open wins, `openBytes_strict`), not equivalence: the golden fixture
   `Tests/golden/xref/repair-diff.pdf` shows an independent repair scan yielding a different
   object map on a strict-openable file. A real C4 needs explicit hypotheses about which
   files and which observations must agree.
2. **Error bounds for the rasterizer's numeric surfaces** vs the ℚ model (Plan §4 "if
   feasible") — targeted, not blanket: fill and stroke already run on integer fixed-point
   with grid-rounding lemmas, so the work is bounding the places floats actually enter
   (transforms, flattening tolerances).
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

**What exists now (task 12.6).** The rig for items 5, 6 and 10 is in `scripts/`; its CI jobs
(`lean4lean`, `compiled-vs-interpreted`, `viewer`, and the pinned-corpus positions/pixels steps)
are in `.github/workflows/ci.yml` since 2026-11-24.
* Item 5: `scripts/lean4lean-check.sh` fetches lean4lean at a pinned commit (its `master`
  targets our v4.36.0), SHA-256-verified, builds it from a fresh directory and re-checks every
  `SafePdf.*` module from its `.olean`. lean4lean is derived from the C++ kernel, so this is a
  second implementation, not an independent theory. Local run (2026-11-23): all 114
  modules re-check, after raising lean4lean's fuel limits; its multi-module mode crashes
  intermittently (SIGSEGV), so the script checks one module per process.
* Item 6: `scripts/compiled-vs-interpreted.sh` runs the suites compiled (`lake exe tests`) and
  in the IR interpreter (`scripts/interp-suites.lean`) and diffs them suite by suite.
  Locally the 21 suites of its default set agree (~7 min interpreted); the raster property
  suites are too slow interpreted for CI so far, and `adversarial` asserts wall-clock bounds.
* Pinned corpus: `scripts/corpus/pinned.txt` (16 manifest ids, every producer family, ~15 MB)
  feeds the pixel and glyph-position comparators and the viewer smoke and corpus runs.
* Item 10: `docs/oss-fuzz.md` is the onboarding plan (targets, harness, `build.sh`,
  `project.yaml` draft, blockers); nothing is fuzzed under libFuzzer yet.

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
