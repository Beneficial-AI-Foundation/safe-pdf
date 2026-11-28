# safe-pdf — Project Plan

**A formally verified PDF viewer, written in Lean 4.**

No formally verified PDF reader exists today. The verified work in this space covers parsers
only, usually for restricted subsets: a 2014 Coq parser with a termination proof
([Bogk & Schöpl](https://ieeexplore.ieee.org/document/6957304/)), a 2021 ACL2 proof-of-concept
parser ([Li et al.](https://ieeexplore.ieee.org/document/9474323/)), and DARPA SafeDocs tooling
([DaeDaLus](https://www.galois.com/project/daedalus), Parsley) that generates memory-safe but
unproven parsers. Nobody has verified xref resolution end-to-end, text extraction, or any part
of rendering. That is the gap this project fills.

---

## 1. Vision and scope

### What we build

A **read-only** PDF viewer whose core is a pure, total, resource-bounded Lean program:

```
bytes → Except Error Document            -- parse (untrusted input)
Document → PageIndex → DisplayList       -- interpret content streams
DisplayList → Bitmap                     -- rasterize
Document → PageIndex → PositionedText    -- text extraction with glyph positions
```

A thin, unverified shell (window, scrolling, clipboard) drives the core. The core has no `IO`
in its type, so it provably cannot touch the network, filesystem, or other processes.

### What we deliberately leave out

These are features in the negative — most historical PDF exploits lived here:

- JavaScript
- Interactive forms (AcroForm / XFA)
- Launch actions, GoToR (links to other files), embedded file execution
- Multimedia, 3D content
- Any network access
- Any modification of the file (strictly read-only)

### Target corpus

Academic and office PDFs: LaTeX output (pdfTeX, LuaTeX, XeTeX), Word/LibreOffice exports,
publisher PDFs (Elsevier, Springer, ACM, IEEE), matplotlib/R figures, scanned papers.
Success is measured against a real corpus (see §7), not against the spec alone.

---

## 2. Prior art and what we take from each

| Project | What it did | What we take |
|---|---|---|
| [Bogk & Schöpl 2014 (Coq)](https://ieee-security.org/TC/SPW2014/papers/5103a198.PDF) | Subset parser, termination proof via decreasing input length; showed xref cycles hang every real reader | The problem statement: **totality of xref resolution is the crown jewel**. Their crafted-file DoS becomes our regression test |
| [Li et al. 2021 (ACL2)](https://conferences.computer.org/sp/pdfs/spw/2021/893400a142.pdf) | Verified reference parser + semantic validator | The pattern: executable reference spec first, efficient implementation proven equivalent later |
| [DARPA SafeDocs](https://www.darpa.mil/research/programs/safe-documents) / [DaeDaLus](https://www.galois.com/project/daedalus) | Reduced PDF to an unambiguous, verification-friendly subset; generated parser survived red-teaming with zero defects | The strategy: **subset first, widen later**. Their format description is a starting point for our spec |
| [Caradoc (ANSSI, OCaml)](https://github.com/ANSSI-FR/caradoc) | Strict + relaxed parser pair, formal grammar for restricted syntax, object type checker | The two-parser architecture: strict path proven, repair path quarantined (§5.4) |
| EverParse / [EverCBOR](https://www.microsoft.com/en-us/research/wp-content/uploads/2025/10/evercbor.pdf) (F*) | Parsers proven memory-safe, functionally correct, non-malleable — but for CBOR, not PDF | The methodology: denotational spec → parser ⇄ serializer round-trip proofs |

---

## 3. Architecture

```
┌────────────────────────────────────────────────────────────┐
│ Shell (unverified, thin)                                   │
│   window, scrolling, selection UI, clipboard, file open    │
└───────────────┬────────────────────────────────────────────┘
                │ pure function calls, structured values only
┌───────────────▼────────────────────────────────────────────┐
│ Verified core (pure Lean, no IO)                           │
│                                                            │
│  Layer 1  Lexer / object parser        (total, proven)     │
│  Layer 2  Xref + trailer + revisions   (termination proof) │
│  Layer 3  Filters: Flate, A85, AHx…    (bounded output)    │
│  Layer 4  Document structure            (acyclic page tree)│
│  Layer 5  Content-stream interpreter    (bounded state)    │
│  Layer 6  Fonts + text extraction       (position mapping) │
│  Layer 7  Rasterizer                    (tested, not proven)│
└───────────────┬────────────────────────────────────────────┘
                │ sandboxed, no capabilities
┌───────────────▼────────────────────────────────────────────┐
│ Quarantine zone (FFI, separate process, if used at all)    │
│   DCT (JPEG), JPEG 2000, JBIG2 decoding                    │
└────────────────────────────────────────────────────────────┘
```

Design rules:

1. **Values crossing layer boundaries are well-typed Lean structures**, never raw byte offsets.
   Once Layer 2 resolves an object, downstream layers cannot re-trigger parsing bugs.
2. **Every recursive structure in the format carries a fuel/measure argument** justified by a
   proof, or an explicit visited set: `/Prev` chains, object-stream indirection, page tree,
   form XObjects, Type 3 glyphs, pattern recursion, CMap `usecmap` chains.
3. **No `panic!`, no `!` indexing, no `partial def` in the core.** CI greps for these
   (`partial`, `unsafe`, `panic!`, `Array.get!`, `sorry`) and fails the build.
4. **FFI code never parses.** If we use a C decoder for JPEG, it receives length-checked
   buffers, runs in a subprocess with no file/network access, and its output is re-validated
   (dimensions, size) before entering the core. JBIG2 via FFI is how FORCEDENTRY happened —
   so JBIG2 ships late, written in Lean, or not at all.

---

## 4. The properties (what "verified" means here)

### Security properties — proven

| # | Property | Statement sketch |
|---|---|---|
| S1 | Memory safety | Free from Lean's type system; the residual obligations are: no `unsafe`, no FFI in the core, no panicking partial functions |
| S2 | Totality / termination | Every core function is `def` (not `partial`), accepted by the termination checker, on **every** byte string — including xref cycles, self-referencing `/Length`, cyclic page trees, recursive XObjects |
| S3 | Bounded resources | For explicit limits L (decompressed bytes, image area, stack depths, object count, ops/page): memory and time are O(f(L, input size)); any excess yields a structured `Error.limitExceeded`, not slowdown |
| S4 | No ambient authority | The core's type contains no `IO`. Checked by the compiler, enforced by code review on the boundary module |
| S5 | Isolation of unverified code | Any FFI decoder runs sandboxed; its outputs are revalidated. (Process-level sandbox is a shell concern; the *revalidation* is proven) |
| S6 | Unambiguous interpretation | Each (file, object id) resolves to at most one object, even across incremental updates; parse is deterministic: `parse bytes = parse bytes` trivially, but also *version-stable* via the executable spec |
| S7 | Local, visible failure | A malformed object/page yields `Error`, never an exception; page n failing does not affect page m; repaired files are flagged `.repaired := true` |
| S8 | Integrity & privacy | The core never modifies a file in place (S4); on an explicit save the annotation writer emits `bytes ++ update`, the original bytes a prefix (C7), to a new file, over the opened file after the user confirms (temporary file + atomic rename; amended 2026-11-23 by the human), or to bib-lean's `PUT` route; permission flags treated as advisory; no network in the core (the bib-lean reader mode's HTTP client is shell code) |

### Correctness properties — proven

| # | Property | Statement sketch |
|---|---|---|
| C1 | Determinism | Core is pure ⇒ free |
| C2 | Coordinate round-trips | `toScreen zoom rot ∘ toPage zoom rot = id` for all zoom > 0, rot ∈ {0,90,180,270} (over ℚ; the float version tested, with proven error bound if feasible) |
| C3 | Text ↔ position | Every extracted char maps to a glyph bbox; selection is monotone in extraction order; highlight → text span → rectangles round-trips |
| C4 | Repair conservativity | On files accepted by the strict parser, repair path ≡ strict path |
| C5 | Spec conformance | Efficient parser ≡ executable denotational spec (the EverParse pattern) |
| C6 | Extracted = displayed | The text extraction and the display list are derived from the *same* interpreter pass, so indexed text is the rendered text (anti text-poisoning) |
| C7 | Incremental update is conservative | `writeAnnots doc marks = bytes ++ update` (ISO 32000-2 §7.5.6: new objects, updated page dictionaries, a cross-reference section with `/Prev`); the strict parser on `bytes ++ update` yields every original object unchanged and, as the pages' annotations, exactly `marks` (`annotationsOf (parse (writeAnnots doc marks)) = marks`); the update is checked by the same parser, there is no writer-side spec |

### Tested, not proven

- Rendering faithfulness: differential testing against pdf.js, MuPDF, pdfium (pixel-diff with
  perceptual threshold).
- Font rasterization quality.
- Float-level numeric behavior of the rasterizer (the ℚ model is the proven reference).

---

## 5. Specification strategy

### 5.1 Spec-first, two implementations

For each layer:

1. Write a **denotational spec**: a small, obviously-correct (possibly slow) Lean function or
   inductive relation. E.g. `ObjSpec : List Token → PdfObject → Prop`.
2. Write the **efficient implementation** (tail-recursive over `ByteArray`, no backtracking).
3. Prove `impl bytes = specInterp bytes` (C5).

Proofs about the *spec* (unambiguity, round-trip) then transfer to the implementation.

### 5.2 Termination measures (the hard, novel part)

- **Xref/`/Prev` chains**: measure = strictly decreasing set of unvisited file offsets
  (`Finset ℕ` bounded by file length). A revisited offset is an error, not a loop.
- **Indirect `/Length`**: resolve through a resolution function with fuel = number of objects;
  a `/Length` that transitively needs its own stream is an error.
- **Page tree**: depth bounded by node count; visited-set on node ids; `/Kids` cycles rejected.
- **XObject / Type 3 / pattern recursion**: nesting fuel (spec-permitted limit, e.g. 32),
  carried in the graphics state, decremented at each `Do` of a form.
- **Object streams**: an object inside an object stream may not itself be the stream's
  container — rank argument on (generation of container, offset).

Bogk & Schöpl's crafted DoS file and mutations of it become permanent regression tests.

### 5.3 Subset-first roadmap (SafeDocs strategy)

Start with a strict subset grammar (roughly Caradoc-strict ∪ what pdfTeX emits), get the
full proof stack working end-to-end, then widen feature by feature. Never widen the grammar
without extending the proofs.

### 5.4 The repair path

Real corpora force a lenient mode (broken xref ⇒ scan for `N 0 obj`). Architecture:

```
bytes → strictParse  ──ok──────────────────────▶ Document (verified path)
          │fail
          ▼
       repair (total, proven terminating) → normalized objects → strictValidate → Document{repaired:=true}
```

The repair module is *proven total and bounded* (S2, S3) but not proven "correct" (there is no
spec for garbage); its output must pass the same strict validation. C4 guarantees it never
changes the meaning of a valid file.

---

## 6. Phased roadmap

Feature tiers from the product side: **Tier 0** = most papers won't display without it,
**Tier 1** = usable reader, **Tier 2** = long tail.

Phases 0–8 are **complete** — milestones M0–M8 ticked, with the evidence recorded in
[progress.md](progress.md) and the full phase descriptions archived in
[docs/plan-archive.md](docs/plan-archive.md).

| Phase | Delivered | Milestone |
|---|---|---|
| 0 | Lake project, CI + proof-hygiene guard, corpus + fuzzing harness, inspector skeleton | M0 |
| 1 | Lexer + object model: spec/impl equivalence, round-trip `parse (print o) = o` | M1 |
| 2 | Xref, trailer, revisions ★: termination + unambiguity proofs, repair path | M2 |
| 3 | Filters in Lean with proven output/work bounds; decompression-bomb suite | M3 |
| 4 | Document structure (acyclic page tree), navigation, encryption | M4 |
| 5 | Content interpreter ≡ spec, typed DisplayList, SVG export | M5 |
| 6 | Fonts (TrueType/CFF/Type 1/CID) + text extraction (C3/C6), 0.9949 vs MuPDF | M6 |
| 7 | Rasterizer (fills, strokes, images, transparency), 99.4% pixel parity, median 64 ms | M7 |
| 8 | Tk viewer shell, annotation display (`/AP`), library API `safe-pdf-core` | M8 |

### Phase 9 — GUI enhancements (viewer UX + user annotations)
Shell work (`Shell/App/`, unverified; Tk-free logic modules with `#guard`s and theorems, as
established in 8.2). The verified core is untouched.
- **Look and feel: imitate PDF.js**, the viewer built into Firefox (Mozilla, Apache-2.0;
  its `web/` sources — `viewer.html`, `viewer.css`, `toolbar.js`, `pdf_sidebar.js`,
  `annotation_editor_layer` — are the reference for layout, spacing, icons and behaviour;
  we re-create the look in Tk, no code or icon files are copied unless their licence and
  attribution are recorded in Decisions). Concretely:
  - *Sidebar*: the document outline opens in a left sidebar **only when the document has
    an outline** (open on load in that case); the sidebar toggle button (far left of the
    toolbar) is hidden when there is none. Nested entries collapse with disclosure
    triangles; clicking an entry jumps.
  - *Toolbar, left*: sidebar toggle, then small ∧ / ∨ previous/next-page arrow buttons
    next to an editable page-number box and the label "of N" — typing a number and Enter
    jumps there; an invalid entry reverts to the current page.
  - *Toolbar, centre*: zoom out (−), zoom in (+) and a zoom drop-down (Automatic Zoom,
    Actual Size, Page Fit, Page Width, 50 %–400 %) showing the current choice.
  - *Toolbar, right*: annotation tools — Highlight (pop-over: colour swatches yellow,
    green, blue, pink, red; thickness slider for free highlights; "Show all" toggle),
    Add comment/note, Add text, Draw (ink), Add image (stamp) — then Print and Save, and a
    `»` overflow menu (first/last page, rotate, scroll and spread modes, document
    properties). Save writes the annotations into the PDF as an **incremental update** to a new
    revision of the file (C7; the original bytes are never modified in place, S8); Print and
    image stamps may land after M9 (recorded in the ledger).
  - *Selection bubble*: selecting text pops a small floating toolbar next to the
    selection — highlight (colour swatch with a drop-down to change colour), comment,
    and delete when an existing highlight is selected — as PDF.js does.
- **Menu bar** (File / Edit / View / Go): a native Tk menubar duplicating the toolbar
  commands (View → Outline, Go → Back / Forward; the keys F9 and Alt+Left/Right stay).
  (Amended 2026-11-20: the outline toggle stays on the toolbar as PDF.js's sidebar button,
  shown only when an outline exists.)
- **Wheel scrolling across pages**: the mouse wheel (macOS trackpad deltas included)
  continues into the next / previous page as the keys already do, instead of stopping at
  the page edge.
- **View modes** (View menu): single page (today's mode), continuous vertical scroll, two
  pages side by side, and continuous facing pages; paging in the facing modes moves two by
  two. Page cache and prefetch extend to the visible neighbours.
- **User highlights in colors**: select text, then highlight it in a chosen color (Edit
  menu or right click); the highlight quads come from the C3 glyph boxes of the selection.
- **Notes**: a text note anchored to a selection or a page point, shown as a marker on the
  page, edited in a small popup.
- **Right-click menu** grows *Highlight* (color submenu) and *Add note…* next to
  Copy / Select all / Find.
- **Persistence — annotations inside the PDF** (decided 2026-11-20; replaces the XFDF
  sidecar as the primary store): user highlights and notes are written as annotation
  objects (`/Subtype /Highlight` with `/QuadPoints` from the C3 glyph boxes, `/Text` notes
  with `/Contents`, `/C` colour, `/M` date, a generated appearance stream so viewers that
  do not synthesise one still draw them) and appended to the file as an **incremental
  update** (ISO 32000-2 §7.5.6: the new objects, the page dictionaries with their `/Annots`
  extended, a cross-reference section and trailer with `/Prev`). The original bytes are a
  prefix of the result and are never modified in place (S8); the writer is a core function
  with the conservativity theorem C7, and the result is validated by opening it with our
  own strict parser before it is written out. Standalone use writes `FILE-annotated.pdf`
  (or overwrites on request, after the validation); the bib-lean reader mode (built here, now owned by the bib-lean side)
  sends it through bib-lean's `PUT` route instead, which keeps the previous revision. Other
  viewers (pdf.js, Acrobat, Okular) therefore find the highlights. XFDF (ISO 19444-1)
  remains as an import/export option, no longer the store.
- **M9**: a paper reads end-to-end with the wheel in every view mode; a highlight and a
  note survive close/reopen inside the PDF (C7 proved; the annotated file opens in
  Acrobat/Okular/pdf.js with the highlights visible, and in our strict parser unchanged);
  side-by-side screenshots of the same paper in our viewer and in Firefox's PDF.js show the
  same toolbar layout (sidebar only with an outline, page box with arrows, centred zoom,
  tools on the right) and the same selection bubble.

### Phase 10 — Viewer polish

(The bib-lean reader mode that used to be this phase was descoped on 2026-11-23 at the
human's request: the integration will be implemented on the bib-lean side, with safe-pdf
consumed there as a library / external reader. The `--biblean` code already built here
(ledger tasks 10.1–10.4, archived) stays in the tree until bib-lean's replacement lands.)

- **Viewer polish (this phase's content)**:
  - The running app presents as **SafePDF** (window title, about); the executable stays
    `viewer` for now.
  - Every transient dismisses on **Escape** and on clicking elsewhere: the tool pop-overs
    (today they never close), highlight/note popups, the find and go-to bars.
  - **Backspace/Delete** removes the selected highlight or note; **undo/redo**
    (Ctrl/Cmd+Z, Ctrl/Cmd+Shift+Z) over mark create/edit/move/delete.
  - An explicit **select-text tool** (the default) in the toolbar; the cursor telegraphs
    the action: I-beam over text, crosshair in draw mode, hand over links.
  - **macOS key conventions**: Cmd variants of every shortcut (Cmd+O/F/C/G/A/W/Z…), bound
    by platform; Ctrl stays on Linux.
  - **Aqua highlight rendering**: translucent fills via an overlay image (Tk Aqua has no
    stipples; outline-only highlights read as dated).
  - **Text selection covers the whole selected text** (added 2026-11-23 at the human's
    request): the selection is a continuous light-blue fill behind all the selected text, as
    in PDF.js and Preview, not small boxes or outlines around glyph runs. Each line's fill
    spans the full line height (no gaps between consecutive lines of a paragraph); interior
    lines of a multi-line selection fill from the line's start to its end; the first line
    fills from the selection start to the line end and the last from the line start to the
    selection end. The ink stays readable through the fill. Copy and search keep working on
    the same glyph ranges; only the drawn shape changes.
- **M10**: the polish list above lands, smoke-tested — Escape dismissal everywhere,
  delete/undo on marks, the select tool with its cursors, Cmd keys on macOS, translucent
  Aqua highlights, the whole-text light-blue selection, and the SafePDF title.

### Phase 11 — Native macOS shell (Tk stays on Linux)

The Tk look is the ceiling on macOS (§8: the shell is unverified and replaceable; the core
as a library is the deliverable). On macOS the viewer becomes a **native AppKit shell**
over the `safe-pdf-core` C API; Linux keeps the Tk shell. Chosen at build time; one shared
Tk-free logic layer (View, Select, Links, Marks, Save) serves both shells.
- Spike first (11.1, **done**): a minimal Cocoa window (open, render, scroll, zoom) over
  the C API; the human's feel check passed ("scrolling, pinch and sharpness feel pretty
  good").
- **The port brief** (the human, 2026-11-24): *same design as the Linux version, but it
  should feel new — updated, modern design and seamless use.* The detailed plan is
  [docs/macos-design.md](docs/macos-design.md): the Tk/PDF.js layout and every behaviour
  rule kept; re-expressed in current AppKit (unified toolbar with SF Symbols and the
  macOS 26 glass treatment, sidebar material, native momentum + live pinch magnification
  with a cross-fade to the sharp re-render, dark mode, accent-coloured selection, sheets
  and popovers, a proper `SafePdf.app` bundle) — glass APIs runtime-gated, minimum
  macOS 14.
- **Architecture (11.2, decided)**: the shared Lean logic is exported through the C API as
  pure functions and flat C structs — anything with a theorem or `#guard` stays in Lean, so
  the proofs keep applying; the shell itself is Swift and owns only widgets and events.
  Rendering, text index, links and outline go through the **confined document worker**
  (Phase 12's 12.2a–d) with priorities, cancellation and deadline kill: the native shell is
  sandboxed and stall-free from day one, retiring the spike's in-process render path.
- Full shell (11.3a–e): C API v2, app scaffold, viewing parity, text/navigation parity,
  marks + save parity — then platform build selection + CI (11.4), an accessibility-driven
  scripted session mirroring the Tk smoke (11.5), and a feel pass with the human (11.6).
- **M11**: the macOS app passes the M8/M9 corpus and session checks natively (Cmd keys,
  momentum scroll, Retina, dark mode); the Linux Tk build stays green and unchanged; the
  human's feel checklist (docs/macos-design.md §5) comes back good.

### Phase 12 — Hardening (from the independent security review)

The review's lesson ([docs/safety.md](docs/safety.md) §5): these items protect the user
even if every current theorem is correct.
- **Capped reads + true strict mode**: share the inspector's capped read with
  `Api.openFile`, XFDF import and the overwrite comparison; `allowRepair := false` skips
  repair work instead of rejecting a repaired result after parsing.
- **Restricted, stoppable document worker**: the core plus document-derived font/image
  processing in a child process the GUI can kill; the GUI brokers file, clipboard and save
  access; no credential enters the child. Async rendering lands
  with it (no UI stalls — page turns block up to ~3 s today).
- **One budget per user operation**: memory reserved for concurrent page buffers,
  thumbnails and caches before dispatch; a shared work allowance through a search, export
  or render; worker ceilings and deadlines enforced outside Lean's cost model.
- **Writer confidentiality**: fresh AES IVs from OS randomness passed into the pure
  writer; an explicit policy for legacy RC4 writes and signed inputs; cryptography review.
- **Honest UI for degraded/hidden content**: trusted file identity visible in document
  full screen; invisible-text provenance in exports; revision-retention notice on
  annotation delete.
- **Independent verification**: lean4lean proof re-check in CI, compiled-vs-interpreted
  differential, viewer/pixel/position CI on a pinned corpus, OSS-Fuzz, external review /
  red team.
- **Proof gaps**: C4 with explicit hypotheses (the `repair-diff.pdf` fixture shows strict
  and repair diverging on a strict-valid file); targeted numeric error bounds for the
  raster float surfaces (fill/stroke are already integer fixed-point).
- **M12**: the review's priority-1/2/3 acceptance criteria hold — a growing input reads
  only through the cap; a strict-only open records zero repair attempts; a platform test
  shows the worker cannot open unrelated files, reach the network or see the token, and
  killing a stalled worker leaves the GUI able to open the next file; an interleaved
  zoom/search/thumbnail CI scenario stays within published memory ceilings.

### Phase 13 — Hardening II (the binary matches the claims)

(Added 2026-11-25 at the human's request, from a check of the S1 and S3 arguments against the
compiled binary. Phase 12 closed the review's boundary items; this phase closes what that
check found and what Phase 12 recorded as still in-process.)

What the check found (measured with `inspect` on the Linux sandbox; the modules involved are
unchanged since): the proofs hold, and the binary does more than they say.
- A single path of `n` segments costs `n²`: 100,000 `l` operators take 7.1 s, from a 1.4 KB
  compressed file — a regression from the optional-content change (the runner keeps the
  machine shared across a call, so every append copies the path).
- A dictionary of `n` distinct keys parses in `n²` (40,000 keys: 15 s); no limit applies.
- One operator is one unit of `maxOpsPerPage`, yet a stacked clip costs 5 ms and a full-page
  fill 2 ms: a page inside the default limits can cost hours. The worker's 20 s deadline
  stops a render; nothing stops the library, the inspector, or the **parse that both GUI
  processes still run themselves** on open and on save.
- The hygiene guard reads source text and a hand-kept theorem list. It has no rule for
  `@[extern]`, `@[implemented_by]`, `axiom` or `native_decide`, never looks at the bounds
  proofs inside compiled definitions, and misses two `partial` functions that
  `deriving Repr` generates in the core.
- Fuzzing stops at 4,096-byte inputs and drives parser entry points only; release builds
  compile out the runtime's bounds assertions (`-DNDEBUG`).
- On the two profiled documents, 38% and 52% of stack samples are inside bignum arithmetic,
  part of it on constants rebuilt on every call.

The rule for this phase: a property is called *proven* for what a theorem states and
*enforced* for what CI checks on every build; what the binary does beyond the model
(wall-clock time, the Lean→C toolchain, the process the code runs in) is tested or
contained — and the documents say which.

- **Time bounds that hold in the binary (S3)**: linear path building again; a duplicate-key
  check that is not quadratic; a **render work allowance** — the counted work behind the
  rasterizer's S3 theorems is charged against one allowance per page render and ends in
  `limitExceeded`, so the bound is deterministic and also protects library users. A
  **scaling suite** times every accumulating structure at `n` and `2n` and fails on
  super-linear growth; the adversarial suite gains long-structure files with time budgets;
  fuzzing gains long inputs under a linear time budget and targets beyond the parser.
- **CI enforces the premises of S1, S2 and S4**: the guard scans the *built environment* of
  the strict modules — every definition (their bounds proofs stand in for run-time bounds
  checks) and theorem depends only on `propext`, `Classical.choice`, `Quot.sound`; no
  `@[extern]`, `@[implemented_by]`, `unsafe`, `axiom` or `partial`, derived ones included;
  no `IO` in a core type. Source rules are added for the constructs the grep misses, the
  two derived `partial` instances are replaced, and the guard is tested against planted
  violations.
- **Exercise what the proofs cannot see**: tests, fuzz, adversarial and the pinned corpus
  run on a build with the runtime's assertions on; the C around the core (Tk shim, worker
  sandbox, macOS C API) is built and tested under sanitizers. (The proof re-check and the
  compiled-vs-interpreted differential exist since Phase 12.)
- **The GUI processes stop parsing documents**: Phase 12 moved rendering, text and links
  into the confined worker; opening (layout, labels, settings, attachments, layers, saved
  marks) and saving (the incremental-update writer and its strict re-parse) still run in
  the Tk viewer and in the macOS app. They move behind the worker protocol, so every
  document-derived computation has a deadline and runs without the GUI's authority; a scan
  of the built environment shows the GUI roots no longer reach the parser, interpreter,
  rasterizer or writer. The save keeps C7 by construction: the GUI appends the worker's
  update to the bytes it read.
- **Cheap performance** (the ℚ reference model and every theorem statement stay as they
  are): constants rebuilt through bignum arithmetic on every call (`2 ^ bpc` per image
  sample; literals ≥ 2³² re-parsed from decimal strings in seven hot functions); 64-bit
  paths with equality theorems for fixed-point multiply and round-divide, where Lean's
  32-bit unboxed `Int` sends every product through GMP; a profiling script so the numbers
  can be reproduced.
- **Statements truth-up**: §4 here, [docs/safety.md](docs/safety.md) and the comparison
  tables say for S1, S2, S3 and S5 what is proven, what is enforced and what is measured —
  and drop what Phase 12 made untrue (S5 "everything runs in the viewer process",
  deterministic IVs, the untested Linux filter).
- **M13**: (1) *time* — the scaling suite passes on every probe (time at `2n` at most 3×
  time at `n`); the long-structure adversarial files finish or end in `limitExceeded`
  within their recorded budgets in the library and the inspector; the long-input fuzz run
  reports no case over its linear budget; (2) *premises* — the environment scan of the
  strict modules reports only the three axioms and no `partial`, `unsafe`, `@[extern]` or
  `@[implemented_by]` beyond compiler-generated ones, and the guard fails on each planted
  violation; (3) *toolchain* — tests, fuzz, adversarial and the pinned corpus pass on the
  assertions build, and the C test binaries pass under sanitizers; (4) *boundary* — the
  scan shows the GUI roots of both shells do not reach the parser, interpreter, rasterizer
  or writer beyond the exceptions recorded in Decisions; opening or saving a document that
  stalls ends at the deadline with a message, the window stays responsive and the next
  file opens; (5) *speed* — corpus page-time median and p95 are no worse than the
  phase-start baseline on the same machine, and no bignum constant is rebuilt per sample
  or per point; (6) *statements* — the documents above are updated to what (1)–(4) now
  establish.

### Phase 14 — Signature verification

(Added 2026-11-26 at the human's request, full scope. Verification only — signing needs key
custody and is a different threat model.)

Why it fits this project: the famous signature-checking failures (signature wrapping, the
incremental-save attacks, the shadow attacks) are **structure attacks, not crypto attacks** —
readers verified the math correctly but misreported *what the signature covers*. That
question is exactly what our revision model and unambiguity proofs reason about, so a
verified viewer can prove the claim every other reader only asserts. Verification is also a
perfect fit for the core: read-only, no secrets, no constant-time requirements (all inputs
public), and pure — trust anchors and the current time enter as data, never through `IO`
(S4 holds; the file's crypto groundwork exists: SHA-256/384/512 with NIST-vector `#guard`s,
signature-dictionary handling in the decrypt and save paths).

- **ASN.1/DER layer** (spec-first, §5.1): denotational spec, efficient implementation,
  equivalence and round-trip theorems; definite lengths only, bounded depth and size from
  `Limits`, total.
- **Crypto verify primitives**: SHA-1 added for legacy signatures (SHA-2 exists); RSA
  verification (`Nat` modexp, PKCS#1 v1.5 and PSS encoding checks) with RFC 8017 / CAVP
  vectors — provable as algebra where cheap; ECDSA over P-256/P-384 (prime-field and curve
  arithmetic) with CAVP vectors.
- **X.509**: certificate parsing, chain building to a caller-supplied anchor set, validity
  against a caller-supplied time, basicConstraints/keyUsage/EKU checks, bounded chain
  length. Name constraints and policy processing recorded as out of scope (Decisions).
- **CMS `SignedData`**: `adbe.pkcs7.detached` and `ETSI.CAdES.detached` (signed attributes:
  contentType, messageDigest, signing time, ESS signing-certificate where present), plus
  the legacy `adbe.pkcs7.sha1` and `adbe.x509.rsa_sha1`.
- **ByteRange + the coverage theorem** (the payoff): well-formedness (exactly the file
  minus the `/Contents` hole), the covered bytes are a byte prefix; theorem tying that
  prefix to the revision model — the signature covers revisions 0..i, and the object-level
  differences between revision i and the displayed document are **enumerated** (the
  anti-shadow-attack property, on `Spec/Unambiguous`'s machinery).
- **Pure verdict in `Api`**: per signature — ByteRange ok, digest ok, signature ok, chain
  trusted/untrusted/expired/incomplete, coverage with the changes-after-signing list,
  revocation `notChecked`. Runs in the confined worker; the shells show it honestly
  (12.5's spirit): "signed — valid, covers the whole document", "signed — N objects
  changed after signing", "signature invalid", "signer not trusted", always with
  "revocation not checked".
- **Trust model**: anchors are bytes supplied by the shell (a user-set directory and/or an
  export of the platform store); whether to bundle the AATL/EUTL lists is the human's
  decision, recorded before the UI task. No network anywhere — revocation and timestamp
  fetching stay out (Tier 2), reported honestly.
- **Tests**: differential against poppler's `pdfsig` and OpenSSL CMS (skip cleanly when
  absent); a signed corpus (existing government files plus generated signed fixtures:
  RSA/ECDSA × v1.5/PSS × SHA-2, CAdES and legacy); an adversarial suite — signature
  wrapping, shadow attacks (hide / replace / hide-and-replace), incremental tampering,
  ByteRange tricks, certificate tricks (expired, wrong keyUsage, self-signed, algorithm
  confusion) — each flagged with the recorded reason within a time budget.
- **M14**: (1) on the signed corpus every verdict agrees with `pdfsig`/OpenSSL (recorded
  trust-set differences aside); (2) every adversarial file is flagged invalid or
  changed-after-signing with the right reason, within its budget; (3) the coverage theorem
  and the DER equivalence are axiom-clean, and the verify primitives pass their vector
  suites; (4) both shells show the verdicts with the honest statuses, including
  "revocation not checked"; (5) the hygiene and environment scans stay clean.

### Tier 2 / later
CCITT fax + JBIG2 (in Lean), JPEG 2000, Type 3 fonts, Separation/DeviceN, blend modes,
optional content groups, tagged-PDF reading order, accessibility export; signatures:
RFC 3161 timestamps, long-term validation (`/DSS`), revocation (OCSP/CRL) fetched through
the GUI broker, PAdES levels beyond B.

#### Printing (deferred)

(Planned 2026-11-27 as Phase 15 at the human's request, issue #21 from the feature list of
#19; **moved to later work on 2026-11-28 at the human's request** — not scheduled. The design
below and the ledger tasks 15.1–15.7, now under "Deferred by the human", are kept for when
it returns.)

**The rule: print the rendered pixels, never the input file.** Handing the document to the
OS print service would have CUPS's filter chain (Ghostscript/poppler) parse the hostile
file — a second, unverified parser outside our sandbox. What is spooled is the output of
our verified rasterizer (marks included), packaged by us — Dangerzone's reconstruction idea
applied to printing — and the UI says so ("printed from SafePDF's rendering at N dpi").

- Print-resolution renders through the confined worker, 300 dpi default (Letter/A4 ≈
  8.4–8.7 Mpx — inside the 10 Mpx per-page cap; 600 dpi needs banded rendering, deferred
  until the human wants it); one print is one user operation under the budget pool
  (reserved before dispatch, progress shown, cancellable).
- A small pure **image-only PDF writer**: one Flate image XObject per page over the
  existing DEFLATE encoder (`Core/Filter/Deflate.lean`; its stored-block decode already
  carries theorems); the output parses under our own strict parser and each stream decodes
  back to the exact raster. The same artifact is **Print to PDF**.
- Linux (Tk has no print dialog): a small dialog of ours — printers from `lpstat -a`, page
  range, copies, dpi — and the generated PDF spooled with `lp`; a fake `lp` on PATH makes
  the whole path smoke-testable.
- macOS: `NSPrintOperation` drawing the worker renders — the native panel (preview,
  ranges, duplex, paper sizes, Save as PDF) comes free.
- `Toolbar.Tool.print` becomes a real command: File → Print…, Ctrl+P / ⌘P in
  `Menu.keyTable` (its `#guard`s keep the platforms consistent).
- **Exit criterion when scheduled (was M15)**: a multi-page document prints on both platforms from the same pixels — the Linux
  smoke captures a spool that strict-parses and pixel-matches the source rasters in MuPDF,
  and the macOS smoke prints to a PDF destination headlessly with the same checks; the
  input file's bytes never reach the print stack; a long print stays within the published
  ceilings and cancel works mid-job; the status line states the dpi.

---

## 7. Testing and evaluation (alongside the proofs)

Proofs show we meet *our* spec; testing shows our spec matches the *world*.

1. **Differential testing** — every phase gains a comparator: objects vs `qpdf --json`,
   pages/boxes vs `mutool info`, text vs `pdftotext`/pdfium, pixels vs MuPDF. Disagreements
   triaged: our bug / their bug / spec ambiguity (document each).
2. **Fuzzing** — continuous AFL-style fuzzing of `parse` and per-layer entry points. The
   totality proofs say panics are *impossible*; the fuzzer checks the unproven glue and the
   proof assumptions (and finds resource-limit miscalibrations).
3. **Adversarial suite** — Bogk DoS file + mutations, decompression bombs, shadow-attack
   samples, polyglots, xref cycles, deep nesting. All must fail *fast and cleanly*.
4. **Corpus tracking** — dashboard per milestone: % opens, % text-accurate, % pixel-accurate,
   median parse/render time. Regressions block merge.
5. **Proof hygiene** — CI: zero `sorry`, `#print axioms` on top-level theorems shows only
   `propext/Classical.choice/Quot.sound`, no `partial`/`unsafe`/`panic!` in `Core/`.

---

## 8. Key design decisions (made) and open questions

**Decided (rationale above):**
- Lean 4 end-to-end for the trusted path; FFI only in the quarantine zone for DCT/JPX.
- Spec-first with equivalence proofs (EverParse pattern), not verified-combinator-only.
- Strict/repair two-parser architecture (Caradoc pattern) with conservativity proof.
- One DisplayList feeding both raster and text (makes C6 structural).
- Rational-arithmetic geometric model as proof reference; float implementation tested.
- The viewer shell is a **native desktop app**, not a webapp: Lean compiles to native code
  via C, so the verified core links directly into any toolkit with a C FFI. A web shell would
  need either server-side parsing (reintroducing the network boundary the threat model
  avoids) or an immature Lean→WASM target. Browser-rendered SVG dumps remain fine as a
  *development* inspector view — the core never runs in a browser.
- **Annotations live inside the PDF, by incremental update** (2026-11-20): user highlights
  and notes are written as standard annotation objects appended to the file (ISO 32000-2
  §7.5.6), never in place, with the conservativity theorem C7 and a re-parse by our own
  strict parser before anything is written. Reason: other viewers must find them; a
  sidecar only we read would make the annotations ours alone. XFDF stays as interchange.
- **bib-lean integration: this repository is a Lake dependency of bib-lean, pinned by
  commit and built from source; the viewer is launched through bib-lean's reader
  contract** (2026-11-20): `viewer --biblean` speaks the contract over loopback HTTP with
  the token on file descriptor 3; `viewer` stays a non-default target so a dependent's
  plain `lake build` never needs Tk; the Lean and Batteries pins must stay in step with
  bib-lean's (Phase 10). **Descoped 2026-11-23 at the human's request: the integration
  moves to the bib-lean side; Phase 10 here is viewer polish only. The `--biblean` code
  stays as-built until bib-lean's replacement lands.**

**Open — revisit at the marked milestone:**
- *Inflate performance in Lean* (M3): if proven-Lean inflate is too slow on big scanned PDFs,
  options: optimize (ByteArray, tail calls), or C zlib in quarantine with Lean re-validation
  — keeping the Lean one as the differential oracle.
- *Rasterizer performance* (M7): compiled Lean should manage; fallback is coarser
  tiling/caching in the shell, never moving raster logic out of the core.
- *How much crypto to trust* (M4): AES from vetted C (sandboxed) vs Lean implementation.
- *GUI toolkit for the shell* (M8): native app decided (above); the toolkit itself is still
  open — GTK, Qt, Tauri, SDL all work via C FFI; the shell is unverified and replaceable.
- *Proof-effort budget*: which C-properties get full mechanization vs property-based testing
  first with proofs retrofitted (C3 is the likeliest to stage this way).

## 9. Risks

| Risk | Impact | Mitigation |
|---|---|---|
| Spec ambiguity (ISO 32000 is loose) | Proofs against a wrong spec | Differential testing (§7.1); adopt SafeDocs/PDF-Association clarifications; document every deviation |
| Font complexity explodes Phase 6 | Schedule | Tier the formats (TrueType → CFF → Type 1 → CID); substitution fallback keeps corpus numbers moving |
| Termination proofs harder than expected | Core novelty at risk | Fuel + visited-set patterns are standard; worst case: explicit fuel with proven-sufficient bounds (weaker but sound) |
| Lean performance | Unusable viewer | Compiled Lean + ByteArray discipline; profile from M1; quarantine-zone escape hatch for image codecs only |
| Proof maintenance cost as grammar widens | Velocity | §5.3: never widen without proofs; spec/impl separation localizes breakage |
| One-person bus factor on proofs | Continuity | Proof patterns documented in-repo (`docs/proof-patterns.md`) from Phase 1 |

## 10. Proposed repository layout

```
safe-pdf/
  Plan.md                      -- this file
  lakefile.lean
  SafePdf/
    Core/                      -- verified: no IO, no partial, no unsafe
      Lex.lean                 -- Phase 1
      Object.lean
      Xref.lean                -- Phase 2
      Filter/                  -- Phase 3 (Flate, A85, ...)
      Doc.lean                 -- Phase 4 (catalog, page tree)
      Crypt.lean
      Content/                 -- Phase 5 (interpreter, DisplayList)
      Font/                    -- Phase 6
      Text.lean
      Raster/                  -- Phase 7
      Limits.lean              -- the resource-limit record (S3)
    Spec/                      -- denotational specs + the theorems
    Repair.lean                -- lenient path (total, conservative)
    Quarantine/                -- FFI decoders + revalidation proofs
    Shell/                     -- unverified native viewer + inspector (MVP track)
  Tests/
    golden/  fuzz/  adversarial/  differential/
  docs/
    proof-patterns.md  deviations-from-spec.md  corpus.md
```

## 11. Immediate next steps

1. Phase 13, first wave: the path-building regression (13.1), the duplicate-key check
   (13.2), the derived `partial` instances (13.8) and the profiling baseline (13.17).
2. Phase 13, design before code: the render work allowance (13.4) and the inventory of
   document work still done in the GUI processes (13.12) are recorded in Decisions first.
3. The external review (12.9) stays deferred by the human.
4. Phase 14 (signature verification) queues behind Phase 13; its two early solo decisions
   (trust anchors, out-of-scope X.509 features) go to Decisions first.
5. Printing (issue #21) is deferred to later work (§6, "Tier 2 / later"); issues #22
   (signatures) and #23 (password-protected PDFs, unscheduled) track the rest of #19's
   feature list.
