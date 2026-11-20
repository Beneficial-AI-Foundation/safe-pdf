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
| S8 | Integrity & privacy | Read-only by construction (S4); permission flags treated as advisory; no network by construction |

### Correctness properties — proven

| # | Property | Statement sketch |
|---|---|---|
| C1 | Determinism | Core is pure ⇒ free |
| C2 | Coordinate round-trips | `toScreen zoom rot ∘ toPage zoom rot = id` for all zoom > 0, rot ∈ {0,90,180,270} (over ℚ; the float version tested, with proven error bound if feasible) |
| C3 | Text ↔ position | Every extracted char maps to a glyph bbox; selection is monotone in extraction order; highlight → text span → rectangles round-trips |
| C4 | Repair conservativity | On files accepted by the strict parser, repair path ≡ strict path |
| C5 | Spec conformance | Efficient parser ≡ executable denotational spec (the EverParse pattern) |
| C6 | Extracted = displayed | The text extraction and the display list are derived from the *same* interpreter pass, so indexed text is the rendered text (anti text-poisoning) |

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

### Phase 0 — Infrastructure (short)
- Lake project, CI (build + `#print axioms` check: no `sorry`, no extra axioms), lint rules
  from §3 rule 3.
- Test corpus harness: golden-file tests, fuzzing entry point (`parse : ByteArray → Except`),
  differential-test runner against `qpdf`/`mutool`/pdf.js (structure + text, later pixels).
- Corpus acquisition: ~2k arXiv PDFs across years/engines, SafeDocs evaluation corpus,
  pdf-association test files, Bogk & Schöpl DoS file.
- Inspector skeleton (`Shell/Inspect`): the unverified debug CLI of the MVP / visibility
  track (see §6, after the phases); each later phase adds a view.
- **Milestone M0**: CI green; fuzzer runs; corpus catalogued.

### Phase 1 — Lexer and object model
- Tokenizer for the 8 object types; strings (literal + hex) with escapes; names with `#xx`;
  numbers (spec ranges); dictionaries, arrays; comments; EOL handling.
- Denotational spec + efficient impl + equivalence proof (first instance of §5.1 — this
  phase *establishes the proof pattern* for everything after).
- Properties landed: S1, S2 (for this layer), S7, C1, C5.
- **M1**: object-level round-trip `parse (print o) = o`; fuzzer finds no panics; property
  tests vs `qpdf --json` object dumps on corpus.

### Phase 2 — File structure: xref, trailer, revisions ★ the crown jewel
- Classic xref tables; trailer; **xref streams** (needs Flate + PNG predictors from Phase 3 —
  co-develop); **object streams**; incremental updates (`/Prev`, `/XRefStm` hybrid files);
  linearized files read as ordinary ones.
- Termination proofs of §5.2. Unambiguity proof S6 (one winner per object id across
  revisions, newest-revision-wins, deterministic).
- Repair path (§5.4): offset-tolerant object scan, totality proof.
- **M2**: 99% of corpus opens (strict or repaired); Bogk-style cyclic files all rejected in
  bounded time; **publishable result** — first machine-checked proof that PDF xref
  resolution terminates on arbitrary input.

### Phase 3 — Filters
- FlateDecode **in Lean** (core format; must be in the trusted path): inflate with proven
  output bound (S3: output ≤ limit or error) and totality. Correctness via round-trip with a
  Lean deflate on random data + differential vs zlib on corpus.
- PNG predictors (proven: output length law), ASCIIHex, ASCII85, RunLength (small, fully
  proven), LZW (totality + bounds).
- DCT/JPX/JBIG2: **not in trusted path** — images decode in the quarantine zone (or late, in
  Lean); a failed image renders as a placeholder box, never fails the page (S7).
- **M3**: decompression-bomb suite (nested streams, 10⁶:1 ratios) all rejected within limits.

### Phase 4 — Document structure
- Catalog, page tree with inheritance (`Resources`, `MediaBox`, `CropBox`, `Rotate`);
  acyclicity proof; `getPage : Document → Fin n → Page` total.
- Outline, named destinations, internal links, page labels (Tier 1 navigation) — same
  visited-set discipline (outlines in the wild contain cycles).
- Standard security handler: RC4, AES-128/256, empty-user-password decrypt; permission flags
  parsed but advisory (S8). (Crypto primitives: smallest trusted implementation, tested
  against vectors; proving AES is out of scope.)
- **M4**: page count + page boxes match `qpdf` on corpus; encrypted publisher PDFs open.

### Phase 5 — Content-stream interpreter
- Graphics state machine: `q/Q` (proven bounded stack), `cm`, color (`DeviceGray/RGB/CMYK`,
  ICC → alternate fallback), path construction/painting/clipping, text operators, XObjects
  (recursion fuel proof), inline images.
- Output: a typed `DisplayList` (the single source for both rasterizer and text extraction —
  this is what makes C6 provable).
- Interpreter state transitions specified as an inductive relation; impl proven against it.
- **M5**: operator coverage report ≥ 99% of corpus ops; interpreter never fails on corpus
  (unknown operators skipped per spec, logged); inspector exports pages as **SVG rendered
  from the DisplayList** — the first visible pages, two phases before the rasterizer.

### Phase 6 — Fonts and text extraction
The biggest engineering item.
- Embedded font programs: TrueType (glyf + cmap), CFF, **Type 1** (TeX!), Type0/CIDFont with
  Identity-H; `/Differences` encodings; standard-14 metrics + substitution.
- Font parsers follow the same spec/impl/totality discipline (fonts are untrusted input —
  Duqu came in through font parsing).
- Text extraction: ToUnicode CMaps, fallback via encoding/glyph names, positioned glyph runs,
  reading-order heuristic (tested, not proven), word/line grouping.
- Properties: C3 (text ↔ position round-trips), C6 (extracted = displayed, by construction
  from the DisplayList).
- **M6**: text extraction ≥ 98% similarity vs pdfium/MuPDF on corpus (normalized edit
  distance); all glyph positions within tolerance.

### Phase 7 — Rasterizer
- In Lean, over the DisplayList: scanline fill (nonzero + even-odd), Bézier flattening with
  proven error bound, stroking, clipping, anti-aliasing; glyph outlines through the same path
  code; images composited from quarantine-zone decodes; soft masks + transparency groups +
  shadings (Tier 1 — matplotlib needs them).
- Proven: totality, resource bounds (S3: work ≤ f(area, display-list size)), C2 coordinate
  round-trips over ℚ. Faithfulness: pixel-differential vs MuPDF/pdf.js (perceptual diff).
- **M7**: ≥ 95% of corpus pages within perceptual threshold; render time budget met
  (target: median page < 100 ms compiled).

### Phase 8 — Viewer shell + annotations
- Shell: a **native desktop app** (decided, §8) — open/render/scroll/zoom/rotate, selection &
  copy (from C3 structures), search,
  outline panel, link activation (URI links: click-through with the real target shown — no
  auto-navigation).
- Display existing annotations via appearance streams (`/AP`) — reuses the interpreter.
- Package: library API (`safe-pdf-core`) + minimal GUI. The core as a library is the real
  deliverable — e.g. as a drop-in verified backend for a Zotero-class reference manager
  (annotation anchoring, text indexing: exactly C2/C3/C6).
- **M8**: daily-drivable viewer on the corpus.

### Phase 9 — GUI enhancements (viewer UX + user annotations)
Shell work (`Shell/App/`, unverified; Tk-free logic modules with `#guard`s and theorems, as
established in 8.2). The verified core is untouched.
- **Menu bar** (File / Edit / View / Go): a native Tk menubar; the *Outline*, *Back* and
  *Forward* toolbar buttons move into it (View → Outline, Go → Back / Forward; the keys F9
  and Alt+Left/Right stay), decluttering the toolbar.
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
- **Persistence — XFDF sidecar**: user highlights and notes are saved in a sidecar `.xfdf`
  file next to the PDF, in XFDF (ISO 19444-1), the standard XML interchange format for PDF
  annotations (Acrobat and others import/export it; highlights as `QuadPoints`, notes as
  text annotations, both in page space). The PDF itself is **never written** — S8
  (read-only by construction) stands; the other usual format, annotation objects written
  into the PDF by incremental update (ISO 32000 §12.5), needs a file writer and is at most
  a later "export annotated copy" feature, never an in-place change.
- **M9**: a paper reads end-to-end with the wheel in every view mode; a highlight and a
  note survive close/reopen through the sidecar; the sidecar imports into Acrobat/Okular.

### Tier 2 / later
CCITT fax + JBIG2 (in Lean), JPEG 2000, Type 3 fonts, Separation/DeviceN, blend modes,
optional content groups, tagged-PDF reading order, accessibility export.

### MVP / visibility track

The full viewer lands at M8, but every milestone ships a visible artifact through the
**inspector**: an unverified debug tool (shell code, outside `Core/`) that grows one view per
phase, so progress can be seen — and the plan adjusted from feedback — long before Phase 8.

| After | Visible artifact |
|---|---|
| M0 | Inspector skeleton; corpus dashboard (§7.4) |
| M1 | Pretty-printed object tree of any PDF, diffable against `qpdf --json` |
| M2 | Xref resolution trace, revision history, repair-path report on real files |
| M3 | Decoded-stream viewer (the raw content streams of real papers) |
| M4 | Page-tree + outline browser; encrypted files open |
| M5 | **SVG export of the DisplayList** — recognizably rendered pages two phases early (paths exact; glyphs as positioned boxes until M6) |
| M6 | Extracted-text browser; text layer overlaid on the SVG |
| M7 | Real raster output replaces the SVG approximation |

**Vertical-slice demo (optional, after M2):** a thin cut through Phases 4–7 — minimal page
tree, text + path operators only, standard-14 metrics, SVG output — fed with corpus files
pre-decompressed by `mutool clean -d` / `qpdf --qdf`, so it needs no filters yet. Value: real
rendered pages shortly after M2, and early exercise of the `DisplayList` type (de-risks the
M5 interface freeze). Rules: it lives outside `Core/`, the §3 / §7.5 hygiene rules are not
weakened for it, and it is deleted piecewise as the verified phases replace it.

### Parallelism

Phases 1–3 are sequential (each needs the previous). After M2: filters-completion, Phase 4,
and Phase 5 can proceed in parallel; Phase 6 (fonts) is independent of Phase 7 (paths/raster)
once the DisplayList type is fixed at M5. Suggested split for 2–3 people: one on
parser/structure proofs, one on interpreter+raster, one on fonts/text.

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
  lakefile.toml
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

1. Phase 0: `lake init`, CI with the proof-hygiene checks, pull the first corpus slice,
   inspector skeleton.
2. Reproduce the Bogk & Schöpl cyclic-xref file; check it hangs/crashes stock tools; commit
   it to `Tests/adversarial/`.
3. Phase 1 lexer: write `Spec/Lex.lean` (denotational) before `Core/Lex.lean` — the first
   spec/impl/equivalence triple sets the pattern for the whole project.
