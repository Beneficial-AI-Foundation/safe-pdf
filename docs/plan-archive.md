# Plan archive — completed phases

Moved out of [Plan.md](../Plan.md) on 2026-11-23: the full descriptions of completed
phases 0–8, the MVP / visibility track (delivered through M7) and the original
parallelism note. Milestone evidence lives in [progress.md](../progress.md) and
[docs/progress-archive.md](progress-archive.md).

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

