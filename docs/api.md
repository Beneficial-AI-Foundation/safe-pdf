# `safe-pdf-core`: the library API

Plan.md §6 Phase 8: *"the core as a library is the real deliverable — e.g. as a drop-in
verified backend for a Zotero-class reference manager (annotation anchoring, text indexing:
exactly C2/C3/C6)."* The API is one module, [`SafePdf/Api.lean`](../SafePdf/Api.lean)
(namespace `SafePdf.Api`): a small, pure facade over the verified core. It adds no
algorithms of its own; every function delegates to the core entry points the viewer and
the inspector use, and its docstring names the guarantees it inherits.

## Using it from another Lake project

The project pins `leanprover/lean4:v4.36.0` and the pure Lean `jpeg2000` package.
Use the same toolchain in your project. The Git identity used by Lake needs read access to
`Beneficial-AI-Foundation/jpeg2000-lean` to fetch the pinned revision on a clean checkout.

`lakefile.lean`:

```lean
require «safe-pdf» from git
  "https://github.com/Beneficial-AI-Foundation/safe-pdf.git" @ "main"   -- or a commit hash
```

(`lakefile.toml`: `[[require]] name = "safe-pdf"`, `git = "…"`, `rev = "main"`.) Then
`import SafePdf.Api`. Building your project builds only the modules `SafePdf.Api` imports
(the verified core; no shell, no Tcl/Tk). In this repository, `lake build SafePdfCore`
builds exactly that closure.

## Example

```lean
import SafePdf.Api
open SafePdf.Api

def main (args : List String) : IO Unit := do
  let some path := args.head? | IO.eprintln "usage: FILE"
  match ← openFile path with
  | .error e => IO.eprintln s!"cannot open: {e}"
  | .ok d =>
    IO.println s!"{d.pageCount} pages"
    for it in outline d do
      IO.println s!"{it.title} -> {reprStr it.target}"
    match pageText d 0 with
    | .ok t =>
      IO.println t.text
      for g in t.glyphs do                 -- glyphs with page-space boxes
        IO.println s!"{g.text} at ({g.origin.x}, {g.origin.y}) box {reprStr g.box}"
    | .error e => IO.eprintln s!"{e}"
    match renderPage d 0 (zoom := 2) with  -- 144 dpi
    | .ok img => IO.println s!"{img.w} x {img.h} RGBA, {img.data.size} bytes"
    | .error e => IO.eprintln s!"{e}"
```

A complete client is [`examples/Extract.lean`](../examples/Extract.lean):

```
$ lake exe extract Tests/golden/pages/outline.pdf
pages: 2
outline: 7 item(s)
  Chapter 1  -> page 2
    Café \ s  -> page 1
    Hi  -> page 1
  Web  -> URI http://example.com
  Missing  -> unresolved "nowhere"
  Far  -> dangling destination
    -> -
page 1 (label 1): crop box [0.000 0.000 200.000 100.000], rotation 0
  text: 0 line(s), 0 glyph(s)
$ lake exe extract --render Tests/golden/text/latin.pdf
pages: 1
...
  [72.000 717.600 156.696 729.600] First line of text.
  ...
  rendered at 72 dpi: 612 x 792 RGBA (1938816 bytes)
```

## Reference

All coordinates are exact rationals (`Rat`) in PDF page space (points, origin bottom-left,
`y` up) unless stated otherwise. Pages are 0-based.

| Function | Result |
|---|---|
| `openBytes (bytes) (o : OpenOptions := {})` | `Except Error Document`. `OpenOptions`: `limits` (default `Limits.default`), `allowRepair` (default `true`; `false` = strict mode). |
| `openFile (path) (o := {})` | `IO (Except Error Document)`: rejects a file larger than `limits.maxInputBytes` before reading it. The only `IO` in the API. |
| `Document.pageCount`, `.repaired`, `.encrypted`, `.version` | document facts |
| `pageInfo d i` | `PageInfo`: `label` (`/PageLabels`, else the page number), `mediaBox`, `cropBox`, `rotation` (`/Rotate`), displayed `size` in points |
| `pageText d i (o := {})` | `PageText`: `text` (reading order), `lines` (`TextLine`: text, box, glyphs left to right), `glyphs` (content order: Unicode `text`, baseline `origin`, `box`, `fontSize`, `dir`, `visible`, provenance `item`/`seq`), `core` (the core result). `TextOptions`: `withAnnots` (default `true`: include annotation appearance text, as the viewer), `layout` (reading-order parameters), `oc` (optional content state, default `none` = the document's default configuration). |
| `renderPage d i zoom (rot := .r0) (oc := none)` | `Image` = `{ w, h, data }`, `4·w·h` RGBA bytes, row-major from the top, white background. `zoom` = pixels per point (1 = 72 dpi); `rot` is added to `/Rotate`. Content hidden by optional content is not painted (`oc`: see `ocState`). |
| `optionalContent d`, `ocState d` | optional content (ISO 32000-2 §8.11): `Option Config` (groups with names, the `/D` configuration: `/Order`, `/RBGroups`, `/Locked`, …; `none` without `/OCProperties`) and the default visibility `State` (the set of groups that are OFF). Change a state with `State.set` or `Config.setGroup` (radio buttons, locked groups) and pass it as `oc` to `renderPage` and `pageText` to show or hide layers. Without `/OCProperties` nothing is hidden. |
| `toScreen info zoom rot p`, `toPage info zoom rot q` | page point ↔ image pixel coordinates (origin top-left, `y` down) for an image rendered with the same `zoom` and `rot` |
| `outline d` | `List OutlineItem`: `title`, `depth`, `target`, `count`, preorder |
| `pageLinks d i` | `List Link`: `rect`, `target` |
| `pageAnnotations d i` | `List Annotation`: `subtype`, `rect`, `contents`, `name` (`/NM`), `author` (`/T`), `flags`, `quadPoints`, `ref` (object number, a stable anchor key), `target` |
| `textString bytes` | decode a PDF text string (UTF-16BE / UTF-8 with BOM, else PDFDocEncoding) |

`Target`: `none`, `page index fit`, `danglingDest fit` (a destination whose page is not in the
document), `unresolved name`, `uri uri`, `action kind` (other actions: never executed or
followed). `Error`: `pdf e` (a core `SafePdf.Error`: malformed, limit exceeded,
unsupported, reference cycle, encryption), `repairRefused e` (strict mode: the strict path
failed with the non-final error `e`; the repair path was not run), `pageOutOfRange i n`,
`badZoom z`; `Error.message` / `toString` give English text.

**Anchoring recipe (C2).** Store an annotation or a selection in page space. To draw it on a
rendered image use `toScreen info zoom rot`; to turn a click on the image into page space use
`toPage info zoom rot`. The two are exact inverses for every positive zoom and every rotation
(theorems below), and `toScreen` is the very matrix the renderer draws with
(`toScreen_eq`), so anchors survive any zoom or rotation change without drift.

**Indexing recipe (C3/C6).** `pageText` returns the text the page *displays* — the glyphs
are read from the display list of the same interpreter pass that renders it — with a box
per glyph; index `t.text` or `t.lines`, keep `(page, glyph index)` or the glyph boxes for hit
highlighting.

## Guarantees

Each is a theorem checked by Lean (axioms: `propext`, `Classical.choice`, `Quot.sound` only),
stated over the API's own types or re-exported from the core:

| Property (Plan.md §4) | Theorem |
|---|---|
| S1/S3: every function is total and bounded by `Limits` | by construction: no `partial`, no `IO` but `openFile`; the core's work bounds (`Limits`, fuel proofs) |
| S7: strict mode never yields a repaired document | `SafePdf.Api.openBytes_strict` |
| C2: `toPage ∘ toScreen = id`, `toScreen ∘ toPage = id` (zoom > 0, every rotation) | `SafePdf.Api.toPage_toScreen`, `SafePdf.Api.toScreen_toPage` |
| C2: `toScreen` is the renderer's view matrix | `SafePdf.Api.toScreen_eq` |
| C6: extracted = displayed (page content) | `SafePdf.Api.pageText_glyphs` (glyphs = extraction of the page's own display list) |
| C3: glyph ↔ display-list provenance | `SafePdf.Api.glyph_provenance` (`Core.Text.extract_from_items`) |
| C3: code bytes neither dropped nor invented | `SafePdf.Api.glyph_codes` (`Core.Text.runGlyphs_codes`) |
| API glyphs are the core glyphs, one to one | `SafePdf.Api.pageText_glyphs_ofCore` |
| Rendered buffer shape `4·w·h` | `SafePdf.Api.renderPage_size` (`Core.Raster.Glyph.renderPage_size`) |
| Outline walk bounded, cycle-safe | `SafePdf.Api.outline_bounded` (`Core.Doc.Nav.outline_items_le`) |

**Not proved** (tested): the reading order and line grouping of `pageText` (a heuristic
matched against MuPDF), glyph box heights (0.2 em below to 0.8 em above the baseline, as the
viewer's selection), pixel accuracy of `renderPage` (compared with MuPDF in CI),
`textString`, annotation and link listing (lenient, rule N1).

## Limits and costs

* Every per-page call (`pageText`, `renderPage`, …) starts from a **fresh** decoded-bytes
  budget (`Limits.maxDecodedTotalBytes`), so calls are independent; nothing is cached —
  cache results yourself if you call twice.
* `renderPage` crops an image side above `Limits.maxPageSide` (16384) pixels; at that size an
  image is up to 1 GiB. Choose the zoom from `PageInfo.size`.
* `renderPage` decodes JPEG, CCITT fax and JPEG 2000 image streams. The JPEG 2000 path
  handles image XObjects, inline images and soft masks under the document's decoded-byte
  and image-area limits. A malformed or unsupported JPEG 2000 image can produce a gray
  placeholder. [JPEG 2000 coverage and limitations](jpx-pages.md#confined-worker-results)
* Remaining limitations listed in the ledger and `docs/deviations-from-spec.md` include
  JBIG2 images (gray placeholders), OpenType (`OTTO`) font programs; documents with a
  non-empty user password; Separation /
  DeviceN colour (approximated); optional-content visibility of page content; scripting and
  actions (never). Unsupported parts degrade (placeholder image, substitute font); they do
  not fail the page.
* Pure functions run in the caller's thread; Lean values are immutable, so a `Document` can
  be shared between tasks (`Task.spawn`) freely.

## Stability

`SafePdf.Api` is the stable surface: names, argument order and result fields listed above
change only with a version bump and a note here. Additions (new fields with defaults, new
functions, new `Target`/`Error` constructors) may happen in minor versions — match with a
wildcard case. Everything under `SafePdf.Core.*` (reachable through `Document.doc` and
`PageText.core`) is internal and may change at any time; the theorems above are restated
over the API so that client proofs do not depend on core names.
