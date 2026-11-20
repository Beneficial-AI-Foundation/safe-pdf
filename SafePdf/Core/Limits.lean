/-!
# Resource limits (Plan.md §4 S3, §10)

The explicit limits `L` under which the core guarantees bounded memory and time.
Every layer takes a `Limits` value; exceeding one yields `Error.limitExceeded`.
-/

namespace SafePdf

/-- Explicit resource limits for the verified core. All sizes are in bytes. -/
structure Limits where
  /-- Maximum input file size. -/
  maxInputBytes : Nat := 1 <<< 30
  /-- Maximum decompressed bytes per stream. -/
  maxDecodedStreamBytes : Nat := 256 <<< 20
  /-- Maximum total decompressed bytes per document. -/
  maxDecodedTotalBytes : Nat := 1 <<< 30
  /-- Maximum image area in pixels. -/
  maxImagePixels : Nat := 1 <<< 28
  /-- Maximum nesting depth of arrays/dictionaries in the object parser. -/
  maxObjectDepth : Nat := 256
  /-- Maximum number of indirect objects. -/
  maxObjects : Nat := 8388607
  /-- Maximum form XObject / Type 3 / pattern nesting (Plan.md §5.2). -/
  maxXObjectDepth : Nat := 32
  /-- Maximum `q` nesting depth in a content stream. -/
  maxGStateDepth : Nat := 256
  /-- Maximum content-stream operators per page. -/
  maxOpsPerPage : Nat := 10000000
  /-- Maximum number of revisions (cross-reference sections) followed along the trailer
  `/Prev` chain of incremental updates (Plan.md §5.2, ISO 32000-2 §7.5.6). Termination of the
  chain walk does not depend on it (the visited set bounds it by the input size); it caps the
  work at `maxRevisions` table parses. Excess yields `Error.limitExceeded .revisions`. -/
  maxRevisions : Nat := 4096
  /-- Maximum number of failed object-parse attempts during the repair scan (Plan.md §5.4).
  After that many failures the scan stops parsing but still records object headers, bounding
  its worst-case time by `O(maxRepairFailures · input size)`. Exhausting it is not an error:
  repair is best-effort, so no `LimitKind` corresponds to it. -/
  maxRepairFailures : Nat := 256
  /-- Maximum number of filters in one stream's `/Filter` chain (ISO 32000-2 §7.3.8.2,
  Plan.md §4 S3). Real files use at most 2–3; the cap bounds the work of one chain at
  `maxFilters` decoding stages, so a chain allocates at most
  `maxFilters · maxDecodedStreamBytes` bytes (`Core.Filter.produced_le_maxFilters`). Excess
  yields `Error.limitExceeded .filters`. -/
  maxFilters : Nat := 8
  /-- Maximum number of `/CharStrings` entries in one embedded font program (Plan.md §6
  Phase 6; task 6.3, `Core.Font.Type1.parse`). Real Type 1 fonts have a few hundred glyphs
  (CJK-free); the cap bounds the per-font charstring work at `maxFontGlyphs · glyphFuel`
  steps. Excess yields `Error.limitExceeded .fontGlyphs`. -/
  maxFontGlyphs : Nat := 4096
  /-- Upper bound (exclusive) on subroutine indices in one embedded font program's `/Subrs`
  (task 6.3); for CFF (task 6.2b) the maximum number of entries of a Global or local Subrs
  INDEX. The Type 1 subroutine table is allocated with `max index + 1` entries, so the cap bounds
  that allocation. Excess yields `Error.limitExceeded .fontSubrs`. -/
  maxFontSubrs : Nat := 32768
  /-- Maximum number of operators and operands one glyph's charstring program may execute,
  subroutine calls included (task 6.3, `Core.Font.Type1.evalGlyph`; task 6.2b,
  `Core.Font.CFF.evalGlyph`). A glyph that runs out is
  **rejected** (listed in `Font1.rejected`, its advance unknown), not fatal to the font, so no
  `LimitKind` corresponds to it (like `maxRepairFailures`). -/
  glyphFuel : Nat := 20000
  /-- Maximum number of form XObject expansions per page (Plan.md §5.2; task 5.2b,
  `Core.Content.Run`). Bounds "billion laughs" form trees that are acyclic and within
  `maxXObjectDepth` but fan out exponentially. Further form `Do`s are skipped with a warning
  (the page still renders what it has, as for `maxOpsPerPage` truncation), so no `LimitKind`
  corresponds to it. -/
  maxFormsPerPage : Nat := 100000
  /-- Maximum number of charstrings (CharStrings INDEX count) in one embedded CFF font program
  (task 6.2b, `Core.Font.CFF.parse`). Separate from `maxFontGlyphs` (Type 1): CID-keyed CFF
  fonts of CJK text legitimately have tens of thousands of glyphs, so the default is the
  format's own 16-bit bound, and the per-font charstring work is bounded by `fontFuel`
  instead of `maxCFFGlyphs · glyphFuel`. Excess yields `Error.limitExceeded .fontGlyphs`. -/
  maxCFFGlyphs : Nat := 65535
  /-- Maximum number of charstring interpreter steps for **all** glyphs of one CFF font
  together (task 6.2b, `Core.Font.CFF.evalList`; default 2²⁵). Once it is spent the remaining
  glyphs are **rejected** (their advances unknown), not fatal to the font, so no `LimitKind`
  corresponds to it (like `glyphFuel`). -/
  fontFuel : Nat := 1 <<< 25
  /-- Maximum number of Font DICTs in a CID-keyed CFF font's `FDArray` (task 6.2b; FDSelect
  stores one byte per entry, so real fonts have at most 256). Excess yields
  `Error.limitExceeded .fontDicts`. -/
  maxFontDicts : Nat := 256
  /-- Maximum number of chords one cubic Bézier segment is flattened into (task 7.2a,
  `Core.Raster.Fill.segCount`; values below 1 act as 1). Makes the edge count of a flattened
  path data-independent: at most `curveSegCap · #segments + 1` edges
  (`Fill.flatten_size_le`). A curve that would need more chords for the flattening tolerance
  is flattened **coarser** (a documented degradation: the error bound `Fill.flatten_err_tol`
  then holds only under the cap condition of `Fill.segCount_tol_of_cap`), so no `LimitKind`
  corresponds to it. At the default tolerance (0.1 px) 512 chords suffice for curves whose
  control polygon spans up to roughly 10⁵ pixels. -/
  curveSegCap : Nat := 512
  /-- Device coordinates are clamped to `±coordLimit` subpixel units (`1/256` px; default
  `2³⁰`, about 4.2 million pixels) when a page-space path is mapped to the device
  (`Core.Raster.Fill.ofContentPath`, the stroker's offsets). Far beyond any window, it keeps
  the integers of the crossing computation moderate. Clamping only moves points that are
  millions of pixels off-screen (a documented degradation), so no `LimitKind` corresponds to
  it. -/
  coordLimit : Nat := 1 <<< 30
  /-- Maximum number of dash steps (element changes along the path) per stroked path (task
  7.2b, `Core.Raster.Stroke.strokeDPath`). The steps are estimated exactly before walking;
  a path whose estimate exceeds the cap is stroked **solid** instead (a documented
  degradation, as MuPDF ignores dash patterns that are too fine), so no `LimitKind`
  corresponds to it. Bounds the stroke edges (`Stroke.strokeEdges_size_le`). -/
  maxDashSteps : Nat := 100000
  /-- Maximum number of chords per quarter of the pen ellipse (task 7.2b,
  `Core.Raster.Stroke.arcCount`; values below 1 act as 1). Every emitted stroke polygon has
  at most `4 · arcSegCap` vertices. A wider pen than the cap resolves is drawn as a
  **coarser** polygon (documented degradation), so no `LimitKind` corresponds to it. -/
  arcSegCap : Nat := 64
  /-- Maximum page width and height in pixels of a rendered page (task 7.2c,
  `Core.Raster.Clip.pageSize`). The default `16384` keeps the pixel count at
  `16384² = 2²⁸ = maxImagePixels`. A page that would be larger at the requested zoom is
  **cropped** to its top-left `maxPageSide × maxPageSide` pixels (documented degradation: the
  viewer can still show the page at that zoom, scrolled), so no `LimitKind` corresponds to
  it. -/
  maxPageSide : Nat := 16384
  /-- Maximum number of cached clip masks per rendered page (task 7.2c,
  `Core.Raster.Clip.ClipCache`). A pure performance knob: an evicted mask is recomputed when
  needed (the work bound `Clip.renderItemsCounted_steps_le` charges every clip as if
  uncached), so it never changes the output and no `LimitKind` corresponds to it. Memory:
  at most `clipCacheSize` masks of at most one page each. -/
  clipCacheSize : Nat := 16
  /-- Maximum marked-content nesting (`BMC`/`BDC` … `EMC`, ISO 32000-2 §14.6) the interpreter
  tracks per content stream (task 6.8d, `Interp.markOp`). Deeper sequences are only counted
  (so their `EMC`s still match) and their `/ActualText` is ignored; no `LimitKind`
  corresponds to it (never an error). -/
  maxMarkedDepth : Nat := 256
  deriving Repr, Inhabited

namespace Limits

/-- The default limits. -/
def default : Limits := {}

end Limits

end SafePdf
