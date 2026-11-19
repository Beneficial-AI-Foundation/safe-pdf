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
  (task 6.3). The subroutine table is allocated with `max index + 1` entries, so the cap bounds
  that allocation. Excess yields `Error.limitExceeded .fontSubrs`. -/
  maxFontSubrs : Nat := 32768
  /-- Maximum number of operators and operands one glyph's charstring program may execute,
  subroutine calls included (task 6.3, `Core.Font.Type1.evalGlyph`). A glyph that runs out is
  **rejected** (listed in `Font1.rejected`, its advance unknown), not fatal to the font, so no
  `LimitKind` corresponds to it (like `maxRepairFailures`). -/
  glyphFuel : Nat := 20000
  /-- Maximum number of form XObject expansions per page (Plan.md §5.2; task 5.2b,
  `Core.Content.Run`). Bounds "billion laughs" form trees that are acyclic and within
  `maxXObjectDepth` but fan out exponentially. Further form `Do`s are skipped with a warning
  (the page still renders what it has, as for `maxOpsPerPage` truncation), so no `LimitKind`
  corresponds to it. -/
  maxFormsPerPage : Nat := 100000
  deriving Repr, Inhabited

namespace Limits

/-- The default limits. -/
def default : Limits := {}

end Limits

end SafePdf
