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
  deriving Repr, Inhabited

namespace Limits

/-- The default limits. -/
def default : Limits := {}

end Limits

end SafePdf
