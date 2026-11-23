/-!
# Structured errors (Plan.md §4 S7)

A malformed input yields an `Error` value, never an exception.
-/

namespace SafePdf

/-- Which resource limit was exceeded (Plan.md §4 S3). -/
inductive LimitKind where
  | inputBytes
  | decodedStreamBytes
  | decodedTotalBytes
  | imagePixels
  | objectDepth
  | objects
  | xobjectDepth
  | gstateDepth
  | opsPerPage
  deriving Repr, DecidableEq, Inhabited

/-- Errors produced by the verified core. -/
inductive Error where
  /-- Malformed input at a byte offset, with a short description. -/
  | malformed (offset : Nat) (msg : String)
  /-- A resource limit was exceeded. -/
  | limitExceeded (kind : LimitKind)
  /-- A feature deliberately left out or not yet supported. -/
  | unsupported (what : String)
  deriving Repr, Inhabited

end SafePdf
