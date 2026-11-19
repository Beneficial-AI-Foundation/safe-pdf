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
  /-- Length of the xref `/Prev` chain (`Limits.maxRevisions`). -/
  | revisions
  /-- Number of filters in one stream's `/Filter` chain (`Limits.maxFilters`). -/
  | filters
  /-- Number of charstrings in one embedded font program (`Limits.maxFontGlyphs`). -/
  | fontGlyphs
  /-- Subroutine index in one embedded font program (`Limits.maxFontSubrs`). -/
  | fontSubrs
  deriving Repr, DecidableEq, Inhabited

/-- Errors produced by the verified core. -/
inductive Error where
  /-- Malformed input at a byte offset, with a short description. -/
  | malformed (offset : Nat) (msg : String)
  /-- A resource limit was exceeded. -/
  | limitExceeded (kind : LimitKind)
  /-- A feature deliberately left out or not yet supported. -/
  | unsupported (what : String)
  /-- A reference cycle in the file's structure, found at a byte offset (Plan.md §5.2, §6
  Phase 2 M2; Bogk & Schöpl 2014): a revisited xref `/Prev` or `/XRefStm` offset, an object
  that lies in its own object stream, or a `/Length` that transitively needs its own stream.
  `what` names the cycle. Unlike `malformed`, a cycle is **final**: `Core.Open.openFile` does
  not try the repair path on it (`Core.Open.openFile_cycle`), since the cyclic file is
  exactly the attack the strict path exists to reject. -/
  | cycle (offset : Nat) (what : String)
  /-- The document is encrypted and cannot be decrypted (Plan.md §6 Phase 4, ISO 32000-2
  §7.6; task 4.6): an unsupported security handler or revision, a non-empty user password, a
  malformed or missing encryption dictionary. `what` says which. Like `cycle`, this error is
  **final**: `Core.Open.openFile` does not try the repair path on it
  (`Core.Open.openFile_setup_final`), since a repaired trailer must never open an encrypted
  file undecrypted (rule E2). Errors of decrypting individual objects (bad padding, short
  data) are `malformed`, not `encryption`. -/
  | encryption (what : String)
  deriving Repr, Inhabited

/-- Whether an error is a structural cycle (`Error.cycle`). Classifies by constructor, never
by message text. -/
def Error.isCycle : Error → Bool
  | .cycle _ _ => true
  | _ => false

/-- Whether an error is an encryption-setup error (`Error.encryption`). Classifies by
constructor, never by message text (task 4.6). -/
def Error.isEncryption : Error → Bool
  | .encryption _ => true
  | _ => false

/-- **Final errors**: after these the repair path is not tried (`Core.Open.openFile`, rules
P5 and E2): a structural cycle (`isCycle`) or an encryption-setup error (`isEncryption`). -/
def Error.isFinal (e : Error) : Bool := e.isCycle || e.isEncryption

end SafePdf
