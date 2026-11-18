import SafePdf.Core.Error
import SafePdf.Core.Limits
import SafePdf.Core.ObjParse

/-!
# Parse entry point (Plan.md §6 Phase 0, §7 item 1)

The single entry point `parse : ByteArray → Except Error Document` that the fuzzer, the
inspector and later the viewer call. In Phase 0 it is a stub: it checks the input size
against `Limits.maxInputBytes` and looks for the `%PDF-x.y` header. `Document` is a stub that
Phase 2 (file structure: xref, trailer, object resolution) replaces.

Phase 1 adds object-level entry points used by the fuzzer and the golden tests:
`parseObjectAt` (one direct object, `Core.ObjParse.parseObject`) and `parseIndirectAt`
(one indirect object or stream, `Core.ObjParse.parseIndirect`). Both are thin delegations.

Pure and total, within the `Core/` rules of CLAUDE.md (forbidden constructs). Every loop is
structurally recursive on a list or on an explicit fuel argument; the header search is
bounded by `headerWindow` and each version component by `maxVersionDigits`.
-/

namespace SafePdf

/-- Placeholder document produced by the Phase 0 stub parser. -/
structure Document where
  /-- Byte offset of the `%PDF-` header (`0` for a well-formed file). -/
  headerOffset : Nat
  /-- `(major, minor)` from the `%PDF-major.minor` header, if it parses. -/
  version : Option (Nat × Nat)
  /-- Length of the input in bytes. -/
  byteLength : Nat
  deriving Repr, Inhabited

namespace Parse

/-- How far from the start of the file the header may begin. Readers such as Acrobat accept
a header anywhere in the first 1024 bytes (ISO 32000-2 Annex H implementation notes). -/
def headerWindow : Nat := 1024

/-- Maximum number of digits read for each version component. -/
def maxVersionDigits : Nat := 4

/-- The bytes of `%PDF-`. -/
def headerMagic : List UInt8 := "%PDF-".toUTF8.toList

/-- `true` iff `pat` occurs in `bytes` starting at offset `i`. -/
def matchesAt (bytes : ByteArray) : List UInt8 → Nat → Bool
  | [], _ => true
  | b :: rest, i => bytes[i]? == some b && matchesAt bytes rest (i + 1)

/-- First offset `< headerWindow` at which `%PDF-` occurs, if any. -/
def findHeader (bytes : ByteArray) : Option Nat :=
  (List.range (min headerWindow bytes.size)).find? (matchesAt bytes headerMagic)

/-- The decimal value of an ASCII digit byte, if it is one. -/
def digitValue (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48) else none

/-- Read up to `fuel` decimal digits starting at `i`, accumulating into `acc`.
Returns the value and the offset just past the last digit read. -/
def readDigits (bytes : ByteArray) : Nat → Nat → Nat → Nat × Nat
  | 0, i, acc => (acc, i)
  | fuel + 1, i, acc =>
    match bytes[i]? >>= digitValue with
    | some d => readDigits bytes fuel (i + 1) (acc * 10 + d)
    | none => (acc, i)

/-- Parse `major.minor` starting at offset `i` (just after `%PDF-`). -/
def readVersion (bytes : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  let (major, j) := readDigits bytes maxVersionDigits i 0
  if j == i then none
  else if bytes[j]? != some 46 then none   -- '.'
  else
    let (minor, k) := readDigits bytes maxVersionDigits (j + 1) 0
    if k == j + 1 then none else some (major, minor)

end Parse

/-- Parse `bytes` under explicit resource limits. Phase 0 stub: checks the input size and the
`%PDF-x.y` header and returns a placeholder `Document`. -/
def parseWith (limits : Limits) (bytes : ByteArray) : Except Error Document :=
  if bytes.size > limits.maxInputBytes then
    .error (.limitExceeded .inputBytes)
  else
    match Parse.findHeader bytes with
    | none => .error (.malformed 0 "missing %PDF header")
    | some off =>
      .ok { headerOffset := off
            version := Parse.readVersion bytes (off + Parse.headerMagic.length)
            byteLength := bytes.size }

/-- Parse `bytes` under `Limits.default`. The fuzzing entry point (Plan.md §6 Phase 0). -/
def parse (bytes : ByteArray) : Except Error Document :=
  parseWith Limits.default bytes

/-- Parse one direct object starting at the next token at or after `pos`, nesting at most
`limits.maxObjectDepth`. Returns the object and the position after its last token.
Delegates to `Core.ObjParse.parseObject`. -/
def parseObjectAt (limits : Limits) (bytes : ByteArray) (pos : Nat) :
    Except Error (PdfObject × Nat) :=
  Core.ObjParse.parseObject limits bytes pos

/-- Parse one indirect object `n g obj … endobj` (or a stream object) starting at the next
token at or after `pos`. Returns it and the position after `endobj`.
Delegates to `Core.ObjParse.parseIndirect`. -/
def parseIndirectAt (limits : Limits) (bytes : ByteArray) (pos : Nat) :
    Except Error (IndirectObject × Nat) :=
  Core.ObjParse.parseIndirect limits bytes pos

end SafePdf
