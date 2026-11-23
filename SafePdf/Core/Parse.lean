import SafePdf.Core.Error
import SafePdf.Core.Limits
import SafePdf.Core.ObjParse
import SafePdf.Core.Open

/-!
# Parse entry point (Plan.md §6 Phase 0, §7 item 1)

The single entry point `parse : ByteArray → Except Error Document` that the fuzzer, the
inspector and later the viewer call. It checks the input size against
`Limits.maxInputBytes`, looks for the `%PDF-x.y` header (within the first 1024 bytes, version
recorded), then opens the document (Phase 2, task 2.11: strict xref chain, else the repair
path, flagged `repaired`; Plan.md §5.4). The `Document` records the header data and the
opened document (`Core.Open.OpenDoc`), through which objects are resolved.

Since task 4.5 the document is opened with `Core.Open.Session.open` (`openFileB` from the full
`Limits.maxDecodedTotalBytes` budget, Plan.md §4 S3): the xref streams of the chain and the
object streams decoded while validating the root are charged, and the `Document` keeps the
resulting `session` (budget left, decoded object streams). Callers that fetch or decode
afterwards (the inspector views, `Core.Doc.ofSession`) start from that session, so one budget
covers the open and everything after it. With enough budget left the opened document is
exactly `Core.Open.openFile`'s (`Core.Open.Session.open_eq`).

Phase 1 adds object-level entry points used by the fuzzer and the golden tests:
`parseObjectAt` (one direct object, `Core.ObjParse.parseObject`) and `parseIndirectAt`
(one indirect object or stream, `Core.ObjParse.parseIndirect`). Both are thin delegations.

Pure and total, within the `Core/` rules of CLAUDE.md (forbidden constructs). Every loop is
structurally recursive on a list or on an explicit fuel argument; the header search is
bounded by `headerWindow` and each version component by `maxVersionDigits`.
-/

namespace SafePdf

/-- A parsed document: header data and the opened cross-reference structure. -/
structure Document where
  /-- Byte offset of the `%PDF-` header (`0` for a well-formed file). -/
  headerOffset : Nat
  /-- `(major, minor)` from the `%PDF-major.minor` header, if it parses. -/
  version : Option (Nat × Nat)
  /-- Length of the input in bytes. -/
  byteLength : Nat
  /-- The opened document (merged xref, trailer); objects resolve through
  `Core.Open.OpenDoc.getObject`. -/
  doc : Core.Open.OpenDoc
  /-- `/Root` of the trailer: the catalog reference `(num, gen)`, validated to resolve to a
  dictionary (`Core.Open.openFile_root`). -/
  root : Nat × Nat
  /-- The session the document was opened in (task 4.5): the decoded-bytes budget left after
  opening and the object streams decoded so far. Fetch and decode through it
  (`Core.Open.Session.getObject`, `Core.Doc.ofSession`, `Core.Doc.decodeStreamS`). -/
  session : Core.Open.Session
  /-- The session's document is `doc`. -/
  session_doc : session.doc = doc

namespace Document

/-- `true` iff the document was opened by the repair path (Plan.md §4 S7). -/
def repaired (d : Document) : Bool := d.doc.repaired

/-- Number of xref sections in the strict chain (`0` when repaired). -/
def revisions (d : Document) : Nat := d.doc.revisions

/-- Number of cross-reference entries (including free ones). -/
def objectCount (d : Document) : Nat := d.doc.objectCount

/-- Whether the trailer has `/Encrypt` (strings and streams stay encrypted until Phase 4). -/
def encrypted (d : Document) : Bool := d.doc.trailer.encrypted

end Document

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

/-- Parse `bytes` under explicit resource limits, logging the repair path (task 12.1): the
input size, the `%PDF-x.y` header, then `Core.Open.Session.openLogged` (strict, else — only
when `allowRepair` — repaired; decodes charged to the document budget, task 4.5). With
`allowRepair := false` the repair path never runs (`parseLogged_strictOnly`). -/
def parseLogged (limits : Limits) (bytes : ByteArray) (allowRepair : Bool := true) :
    Except Error Document × Core.Open.RepairLog :=
  if bytes.size > limits.maxInputBytes then
    (.error (.limitExceeded .inputBytes), ⟨0, false⟩)
  else
    match Parse.findHeader bytes with
    | none => (.error (.malformed 0 "missing %PDF header"), ⟨0, false⟩)
    | some off =>
      match Core.Open.Session.openLogged limits bytes allowRepair with
      | (.error e, log) => (.error e, log)
      | (.ok s, log) =>
        match s.doc.trailer.root? with
        | none => (.error (.malformed 0 "trailer has no /Root"), log)
        | some root =>
          (.ok { headerOffset := off
                 version := Parse.readVersion bytes (off + Parse.headerMagic.length)
                 byteLength := bytes.size
                 doc := s.doc
                 root
                 session := s
                 session_doc := rfl }, log)

/-- Parse `bytes` under explicit resource limits: the input size, the `%PDF-x.y` header,
then `Core.Open.Session.open` (strict, else repaired unless `allowRepair := false`; decodes
charged to the document budget, task 4.5). `parseLogged` without the log. -/
def parseWith (limits : Limits) (bytes : ByteArray) (allowRepair : Bool := true) :
    Except Error Document :=
  (parseLogged limits bytes allowRepair).1

/-- **Strict-only parse** (task 12.1, M12 "a strict-only open records zero repair
attempts"): with `allowRepair := false` the repair path runs zero times, and a parsed
document is not repaired. -/
theorem parseLogged_strictOnly (limits : Limits) (bytes : ByteArray) :
    (parseLogged limits bytes false).2.attempts = 0 ∧
    ∀ d, (parseLogged limits bytes false).1 = .ok d → d.repaired = false := by
  obtain ⟨ha, hr⟩ := Core.Open.Session.openLogged_false limits bytes
  unfold parseLogged
  split
  · exact ⟨rfl, fun d hd => by cases hd⟩
  · split
    · exact ⟨rfl, fun d hd => by cases hd⟩
    · rcases ho : Core.Open.Session.openLogged limits bytes false with ⟨r, log⟩
      rw [ho] at ha hr
      simp only at ha hr
      rcases r with e | s
      · exact ⟨ha, fun d hd => by cases hd⟩
      · simp only
        split
        · exact ⟨ha, fun d hd => by cases hd⟩
        · refine ⟨ha, fun d hd => ?_⟩
          simp only [Except.ok.injEq] at hd
          subst hd
          exact hr s rfl

/-- A refused parse (`refused = true`) had repair off: the strict path failed with a
non-final error and the repair path did not run. -/
theorem parseLogged_refused {limits : Limits} {bytes : ByteArray} {allowRepair : Bool}
    (h : (parseLogged limits bytes allowRepair).2.refused = true) : allowRepair = false := by
  unfold parseLogged at h
  split at h
  · cases h
  · split at h
    · cases h
    · rcases ho : Core.Open.Session.openLogged limits bytes allowRepair with ⟨r, log⟩
      have hlog : (Core.Open.Session.openLogged limits bytes allowRepair).2 = log := by rw [ho]
      rw [ho] at h
      have hl : log.refused = true := by
        rcases r with e | s
        · exact h
        · simp only at h
          split at h <;> exact h
      unfold Core.Open.Session.openLogged at hlog
      rcases hb : Core.Open.openFileBLogged limits (Core.Filter.Budget.init limits) bytes allowRepair
        with ⟨⟨r1, b1, c1⟩, log1⟩
      rw [hb] at hlog
      have hl1 : (Core.Open.openFileBLogged limits (Core.Filter.Budget.init limits) bytes allowRepair).2.refused
          = true := by
        rw [hb]; rcases r1 with e | d <;> (simp only at hlog; subst hlog; exact hl)
      unfold Core.Open.openFileBLogged at hl1
      cases allowRepair
      · rfl
      · split at hl1
        · cases hl1
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hl1
          split at hl1
          · cases hl1
          · split at hl1 <;> cases hl1

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
