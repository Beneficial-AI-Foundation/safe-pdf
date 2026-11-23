import SafePdf
import SafePdf.Core.Write.Incremental

/-!
# Incremental-update writer (task 9.5a)

Plan.md §4 S8/C7, §6 Phase 9 "Persistence — annotations inside the PDF"; ISO 32000-2 §7.5.6.
Fixtures: `Tests/fixtures-write/` (`generate.py`), the encrypted fixtures of
`Tests/adversarial/encrypted/`.

For every fixture, one dummy `/Square` (and, on two-page files, a second mark on page 2)
is appended with `Write.Incremental.writeAnnots`, then the result is checked against the
original with our own strict parser — the parts of C7 that `Spec.Write` does not prove at
the object level are tested here:

* the original bytes are a prefix of the result;
* `Open.openFile` opens the result strictly (not repaired) with one more revision;
* **every original object** (every in-use or compressed entry of the original's merged
  section) that the update does not rewrite fetches identically (`getObject`, same body, or
  an error in both);
* each rewritten page's annotation list (`annotsOf`) is the old one followed by references
  that resolve to exactly the marks; every other key of the page dictionary is unchanged;
* `Doc.openDoc` on the result gives the same page count;
* a second update on top of the first works (two stacked updates).

Encrypted inputs (task 9.5f, rule W10): every encrypted fixture of
`Tests/adversarial/encrypted/` that opens (RC4 V1/V2/V4, AES-128, AES-256 R5/R6, an object
stream with an indirect `/Length`, a signature dictionary) goes through the same checks, plus:
the result keeps the file key, and the update holds no mark string in the clear.

Refusals: a document opened through the repair path (`Error.unsupported`, rule W1; also an
encrypted one), a page index out of range, a duplicate page index, a non-canonical mark
(duplicate key), a mark with a reference out of range.

Environment:
* `SAFEPDF_WRITE_CORPUS=DIR` also runs the checks on every `*.pdf` of `DIR` (encrypted files
  included, task 9.5f).
* `SAFEPDF_WRITE_OUT=DIR` writes each result as `DIR/<name>` (for `qpdf --check`,
  `mutool draw`).
-/

namespace SafePdf.Tests.WriteIncremental

open SafePdf SafePdf.Core
open SafePdf.Core.Write.Incremental

/-- Fixture directory. -/
def dir : System.FilePath := "Tests" / "fixtures-write"

/-- Encrypted fixture directory. -/
def encDir : System.FilePath := "Tests" / "adversarial" / "encrypted"

/-- Error summary. -/
def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o w => s!"cycle@{o}: {w}"
  | .encryption w => s!"encryption: {w}"

/-- Report a failed check. -/
def check (ctx what : String) (ok : Bool) (detail : String := "") : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL {ctx}: {what} {detail}"
  return 1

/-- A name. -/
def nm (s : String) : Name := Name.ofString s

/-- A dummy square annotation (`/Rect` from the arguments). -/
def square (x y w h : Int) : Dict :=
  [(nm "Type", .name (nm "Annot")), (nm "Subtype", .name (nm "Square")),
    (nm "Rect", .array [.int x, .int y, .int (x + w), .int (y + h)]),
    (nm "C", .array [.int 0, .int 0, .int 1]),
    (nm "BS", .dict [(nm "W", .int 4)]),
    (nm "Contents", .string "safe-pdf 9.5a".toUTF8.toList)]

/-- Same result: equal bodies, or an error in both. -/
def sameResult (a b : Except Error IndirectBody) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error _, .error _ => true
  | _, _ => false

/-- The generation an entry is fetched with. -/
def genOf : Xref.XrefEntry → Option Nat
  | .inUse _ g => some g
  | .compressed _ _ => some 0
  | .free _ _ => none

/-- Check one write of `marks` into `bytes`; returns the failures and the result. -/
def checkWrite (ctx : String) (bytes : ByteArray) (marks : Marks) :
    IO (Nat × Option ByteArray) := do
  let lim := Limits.default
  match Doc.openDoc lim bytes with
  | .error e => return (← check ctx "openDoc (original)" false (errS e), none)
  | .ok doc =>
  match writeAnnots lim doc marks, plan lim doc marks [] with
  | .error e, _ => return (← check ctx "writeAnnots" false (errS e), none)
  | _, .error e => return (← check ctx "plan" false (errS e), none)
  | .ok out, .ok p =>
    let mut f := 0
    f := f + (← check ctx "original is a prefix"
      (out.size ≥ bytes.size && out.extract 0 bytes.size == bytes))
    match Open.openFile lim out with
    | .error e => return (f + (← check ctx "openFile (result)" false (errS e)), some out)
    | .ok d' =>
      let d := doc.file
      f := f + (← check ctx "result strict" (!d'.repaired))
      f := f + (← check ctx "one more revision" (d'.revisions == d.revisions + 1)
        s!"{d.revisions} → {d'.revisions}")
      -- every original object not rewritten fetches identically
      let mut compared := 0
      let mut differ := 0
      for (n, e) in d.xref.entries do
        if p.keys.contains n then continue
        match genOf e with
        | none => pure ()
        | some g =>
          compared := compared + 1
          if !sameResult (d'.getObject lim n g) (d.getObject lim n g) then
            differ := differ + 1
            if differ ≤ 3 then IO.println s!"  {ctx}: object {n} {g} differs"
      f := f + (← check ctx "original objects unchanged" (differ == 0)
        s!"{differ} of {compared} differ")
      -- annotation lists and the rest of each page dictionary
      for pp in p.pages do
        let marksHere := (marks.find? (·.1 == pp.index)).map (·.2) |>.getD []
        match annotsOf d' lim pp.num pp.gen, annotsOf d lim pp.num pp.gen with
        | .ok now, .ok before =>
          let refs := now.drop before.length
          f := f + (← check ctx s!"page {pp.index}: old annotations kept first"
            (now.take before.length == before))
          let resolved := refs.map fun r => match r with
            | .ref n g => match d'.getObject lim n g with
              | .ok (.obj (.dict m)) => some m
              | _ => none
            | _ => none
          f := f + (← check ctx s!"page {pp.index}: new annotations are the marks"
            (resolved == marksHere.map some) s!"{refs.length} refs")
        | _, _ => f := f + (← check ctx s!"page {pp.index}: annotsOf" false)
        match d'.getObject lim pp.num pp.gen with
        | .ok (.obj (.dict pd')) =>
          let others := pd'.filter (·.1 != nameAnnots)
          f := f + (← check ctx s!"page {pp.index}: other keys unchanged"
            (others == pp.dict.filter (·.1 != nameAnnots)))
        | _ => f := f + (← check ctx s!"page {pp.index}: page dictionary" false)
      match Doc.openDoc lim out with
      | .ok doc' => f := f + (← check ctx "same page count" (doc'.pageCount == doc.pageCount))
      | .error e => f := f + (← check ctx "openDoc (result)" false (errS e))
      return (f, some out)

/-- Marks for a document: a square on page 1 (and one on page 2 when it exists). -/
def marksFor (pages : Nat) : Marks :=
  if pages ≥ 2 then [(0, [square 20 20 60 40]), (1, [square 30 120 50 50, square 100 30 40 40])]
  else [(0, [square 20 20 60 40])]

/-- Write a result to `SAFEPDF_WRITE_OUT` if set. -/
def dump (name : String) (out : ByteArray) : IO Unit := do
  match ← IO.getEnv "SAFEPDF_WRITE_OUT" with
  | some d =>
    IO.FS.createDirAll d
    IO.FS.writeBinFile (System.FilePath.mk d / name) out
  | none => pure ()

/-- Run one file: a write, then a second write on top of the result. -/
def runFile (name : String) (bytes : ByteArray) (verbose : Bool := true) : IO Nat := do
  let lim := Limits.default
  let pages := match Doc.openDoc lim bytes with
    | .ok doc => doc.pageCount
    | .error _ => 0
  let (f, out?) ← checkWrite name bytes (marksFor pages)
  let mut f := f
  if let some out := out? then
    dump name out
    let (f2, out2?) ← checkWrite s!"{name} (second update)" out [(0, [square 140 140 30 30])]
    f := f + f2
    if let some out2 := out2? then dump s!"2-{name}" out2
  if verbose || f > 0 then
    IO.println s!"  {name}: {if f == 0 then "ok" else s!"{f} failure(s)"}"
  return f

/-- An encrypted file (task 9.5f, rule W10): the same checks as `runFile` (every original
object fetches — decrypted — identically, the marks decrypt back exactly, a second update
works), plus: the result keeps the file key, and the update holds no mark string in the
clear. -/
def runEncrypted (name : String) (bytes : ByteArray) (verbose : Bool := true) : IO Nat := do
  let lim := Limits.default
  match Doc.openDoc lim bytes with
  | .error e => check name "openDoc (encrypted original)" false (errS e)
  | .ok doc =>
    let mut f := 0
    f := f + (← check name "original has a decryption state" doc.file.crypt.isSome)
    match writeAnnots lim doc (marksFor doc.pageCount) with
    | .error e => return f + (← check name "writeAnnots (encrypted)" false (errS e))
    | .ok out =>
      let upd := (out.extract bytes.size out.size).toList
      let pat := "safe-pdf 9.5a".toUTF8.toList
      let clear := (List.range (upd.length + 1)).any fun i => (upd.drop i).take pat.length == pat
      f := f + (← check name "mark strings encrypted in the update" (!clear))
      match Open.openFile lim out with
      | .ok d' => f := f + (← check name "same file key"
          (match d'.crypt, doc.file.crypt with
            | some a, some b => a.fileKey.data == b.fileKey.data
            | _, _ => false))
      | .error e => f := f + (← check name "openFile (encrypted result)" false (errS e))
    return f + (← runFile name bytes verbose)

/-- Unit checks of `Write.Encrypt` (task 9.5f): for every method and data length 0–40,
`Crypt.decryptBytes` inverts `encryptBytes`, the output length is `methodLen`, AES output is
IV + whole blocks; the IV is deterministic and differs with counter, kind and plaintext. -/
def runEncryptUnit : IO Nat := do
  let mut f := 0
  let k16 : ByteArray := ⟨(List.range 16).toArray.map (·.toUInt8)⟩
  let k32 : ByteArray := ⟨(List.range 32).toArray.map (fun i => (3 * i + 1).toUInt8)⟩
  let cases : List (Crypt.Method × ByteArray) :=
    [(.identity, k16), (.rc4, ⟨k16.data.extract 0 5⟩), (.rc4, k16), (.aesv2, k16), (.aesv3, k32)]
  for (m, key) in cases do
    for n in List.range 41 do
      let data : ByteArray := ⟨(List.range n).toArray.map (fun i => (7 * i + n).toUInt8)⟩
      match Write.Encrypt.encryptBytes m k32 key 12 0 n 0x73 data with
      | .error e => f := f + (← check "encrypt-unit" s!"{reprStr m} n={n} encrypt" false (errS e))
      | .ok c =>
        f := f + (← check "encrypt-unit" s!"{reprStr m} n={n} length"
          (c.size == Write.Encrypt.methodLen m n))
        match Crypt.decryptBytes m key c with
        | .ok p => f := f + (← check "encrypt-unit" s!"{reprStr m} n={n} round trip"
            (p.data == data.data))
        | .error e => f := f + (← check "encrypt-unit" s!"{reprStr m} n={n} decrypt" false
            (errS e))
  let iv (ctr : Nat) (kind : UInt8) (pt : List UInt8) :=
    (Write.Encrypt.deriveIv k32 12 0 ctr kind ⟨pt.toArray⟩).data
  f := f + (← check "encrypt-unit" "IV is 16 bytes, deterministic"
    ((iv 0 0x73 [1, 2]).size == 16 && iv 0 0x73 [1, 2] == iv 0 0x73 [1, 2]))
  f := f + (← check "encrypt-unit" "IV differs by counter, kind, plaintext"
    (iv 0 0x73 [1, 2] != iv 1 0x73 [1, 2] && iv 0 0x73 [1, 2] != iv 0 0x53 [1, 2] &&
      iv 0 0x73 [1, 2] != iv 0 0x73 [1, 3]))
  return f

/-- Refusals on a plain file. -/
def runRefusals : IO Nat := do
  let lim := Limits.default
  let bytes ← IO.FS.readBinFile (dir / "classic.pdf")
  match Doc.openDoc lim bytes with
  | .error e => check "refusals" "openDoc" false (errS e)
  | .ok doc =>
    let isErr (r : Except Error ByteArray) : Bool := match r with
      | .error _ => true
      | .ok _ => false
    let mut f := 0
    f := f + (← check "refusals" "page index out of range"
      (isErr (writeAnnots lim doc [(7, [square 0 0 1 1])])))
    f := f + (← check "refusals" "duplicate page index"
      (isErr (writeAnnots lim doc [(0, [square 0 0 1 1]), (0, [square 0 0 1 1])])))
    f := f + (← check "refusals" "non-canonical mark (duplicate key)"
      (isErr (writeAnnots lim doc [(0, [[(nm "A", PdfObject.int 1), (nm "A", PdfObject.int 2)]])])))
    f := f + (← check "refusals" "reference out of range in a mark"
      (isErr (writeAnnots lim doc [(0, [[(nm "P", PdfObject.ref 0 0)]])])))
    -- an empty mark list still rewrites the page (with the same annotations)
    f := f + (← check "refusals" "empty marks accepted" (!isErr (writeAnnots lim doc [])))
    -- a document opened through the repair path is refused (rule W1)
    let broken ← IO.FS.readBinFile (dir / "broken-xref.pdf")
    match Doc.openDoc lim broken with
    | .error e => f := f + (← check "refusals" "openDoc (broken-xref)" false (errS e))
    | .ok bdoc =>
      f := f + (← check "refusals" "broken-xref opens repaired" bdoc.file.repaired)
      f := f + (← check "refusals" "repaired document refused"
        (match writeAnnots lim bdoc [(0, [square 0 0 1 1])] with
          | .error (.unsupported _) => true
          | _ => false))
    -- an encrypted document opened through the repair path stays refused (rule W1)
    let rbytes ← IO.FS.readBinFile (encDir / "repair-aesv2.pdf")
    match Doc.openDoc lim rbytes with
    | .error e => f := f + (← check "refusals" "openDoc (repair-aesv2)" false (errS e))
    | .ok rdoc =>
      f := f + (← check "refusals" "repair-aesv2 opens repaired and decrypted"
        (rdoc.file.repaired && rdoc.file.crypt.isSome))
      f := f + (← check "refusals" "repaired encrypted document refused"
        (match writeAnnots lim rdoc [(0, [square 0 0 1 1])] with
          | .error (.unsupported _) => true
          | _ => false))
    return f

/-- Fixture names. -/
def fixtures : List String :=
  ["classic.pdf", "annots-indirect.pdf", "annots-null.pdf", "updated.pdf", "xrefstream.pdf",
    "hybrid.pdf", "page-gen.pdf", "linearized.pdf"]

/-- Encrypted fixtures (written, task 9.5f; every handler of `Tests/adversarial/encrypted/` that opens). -/
def encrypted : List String :=
  ["rc4-40.pdf", "rc4-128.pdf", "rc4-v4.pdf", "aesv2.pdf", "aesv3.pdf", "aesv3-r5.pdf",
    "objstm-length-aesv2.pdf", "sig-aesv2.pdf"]

/-- **Suite entry point.** -/
def run : IO Nat := do
  let mut f := 0
  for name in fixtures do
    let path := dir / name
    if ← path.pathExists then
      f := f + (← runFile name (← IO.FS.readBinFile path))
    else IO.println s!"  {name}: skipped (not generated)"
  for name in encrypted do
    f := f + (← runEncrypted name (← IO.FS.readBinFile (encDir / name)))
  f := f + (← runRefusals)
  f := f + (← runEncryptUnit)
  match ← IO.getEnv "SAFEPDF_WRITE_CORPUS" with
  | none => pure ()
  | some cdir =>
    let entries ← System.FilePath.readDir cdir
    let names := (entries.map (·.fileName)).filter (·.endsWith ".pdf") |>.qsort (· < ·)
    for name in names do
      let bytes ← IO.FS.readBinFile (System.FilePath.mk cdir / name)
      let t0 ← IO.monoMsNow
      let enc := match Open.openFile Limits.default bytes with
        | .ok d => d.trailer.encrypted
        | .error _ => false
      let r ← if enc then runEncrypted name bytes false else runFile name bytes false
      let t1 ← IO.monoMsNow
      IO.println s!"  corpus {name}: {if r == 0 then (if enc then "ok (encrypted)" else "ok") else "FAIL"} ({t1 - t0} ms)"
      f := f + r
  return f

end SafePdf.Tests.WriteIncremental
