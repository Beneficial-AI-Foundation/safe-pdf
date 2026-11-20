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

Removal and supersession (task 9.5g, rule W11, `runEdit`), on every fixture and encrypted
fixture: after a first write of two squares A, B on page 1 (and C on page 2), one
`writeUpdate` removes A's reference, supersedes B (and C) under their own numbers with new
dictionaries, and adds a square D. Checked: the first result is a byte prefix; strict reopen
with one more revision; every object number the update does not write fetches identically;
page 1's annotation list is the old one without A (B in place) followed by D, the other page
keys unchanged; B and C fetch exactly their new dictionaries; page 2 is not rewritten (C's
reference is unchanged); `qpdf --check` (skipped without qpdf, probed by `qpdf --version`);
for encrypted files no plaintext in the update; a third update on top (`writeAnnots`) keeps
everything. Refusals: removing a reference that is not on the page, superseding a page
object, an object twice, a free or out-of-range number.

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

/-- `qpdf --check` exit code, if `qpdf` runs (probed with `--version` first: a missing
command does not throw, the child exits 255). -/
def qpdfCheck (bytes : ByteArray) : IO (Option UInt32) := do
  try
    let probe ← IO.Process.output { cmd := "qpdf", args := #["--version"] }
    if probe.exitCode != 0 then return none
    let (h, tmp) ← IO.FS.createTempFile
    h.flush
    IO.FS.writeBinFile tmp bytes
    let out ← IO.Process.output { cmd := "qpdf", args := #["--check", tmp.toString] }
    IO.FS.removeFile tmp
    return some out.exitCode
  catch _ => return none

/-- A square with another colour and contents (the superseding dictionary). -/
def square2 (x y w h : Int) : Dict :=
  [(nm "Type", .name (nm "Annot")), (nm "Subtype", .name (nm "Square")),
    (nm "Rect", .array [.int x, .int y, .int (x + w), .int (y + h)]),
    (nm "C", .array [.int 1, .int 0, .int 0]),
    (nm "Contents", .string "safe-pdf 9.5g".toUTF8.toList)]

/-- The page plan's annotation references after `n` old ones. -/
def lastRefs (d : Open.OpenDoc) (lim : Limits) (pg : Doc.Page) (k : Nat) :
    List (Nat × Nat) :=
  match annotsOf d lim pg.num pg.gen with
  | .ok xs => (xs.drop (xs.length - k)).filterMap fun o => match o with
    | .ref n g => some (n, g)
    | _ => none
  | .error _ => []

/-- **Removal and supersession** (task 9.5g; see the module doc) on `bytes`. -/
def runEdit (name : String) (bytes : ByteArray) (enc : Bool) : IO Nat := do
  let lim := Limits.default
  let ctx := s!"{name} (edit)"
  let .ok doc := Doc.openDoc lim bytes | return (← check ctx "openDoc" false)
  let two := doc.pageCount ≥ 2
  let first : Marks := [(0, [square 20 20 60 40, square 100 20 60 40])] ++
    (if two then [(1, [square 30 120 50 50])] else [])
  let .ok out1 := writeAnnots lim doc first | return (← check ctx "first write" false)
  let .ok doc1 := Doc.openDoc lim out1 | return (← check ctx "reopen first write" false)
  let (some pg0, pg1) := (doc1.pages[0]?, doc1.pages[1]?) | return (← check ctx "pages" false)
  let [rA, rB] := lastRefs doc1.file lim pg0 2 | return (← check ctx "first refs" false)
  let rC := (pg1.map fun pg => lastRefs doc1.file lim pg 1).getD [] |>.head?
  let newB := square2 100 20 60 40
  let newC := square2 30 120 50 50
  let sups : List Supersede := [(rB.1, rB.2, newB)] ++
    ((if two then rC else none).map fun r => (r.1, r.2, newC)).toList
  let edits : Edits := [⟨0, [rA], [square 200 20 30 30]⟩]
  match writeUpdate lim doc1 edits sups, planUpdate lim doc1 edits sups with
  | .error e, _ => check ctx "writeUpdate" false (errS e)
  | _, .error e => check ctx "planUpdate" false (errS e)
  | .ok out2, .ok p =>
    let mut f := 0
    f := f + (← check ctx "first result is a prefix"
      (out2.size ≥ out1.size && out2.extract 0 out1.size == out1))
    if enc then
      let upd := (out2.extract out1.size out2.size).toList
      let pat := "safe-pdf 9.5g".toUTF8.toList
      f := f + (← check ctx "superseding strings encrypted"
        (!(List.range (upd.length + 1)).any fun i => (upd.drop i).take pat.length == pat))
    match Open.openFile lim out2 with
    | .error e => return f + (← check ctx "strict reopen" false (errS e))
    | .ok d' =>
      let d := doc1.file
      f := f + (← check ctx "strict, one more revision"
        (!d'.repaired && d'.revisions == d.revisions + 1))
      let mut differ := 0
      for (n, e) in d.xref.entries do
        if p.keys.contains n then continue
        if let some g := genOf e then
          if !sameResult (d'.getObject lim n g) (d.getObject lim n g) then differ := differ + 1
      f := f + (← check ctx "objects not written unchanged" (differ == 0) s!"{differ} differ")
      match annotsOf d lim pg0.num pg0.gen, annotsOf d' lim pg0.num pg0.gen with
      | .ok before, .ok now =>
        let kept := before.filter (· != .ref rA.1 rA.2)
        f := f + (← check ctx "page 1: old list without A, then D"
          (now.take kept.length == kept && now.length == kept.length + 1 &&
            before.contains (.ref rA.1 rA.2) && kept.contains (.ref rB.1 rB.2)))
        match now.getLast? with
        | some (.ref n g) => f := f + (← check ctx "D fetches"
            (match d'.getObject lim n g with
              | .ok (.obj (.dict x)) => x == square 200 20 30 30
              | _ => false))
        | _ => f := f + (← check ctx "D reference" false)
      | _, _ => f := f + (← check ctx "annotsOf" false)
      match d.getObject lim pg0.num pg0.gen, d'.getObject lim pg0.num pg0.gen with
      | .ok (.obj (.dict a)), .ok (.obj (.dict b)) =>
        f := f + (← check ctx "page 1: other keys unchanged"
          (a.filter (·.1 != nameAnnots) == b.filter (·.1 != nameAnnots)))
      | _, _ => f := f + (← check ctx "page 1 dictionary" false)
      f := f + (← check ctx "B superseded"
        (match d'.getObject lim rB.1 rB.2 with
          | .ok (.obj (.dict x)) => x == newB
          | _ => false))
      if two then
        if let (some r, some pg) := (rC, pg1) then
          f := f + (← check ctx "C superseded, page 2 not rewritten"
            ((match d'.getObject lim r.1 r.2 with
              | .ok (.obj (.dict x)) => x == newC
              | _ => false) && !p.keys.contains pg.num &&
              (match annotsOf d' lim pg.num pg.gen, annotsOf d lim pg.num pg.gen with
                | .ok x, .ok y => x == y
                | _, _ => false)))
      match ← qpdfCheck out2 with
      | some code => f := f + (← check ctx "qpdf --check" (code == 0) s!"exit {code}")
      | none => pure ()
      dump s!"edit-{name}" out2
      -- a third update on top
      match Doc.openDoc lim out2 with
      | .error e => f := f + (← check ctx "reopen for the third update" false (errS e))
      | .ok doc2 =>
        match writeAnnots lim doc2 [(0, [square 140 140 30 30])] with
        | .error e => f := f + (← check ctx "third update" false (errS e))
        | .ok out3 =>
          f := f + (← check ctx "third update: prefix" (out3.extract 0 out2.size == out2))
          match Open.openFile lim out3 with
          | .ok d3 =>
            f := f + (← check ctx "third update: strict, B kept, A still gone"
              (!d3.repaired && (match d3.getObject lim rB.1 rB.2 with
                | .ok (.obj (.dict x)) => x == newB
                | _ => false) &&
                (match annotsOf d3 lim pg0.num pg0.gen with
                  | .ok xs => !xs.contains (.ref rA.1 rA.2) && xs.contains (.ref rB.1 rB.2)
                  | .error _ => false)))
          | .error e => f := f + (← check ctx "third update reopen" false (errS e))
          match ← qpdfCheck out3 with
          | some code => f := f + (← check ctx "third update: qpdf --check" (code == 0))
          | none => pure ()
      -- refusals
      let isErr (r : Except Error ByteArray) : Bool := match r with
        | .error _ => true
        | .ok _ => false
      f := f + (← check ctx "refuse removing a reference not on the page"
        (isErr (writeUpdate lim doc1 [⟨0, [(rA.1 + 100000, 0)], []⟩] [])))
      f := f + (← check ctx "refuse superseding a page object"
        (isErr (writeUpdate lim doc1 [] [(pg0.num, pg0.gen, [])])))
      f := f + (← check ctx "refuse superseding an object twice"
        (isErr (writeUpdate lim doc1 [] [(rB.1, rB.2, []), (rB.1, rB.2, [])])))
      f := f + (← check ctx "refuse superseding a number beyond /Size"
        (isErr (writeUpdate lim doc1 [] [(d.trailer.size + 5, 0, [])])))
      f := f + (← check ctx "refuse superseding under the wrong generation"
        (isErr (writeUpdate lim doc1 [] [(rB.1, rB.2 + 1, [])])))
      if f == 0 then IO.println s!"  {ctx}: ok"
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
      f := f + (← runEdit name (← IO.FS.readBinFile path) false)
    else IO.println s!"  {name}: skipped (not generated)"
  for name in encrypted do
    f := f + (← runEncrypted name (← IO.FS.readBinFile (encDir / name)))
    f := f + (← runEdit name (← IO.FS.readBinFile (encDir / name)) true)
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
