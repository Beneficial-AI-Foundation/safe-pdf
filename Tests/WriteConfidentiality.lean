import SafePdf
import SafePdf.Shell.App.Save

/-!
# Writer confidentiality (task 12.4)

Plan.md §6 Phase 12 "Writer confidentiality"; `Core.Write.Encrypt` rule E3', the protection
policy of `Shell.App.Save`. Fixtures: `Tests/fixtures-write/encrypted/` (qpdf, empty user
password) and small signed / certified PDFs built here (`mkPdf`; the signatures are
placeholders — only their structure matters to the policy).

* **Fresh IVs**: `Save.freshSeed` gives 64 bytes, different on every call. For the AES-128,
  AES-256 and AES-256-with-object-streams fixtures, `Save.build` with a note mark and two
  fresh seeds gives two results that both start with the original bytes, both reopen
  strictly with the note read back (`build`'s own check), differ (the IVs differ), and do not
  hold the note's text in the clear; the same seed twice gives the same bytes (the core is
  deterministic in its seed). Saving again on top of each result (a second note) works and
  reopens strictly too.
* **RC4 policy**: for the RC4-40 and RC4-128 fixtures the save is written (no IV: two seeds
  give identical bytes) and `notes` is exactly `[rc4Note]`; AES files get no note.
* **Signed-input policy**: a signed file (`/SigFlags 3`), one signed only through its field
  `/V` (no `/SigFlags`), and a certified one with `/DocMDP /P 3` are saved with exactly
  `[signedNote]`, their original bytes a prefix of the result and the signature dictionary
  fetching unchanged; certified files with `/P 1`, `/P 2` and without `/P` (default 2) are
  refused with `certifiedRefusal`; an unsigned file is `.unsigned` with no notes.
-/

namespace SafePdf.Tests.WriteConfidentiality

open SafePdf SafePdf.Core
open SafePdf.Shell.App
open SafePdf.Shell.App.Marks (Store)

/-- Report a failed check. -/
def check (ctx what : String) (ok : Bool) (detail : String := "") : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL {ctx}: {what} {detail}"
  return 1

/-- The encrypted fixtures. -/
def encDir : System.FilePath := "Tests" / "fixtures-write" / "encrypted"

/-- A fixed date, so that only the seed varies between two builds. -/
def date : String := "D:20261123120000Z"

/-- Open strictly. -/
def openStrict (bytes : ByteArray) : Except String Doc.Doc :=
  match Api.openBytes bytes { allowRepair := false } with
  | .ok d => .ok d.doc
  | .error e => .error e.message

/-- A store with one note of text `t` on page 1 (after the store's existing marks). -/
def withNote (s : Store) (t : String) (y : Rat := 700) : Store :=
  (s.addNote 0 .yellow t (.point ⟨100, y⟩)).1

/-- Whether `needle` occurs in `hay`. -/
def contains (hay needle : ByteArray) : Bool :=
  needle.size ≤ hay.size &&
    (List.range (hay.size - needle.size + 1)).any fun i =>
      (hay.extract i (i + needle.size)).data == needle.data

/-- The secret text of the notes. -/
def secret : String := "confidential note 12.4"

/-- One encrypted fixture: two saves with fresh seeds, determinism per seed, the policy
notes, a stacked second save. `aes`: the file uses AES (else RC4). -/
def runEnc (name : String) (aes : Bool) : IO Nat := do
  let ctx := s!"enc {name}"
  let path := encDir / name
  unless ← path.pathExists do
    return ← check ctx "fixture present" false path.toString
  let bytes ← IO.FS.readBinFile path
  let .ok doc := openStrict bytes | return ← check ctx "open original" false
  let mut f := 0
  let lim : Limits := {}
  let store := withNote {} secret
  let s1 ← Save.freshSeed
  let s2 ← Save.freshSeed
  let pol := Save.protection doc lim
  f := f + (← check ctx "notes" (Save.notes pol == (if aes then [] else [Save.rc4Note]))
    (reprStr pol))
  f := f + (← check ctx "no refusal" (Save.refusal pol).isNone)
  match Save.build lim doc store date s1, Save.build lim doc store date s2,
      Save.build lim doc store date s1 with
  | .ok (o1, got1, _), .ok (o2, _, _), .ok (o1', _, _) =>
    f := f + (← check ctx "note read back" (got1.length == 1))
    f := f + (← check ctx "original is a prefix (1)" (Save.isPrefix bytes o1))
    f := f + (← check ctx "original is a prefix (2)" (Save.isPrefix bytes o2))
    f := f + (← check ctx "same seed, same bytes" (o1.data == o1'.data))
    if aes then
      f := f + (← check ctx "fresh seeds give different ciphertexts" (o1.data != o2.data))
    else
      f := f + (← check ctx "RC4 has no IV: same bytes for any seed" (o1.data == o2.data))
    let upd := o1.extract bytes.size o1.size
    f := f + (← check ctx "note text not in the clear" (!contains upd secret.toUTF8))
    -- A second save on top of each result reopens strictly with both notes.
    for (o, k) in [(o1, 1), (o2, 2)] do
      match openStrict o with
      | .error e => f := f + (← check ctx s!"reopen result {k}" false e)
      | .ok d1 =>
        let st1 : Store := { (withNote {} secret) with saved := [1] }
        let st2 := withNote st1 "second note" 650
        match Save.build lim d1 st2 date (← Save.freshSeed) with
        | .error e => f := f + (← check ctx s!"second save on result {k}" false e)
        | .ok (o3, got3, n3) =>
          f := f + (← check ctx s!"second save {k}: prefix" (Save.isPrefix o o3))
          f := f + (← check ctx s!"second save {k}: one new mark, two in the file"
            (n3 == 1 && got3.length == 2) s!"{n3} {got3.length}")
          f := f + (← check ctx s!"second save {k}: reopens strictly" (openStrict o3).toBool)
  | .error e, _, _ => f := f + (← check ctx "build 1" false e)
  | _, .error e, _ => f := f + (← check ctx "build 2" false e)
  | _, _, .error e => f := f + (← check ctx "build 1'" false e)
  return f

/-! ## Signed inputs -/

/-- `n` as 10 decimal digits. -/
def pad10 (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (10 - s.length) '0') ++ s

/-- A classic one-revision PDF with objects `1 …` (`objs`), `/Root 1 0 R`. -/
def mkPdf (objs : List String) : ByteArray := Id.run do
  let mut out := "%PDF-1.7\n"
  let mut offs : Array Nat := #[]
  for (o, i) in objs.zip (List.range objs.length) do
    offs := offs.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{o}\nendobj\n"
  let x := out.utf8ByteSize
  out := out ++ s!"xref\n0 {objs.length + 1}\n0000000000 65535 f\r\n"
  for off in offs do
    out := out ++ s!"{pad10 off} 00000 n\r\n"
  out := out ++ s!"trailer\n<< /Size {objs.length + 1} /Root 1 0 R >>\nstartxref\n{x}\n%%EOF\n"
  return out.toUTF8

/-- A one-page document with a signature field; `flags` adds `/SigFlags 3`, `mdp` makes the
signature a certification one (`some none`: without `/P`; `some (some p)`: `/P p`). -/
def sigPdf (flags : Bool) (mdp : Option (Option Nat)) : ByteArray :=
  let sf := if flags then "/SigFlags 3 " else ""
  let perms := if mdp.isSome then " /Perms << /DocMDP 5 0 R >>" else ""
  let ref := match mdp with
    | none => ""
    | some p =>
      let pe := match p with | some p => s!"/P {p} " | none => ""
      s!" /Reference [<< /Type /SigRef /TransformMethod /DocMDP /TransformParams \
        << /Type /TransformParams {pe}/V /1.2 >> >>]"
  mkPdf [
    s!"<< /Type /Catalog /Pages 2 0 R /AcroForm << {sf}/Fields [4 0 R] >>{perms} >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Annots [4 0 R] >>",
    "<< /Type /Annot /Subtype /Widget /FT /Sig /T (Signature1) /Rect [0 0 0 0] /F 132 \
      /P 3 0 R /V 5 0 R >>",
    s!"<< /Type /Sig /Filter /Adobe.PPKLite /SubFilter /adbe.pkcs7.detached \
      /ByteRange [0 100 200 100] /Contents <00112233> /M (D:20261123000000Z){ref} >>"]

/-- An unsigned one-page document. -/
def plainPdf : ByteArray :=
  mkPdf ["<< /Type /Catalog /Pages 2 0 R >>", "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] >>"]

/-- One signed-input case: expected signature state and whether Save writes. -/
def runSig (name : String) (bytes : ByteArray) (want : Save.SigState) : IO Nat := do
  let ctx := s!"sig {name}"
  let .ok doc := openStrict bytes | return ← check ctx "open" false
  let lim : Limits := {}
  let mut f := 0
  let pol := Save.protection doc lim
  f := f + (← check ctx "signature state" (pol.sig == want) (reprStr pol.sig))
  let store := withNote {} "note on a signed file"
  match Save.refusal pol, Save.build lim doc store date (← Save.freshSeed) with
  | some why, .error e =>
    f := f + (← check ctx "refused with the policy's message" (e == why) e)
  | some _, .ok _ => f := f + (← check ctx "refused" false)
  | none, .error e => f := f + (← check ctx "written" false e)
  | none, .ok (out, got, n) =>
    f := f + (← check ctx "original is a prefix" (Save.isPrefix bytes out))
    f := f + (← check ctx "note read back" (got.length == 1 && n == 1))
    let wantNotes := if want == .unsigned then [] else [Save.signedNote]
    f := f + (← check ctx "notes" (Save.notesFor lim doc n == wantNotes))
    -- The signature dictionary (object 5) is untouched by the update.
    match Api.openBytes out { allowRepair := false } with
    | .error e => f := f + (← check ctx "reopen" false e.message)
    | .ok d' =>
      if want != .unsigned then
        f := f + (← check ctx "signature dictionary unchanged"
          (match d'.doc.file.getObject lim 5 0, doc.file.getObject lim 5 0 with
            | .ok a, .ok b => a == b
            | _, _ => false))
  return f

/-- **The suite.** -/
def run : IO Nat := do
  let mut f := 0
  let a ← Save.freshSeed
  let b ← Save.freshSeed
  f := f + (← check "seed" "fresh seeds are 64 bytes and differ"
    (a.size == 64 && b.size == 64 && a.data != b.data) s!"{a.size} {b.size}")
  for (n, aes) in [("aes-128.pdf", true), ("aes-256.pdf", true), ("aes-256-objstm.pdf", true),
      ("rc4-40.pdf", false), ("rc4-128.pdf", false)] do
    f := f + (← runEnc n aes)
  f := f + (← runSig "signed (SigFlags)" (sigPdf true none) .signed)
  f := f + (← runSig "signed (field /V only)" (sigPdf false none) .signed)
  f := f + (← runSig "certified P3" (sigPdf true (some (some 3))) (.certified 3))
  f := f + (← runSig "certified P1" (sigPdf true (some (some 1))) (.certified 1))
  f := f + (← runSig "certified P2" (sigPdf true (some (some 2))) (.certified 2))
  f := f + (← runSig "certified default P" (sigPdf true (some none)) (.certified 2))
  f := f + (← runSig "unsigned" plainPdf .unsigned)
  IO.println s!"write-confidentiality: {f} failure(s)"
  return f

end SafePdf.Tests.WriteConfidentiality
