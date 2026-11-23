import SafePdf

/-!
# Encrypted documents (task 4.3b; Plan.md §6 Phase 4, ISO 32000-2 §7.6)

The files under `Tests/adversarial/encrypted/` are written by `generate.py` there (stdlib
only; its RC4 and AES are independent of `Core.Crypt`). For each file with an empty user
password:

* `Core.Doc.openDoc` opens it (strict, not repaired) with one page and a decryption state;
* object 5's `/Title` decrypts to the expected text string (string decryption);
* object 4, the Flate content stream, decrypts and decodes to the expected content;
* object 6, inside object stream 7, has the expected `/Kind` string, through `getObject`
  and through a budgeted `Session` (object-stream data decrypted, members not decrypted
  again);
* object 8, the xref stream, is returned raw (7 bytes per `/Size` entry, not decrypted);
* object 9, the encryption dictionary (when indirect), is returned raw: its `/O` is the
  handler's `/O`;
* `/V 4`, `/V 5`: object 10, a `[/Crypt /FlateDecode]` stream with the `/Identity` crypt
  filter, decodes to its text (not decrypted with `/StmF`);
* `aesv2.pdf` (`/EncryptMetadata false`): object 11, a `/Type /Metadata` stream, is returned
  as stored;
* `/V 5`: the `/Perms` check passes.

The files with user password `secret` must fail to open (strict error, no repair) with
`Error.encryption` "non-empty user password …".

Task 4.6:

* `repair-aesv2.pdf` (broken `startxref`, no `trailer` keyword): opens **repaired** and
  decrypted — `/Encrypt` and `/ID` are recovered from the xref stream dictionary (object 6,
  in an object stream, is not reachable through the scanned section and is not checked);
* `repair-lost-encrypt.pdf` (`/Encrypt 99 0 R`, missing, broken `startxref`): `openFile`
  fails with `Error.encryption`, never opens undecrypted;
* `objstm-length-aesv2.pdf`: the `/Length` of content stream 4 is an integer inside the
  encrypted object stream 7 (decrypted before decoding, rule L6); object 13 has the named
  crypt filter `/AltCF` (RC4, unlike `/StmF`) and decodes through `Filter`;
* `sig-aesv2.pdf`: the catalog's usage-rights signature `/Perms /UR3` (no `/Type`, has
  `/ByteRange`, as on USCIS form G-1145) keeps its clear-text `/Contents` (37 bytes, not a
  valid AES ciphertext: decrypting it used to fail the strict open), while its `/M` string is
  decrypted; the file opens strictly.
-/

namespace SafePdf.Tests.Crypt

open SafePdf
open SafePdf.Core

/-- The test files' directory. -/
def dir : System.FilePath := "Tests" / "adversarial" / "encrypted"

/-- Expected plaintexts (as in `generate.py`). -/
def title : List UInt8 := "Encrypted title ".toUTF8.toList ++ [0xE9]
/-- The `/Kind` string of object 6. -/
def kind : List UInt8 := "inside an object stream".toUTF8.toList
/-- The content stream. -/
def content : List UInt8 := "BT /F1 24 Tf 72 700 Td (Hello, encrypted world) Tj ET".toUTF8.toList
/-- The `/Identity` crypt-filter stream. -/
def identityData : List UInt8 := "identity crypt filter: stored in the clear".toUTF8.toList
/-- The `/AltCF` crypt-filter stream (object 13). -/
def namedData : List UInt8 := "named crypt filter /AltCF: RC4 although /StmF is AESV2".toUTF8.toList
/-- The metadata stream. -/
def metadata : List UInt8 :=
  ("<?xpacket begin='' id='W5M0MpCehiHzreSzNTczkc9d'?>" ++
    "<x:xmpmeta xmlns:x='adobe:ns:meta/'/>").toUTF8.toList

/-- One test file: name, whether `/Encrypt` is indirect (object 9), whether it has the
`/V ≥ 4` identity stream, the metadata stream, `/Perms`, whether it opens repaired (task
4.6: object 6 is then not checked), and whether it has the `/AltCF` stream 13. -/
structure Case where
  name : String
  encIndirect : Bool
  identity : Bool
  metadata : Bool
  perms : Bool
  repaired : Bool := false
  named : Bool := false

/-- The files with an empty user password. -/
def cases : List Case :=
  [ ⟨"rc4-40.pdf", false, false, false, false, false, false⟩,
    ⟨"rc4-128.pdf", true, false, false, false, false, false⟩,
    ⟨"rc4-v4.pdf", true, true, false, false, false, false⟩,
    ⟨"aesv2.pdf", true, true, true, false, false, false⟩,
    ⟨"aesv3-r5.pdf", true, true, false, true, false, false⟩,
    ⟨"aesv3.pdf", true, true, false, true, false, false⟩,
    ⟨"repair-aesv2.pdf", true, true, true, false, true, false⟩,
    ⟨"objstm-length-aesv2.pdf", true, true, false, false, false, true⟩,
    ⟨"sig-aesv2.pdf", true, true, false, false, false, false⟩ ]

/-- The clear-text `/Contents` of `sig-aesv2.pdf` (`generate.py`: SHA-256 counter mode over
`sig/contents`, 37 bytes). -/
def sigContents : List UInt8 :=
  ((Crypt.Sha2.sha256 "sig/contents/0".toUTF8) ++
    (Crypt.Sha2.sha256 "sig/contents/1".toUTF8)).toList.take 37

/-- The `/UR3` signature dictionary of the catalog (object 1) of `sig-aesv2.pdf`. -/
def ur3Of (b : Except Error IndirectBody) : Except Error IndirectBody :=
  match b with
  | .ok (.obj (.dict d)) =>
    match Dict.get? d (Name.ofString "Perms") with
    | some (.dict p) =>
      match Dict.get? p (Name.ofString "UR3") with
      | some (.dict u) => .ok (.obj (.dict u))
      | _ => .error (.malformed 0 "no /UR3")
    | _ => .error (.malformed 0 "no /Perms")
  | .ok _ => .error (.malformed 0 "catalog not a dictionary")
  | .error e => .error e


/-- Error summary. -/
def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limit {reprStr k}"
  | .unsupported w => s!"unsupported: {w}"
  | .cycle o w => s!"cycle@{o}: {w}"
  | .encryption w => s!"encryption: {w}"

/-- A string entry of a dictionary body. -/
def strOf (b : Except Error IndirectBody) (k : String) : Except String (List UInt8) :=
  match b with
  | .ok (.obj (.dict d)) =>
    match Dict.get? d (Name.ofString k) with
    | some (.string s) => .ok s
    | _ => .error s!"no string /{k}"
  | .ok _ => .error "not a dictionary"
  | .error e => .error (errS e)

/-- The decoded data of a stream body. -/
def decoded (b : Except Error IndirectBody) : Except String (List UInt8) :=
  match b with
  | .ok (.stream s) =>
    match Filter.decodeStream Limits.default s.dict s.data with
    | .ok (.data out) => .ok out.toList
    | .ok _ => .error "image"
    | .error e => .error (errS e)
  | .ok _ => .error "not a stream"
  | .error e => .error (errS e)

/-- The raw data of a stream body. -/
def rawData (b : Except Error IndirectBody) : Except String (List UInt8) :=
  match b with
  | .ok (.stream s) => .ok s.data.toList
  | .ok _ => .error "not a stream"
  | .error e => .error (errS e)

/-- Report one check; returns the failure count. -/
def check (ctx what : String) (ok : Bool) (detail : String := "") : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL {ctx}: {what} {detail}"
  return 1

/-- Compare an `Except String` result with the expected bytes. -/
def checkEq (ctx what : String) (r : Except String (List UInt8)) (exp : List UInt8) : IO Nat :=
  match r with
  | .ok v => check ctx what (v == exp) s!"(got {v.length} bytes)"
  | .error e => check ctx what false e

/-- Run the checks of one file. -/
def runCase (c : Case) : IO Nat := do
  let lim := Limits.default
  let bytes ← IO.FS.readBinFile (dir / c.name)
  let mut f := 0
  match Doc.openDoc lim bytes with
  | .error e => f := f + (← check c.name "openDoc" false (errS e))
  | .ok doc =>
    f := f + (← check c.name "one page" (doc.pageCount == 1) s!"{doc.pageCount}")
    f := f + (← check c.name (if c.repaired then "repaired" else "strict")
      (doc.file.repaired == c.repaired))
    let d := doc.file
    match d.crypt with
    | none => f := f + (← check c.name "decryption state" false)
    | some st =>
      if c.perms then
        f := f + (← check c.name "/Perms" (st.permsOk == some true))
      if c.encIndirect then
        f := f + (← checkEq c.name "/Encrypt not decrypted" (strOf (d.getObject lim 9 0) "O")
          st.handler.o.toList)
    f := f + (← checkEq c.name "/Title" (strOf (d.getObject lim 5 0) "Title") title)
    f := f + (← checkEq c.name "content stream" (decoded (d.getObject lim 4 0)) content)
    if !c.repaired then
      f := f + (← checkEq c.name "object-stream member" (strOf (d.getObject lim 6 0) "Kind") kind)
      let sess := Open.Session.ofDoc lim d
      let (r6, sess) := sess.getObject lim 6 0
      f := f + (← checkEq c.name "object-stream member (session)" (strOf r6 "Kind") kind)
      let (r6', _) := sess.getObject lim 6 0
      f := f + (← checkEq c.name "object-stream member (session, cached)" (strOf r6' "Kind") kind)
    if c.named then
      f := f + (← checkEq c.name "/AltCF crypt filter" (decoded (d.getObject lim 13 0)) namedData)
    f := f + (← check c.name "xref stream raw"
      (match rawData (d.getObject lim 8 0) with
        | .ok v => v.length == 7 * d.trailer.size | .error _ => false))
    if c.identity then
      f := f + (← checkEq c.name "/Identity crypt filter" (decoded (d.getObject lim 10 0))
        identityData)
    if c.metadata then
      f := f + (← checkEq c.name "unencrypted metadata" (rawData (d.getObject lim 11 0)) metadata)
  IO.println s!"  {c.name}: {if f == 0 then "ok" else s!"{f} failure(s)"}"
  return f

/-- A file with a non-empty user password must fail cleanly. -/
def runWrongPassword (name : String) : IO Nat := do
  let bytes ← IO.FS.readBinFile (dir / name)
  let r := match Open.openFile Limits.default bytes with
    | .error (.encryption w) => if w.startsWith "non-empty user password" then none else some w
    | .error e => some (errS e)
    | .ok _ => some "opened"
  match r with
  | none => IO.println s!"  {name}: rejected (non-empty user password)"; return 0
  | some w => check name "must fail with non-empty user password" false w

/-- `sig-aesv2.pdf`: the signature `/Contents` is not decrypted, `/M` is (rule C7''). -/
def runSig (name : String) : IO Nat := do
  let lim := Limits.default
  let bytes ← IO.FS.readBinFile (dir / name)
  match Open.openFile lim bytes with
  | .error e => check name "openFile" false (errS e)
  | .ok d =>
    let mut f := 0
    f := f + (← check name "strict" (!d.repaired))
    let u := ur3Of (d.getObject lim 1 0)
    f := f + (← checkEq name "signature /Contents kept" (strOf u "Contents") sigContents)
    f := f + (← checkEq name "signature /M decrypted" (strOf u "M")
      "D:20261119120000Z".toUTF8.toList)
    IO.println s!"  {name} signature: {if f == 0 then "ok" else s!"{f} failure(s)"}"
    return f

/-- A repaired file whose `/Encrypt` cannot be resolved must fail with `Error.encryption`
(task 4.6), on the plain and the budgeted path. -/
def runLostEncrypt (name : String) : IO Nat := do
  let bytes ← IO.FS.readBinFile (dir / name)
  let lim := Limits.default
  let r := match Open.openFile lim bytes with
    | .error (.encryption _) => none
    | .error e => some (errS e)
    | .ok _ => some "opened"
  let rb := match (Open.openFileB lim (Filter.Budget.init lim) bytes).1 with
    | .error (.encryption _) => none
    | .error e => some (errS e)
    | .ok _ => some "opened"
  match r, rb with
  | none, none => IO.println s!"  {name}: rejected (Error.encryption)"; return 0
  | some w, _ => check name "must fail with Error.encryption" false w
  | _, some w => check name "must fail with Error.encryption (budgeted)" false w

/-- **Entry point.** The number of failures. -/
def run : IO Nat := do
  let mut f := 0
  for c in cases do
    f := f + (← runCase c)
  f := f + (← runWrongPassword "userpw-rc4-128.pdf")
  f := f + (← runWrongPassword "userpw-aesv3.pdf")
  f := f + (← runLostEncrypt "repair-lost-encrypt.pdf")
  f := f + (← runSig "sig-aesv2.pdf")
  return f

end SafePdf.Tests.Crypt
