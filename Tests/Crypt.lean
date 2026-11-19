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
* object 8, the xref stream, is returned raw (84 bytes, not decrypted);
* object 9, the encryption dictionary (when indirect), is returned raw: its `/O` is the
  handler's `/O`;
* `/V 4`, `/V 5`: object 10, a `[/Crypt /FlateDecode]` stream with the `/Identity` crypt
  filter, decodes to its text (not decrypted with `/StmF`);
* `aesv2.pdf` (`/EncryptMetadata false`): object 11, a `/Type /Metadata` stream, is returned
  as stored;
* `/V 5`: the `/Perms` check passes.

The files with user password `secret` must fail to open (strict error, no repair) with `Error.unsupported`
"non-empty user password …".
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
/-- The metadata stream. -/
def metadata : List UInt8 :=
  ("<?xpacket begin='' id='W5M0MpCehiHzreSzNTczkc9d'?>" ++
    "<x:xmpmeta xmlns:x='adobe:ns:meta/'/>").toUTF8.toList

/-- One test file: name, whether `/Encrypt` is indirect (object 9), whether it has the
`/V ≥ 4` identity stream, the metadata stream, and `/Perms`. -/
structure Case where
  name : String
  encIndirect : Bool
  identity : Bool
  metadata : Bool
  perms : Bool

/-- The files with an empty user password. -/
def cases : List Case :=
  [ ⟨"rc4-40.pdf", false, false, false, false⟩,
    ⟨"rc4-128.pdf", true, false, false, false⟩,
    ⟨"rc4-v4.pdf", true, true, false, false⟩,
    ⟨"aesv2.pdf", true, true, true, false⟩,
    ⟨"aesv3-r5.pdf", true, true, false, true⟩,
    ⟨"aesv3.pdf", true, true, false, true⟩ ]

/-- Error summary. -/
def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limit {reprStr k}"
  | .unsupported w => s!"unsupported: {w}"
  | .cycle o w => s!"cycle@{o}: {w}"

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
    f := f + (← check c.name "strict" (!doc.file.repaired))
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
    f := f + (← checkEq c.name "object-stream member" (strOf (d.getObject lim 6 0) "Kind") kind)
    let sess := Open.Session.ofDoc lim d
    let (r6, sess) := sess.getObject lim 6 0
    f := f + (← checkEq c.name "object-stream member (session)" (strOf r6 "Kind") kind)
    let (r6', _) := sess.getObject lim 6 0
    f := f + (← checkEq c.name "object-stream member (session, cached)" (strOf r6' "Kind") kind)
    f := f + (← check c.name "xref stream raw"
      (match rawData (d.getObject lim 8 0) with | .ok v => v.length == 84 | .error _ => false))
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
    | .error (.unsupported w) => if w.startsWith "encryption: non-empty user password" then none else some w
    | .error e => some (errS e)
    | .ok _ => some "opened"
  match r with
  | none => IO.println s!"  {name}: rejected (non-empty user password)"; return 0
  | some w => check name "must fail with non-empty user password" false w

/-- **Entry point.** The number of failures. -/
def run : IO Nat := do
  let mut f := 0
  for c in cases do
    f := f + (← runCase c)
  f := f + (← runWrongPassword "userpw-rc4-128.pdf")
  f := f + (← runWrongPassword "userpw-aesv3.pdf")
  return f

end SafePdf.Tests.Crypt
