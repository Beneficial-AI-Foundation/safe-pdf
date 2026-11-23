import SafePdf.Core.Object
import SafePdf.Core.Crypt.Md5
import SafePdf.Core.Crypt.Sha2
import SafePdf.Core.Crypt.Rc4
import SafePdf.Core.Crypt.Aes

/-!
# The standard security handler (Plan.md §6 Phase 4, §3 S8; task 4.3b)

ISO 32000-2 §7.6: parse the encryption dictionary (`/Encrypt`) of the standard security
handler, derive the file key for the **empty user password**, and decrypt strings and stream
data of individual objects. The wiring into object resolution (`OpenDoc.getObject`, object
streams) is in `Core.Open`.

## Supported (rules C1–C8)

* C1. `/Filter /Standard` only (other security handlers, e.g. public-key `/Adobe.PubSec`,
  are `Error.unsupported`). `/SubFilter` is ignored.
* C2. `/V 1` (RC4, 40-bit, `/R 2`), `/V 2` (RC4, 40–128-bit `/Length`, `/R 3`), `/V 4`
  (crypt filters, `/R 4`), `/V 5` (AES-256, `/R 6`, and the deprecated Adobe `/R 5`). `/V 0`
  and `/V 3` are `unsupported`; `/R` outside 2–6 is `unsupported`.
* C3. Crypt filters (§7.6.5, `/V 4` and `/V 5`): `/CF` maps names to `/CFM` methods —
  `/None` (identity), `/V2` (RC4), `/AESV2` (AES-128-CBC), `/AESV3` (AES-256-CBC); `/StmF`
  and `/StrF` (default `/Identity`) pick the stream and string methods; the name `/Identity`
  is always the identity. `/V 1`, `/V 2`: both methods are RC4. `/EFF` is ignored (embedded
  file streams are decrypted with `/StmF`).
* C4. **File key, empty user password only** (§7.6.4.3): Algorithm 2 for `/R 2`–`/R 4`
  (the `/EncryptMetadata false` tweak for `/R 4`), checked against `/U` by Algorithm 4
  (`/R 2`) or 5 (`/R 3`, `/R 4`, first 16 bytes); Algorithm 2.A for `/R 5`, `/R 6`: the
  validation salt of `/U` checks the password, the key salt gives the intermediate key that
  decrypts `/UE` (AES-256-CBC, zero IV, no padding). The hash is Algorithm 2.B for `/R 6` and
  plain SHA-256 for `/R 5`. If the empty password does not match `/U`, the result is
  `Error.unsupported "non-empty user password …"`: the file may well be valid, but asking for
  and handling passwords (and owner-password authentication) is not supported.
* C5. **Per-object key** (Algorithm 1): `/V < 5`: MD5 of the file key, the low 3 bytes of the
  object number and the low 2 bytes of the generation (little-endian), plus `sAlT` for
  `/AESV2`; the first `min(n + 5, 16)` bytes. `/AESV3` uses the file key itself.
* C6. **Decryption** (§7.6.3): RC4 over the whole data; AES: the first 16 bytes are the IV,
  the rest is CBC with PKCS#7 padding (strict). An empty AES string or stream decrypts to
  empty (some writers leave empty strings unencrypted).
* C7. **What is decrypted** (§7.6.2): every string of an object (recursively in arrays and
  dictionaries, also in stream dictionaries) and stream data — **except** the encryption
  dictionary itself (`State.encRef`), cross-reference streams (`/Type /XRef`: nothing), the
  data of `/Type /Metadata` streams when `/EncryptMetadata false`, and stream data whose
  first filter is `/Crypt` naming `/Identity` (the stream's own crypt filter overrides
  `/StmF`; a named non-identity `/Crypt` filter decrypts with that filter's method). Strings
  in the `/Contents` of signature dictionaries are also unencrypted per §7.6.2 (rule C7'').
* C7''. (Task 4.6.) **Signature dictionaries** (`isSigDict`: `/Type /Sig` or
  `/DocTimeStamp`, or any dictionary with `/ByteRange`, e.g. a usage-rights `/Perms /UR3`
  signature): the value of `/Contents` is kept as is (§7.6.2: it is not encrypted; decrypting
  it fails AES padding, as on USCIS form G-1145). Its other strings are decrypted. A string
  that fails to decrypt anywhere else is still an error of the whole object (and, for the
  root, of the open): the encrypted file then fails visibly rather than showing undecrypted
  or partially decrypted content (decision of task 4.6).
* C7'. (Task 4.6.) A stream decrypted with its **own** named crypt filter (`ownCrypt`: first
  filter `/Crypt`, `/Name` not `/Identity`) is returned with that stage's `/DecodeParms`
  `/Name` set to `/Identity` (`markApplied`): the data no longer needs that filter, and
  `Core.Filter` (rule F4) then passes it through, while still rejecting a named crypt filter
  that was not applied. The dictionary's depth is unchanged (`markApplied_depth`). Only a
  direct `/Filter` and `/DecodeParms` are read for this (as for `streamMethod`). Objects inside an object stream are not
  decrypted again: the object stream's data is (`Core.Open`).
* C9. Errors of `setup` (unsupported handler or revision, wrong password, malformed
  dictionary) are `Error.encryption` (`setupError`, task 4.6: by constructor, never by
  message text), so that `Core.Open` treats them as final (`Error.isFinal`) instead of
  trying repair. Errors of decrypting one object (`decryptBytes`, `methodFor` of a stream's
  own crypt filter) stay `malformed`: they concern that object, not the document.
* C8. **Permissions are advisory** (S8): `/P` is parsed and kept; nothing is enforced.
  `/Perms` (`/R 5`, `/R 6`) is checked (`State.permsOk`) but a mismatch is not an error.

## Theorems

* `decryptObj_depth`, `decryptDict_depth`, `decryptBody_shape`: decryption preserves the
  nesting depth exactly (only string bytes change).
* `decryptBytes_size_le`, `decryptBytes_rc4_size`, `decryptBytes_aes_size`: RC4 preserves
  length; AES output is at most input − 16. (The primitives carry no size theorems; these
  laws are guaranteed by a check in `decryptBytes` that turns a violation into an error.)
* `decryptData_size_le`, `decryptContainer_size_le`: stream data never grows.
-/

namespace SafePdf.Core.Crypt

open SafePdf

/-! ## Byte helpers -/

/-- The bytes of a byte list. -/
def bytesOf (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- The low 32 bits of `p` (two's complement), little-endian. -/
def le32 (p : Int) : ByteArray :=
  let u := (p % 4294967296).toNat
  bytesOf [u.toUInt8, (u / 256).toUInt8, (u / 65536).toUInt8, (u / 16777216).toUInt8]

/-- Byte-array equality. -/
def beqBytes (a b : ByteArray) : Bool := a.data == b.data

/-- Every byte XORed with `i`. -/
def xorAll (k : ByteArray) (i : UInt8) : ByteArray := ⟨k.data.map (· ^^^ i)⟩

/-- The text of a name (bytes as Latin-1), for messages. -/
def nameText (n : Name) : String := String.ofList (n.bytes.map (fun b => Char.ofNat b.toNat))

/-- The 32-byte password padding string (ISO 32000-2 §7.6.4.3.2, Algorithm 2 step a). -/
def padding : ByteArray := ⟨#[0x28, 0xBF, 0x4E, 0x5E, 0x4E, 0x75, 0x8A, 0x41, 0x64, 0x00, 0x4E,
  0x56, 0xFF, 0xFA, 0x01, 0x08, 0x2E, 0x2E, 0x00, 0xB6, 0xD0, 0x68, 0x3E, 0x80, 0x2F, 0x0C, 0xA9,
  0xFE, 0x64, 0x53, 0x69, 0x7A]⟩

/-! ## The handler -/

/-- A crypt method (ISO 32000-2 §7.6.5, `/CFM`). -/
inductive Method where
  /-- No encryption (`/None`, `/Identity`). -/
  | identity
  /-- RC4 (`/V2`, and `/V 1`, `/V 2` handlers). -/
  | rc4
  /-- AES-128-CBC (`/AESV2`). -/
  | aesv2
  /-- AES-256-CBC (`/AESV3`). -/
  | aesv3
  deriving DecidableEq, Repr, Inhabited

/-- A parsed standard-security-handler encryption dictionary (rules C1–C3, C8). -/
structure Handler where
  /-- `/V`: the algorithm (1, 2, 4 or 5). -/
  v : Nat
  /-- `/R`: the revision (2–6). -/
  r : Nat
  /-- File key length in bytes (5–16 for `/V < 5`, 32 for `/V 5`). -/
  keyLen : Nat
  /-- `/P`: the permission flags (advisory, S8). -/
  p : Int
  /-- `/O` (32 bytes for `/R ≤ 4`, 48 for `/R 5`, `/R 6`). -/
  o : ByteArray
  /-- `/U` (32 or 48 bytes, like `/O`). -/
  u : ByteArray
  /-- `/OE` (`/R 5`, `/R 6`; else empty). -/
  oe : ByteArray
  /-- `/UE` (`/R 5`, `/R 6`; else empty). -/
  ue : ByteArray
  /-- `/Perms` (`/R 5`, `/R 6`, if present; else empty). -/
  perms : ByteArray
  /-- `/EncryptMetadata` (default `true`). -/
  encryptMetadata : Bool
  /-- The stream method (`/StmF`). -/
  stmF : Method
  /-- The string method (`/StrF`). -/
  strF : Method
  /-- The named crypt filters of `/CF`. -/
  filters : List (Name × Method)

/-- `/Encrypt` error helper. -/
def bad (msg : String) : Error := .malformed 0 ("/Encrypt: " ++ msg)

/-- Integer entry. -/
def getInt (d : Dict) (k : String) : Option Int :=
  match Dict.get? d (Name.ofString k) with
  | some (.int i) => some i
  | _ => none

/-- Name entry. -/
def getName (d : Dict) (k : String) : Option Name :=
  match Dict.get? d (Name.ofString k) with
  | some (.name n) => some n
  | _ => none

/-- String entry. -/
def getStr (d : Dict) (k : String) : Option ByteArray :=
  match Dict.get? d (Name.ofString k) with
  | some (.string s) => some (bytesOf s)
  | _ => none

/-- Boolean entry. -/
def getBool (d : Dict) (k : String) : Option Bool :=
  match Dict.get? d (Name.ofString k) with
  | some (.bool b) => some b
  | _ => none

/-- Dictionary entry. -/
def getDict (d : Dict) (k : String) : Option Dict :=
  match Dict.get? d (Name.ofString k) with
  | some (.dict e) => some e
  | _ => none

/-- The method of a `/CFM` name (rule C3); absent is `/None`. -/
def methodOfCfm : Option Name → Except Error Method
  | none => .ok .identity
  | some n =>
    if n = Name.ofString "None" then .ok .identity
    else if n = Name.ofString "V2" then .ok .rc4
    else if n = Name.ofString "AESV2" then .ok .aesv2
    else if n = Name.ofString "AESV3" then .ok .aesv3
    else .error (.unsupported s!"crypt filter method /{nameText n}")

/-- The named crypt filters of a `/CF` dictionary (rule C3). -/
def parseFilters (cf : Dict) : Except Error (List (Name × Method)) :=
  cf.mapM fun (k, v) =>
    match v with
    | .dict fd => (methodOfCfm (getName fd "CFM")).map (fun m => (k, m))
    | _ => .error (bad s!"/CF /{nameText k} is not a dictionary")

/-- The method named `n`: `/Identity`, or a filter of `/CF` (rule C3). -/
def methodFor (filters : List (Name × Method)) (n : Name) : Except Error Method :=
  if n = Name.ofString "Identity" then .ok .identity
  else
    match filters.lookup n with
    | some m => .ok m
    | none => .error (bad s!"crypt filter /{nameText n} is not in /CF")

/-- A required string entry of at least `n` bytes, truncated to `n`. -/
def strField (d : Dict) (k : String) (n : Nat) : Except Error ByteArray :=
  match getStr d k with
  | some s => if n ≤ s.size then .ok (s.extract 0 n) else .error (bad s!"/{k} is shorter than {n} bytes")
  | none => .error (bad s!"/{k} is missing or not a string")

/-- The key length in bytes of a `/V 4` handler: the `/Length` of the crypt filter used by
`/StmF` or `/StrF` (bytes if at most 16, else bits), else `/Length` (bits), else 16; 16 when
an AES-128 filter is in use. -/
def v4KeyLen (d : Dict) (cf : Dict) (stm str : Name) (aes : Bool) : Nat :=
  if aes then 16
  else
    let fl : Option Int :=
      match (getDict cf (nameText stm)).bind (getInt · "Length") with
      | some l => some l
      | none => (getDict cf (nameText str)).bind (getInt · "Length")
    match fl with
    | some l => if l ≤ 16 then l.toNat else l.toNat / 8
    | none => match getInt d "Length" with
      | some l => l.toNat / 8
      | none => 16

/-- **Entry point.** Parse an encryption dictionary (rules C1–C3, C8). -/
def parseEncrypt (d : Dict) : Except Error Handler := do
  match getName d "Filter" with
  | some n =>
    unless n = Name.ofString "Standard" do
      throw (.unsupported s!"security handler /{nameText n} (only /Standard is supported)")
  | none => throw (bad "/Filter is missing")
  let v ← match getInt d "V" with
    | some v => pure v.toNat
    | none => pure 0
  unless v = 1 ∨ v = 2 ∨ v = 4 ∨ v = 5 do
    throw (.unsupported s!"/V {v} is not supported")
  let r ← match getInt d "R" with
    | some r => pure r.toNat
    | none => throw (bad "/R is missing")
  unless (v < 5 ∧ 2 ≤ r ∧ r ≤ 4) ∨ (v = 5 ∧ (r = 5 ∨ r = 6)) do
    throw (.unsupported s!"/V {v} /R {r} is not supported")
  let p ← match getInt d "P" with
    | some p => pure p
    | none => throw (bad "/P is missing")
  let encryptMetadata := (getBool d "EncryptMetadata").getD true
  let ouLen := if v = 5 then 48 else 32
  let o ← strField d "O" ouLen
  let u ← strField d "U" ouLen
  let (oe, ue, perms) ← if v = 5 then do
      let oe ← strField d "OE" 32
      let ue ← strField d "UE" 32
      let perms := match getStr d "Perms" with
        | some s => if 16 ≤ s.size then s.extract 0 16 else ByteArray.empty
        | none => ByteArray.empty
      pure (oe, ue, perms)
    else pure (ByteArray.empty, ByteArray.empty, ByteArray.empty)
  if v < 4 then
    let keyLen ← if v = 1 then pure 5 else do
      let bits := ((getInt d "Length").getD 40).toNat
      unless bits % 8 = 0 ∧ 40 ≤ bits ∧ bits ≤ 128 do
        throw (bad s!"/Length {bits} is not a multiple of 8 in 40–128")
      pure (bits / 8)
    return { v, r, keyLen, p, o, u, oe, ue, perms, encryptMetadata,
             stmF := .rc4, strF := .rc4, filters := [] }
  else
    let cf := (getDict d "CF").getD []
    let filters ← parseFilters cf
    let stmN := (getName d "StmF").getD (Name.ofString "Identity")
    let strN := (getName d "StrF").getD (Name.ofString "Identity")
    let stmF ← methodFor filters stmN
    let strF ← methodFor filters strN
    let keyLen ← if v = 5 then pure 32 else do
      let n := v4KeyLen d cf stmN strN (stmF = .aesv2 ∨ strF = .aesv2)
      unless 5 ≤ n ∧ n ≤ 16 do throw (bad s!"key length {n} bytes is not in 5–16")
      pure n
    return { v, r, keyLen, p, o, u, oe, ue, perms, encryptMetadata, stmF, strF, filters }

/-! ## File key for the empty user password (rule C4) -/

/-- The error for a file whose user password is not empty (rule C4). -/
def wrongPassword : Error :=
  .encryption "non-empty user password (only the empty user password is supported)"

/-- An error of the encryption setup as `Error.encryption` (rule C9, task 4.6): `malformed`
(with its byte offset when non-zero) and `unsupported` become `encryption`; `encryption`,
`cycle` and `limitExceeded` are kept (a cycle is final anyway; a limit is not a property of
the encryption). By constructor only. -/
def setupError : Error → Error
  | .malformed o m => .encryption (if o = 0 then m else s!"{m} (byte {o})")
  | .unsupported w => .encryption w
  | e => e

/-- **Setup errors are final** (rule C9): a converted setup error is final
(`Error.isFinal`: `encryption` or `cycle`) unless it is a resource limit. -/
theorem setupError_final {e : Error} (hl : ∀ k, e ≠ .limitExceeded k) :
    (setupError e).isFinal = true := by
  cases e with
  | malformed o m => rfl
  | unsupported w => rfl
  | encryption w => rfl
  | cycle o w => rfl
  | limitExceeded k => exact absurd rfl (hl k)

/-- **Algorithm 2** (`/R 2`–`/R 4`) with the empty user password and the first `/ID` string. -/
def algorithm2 (h : Handler) (id0 : ByteArray) : ByteArray :=
  let n := h.keyLen
  let m := padding ++ h.o ++ le32 h.p ++ id0 ++
    (if 4 ≤ h.r ∧ !h.encryptMetadata then ⟨#[0xFF, 0xFF, 0xFF, 0xFF]⟩ else ByteArray.empty)
  let h0 := Md5.md5 m
  let k := if 3 ≤ h.r then Nat.repeat (fun x => Md5.md5 (x.extract 0 n)) 50 h0 else h0
  k.extract 0 n

/-- **Algorithms 4 and 5**: the `/U` check of the key (the first 32 bytes for `/R 2`, the
first 16 for `/R 3`, `/R 4`). -/
def userKeyOk (h : Handler) (id0 key : ByteArray) : Bool :=
  if h.r = 2 then beqBytes (Rc4.rc4 key padding) h.u
  else
    let x0 := Rc4.rc4 key (Md5.md5 (padding ++ id0))
    let x := (List.range' 1 19).foldl (fun x i => Rc4.rc4 (xorAll key i.toUInt8) x) x0
    beqBytes x (h.u.extract 0 16)

/-- 64 repetitions of `b`. -/
def repeat64 (b : ByteArray) : ByteArray :=
  (List.range 64).foldl (fun acc _ => acc ++ b) (ByteArray.emptyWithCapacity (64 * b.size))

/-- The first 16 bytes of `e` as a big-endian number, modulo 3 (= their sum modulo 3). -/
def sumMod3 (e : ByteArray) : Nat :=
  ((List.range 16).foldl (fun s i => s + (e[i]?.getD 0).toNat) 0) % 3

/-- The rounds of Algorithm 2.B (at least 64; stop after round `i` once the last byte of `E`
is at most `i - 32`, so at most 288 rounds: `fuel` 300 never runs out). -/
def hash2BLoop (pw udata : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, k => k.extract 0 32
  | fuel + 1, i, k =>
    match Aes.cbcEncryptNoPad (k.extract 0 16) (k.extract 16 32) (repeat64 (pw ++ k ++ udata)) with
    | .error _ => k.extract 0 32
    | .ok e =>
      let s := sumMod3 e
      let k' := if s = 0 then Sha2.sha256 e else if s = 1 then Sha2.sha384 e else Sha2.sha512 e
      let last := (e[e.size - 1]?.getD 0).toNat
      if 64 ≤ i + 1 ∧ last + 32 ≤ i + 1 then k'.extract 0 32
      else hash2BLoop pw udata fuel (i + 1) k'

/-- **Algorithm 2.B** (`/R 6`): the hash of password `pw`, `salt` and `udata`. -/
def hash2B (pw salt udata : ByteArray) : ByteArray :=
  hash2BLoop pw udata 300 0 (Sha2.sha256 (pw ++ salt ++ udata))

/-- The `/R 5` / `/R 6` password hash: SHA-256 (`/R 5`) or Algorithm 2.B (`/R 6`). -/
def hashR (r : Nat) (pw salt udata : ByteArray) : ByteArray :=
  if r = 5 then Sha2.sha256 (pw ++ salt ++ udata) else hash2B pw salt udata

/-- **Entry point.** The file key for the empty user password (rule C4), with `id0` the first
string of the trailer's `/ID` (empty if absent). A key that does not match `/U` is
`wrongPassword`. -/
def deriveKey (h : Handler) (id0 : ByteArray) : Except Error ByteArray :=
  if h.v = 5 then
    let pw := ByteArray.empty
    if beqBytes (hashR h.r pw (h.u.extract 32 40) ByteArray.empty) (h.u.extract 0 32) then
      Aes.cbcDecrypt (hashR h.r pw (h.u.extract 40 48) ByteArray.empty) (zeros 16) h.ue false
    else .error wrongPassword
  else
    let key := algorithm2 h id0
    if userKeyOk h id0 key then .ok key else .error wrongPassword

/-- `/Perms` check (`/R 5`, `/R 6`, Algorithm 2.A step f / Algorithm 13): bytes 9–11 of the
decrypted `/Perms` are `adb`. `none` when there is nothing to check. -/
def permsOk (h : Handler) (key : ByteArray) : Option Bool :=
  if h.v = 5 ∧ h.perms.size = 16 then
    match Aes.ecbDecrypt key h.perms with
    | .ok p => some (p[9]? == some 0x61 && p[10]? == some 0x64 && p[11]? == some 0x62)
    | .error _ => some false
  else none

/-- The first string of a trailer's `/ID` array (empty if absent). -/
def id0Of (trailer : Dict) : ByteArray :=
  match Dict.get? trailer (Name.ofString "ID") with
  | some (.array (.string s :: _)) => bytesOf s
  | _ => ByteArray.empty

/-! ## Decryption state and per-object keys -/

/-- The decryption state of an opened encrypted document. -/
structure State where
  /-- The parsed handler. -/
  handler : Handler
  /-- The file key. -/
  fileKey : ByteArray
  /-- The encryption dictionary's object, if it is indirect (never decrypted, C7). -/
  encRef : Option (Nat × Nat)
  /-- The `/Perms` check (advisory). -/
  permsOk : Option Bool

/-- **Entry point.** The decryption state for encryption dictionary `enc` (at `encRef`) and
trailer dictionary `trailer`: parse, derive the key, check `/Perms`. -/
def setup (enc trailer : Dict) (encRef : Option (Nat × Nat)) : Except Error State :=
  match parseEncrypt enc with
  | .error e => .error (setupError e)
  | .ok h =>
    match deriveKey h (id0Of trailer) with
    | .error e => .error (setupError e)
    | .ok key => .ok { handler := h, fileKey := key, encRef, permsOk := permsOk h key }

/-- **Algorithm 1**: the key for object `num gen` under `m` (rule C5). -/
def objectKey (m : Method) (fileKey : ByteArray) (num gen : Nat) : ByteArray :=
  match m with
  | .aesv3 => fileKey
  | _ =>
    let n := fileKey.size
    let salt : ByteArray := if m = .aesv2 then ⟨#[0x73, 0x41, 0x6C, 0x54]⟩ else ByteArray.empty
    let msg := fileKey ++ bytesOf [num.toUInt8, (num / 256).toUInt8, (num / 65536).toUInt8,
      gen.toUInt8, (gen / 256).toUInt8] ++ salt
    (Md5.md5 msg).extract 0 (min (n + 5) 16)

/-- **Decrypt** `data` under `m` with object key `key` (rule C6). The size laws are checked
(a violation would be a primitive bug; it is an error, never a silent result). -/
def decryptBytes (m : Method) (key data : ByteArray) : Except Error ByteArray :=
  match m with
  | .identity => .ok data
  | .rc4 =>
    let out := Rc4.rc4 key data
    if out.size = data.size then .ok out
    else .error (.malformed 0 "RC4: output size differs from input size")
  | .aesv2 | .aesv3 =>
    if data.size = 0 then .ok ByteArray.empty
    else if data.size < 16 then .error (.malformed 0 "AES: data shorter than its 16-byte IV")
    else
      match Aes.cbcDecrypt key (data.extract 0 16) (data.extract 16 data.size) true with
      | .error e => .error e
      | .ok out =>
        if out.size ≤ data.size - 16 then .ok out
        else .error (.malformed 0 "AES: output longer than the ciphertext")

/-! ## Decrypting objects (rule C7) -/

/-- Whether a dictionary is a **signature dictionary** (ISO 32000-2 §12.8.1, rule C7''): its
`/Type` is `/Sig` or `/DocTimeStamp`, or it has a `/ByteRange` (usage-rights signatures such
as `/Perms /UR3` often omit `/Type`). Its `/Contents` string is not encrypted (§7.6.2). -/
def isSigDict (d : List (Name × PdfObject)) : Bool :=
  (match Dict.get? d (Name.ofString "Type") with
    | some (.name t) => t == Name.ofString "Sig" || t == Name.ofString "DocTimeStamp"
    | _ => false) ||
  (Dict.get? d (Name.ofString "ByteRange")).isSome

/-- Whether entry key `k` of a dictionary is left as is: `/Contents` of a signature dictionary
(`sig`, rule C7''). -/
def keepEntry (sig : Bool) (k : Name) : Bool := sig && k == Name.ofString "Contents"

mutual
/-- Decrypt every string of an object with `f` (recursively). -/
def decryptObj (f : List UInt8 → Except Error (List UInt8)) : PdfObject → Except Error PdfObject
  | .null => .ok .null
  | .bool b => .ok (.bool b)
  | .int i => .ok (.int i)
  | .real r => .ok (.real r)
  | .name n => .ok (.name n)
  | .ref n g => .ok (.ref n g)
  | .string s =>
    match f s with
    | .ok s' => .ok (.string s')
    | .error e => .error e
  | .array xs =>
    match decryptList f xs with
    | .ok ys => .ok (.array ys)
    | .error e => .error e
  | .dict d =>
    match decryptDict f (isSigDict d) d with
    | .ok d' => .ok (.dict d')
    | .error e => .error e

/-- `decryptObj` over a list. -/
def decryptList (f : List UInt8 → Except Error (List UInt8)) :
    List PdfObject → Except Error (List PdfObject)
  | [] => .ok []
  | x :: xs =>
    match decryptObj f x with
    | .error e => .error e
    | .ok y =>
      match decryptList f xs with
      | .error e => .error e
      | .ok ys => .ok (y :: ys)

/-- `decryptObj` over the values of a dictionary (keys unchanged); with `sig` (a signature
dictionary) the `/Contents` value is kept as is (`keepEntry`, rule C7''). -/
def decryptDict (f : List UInt8 → Except Error (List UInt8)) (sig : Bool) :
    List (Name × PdfObject) → Except Error (List (Name × PdfObject))
  | [] => .ok []
  | (k, v) :: rest =>
    match (if keepEntry sig k then .ok v else decryptObj f v) with
    | .error e => .error e
    | .ok v' =>
      match decryptDict f sig rest with
      | .error e => .error e
      | .ok rest' => .ok ((k, v') :: rest')
end

mutual
/-- **Depth preserved**: decryption changes only string bytes. -/
theorem decryptObj_depth (f : List UInt8 → Except Error (List UInt8)) :
    (o : PdfObject) → ∀ {o' : PdfObject}, decryptObj f o = .ok o' → o'.depth = o.depth
  | .null, _, h => by unfold decryptObj at h; cases h; rfl
  | .bool _, _, h => by unfold decryptObj at h; cases h; rfl
  | .int _, _, h => by unfold decryptObj at h; cases h; rfl
  | .real _, _, h => by unfold decryptObj at h; cases h; rfl
  | .name _, _, h => by unfold decryptObj at h; cases h; rfl
  | .ref _ _, _, h => by unfold decryptObj at h; cases h; rfl
  | .string s, _, h => by
    unfold decryptObj at h
    split at h
    · cases h; rfl
    · cases h
  | .array xs, _, h => by
    unfold decryptObj at h
    split at h
    · rename_i ys hys
      cases h
      simp only [PdfObject.depth]
      rw [decryptList_depth f xs hys]
    · cases h
  | .dict d, _, h => by
    unfold decryptObj at h
    split at h
    · rename_i d' hd
      cases h
      simp only [PdfObject.depth]
      rw [decryptDict_depth f _ d hd]
    · cases h

/-- Depth preserved over a list. -/
theorem decryptList_depth (f : List UInt8 → Except Error (List UInt8)) :
    (xs : List PdfObject) → ∀ {ys : List PdfObject}, decryptList f xs = .ok ys →
      PdfObject.depthList ys = PdfObject.depthList xs
  | [], _, h => by unfold decryptList at h; cases h; rfl
  | x :: xs, _, h => by
    unfold decryptList at h
    split at h
    · cases h
    · rename_i y hy
      split at h
      · cases h
      · rename_i ys hys
        cases h
        simp only [PdfObject.depthList]
        rw [decryptObj_depth f x hy, decryptList_depth f xs hys]

/-- Depth preserved over dictionary values. -/
theorem decryptDict_depth (f : List UInt8 → Except Error (List UInt8)) (sig : Bool) :
    (d : List (Name × PdfObject)) → ∀ {d' : List (Name × PdfObject)},
      decryptDict f sig d = .ok d' → PdfObject.depthDict d' = PdfObject.depthDict d
  | [], _, h => by unfold decryptDict at h; cases h; rfl
  | (k, v) :: rest, _, h => by
    unfold decryptDict at h
    split at h
    · cases h
    · rename_i v' hv
      split at h
      · cases h
      · rename_i rest' hr
        cases h
        have hvd : v'.depth = v.depth := by
          by_cases hk : keepEntry sig k = true
          · simp only [hk, ↓reduceIte, Except.ok.injEq] at hv; rw [hv]
          · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hv; exact decryptObj_depth f v hv
        simp only [PdfObject.depthDict]
        rw [hvd, decryptDict_depth f sig rest hr]
end

/-- The string decryptor of object `num gen`: `/StrF` with the object's key. -/
def stringFn (st : State) (num gen : Nat) : List UInt8 → Except Error (List UInt8) :=
  let m := st.handler.strF
  let key := objectKey m st.fileKey num gen
  fun s => (decryptBytes m key (bytesOf s)).map ByteArray.toList

/-- Whether a dictionary has `/Type /n`. -/
def hasType (d : Dict) (n : String) : Bool :=
  match Dict.get? d (Name.ofString "Type") with
  | some (.name t) => t = Name.ofString n
  | _ => false

/-- The first filter of a stream dictionary, if any. -/
def firstFilter (d : Dict) : Option Name :=
  match Dict.get? d (Name.ofString "Filter") with
  | some (.name n) => some n
  | some (.array (.name n :: _)) => some n
  | _ => none

/-- The `/Name` of the first `/DecodeParms` entry (the `/Crypt` filter's), default
`/Identity`. -/
def cryptName (d : Dict) : Name :=
  let parms : Option Dict :=
    match Dict.get? d (Name.ofString "DecodeParms") with
    | some (.dict p) => some p
    | some (.array (.dict p :: _)) => some p
    | _ => none
  (parms.bind (getName · "Name")).getD (Name.ofString "Identity")

/-- The method for a stream's data: its own `/Crypt` filter if its first filter is `/Crypt`,
else `/StmF` (rule C7). -/
def streamMethod (h : Handler) (d : Dict) : Except Error Method :=
  match firstFilter d with
  | some n => if n = Name.ofString "Crypt" then methodFor h.filters (cryptName d) else .ok h.stmF
  | none => .ok h.stmF

/-- **Decrypt stream data** of object `num gen` (rule C7): unchanged for `/Type /Metadata`
when `/EncryptMetadata false`; else `streamMethod` with the object's key. -/
def decryptData (st : State) (num gen : Nat) (s : Stream) : Except Error ByteArray :=
  if hasType s.dict "Metadata" ∧ !st.handler.encryptMetadata then .ok s.data
  else
    match streamMethod st.handler s.dict with
    | .error e => .error e
    | .ok m => decryptBytes m (objectKey m st.fileKey num gen) s.data

/-- Whether `decryptData` applies the stream's **own** named crypt filter (rule C7'): its
first filter is `/Crypt` with a `/Name` other than `/Identity`, and the data is decrypted
(not the `/EncryptMetadata false` metadata exception). -/
def ownCrypt (h : Handler) (d : Dict) : Bool :=
  !(hasType d "Metadata" ∧ !h.encryptMetadata) &&
    firstFilter d == some (Name.ofString "Crypt") && cryptName d != Name.ofString "Identity"

/-- One parameter entry: a `/Name` whose value is a name becomes `/Name /Identity`. -/
def identityEntry (kv : Name × PdfObject) : Name × PdfObject :=
  match kv.2 with
  | .name _ => if kv.1 = Name.ofString "Name" then (kv.1, .name (Name.ofString "Identity")) else kv
  | _ => kv

/-- A crypt filter's parameter dictionary with its `/Name` (a name) set to `/Identity`. -/
def identityParms (p : Dict) : Dict := p.map identityEntry

/-- The `/DecodeParms` value with the first (the `/Crypt` stage's) parameters made
`/Identity` (`identityParms`); anything else unchanged. -/
def appliedParms : PdfObject → PdfObject
  | .dict p => .dict (identityParms p)
  | .array (.dict p :: rest) => .array (.dict (identityParms p) :: rest)
  | o => o

/-- **Mark the stream's own crypt filter as applied** (rule C7', task 4.6): its `/Crypt`
stage now names `/Identity`, so `Filter` passes the (already decrypted) data through
instead of rejecting the named crypt filter. -/
def markApplied (d : Dict) : Dict :=
  d.map fun kv => if kv.1 = Name.ofString "DecodeParms" then (kv.1, appliedParms kv.2) else kv

/-- **Entry point.** Decrypt the body of object `num gen` (rule C7): not the encryption
dictionary, not a cross-reference stream; strings everywhere, stream data by `decryptData`.
A stream decrypted with its own named crypt filter has that stage marked applied
(`markApplied`, rule C7'). -/
def decryptBody (st : State) (num gen : Nat) (b : IndirectBody) : Except Error IndirectBody :=
  if st.encRef = some (num, gen) then .ok b
  else
    match b with
    | .obj o => (decryptObj (stringFn st num gen) o).map IndirectBody.obj
    | .stream s =>
      if hasType s.dict "XRef" then .ok b
      else
        match decryptDict (stringFn st num gen) (isSigDict s.dict) s.dict with
        | .error e => .error e
        | .ok d' =>
          match decryptData st num gen s with
          | .error e => .error e
          | .ok data =>
            .ok (.stream ⟨if ownCrypt st.handler s.dict then markApplied d' else d', data⟩)

/-- **Entry point.** Decrypt the data of object stream `c` (generation 0) before decoding it
(rule C7; its dictionary is used as is, its members are not decrypted again). -/
def decryptContainer (st : State) (c : Nat) (s : Stream) : Except Error Stream :=
  match decryptData st c 0 s with
  | .error e => .error e
  | .ok data => .ok { s with data }

/-! ## Theorems -/

/-- `identityEntry` keeps the value's depth (a name replaces a name). -/
theorem identityEntry_depth (kv : Name × PdfObject) :
    (identityEntry kv).2.depth = kv.2.depth := by
  unfold identityEntry
  split
  · rename_i n h
    split
    · simp only [h, PdfObject.depth]
    · rfl
  · rfl

/-- `identityParms` keeps the depth. -/
theorem identityParms_depth : (p : Dict) →
    PdfObject.depthDict (identityParms p) = PdfObject.depthDict p
  | [] => rfl
  | (k, v) :: rest => by
    have ih := identityParms_depth rest
    have he := identityEntry_depth (k, v)
    simp only [identityParms, List.map_cons] at ih ⊢
    rcases hk : identityEntry (k, v) with ⟨k', v'⟩
    rw [hk] at he
    simp only at he
    simp only [PdfObject.depthDict, he, ih]

/-- `appliedParms` keeps the depth. -/
theorem appliedParms_depth (o : PdfObject) : (appliedParms o).depth = o.depth := by
  unfold appliedParms
  split
  · simp only [PdfObject.depth, identityParms_depth]
  · simp only [PdfObject.depth, PdfObject.depthList, identityParms_depth]
  · rfl

/-- `markApplied` keeps the depth. -/
theorem markApplied_depth : (d : Dict) →
    PdfObject.depthDict (markApplied d) = PdfObject.depthDict d
  | [] => rfl
  | (k, v) :: rest => by
    have ih := markApplied_depth rest
    simp only [markApplied, List.map_cons] at ih ⊢
    split <;> simp only [PdfObject.depthDict, appliedParms_depth, ih]

/-- **Shape and depth preserved**: a decrypted body has the same kind and the same depth
(a stream's dictionary depth). -/
theorem decryptBody_shape {st : State} {num gen : Nat} {b b' : IndirectBody}
    (h : decryptBody st num gen b = .ok b') :
    (∃ o o', b = .obj o ∧ b' = .obj o' ∧ o'.depth = o.depth) ∨
    (∃ s s', b = .stream s ∧ b' = .stream s' ∧
      (PdfObject.dict s'.dict).depth = (PdfObject.dict s.dict).depth) := by
  unfold decryptBody at h
  split at h
  · cases h
    cases b with
    | obj o => exact .inl ⟨o, o, rfl, rfl, rfl⟩
    | stream s => exact .inr ⟨s, s, rfl, rfl, rfl⟩
  · split at h
    · rename_i o
      cases ho : decryptObj (stringFn st num gen) o with
      | error e => rw [ho] at h; cases h
      | ok o' =>
        rw [ho] at h
        cases h
        exact .inl ⟨o, o', rfl, rfl, decryptObj_depth _ o ho⟩
    · rename_i s
      split at h
      · cases h; exact .inr ⟨s, s, rfl, rfl, rfl⟩
      · split at h
        · cases h
        · rename_i d' hd
          split at h
          · cases h
          · cases h
            refine .inr ⟨s, _, rfl, rfl, ?_⟩
            simp only [PdfObject.depth]
            split
            · rw [markApplied_depth, decryptDict_depth _ _ s.dict hd]
            · rw [decryptDict_depth _ _ s.dict hd]

/-- **Size law**: decryption never makes data longer. -/
theorem decryptBytes_size_le {m : Method} {key data out : ByteArray}
    (h : decryptBytes m key data = .ok out) : out.size ≤ data.size := by
  unfold decryptBytes at h
  split at h
  · cases h; exact Nat.le_refl _
  · simp only at h
    split at h
    · rename_i hs; cases h; exact Nat.le_of_eq hs
    · cases h
  all_goals
    split at h
    · cases h; simp
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h; omega
          · cases h

/-- **RC4 preserves length.** -/
theorem decryptBytes_rc4_size {key data out : ByteArray}
    (h : decryptBytes .rc4 key data = .ok out) : out.size = data.size := by
  unfold decryptBytes at h
  simp only at h
  split at h
  · rename_i hs; cases h; exact hs
  · cases h

/-- **AES output is at most the input minus the 16-byte IV.** -/
theorem decryptBytes_aes_size {m : Method} (hm : m = .aesv2 ∨ m = .aesv3) {key data out : ByteArray}
    (h : decryptBytes m key data = .ok out) : out.size ≤ data.size - 16 := by
  rcases hm with rfl | rfl
  all_goals
    unfold decryptBytes at h
    simp only at h
    split at h
    · cases h; simp
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h; assumption
          · cases h

/-- Decrypted stream data is never longer than the raw data. -/
theorem decryptData_size_le {st : State} {num gen : Nat} {s : Stream} {out : ByteArray}
    (h : decryptData st num gen s = .ok out) : out.size ≤ s.data.size := by
  unfold decryptData at h
  split at h
  · cases h; exact Nat.le_refl _
  · split at h
    · cases h
    · exact decryptBytes_size_le h

/-- A decrypted container is never longer than the raw one, and keeps its dictionary. -/
theorem decryptContainer_size_le {st : State} {c : Nat} {s s' : Stream}
    (h : decryptContainer st c s = .ok s') : s'.data.size ≤ s.data.size ∧ s'.dict = s.dict := by
  unfold decryptContainer at h
  split at h
  · cases h
  · rename_i data hd
    cases h
    exact ⟨decryptData_size_le hd, rfl⟩

/-! ## Tests (vectors from `Tests/adversarial/encrypted/generate.py --vectors`) -/

section Tests

/-- Test helper: hex decoding. -/
private def fromHex (s : String) : ByteArray := Id.run do
  let digit (c : Char) : UInt8 :=
    if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
    else 0
  let cs := s.toList.filter (· ≠ ' ')
  let mut out := ByteArray.empty
  for i in [0:cs.length / 2] do
    out := out.push (digit (cs.getD (2 * i) '0') * 16 + digit (cs.getD (2 * i + 1) '0'))
  return out

/-- The `/V 2 /R 3` handler of `rc4-128.pdf`. -/
private def hR3 : Handler :=
  { v := 2, r := 3, keyLen := 16, p := -3904,
    o := fromHex "566fa873ee33c797cd3b904fdadf814afa34df9a38f6ed41b984e2c6da2aa6f5",
    u := fromHex "9ca29d4b638cb40bf27dd655f1f33bccb3ec8ce954c04700415994a5c25e4f08",
    oe := .empty, ue := .empty, perms := .empty, encryptMetadata := true,
    stmF := .rc4, strF := .rc4, filters := [] }

private def id0R3 : ByteArray := fromHex "dc51a2a67d2df2d1c9ccd5c6895c1ad3"

-- Algorithm 2 (R3) and the Algorithm 5 /U check
#guard beqBytes (algorithm2 hR3 id0R3) (fromHex "8dae4d9b5ba0e99b2364e878ed358dae")
#guard userKeyOk hR3 id0R3 (fromHex "8dae4d9b5ba0e99b2364e878ed358dae")
#guard (match deriveKey hR3 id0R3 with
  | .ok k => beqBytes k (fromHex "8dae4d9b5ba0e99b2364e878ed358dae")
  | .error _ => false)
-- a different /ID: the empty password no longer matches /U
#guard (match deriveKey hR3 (fromHex "00") with
  | .error (.encryption _) => true
  | _ => false)
-- Algorithm 2.B (R6) with the empty password and with "ab", salt 00 01 … 07
#guard beqBytes (hash2B .empty (fromHex "0001020304050607") .empty)
  (fromHex "1403c04eb647d2e60452dfc4eb0a5e0cf322e8a83a759eabbd17d498a93ba041")
#guard beqBytes (hash2B "ab".toUTF8 (fromHex "0001020304050607") .empty)
  (fromHex "c32dd6b278b1f45a9655b4dcb8b478b9b3464b13657a41f2227edc90b84d2d52")
-- Algorithm 1 with the AESV2 salt
#guard beqBytes (objectKey .aesv2 (fromHex "000102030405060708090a0b0c0d0e0f") 5 0)
  (fromHex "205d415ca0043cb9e10644804364a2e6")
-- the /P bytes
#guard (le32 (-3904)).data == #[0xC0, 0xF0, 0xFF, 0xFF]
-- rule C7': an applied named crypt filter is marked /Identity; /Identity is not "own"
private def cryptDict (parms : PdfObject) : Dict :=
  [(Name.ofString "Filter", .array [.name (Name.ofString "Crypt"), .name (Name.ofString "FlateDecode")]),
   (Name.ofString "DecodeParms", parms)]
private def altParms : PdfObject :=
  .array [.dict [(Name.ofString "Name", .name (Name.ofString "AltCF"))], .null]
#guard ownCrypt hR3 (cryptDict altParms)
#guard !ownCrypt hR3 (cryptDict (.array [.dict [(Name.ofString "Name", .name (Name.ofString "Identity"))], .null]))
#guard !ownCrypt hR3 [(Name.ofString "Filter", .name (Name.ofString "FlateDecode"))]
#guard cryptName (markApplied (cryptDict altParms)) == Name.ofString "Identity"
#guard cryptName (cryptDict altParms) == Name.ofString "AltCF"
-- an AES string round-trip shape: empty decrypts to empty, 5 bytes is an error
#guard (match decryptBytes .aesv2 (zeros 16) .empty with | .ok b => b.size == 0 | _ => false)
#guard (match decryptBytes .aesv2 (zeros 16) (zeros 5) with | .error _ => true | _ => false)
-- parsing: /V 3 and a public-key handler are unsupported
#guard (match parseEncrypt [(Name.ofString "Filter", .name (Name.ofString "Adobe.PubSec"))] with
  | .error (.unsupported _) => true
  | _ => false)
#guard (match parseEncrypt [(Name.ofString "Filter", .name (Name.ofString "Standard")),
    (Name.ofString "V", .int 3)] with
  | .error (.unsupported _) => true
  | _ => false)

end Tests

end SafePdf.Core.Crypt
