import SafePdf.Core.Crypt

/-!
# Encrypting the objects of an incremental update (Plan.md §4 S8/C7, §6 Phase 9 "Persistence — annotations inside the PDF"; task 9.5f)

The incremental-update writer (`Core.Write.Incremental`) appends objects to an opened
document. When that document is encrypted (ISO 32000-2 §7.6), the new objects' strings and
stream data must be encrypted with the document's own security handler, so that every
reader — ours included — decrypts them like the original objects. This module is the
inverse of `Core.Crypt.decryptBody` for the objects the writer produces.

## Rules (E1–E7)

* E1. **Same handler, same key.** The opened document's decryption state `Crypt.State` (file
  key derived for the empty user password, the parsed `/Encrypt` handler) is reused; the
  per-object key is `Crypt.objectKey` (Algorithm 1: MD5 of file key, object number,
  generation, and the `sAlT` suffix for `/AESV2`; the file key itself for `/AESV3`).
* E2. **Methods** (§7.6.3, §7.6.5): strings use `/StrF`, stream data `/StmF`
  (`/V 1`, `/V 2`: RC4 for both); `/Identity` (and `/None`) leave the bytes as they are; RC4
  is its own inverse (`Rc4.rc4`); AES-128 and AES-256 are CBC with PKCS#7 padding
  (`pkcs7Pad`, then `Aes.cbcEncryptNoPad`) and the 16-byte IV prepended.
* E3. **Deterministic IV** (the pure core has no randomness): the IV is the first 16 bytes of
  `SHA-256("safe-pdf 9.5f IV" ‖ file key ‖ num ‖ gen ‖ counter ‖ kind ‖ plaintext)`
  (`deriveIv`; numbers as 4-byte little-endian, `kind` = `s` for a string, `S` for stream
  data, `counter` = the string's position in the object's depth-first string order). The
  IV is thus distinct for distinct (key, object, position, plaintext) — a fresh IV per
  plaintext as CBC confidentiality requires — and readers need no particular IV (§7.6.3:
  "a 16-byte random number" is a writer recommendation; decryption reads it from the data).
  Identical plaintexts at the same position of the same object encrypt identically, which
  reveals only that a re-written object is unchanged.
* E4. **What is encrypted** mirrors `Crypt.decryptBody` (rule C7 there): every string of an
  object, recursively, except the `/Contents` value of a signature dictionary
  (`Crypt.isSigDict`, `Crypt.keepEntry`); nothing of the encryption dictionary
  (`State.encRef`) or of a cross-reference stream (`/Type /XRef`); the data of a
  `/Type /Metadata` stream is left plain when `/EncryptMetadata false`.
* E5. A stream whose first filter is `/Crypt` (its own crypt filter) is refused
  (`Error.unsupported`): the writer never produces one, and the decryption side would mark
  the stage applied (rule C7'), so the self-check could not match it.
* E6. **Stream `/Length`** is the length of the *written* (encrypted) data: `encLen`
  predicts it from the method, `encryptStream` checks the prediction, and the writer sets
  `/Length` on the encrypted dictionary.
* E7. Errors (an AES key of a bad size, a failed prediction) are `Error.malformed`; the
  writer's strict self-check (`Incremental` rule W8) is what guarantees that every written
  object decrypts back exactly — the primitives themselves are vector-tested, not proved
  (Plan.md §6 Phase 4).

## Theorems

* `pkcs7Pad_size`, `pkcs7Pad_mod`, `pkcs7Pad_gt`: padding adds 1–16 bytes and yields whole
  blocks.
* `encLen_none`: without encryption the written length is the data length.
-/

namespace SafePdf.Core.Write.Encrypt

open SafePdf
open SafePdf.Core.Crypt (State Method objectKey bytesOf isSigDict keepEntry hasType firstFilter)

/-! ## AES-CBC encryption with PKCS#7 padding (rule E2) -/

/-- **PKCS#7 padding** (RFC 5652 §6.3) to 16-byte blocks: `n = 16 − size mod 16` bytes of
value `n` (a whole block when the data is already aligned). -/
def pkcs7Pad (d : ByteArray) : ByteArray :=
  let n := 16 - d.size % 16
  d ++ ⟨Array.replicate n n.toUInt8⟩

/-- The padded size. -/
theorem pkcs7Pad_size (d : ByteArray) : (pkcs7Pad d).size = d.size + (16 - d.size % 16) := by
  simp only [pkcs7Pad, ByteArray.size_append]
  show _ + (Array.replicate _ _).size = _
  rw [Array.size_replicate]

/-- Padding yields whole blocks. -/
theorem pkcs7Pad_mod (d : ByteArray) : (pkcs7Pad d).size % 16 = 0 := by
  rw [pkcs7Pad_size]
  have := Nat.mod_lt d.size (by decide : 16 > 0)
  omega

/-- Padding always adds at least one byte (so unpadding is unambiguous). -/
theorem pkcs7Pad_gt (d : ByteArray) : d.size < (pkcs7Pad d).size := by
  rw [pkcs7Pad_size]
  have := Nat.mod_lt d.size (by decide : 16 > 0)
  omega

/-- Four little-endian bytes of `n` (mod 2³²). -/
def u32 (n : Nat) : ByteArray :=
  bytesOf [n.toUInt8, (n / 256).toUInt8, (n / 65536).toUInt8, (n / 16777216).toUInt8]

/-- Domain-separation prefix of the IV hash (rule E3). -/
def ivDomain : ByteArray := "safe-pdf 9.5f IV".toUTF8

/-- **The deterministic IV** (rule E3): the first 16 bytes of
`SHA-256(ivDomain ‖ fileKey ‖ num ‖ gen ‖ ctr ‖ kind ‖ plaintext)`. -/
def deriveIv (fileKey : ByteArray) (num gen ctr : Nat) (kind : UInt8) (pt : ByteArray) :
    ByteArray :=
  (Crypt.Sha2.sha256 (ivDomain ++ fileKey ++ u32 num ++ u32 gen ++ u32 ctr ++ bytesOf [kind] ++
    pt)).extract 0 16

/-- **AES-CBC encryption** with PKCS#7 padding, the IV prepended (ISO 32000-2 §7.6.3). -/
def aesEncrypt (key iv data : ByteArray) : Except Error ByteArray :=
  match Crypt.Aes.cbcEncryptNoPad key iv (pkcs7Pad data) with
  | .ok c => .ok (iv ++ c)
  | .error e => .error e

/-- **Encrypt** `data` under method `m` with object key `key` (rule E2); `fileKey`, `num`,
`gen`, `ctr`, `kind` only feed the AES IV (rule E3). -/
def encryptBytes (m : Method) (fileKey key : ByteArray) (num gen ctr : Nat) (kind : UInt8)
    (data : ByteArray) : Except Error ByteArray :=
  match m with
  | .identity => .ok data
  | .rc4 => .ok (Crypt.Rc4.rc4 key data)
  | .aesv2 | .aesv3 => aesEncrypt key (deriveIv fileKey num gen ctr kind data) data

/-- The size of `encryptBytes m … data` for data of `n` bytes (rule E6): unchanged for the
identity and RC4; IV + padded data for AES. -/
def methodLen (m : Method) (n : Nat) : Nat :=
  match m with
  | .identity | .rc4 => n
  | .aesv2 | .aesv3 => 16 + n + (16 - n % 16)

/-! ## Strings of an object (rule E4) -/

/-- A string encryptor: string counter and plaintext to ciphertext. -/
abbrev StringEnc := Nat → List UInt8 → Except Error (List UInt8)

mutual
/-- Encrypt every string of an object with `f`, numbering strings from `c` in depth-first
order; returns the object and the next counter. -/
def encryptObj (f : StringEnc) (c : Nat) : PdfObject → Except Error (PdfObject × Nat)
  | .null => .ok (.null, c)
  | .bool b => .ok (.bool b, c)
  | .int i => .ok (.int i, c)
  | .real r => .ok (.real r, c)
  | .name n => .ok (.name n, c)
  | .ref n g => .ok (.ref n g, c)
  | .string s =>
    match f c s with
    | .ok s' => .ok (.string s', c + 1)
    | .error e => .error e
  | .array xs =>
    match encryptList f c xs with
    | .ok (ys, c') => .ok (.array ys, c')
    | .error e => .error e
  | .dict d =>
    match encryptDict f (isSigDict d) c d with
    | .ok (d', c') => .ok (.dict d', c')
    | .error e => .error e

/-- `encryptObj` over a list. -/
def encryptList (f : StringEnc) (c : Nat) :
    List PdfObject → Except Error (List PdfObject × Nat)
  | [] => .ok ([], c)
  | x :: xs =>
    match encryptObj f c x with
    | .error e => .error e
    | .ok (y, c1) =>
      match encryptList f c1 xs with
      | .error e => .error e
      | .ok (ys, c2) => .ok (y :: ys, c2)

/-- `encryptObj` over the values of a dictionary; with `sig` (a signature dictionary) the
`/Contents` value is kept as is (`Crypt.keepEntry`, rule E4). -/
def encryptDict (f : StringEnc) (sig : Bool) (c : Nat) :
    List (Name × PdfObject) → Except Error (List (Name × PdfObject) × Nat)
  | [] => .ok ([], c)
  | (k, v) :: rest =>
    match (if keepEntry sig k then .ok (v, c) else encryptObj f c v) with
    | .error e => .error e
    | .ok (v', c1) =>
      match encryptDict f sig c1 rest with
      | .error e => .error e
      | .ok (rest', c2) => .ok ((k, v') :: rest', c2)
end

/-- The string encryptor of object `num gen`: `/StrF` with the object's key. -/
def stringEnc (st : State) (num gen : Nat) : StringEnc :=
  let m := st.handler.strF
  let key := objectKey m st.fileKey num gen
  fun c s => (encryptBytes m st.fileKey key num gen c 0x73 (bytesOf s)).map ByteArray.toList

/-- **Entry point.** Encrypt direct object `o` written as object `num gen` (rule E4): every
string, except in the encryption dictionary itself. -/
def encryptObject (st : State) (num gen : Nat) (o : PdfObject) : Except Error PdfObject :=
  if st.encRef = some (num, gen) then .ok o
  else (encryptObj (stringEnc st num gen) 0 o).map Prod.fst

/-! ## Streams (rules E4–E6) -/

/-- Whether stream data with dictionary `d` stays plain (rule E4): a cross-reference stream,
or a metadata stream when `/EncryptMetadata false`. -/
def plainData (st : State) (d : Dict) : Bool :=
  hasType d "XRef" || (hasType d "Metadata" && !st.handler.encryptMetadata)

/-- **The written data length** of a stream with dictionary `d` and `n` data bytes (rule
E6): `n` without encryption or for plain data, else the `/StmF` method's length. -/
def encLen (st : Option State) (d : Dict) (n : Nat) : Nat :=
  match st with
  | none => n
  | some st => if plainData st d then n else methodLen st.handler.stmF n

/-- Without encryption the written length is the data length. -/
theorem encLen_none (d : Dict) (n : Nat) : encLen none d n = n := rfl

/-- **Entry point.** Encrypt a stream written as object `num gen` (rules E4–E6): the
dictionary's strings and the data (the caller sets `/Length` to the written data's length,
rule E6). A stream
with its own `/Crypt` filter is refused (rule E5). Cross-reference streams and the encryption
dictionary are written as they are. -/
def encryptStream (st : State) (num gen : Nat) (d : Dict) (data : List UInt8) :
    Except Error (Dict × List UInt8) :=
  if firstFilter d = some (Name.ofString "Crypt") then
    .error (.unsupported "writing a stream with its own /Crypt filter")
  else if st.encRef = some (num, gen) || hasType d "XRef" then
    .ok (d, data)
  else
    let m := st.handler.stmF
    let data' : Except Error ByteArray :=
      if plainData st d then .ok (bytesOf data)
      else encryptBytes m st.fileKey (objectKey m st.fileKey num gen) num gen 0 0x53 (bytesOf data)
    match data' with
    | .error e => .error e
    | .ok out =>
      if out.size = encLen (some st) d data.length then
        match encryptDict (stringEnc st num gen) (isSigDict d) 0 d with
        | .error e => .error e
        | .ok (d', _) => .ok (d', out.toList)
      else .error (.malformed 0 "stream encryption: unexpected output length (internal error)")

end SafePdf.Core.Write.Encrypt
