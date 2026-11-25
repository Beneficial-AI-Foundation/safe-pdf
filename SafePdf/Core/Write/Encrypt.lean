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
  reveals only that a re-written object is unchanged. This is the IV for the default (empty)
  seed only; the viewer always passes a seed (E3').
* E3'. **Fresh IVs** (task 12.4, Plan.md §6 Phase 12 "Writer confidentiality"): the pure core
  still generates no randomness, but every entry point takes an IV seed (`seed`, default
  empty) that the shell fills with fresh bytes from the operating system on every save
  (`Shell.App.Save.freshSeed`). With a non-empty seed the IV is the first 16 bytes of
  `SHA-256(ivDomainSeeded ‖ |seed| ‖ seed ‖ file key ‖ num ‖ gen ‖ counter ‖ kind ‖ plaintext)`
  (`ivInput`, `deriveIv`): a different seed per save gives unrelated IVs, so saving the same
  object twice yields different ciphertexts, and an observer without the seed (it is never
  written) cannot predict an IV. Readers take the IV from the data (§7.6.3), so the seed
  changes nothing for them, and the writer's self-check (`Incremental` rule W8) still
  decrypts every written object back to its plaintext, for every seed.
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
* `aesEncrypt_prefix`, `aesEncrypt_extract`: AES output starts with its IV.
* `aesEncrypt_iv_ne`: distinct IVs (of one size) give distinct ciphertexts, for every key and
  plaintexts (task 12.4).
* `#guard`s (task 12.4): `decryptBytes` inverts `encryptBytes` for every method, lengths
  0–40 and three seeds; the same plaintext under different seeds encrypts differently (AES);
  the empty seed gives task 9.5f's IV unchanged.
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

/-- Domain-separation prefix of the seeded IV hash (rule E3', task 12.4). -/
def ivDomainSeeded : ByteArray := "safe-pdf 12.4 IV".toUTF8

/-- The hash input that identifies one encrypted string or stream data (rule E3'):
`ivDomainSeeded ‖ |seed| ‖ seed` with a non-empty seed, `ivDomain` without one, then
`fileKey ‖ num ‖ gen ‖ ctr ‖ kind ‖ plaintext`. -/
def ivInput (seed fileKey : ByteArray) (num gen ctr : Nat) (kind : UInt8) (pt : ByteArray) :
    ByteArray :=
  let pre := if seed.size = 0 then ivDomain else ivDomainSeeded ++ u32 seed.size ++ seed
  pre ++ fileKey ++ u32 num ++ u32 gen ++ u32 ctr ++ bytesOf [kind] ++ pt

/-- **The IV** (rules E3, E3'): the first 16 bytes of `SHA-256 (ivInput seed …)`. With the
default empty `seed` it is the deterministic IV of task 9.5f
(`SHA-256(ivDomain ‖ fileKey ‖ num ‖ gen ‖ ctr ‖ kind ‖ plaintext)`); with a fresh random
`seed` from the shell (task 12.4) it is unpredictable and differs between saves. -/
def deriveIv (fileKey : ByteArray) (num gen ctr : Nat) (kind : UInt8) (pt : ByteArray)
    (seed : ByteArray := ByteArray.empty) : ByteArray :=
  (Crypt.Sha2.sha256 (ivInput seed fileKey num gen ctr kind pt)).extract 0 16

/-- **AES-CBC encryption** with PKCS#7 padding, the IV prepended (ISO 32000-2 §7.6.3). -/
def aesEncrypt (key iv data : ByteArray) : Except Error ByteArray :=
  match Crypt.Aes.cbcEncryptNoPad key iv (pkcs7Pad data) with
  | .ok c => .ok (iv ++ c)
  | .error e => .error e

/-- **The IV leads the ciphertext** (rule E2): a successful AES encryption is the IV followed
by the CBC blocks. -/
theorem aesEncrypt_prefix {key iv data c : ByteArray} (h : aesEncrypt key iv data = .ok c) :
    ∃ t, c = iv ++ t := by
  unfold aesEncrypt at h
  split at h
  · exact ⟨_, (Except.ok.inj h).symm⟩
  · cases h

/-- The IV is recoverable from the ciphertext: its first `iv.size` bytes. -/
theorem aesEncrypt_extract {key iv data c : ByteArray} (h : aesEncrypt key iv data = .ok c) :
    c.extract 0 iv.size = iv := by
  obtain ⟨t, rfl⟩ := aesEncrypt_prefix h
  exact ByteArray.extract_append_eq_left rfl

/-- **Distinct IVs give distinct ciphertexts** (task 12.4): two successful AES encryptions
under IVs of the same size that differ never produce the same bytes — for every key and
every pair of plaintexts, in particular for the same plaintext. -/
theorem aesEncrypt_iv_ne {key iv iv' d d' c c' : ByteArray}
    (h : aesEncrypt key iv d = .ok c) (h' : aesEncrypt key iv' d' = .ok c')
    (hs : iv.size = iv'.size) (hne : iv ≠ iv') : c ≠ c' := by
  intro hc
  apply hne
  have e1 := aesEncrypt_extract h
  have e2 := aesEncrypt_extract h'
  rw [hs, hc] at e1
  exact e1.symm.trans e2

/-- **Encrypt** `data` under method `m` with object key `key` (rule E2); `fileKey`, `num`,
`gen`, `ctr`, `kind` and `seed` only feed the AES IV (rules E3, E3'). -/
def encryptBytes (m : Method) (fileKey key : ByteArray) (num gen ctr : Nat) (kind : UInt8)
    (data : ByteArray) (seed : ByteArray := ByteArray.empty) : Except Error ByteArray :=
  match m with
  | .identity => .ok data
  | .rc4 => .ok (Crypt.Rc4.rc4 key data)
  | .aesv2 | .aesv3 => aesEncrypt key (deriveIv fileKey num gen ctr kind data seed) data

/-- The size of `encryptBytes m … data` for data of `n` bytes (rule E6): unchanged for the
identity and RC4; IV + padded data for AES. -/
def methodLen (m : Method) (n : Nat) : Nat :=
  match m with
  | .identity | .rc4 => n
  | .aesv2 | .aesv3 => 16 + n + (16 - n % 16)

/-! ## Round trip and IV freshness, checked at build time (task 12.4)

The AES and RC4 primitives are vector-tested, not proved (rule E7), so the round trip
`decryptBytes ∘ encryptBytes = id` is checked here for every method, several data lengths
and several IV seeds (the empty one of task 9.5f and two random-looking ones); and that the
same plaintext under the same key with different seeds gives different ciphertexts (for AES;
RC4 has no IV). `aesEncrypt_iv_ne` is the general statement for distinct IVs. -/

/-- Test seeds: none, and two 32-byte ones. -/
def testSeeds : List ByteArray :=
  [ByteArray.empty, ⟨(List.range 32).toArray.map (fun i => (5 * i + 9).toUInt8)⟩,
   ⟨(List.range 32).toArray.map (fun i => (11 * i + 200).toUInt8)⟩]

/-- Test keys per method (5- and 16-byte RC4, AES-128, AES-256). -/
def testKeys : List (Method × ByteArray) :=
  let k16 : ByteArray := ⟨(List.range 16).toArray.map (·.toUInt8)⟩
  let k32 : ByteArray := ⟨(List.range 32).toArray.map (fun i => (3 * i + 1).toUInt8)⟩
  [(.identity, k16), (.rc4, ⟨k16.data.extract 0 5⟩), (.rc4, k16), (.aesv2, k16), (.aesv3, k32)]

/-- Test plaintext of `n` bytes. -/
def testData (n : Nat) : ByteArray := ⟨(List.range n).toArray.map (fun i => (7 * i + n).toUInt8)⟩

/-- Whether encrypting `testData n` with `seed` decrypts back to it. -/
def roundTrips (m : Method) (key seed : ByteArray) (n : Nat) : Bool :=
  match encryptBytes m key key 7 0 n 0x73 (testData n) seed with
  | .error _ => false
  | .ok c =>
    c.size == methodLen m n &&
    match Crypt.decryptBytes m key c with
    | .ok p => p.data == (testData n).data
    | .error _ => false

#guard testKeys.all fun (m, key) => testSeeds.all fun seed =>
  [0, 1, 15, 16, 17, 40].all (roundTrips m key seed)

/-- The ciphertext of `testData n` under `seed`, or empty on an error. -/
def testCipher (m : Method) (key seed : ByteArray) (n : Nat) : ByteArray :=
  match encryptBytes m key key 7 0 n 0x73 (testData n) seed with
  | .ok c => c
  | .error _ => ByteArray.empty

#guard testKeys.all fun (m, key) => (m == .aesv2 || m == .aesv3) →
  [0, 16, 33].all fun n =>
    let cs := testSeeds.map fun seed => (testCipher m key seed n).data
    cs.all (·.size > 0) && cs.Nodup

-- The empty seed is task 9.5f's deterministic IV, unchanged.
#guard (deriveIv (testData 16) 3 0 1 0x73 (testData 5)).data ==
  ((Crypt.Sha2.sha256 (ivDomain ++ testData 16 ++ u32 3 ++ u32 0 ++ u32 1 ++ bytesOf [0x73] ++
    testData 5)).extract 0 16).data

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

/-- The string encryptor of object `num gen`: `/StrF` with the object's key; `seed` feeds
the AES IVs (rule E3'). -/
def stringEnc (st : State) (num gen : Nat) (seed : ByteArray := ByteArray.empty) : StringEnc :=
  let m := st.handler.strF
  let key := objectKey m st.fileKey num gen
  fun c s => (encryptBytes m st.fileKey key num gen c 0x73 (bytesOf s) seed).map ByteArray.toList

/-- **Entry point.** Encrypt direct object `o` written as object `num gen` (rule E4): every
string, except in the encryption dictionary itself; `seed` feeds the AES IVs (rule E3'). -/
def encryptObject (st : State) (num gen : Nat) (o : PdfObject)
    (seed : ByteArray := ByteArray.empty) : Except Error PdfObject :=
  if st.encRef = some (num, gen) then .ok o
  else (encryptObj (stringEnc st num gen seed) 0 o).map Prod.fst

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
def encryptStream (st : State) (num gen : Nat) (d : Dict) (data : List UInt8)
    (seed : ByteArray := ByteArray.empty) : Except Error (Dict × List UInt8) :=
  if firstFilter d = some (Name.ofString "Crypt") then
    .error (.unsupported "writing a stream with its own /Crypt filter")
  else if st.encRef = some (num, gen) || hasType d "XRef" then
    .ok (d, data)
  else
    let m := st.handler.stmF
    let data' : Except Error ByteArray :=
      if plainData st d then .ok (bytesOf data)
      else encryptBytes m st.fileKey (objectKey m st.fileKey num gen) num gen 0 0x53 (bytesOf data)
        seed
    match data' with
    | .error e => .error e
    | .ok out =>
      if out.size = encLen (some st) d data.length then
        match encryptDict (stringEnc st num gen seed) (isSigDict d) 0 d with
        | .error e => .error e
        | .ok (d', _) => .ok (d', out.toList)
      else .error (.malformed 0 "stream encryption: unexpected output length (internal error)")

end SafePdf.Core.Write.Encrypt
