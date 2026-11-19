import SafePdf.Core.Error

/-!
# AES (Plan.md §6 Phase 4, task 4.3a; FIPS 197, NIST SP 800-38A)

The AES block cipher and the modes the PDF standard security handler needs
(ISO 32000-2 §7.6.3–7.6.4):

* **CBC decryption with PKCS#7 unpadding** for `/AESV2` (AES-128) and `/AESV3` (AES-256)
  streams and strings, whose first 16 bytes are the IV (`cbcDecrypt … true`);
* **CBC decryption without padding**, zero IV, for `/UE` and `/OE` (`cbcDecrypt … false`);
* **CBC encryption without padding** for the revision 6 hash (Algorithm 2.B uses AES-128-CBC
  encryption of the repeated input; `cbcEncryptNoPad`);
* **ECB** single-block decryption (and encryption) for `/Perms` (`ecbDecrypt`, `ecbEncrypt`).

Plan.md §6 Phase 4 asks for the smallest trusted implementation, checked against published
test vectors; proving AES correct is out of scope. Keys of 16, 24 and 32 bytes are accepted
(AES-128/192/256); any other key length, an IV that is not 16 bytes, or data whose length is
not a multiple of 16 is `Error.malformed`. Every loop runs over a `Std.Range` (no `partial`)
and every table or byte access uses `getD` / `[i]?.getD` — no `!`-indexing.

## Representation

The 16-byte state is four big-endian `UInt32` column words: column `c` packs state bytes
`s[0,c] … s[3,c]` = input bytes `4c … 4c+3`, row 0 in the top byte (FIPS 197 §3.4). The key
schedule is the `Array UInt32` of FIPS 197 §5.2 in the same packing, so `AddRoundKey` is a
word XOR. `MixColumns` works on whole words with the packed `xtime` trick;
`InvMixColumns` is `MixColumns` after the standard pre-multiplication by `{04}x² + {05}`
(the factorization `InvMix = Mix ∘ (04x² + 05)`).

## Padding (`cbcDecrypt … true`)

PKCS#7 (RFC 5652 §6.3, as ISO 32000-2 §7.6.3.2 requires): the last plaintext byte `n` must
satisfy `1 ≤ n ≤ 16` and the last `n` bytes must all equal `n`; otherwise the result is
`Error.malformed` (strict). Empty ciphertext is an error when padding is expected (a padded
message has at least one block). Lenient handling, if wanted, belongs to the caller, which can
decrypt with `pad = false` and inspect the tail itself.
-/

namespace SafePdf.Core.Crypt.Aes

open SafePdf

/-- The AES S-box (FIPS 197 Figure 7). -/
def sbox : Array UInt8 := #[
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

/-- The inverse S-box (FIPS 197 Figure 14), computed by inverting `sbox`; checked below to
be its two-sided inverse. -/
def invSbox : Array UInt8 := Id.run do
  let mut inv : Array UInt8 := Array.replicate 256 0
  for i in [0:256] do
    inv := inv.setIfInBounds (sbox.getD i 0).toNat i.toUInt8
  return inv

/-- S-box lookup on the low byte of `x`, as a word. -/
@[inline] def sb (x : UInt32) : UInt32 := (sbox.getD (x &&& 0xff).toNat 0).toUInt32

/-- Inverse S-box lookup on the low byte of `x`, as a word. -/
@[inline] def isb (x : UInt32) : UInt32 := (invSbox.getD (x &&& 0xff).toNat 0).toUInt32

/-- Left rotation of a word by `n` bits (`0 < n < 32`). -/
@[inline] def rotl (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- Multiplication by `{02}` in GF(2⁸) of each of the four bytes of a word (FIPS 197 §4.2.1). -/
@[inline] def xtime4 (w : UInt32) : UInt32 :=
  ((w &&& 0x7f7f7f7f) <<< 1) ^^^ (((w >>> 7) &&& 0x01010101) * 0x1b)

/-- `MixColumns` on one column word (FIPS 197 §5.1.3):
`out_r = 2·a_r ⊕ 3·a_{r+1} ⊕ a_{r+2} ⊕ a_{r+3}`. -/
@[inline] def mixColumn (w : UInt32) : UInt32 :=
  let r8 := rotl w 8
  xtime4 (w ^^^ r8) ^^^ r8 ^^^ rotl w 16 ^^^ rotl w 24

/-- `InvMixColumns` on one column word (FIPS 197 §5.3.3), as `MixColumns` after adding
`{04}·(a_r ⊕ a_{r+2})` to each byte. -/
@[inline] def invMixColumn (w : UInt32) : UInt32 :=
  mixColumn (w ^^^ xtime4 (xtime4 (w ^^^ rotl w 16)))

/-- `SubWord` (FIPS 197 §5.2): the S-box applied to each byte of a word. -/
@[inline] def subWord (w : UInt32) : UInt32 :=
  (sb (w >>> 24) <<< 24) ||| (sb (w >>> 16) <<< 16) ||| (sb (w >>> 8) <<< 8) ||| sb w

/-- An expanded AES key: the number of rounds `Nr` (10, 12 or 14) and the `4 (Nr + 1)`
round-key words of FIPS 197 §5.2. -/
structure Key where
  /-- The number of rounds. -/
  rounds : Nat
  /-- The key schedule, four words per round key. -/
  w : Array UInt32

/-- The big-endian word at byte offset `i` (out-of-range bytes read as 0). -/
@[inline] def be32 (b : ByteArray) (i : Nat) : UInt32 :=
  ((b[i]?.getD 0).toUInt32 <<< 24) ||| ((b[i+1]?.getD 0).toUInt32 <<< 16) |||
    ((b[i+2]?.getD 0).toUInt32 <<< 8) ||| (b[i+3]?.getD 0).toUInt32

/-- Key expansion (FIPS 197 §5.2) for a 16-, 24- or 32-byte key; any other length is
`Error.malformed`. -/
def expandKey (key : ByteArray) : Except Error Key := do
  let nk := key.size / 4
  unless key.size = 16 ∨ key.size = 24 ∨ key.size = 32 do
    throw (.malformed 0 s!"AES key must be 16, 24 or 32 bytes, got {key.size}")
  let nr := nk + 6
  let total := 4 * (nr + 1)
  let mut w : Array UInt32 := Array.mkEmpty total
  for i in [0:nk] do
    w := w.push (be32 key (4 * i))
  let mut rcon : UInt32 := 0x01
  for i in [nk:total] do
    let mut temp := w.getD (i - 1) 0
    if i % nk = 0 then
      temp := subWord (rotl temp 8) ^^^ (rcon <<< 24)
      rcon := (xtime4 rcon) &&& 0xff
    else if nk > 6 ∧ i % nk = 4 then
      temp := subWord temp
    w := w.push (w.getD (i - nk) 0 ^^^ temp)
  return ⟨nr, w⟩

/-- A 16-byte block as four column words. -/
abbrev Block := UInt32 × UInt32 × UInt32 × UInt32

/-- Reads the block at byte offset `off` (out-of-range bytes read as 0). -/
@[inline] def readBlock (b : ByteArray) (off : Nat) : Block :=
  (be32 b off, be32 b (off + 4), be32 b (off + 8), be32 b (off + 12))

/-- Appends a block's 16 bytes to `out`. -/
@[inline] def pushBlock (out : ByteArray) (blk : Block) : ByteArray :=
  let push32 (o : ByteArray) (w : UInt32) : ByteArray :=
    (((o.push (w >>> 24).toUInt8).push (w >>> 16).toUInt8).push (w >>> 8).toUInt8).push w.toUInt8
  push32 (push32 (push32 (push32 out blk.1) blk.2.1) blk.2.2.1) blk.2.2.2

/-- XOR of two blocks. -/
@[inline] def xorBlock (a b : Block) : Block :=
  (a.1 ^^^ b.1, a.2.1 ^^^ b.2.1, a.2.2.1 ^^^ b.2.2.1, a.2.2.2 ^^^ b.2.2.2)

/-- `AddRoundKey` with round key `r`. -/
@[inline] def addRoundKey (k : Key) (r : Nat) (s : Block) : Block :=
  xorBlock s (k.w.getD (4 * r) 0, k.w.getD (4 * r + 1) 0, k.w.getD (4 * r + 2) 0,
    k.w.getD (4 * r + 3) 0)

/-- `SubBytes` then `ShiftRows` (FIPS 197 §5.1.1–5.1.2): output column `c`, row `r` is
`S(in[(c + r) mod 4][r])`. -/
@[inline] def subShift (s : Block) : Block :=
  let (c0, c1, c2, c3) := s
  let col (a b c d : UInt32) : UInt32 :=
    (sb (a >>> 24) <<< 24) ||| (sb (b >>> 16) <<< 16) ||| (sb (c >>> 8) <<< 8) ||| sb d
  (col c0 c1 c2 c3, col c1 c2 c3 c0, col c2 c3 c0 c1, col c3 c0 c1 c2)

/-- `InvShiftRows` then `InvSubBytes` (FIPS 197 §5.3.1–5.3.2): output column `c`, row `r` is
`S⁻¹(in[(c − r) mod 4][r])`. -/
@[inline] def invSubShift (s : Block) : Block :=
  let (c0, c1, c2, c3) := s
  let col (a b c d : UInt32) : UInt32 :=
    (isb (a >>> 24) <<< 24) ||| (isb (b >>> 16) <<< 16) ||| (isb (c >>> 8) <<< 8) ||| isb d
  (col c0 c3 c2 c1, col c1 c0 c3 c2, col c2 c1 c0 c3, col c3 c2 c1 c0)

/-- `MixColumns` on every column. -/
@[inline] def mixBlock (s : Block) : Block :=
  (mixColumn s.1, mixColumn s.2.1, mixColumn s.2.2.1, mixColumn s.2.2.2)

/-- `InvMixColumns` on every column. -/
@[inline] def invMixBlock (s : Block) : Block :=
  (invMixColumn s.1, invMixColumn s.2.1, invMixColumn s.2.2.1, invMixColumn s.2.2.2)

/-- The AES cipher on one block (FIPS 197 §5.1, Figure 5). -/
def encryptBlock (k : Key) (b : Block) : Block := Id.run do
  let mut s := addRoundKey k 0 b
  for r in [1:k.rounds] do
    s := addRoundKey k r (mixBlock (subShift s))
  return addRoundKey k k.rounds (subShift s)

/-- The AES inverse cipher on one block (FIPS 197 §5.3, Figure 12). -/
def decryptBlock (k : Key) (b : Block) : Block := Id.run do
  let mut s := addRoundKey k k.rounds b
  for i in [1:k.rounds] do
    s := invMixBlock (addRoundKey k (k.rounds - i) (invSubShift s))
  return addRoundKey k 0 (invSubShift s)

/-- Checks that `data` is a whole number of blocks. -/
def checkBlocks (data : ByteArray) : Except Error Unit :=
  unless data.size % 16 = 0 do
    throw (.malformed data.size s!"AES data length {data.size} is not a multiple of 16")

/-- Checks that `iv` is one block. -/
def checkIv (iv : ByteArray) : Except Error Unit :=
  unless iv.size = 16 do
    throw (.malformed 0 s!"AES IV must be 16 bytes, got {iv.size}")

/-- Removes PKCS#7 padding strictly (RFC 5652 §6.3): the last byte `n` must be `1 … 16`,
the data at least `n` bytes long, and the last `n` bytes all `n`. The error offset is the
position of the offending byte. -/
def unpad (p : ByteArray) : Except Error ByteArray := do
  if p.size = 0 then throw (.malformed 0 "PKCS#7: no padding block")
  let n := (p[p.size - 1]?.getD 0).toNat
  unless 1 ≤ n ∧ n ≤ 16 ∧ n ≤ p.size do
    throw (.malformed (p.size - 1) s!"PKCS#7: bad padding length {n}")
  for i in [p.size - n:p.size] do
    unless (p[i]?.getD 0).toNat = n do
      throw (.malformed i "PKCS#7: inconsistent padding bytes")
  return p.extract 0 (p.size - n)

/-- AES-CBC decryption (SP 800-38A §6.2) of `data` with `key` (16, 24 or 32 bytes) and the
16-byte `iv`. With `pad`, PKCS#7 padding is checked and removed (strictly; see `unpad`).
`data` must be a multiple of 16 bytes (and non-empty when `pad`). -/
def cbcDecrypt (key iv data : ByteArray) (pad : Bool) : Except Error ByteArray := do
  let k ← expandKey key
  checkIv iv
  checkBlocks data
  let mut out := ByteArray.emptyWithCapacity data.size
  let mut prev := readBlock iv 0
  for i in [0:data.size / 16] do
    let c := readBlock data (16 * i)
    out := pushBlock out (xorBlock (decryptBlock k c) prev)
    prev := c
  if pad then unpad out else return out

/-- AES-CBC encryption (SP 800-38A §6.2) without padding: `data` must be a multiple of 16
bytes. Used by the revision 6 password hash (ISO 32000-2 Algorithm 2.B). -/
def cbcEncryptNoPad (key iv data : ByteArray) : Except Error ByteArray := do
  let k ← expandKey key
  checkIv iv
  checkBlocks data
  let mut out := ByteArray.emptyWithCapacity data.size
  let mut prev := readBlock iv 0
  for i in [0:data.size / 16] do
    let c := encryptBlock k (xorBlock (readBlock data (16 * i)) prev)
    out := pushBlock out c
    prev := c
  return out

/-- AES-ECB decryption (SP 800-38A §6.1) without padding: `data` must be a multiple of 16
bytes. Used for `/Perms` (ISO 32000-2 Algorithm 13). -/
def ecbDecrypt (key data : ByteArray) : Except Error ByteArray := do
  let k ← expandKey key
  checkBlocks data
  let mut out := ByteArray.emptyWithCapacity data.size
  for i in [0:data.size / 16] do
    out := pushBlock out (decryptBlock k (readBlock data (16 * i)))
  return out

/-- AES-ECB encryption (SP 800-38A §6.1) without padding: `data` must be a multiple of 16
bytes. -/
def ecbEncrypt (key data : ByteArray) : Except Error ByteArray := do
  let k ← expandKey key
  checkBlocks data
  let mut out := ByteArray.emptyWithCapacity data.size
  for i in [0:data.size / 16] do
    out := pushBlock out (encryptBlock k (readBlock data (16 * i)))
  return out

/-! ## Test vectors -/

/-- Decodes a hex string (whitespace ignored); test helper. -/
private def fromHex (s : String) : ByteArray := Id.run do
  let digit (c : Char) : UInt8 :=
    if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
    else 0
  let cs := (s.toList.filter (fun c => !c.isWhitespace)).toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push (digit (cs.getD (2 * i) '0') * 16 + digit (cs.getD (2 * i + 1) '0'))
  return out

/-- Whether `r` succeeded with the bytes of hex `h`. -/
private def okHex (r : Except Error ByteArray) (h : String) : Bool :=
  match r with
  | .ok b => b.data == (fromHex h).data
  | .error _ => false

/-- Whether `r` failed. -/
private def isErr (r : Except Error ByteArray) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

#guard (fromHex "00 0aFf10").data == #[0x00, 0x0a, 0xff, 0x10]
-- `invSbox` is the two-sided inverse of `sbox`.
#guard (List.range 256).all fun i => (invSbox.getD (sbox.getD i 0).toNat 0).toNat == i
#guard (List.range 256).all fun i => (sbox.getD (invSbox.getD i 0).toNat 0).toNat == i
#guard sbox.size == 256 && invSbox.size == 256
-- FIPS 197 Appendix A.1: the last AES-128 round-key word of key 2b7e1516…
#guard ((expandKey (fromHex "2b7e151628aed2a6abf7158809cf4f3c")).toOption.map
  (fun k => k.w.getD 43 0)) == some 0xb6630ca6

/-- FIPS 197 Appendix C plaintext. -/
private def pC : String := "00112233445566778899aabbccddeeff"

-- FIPS 197 C.1 (AES-128), C.2 (AES-192), C.3 (AES-256): encrypt and decrypt.
#guard okHex (ecbEncrypt (fromHex "000102030405060708090a0b0c0d0e0f") (fromHex pC))
  "69c4e0d86a7b0430d8cdb78070b4c55a"
#guard okHex (ecbDecrypt (fromHex "000102030405060708090a0b0c0d0e0f")
  (fromHex "69c4e0d86a7b0430d8cdb78070b4c55a")) pC
#guard okHex (ecbEncrypt (fromHex "000102030405060708090a0b0c0d0e0f1011121314151617")
  (fromHex pC)) "dda97ca4864cdfe06eaf70a0ec0d7191"
#guard okHex (ecbDecrypt (fromHex "000102030405060708090a0b0c0d0e0f1011121314151617")
  (fromHex "dda97ca4864cdfe06eaf70a0ec0d7191")) pC
#guard okHex (ecbEncrypt
  (fromHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f") (fromHex pC))
  "8ea2b7ca516745bfeafc49904b496089"
#guard okHex (ecbDecrypt
  (fromHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
  (fromHex "8ea2b7ca516745bfeafc49904b496089")) pC

/-- SP 800-38A F.1/F.2 plaintext (four blocks). -/
private def p38a : String :=
  "6bc1bee22e409f96e93d7e117393172a ae2d8a571e03ac9c9eb76fac45af8e51" ++
  "30c81c46a35ce411e5fbc1191a0a52ef f69f2445df4f9b17ad2b417be66c3710"

/-- SP 800-38A AES-128 key. -/
private def k128 : String := "2b7e151628aed2a6abf7158809cf4f3c"

/-- SP 800-38A AES-256 key. -/
private def k256 : String := "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4"

/-- SP 800-38A CBC IV. -/
private def iv38a : String := "000102030405060708090a0b0c0d0e0f"

/-- SP 800-38A F.2.1 / F.2.2 ciphertext (CBC-AES128). -/
private def cCbc128 : String :=
  "7649abac8119b246cee98e9b12e9197d 5086cb9b507219ee95db113a917678b2" ++
  "73bed6b8e3c1743b7116e69e22229516 3ff1caa1681fac09120eca307586e1a7"

/-- SP 800-38A F.2.5 / F.2.6 ciphertext (CBC-AES256). -/
private def cCbc256 : String :=
  "f58c4c04d6e5f1ba779eabfb5f7bfbd6 9cfc4e967edb808d679f777bc6702c7d" ++
  "39f23369a9d9bacfa530e26304231461 b2eb05e2c39be9fcda6c19078c6a9d1b"

-- SP 800-38A F.1.1 / F.1.2 (ECB-AES128).
#guard okHex (ecbEncrypt (fromHex k128) (fromHex p38a))
  ("3ad77bb40d7a3660a89ecaf32466ef97 f5d3d58503b9699de785895a96fdbaaf" ++
   "43b1cd7f598ece23881b00e3ed030688 7b0c785e27e8ad3f8223207104725dd4")
-- SP 800-38A F.2.1 / F.2.2 (CBC-AES128) and F.2.5 / F.2.6 (CBC-AES256).
#guard okHex (cbcEncryptNoPad (fromHex k128) (fromHex iv38a) (fromHex p38a)) cCbc128
#guard okHex (cbcDecrypt (fromHex k128) (fromHex iv38a) (fromHex cCbc128) false) p38a
#guard okHex (cbcEncryptNoPad (fromHex k256) (fromHex iv38a) (fromHex p38a)) cCbc256
#guard okHex (cbcDecrypt (fromHex k256) (fromHex iv38a) (fromHex cCbc256) false) p38a

/-- CBC-AES128 encryption (SP 800-38A key and IV) of `p` (hex) with PKCS#7-style tail `tail`
(hex) appended as given — used to build padding test cases. -/
private def encWithTail (p tail : String) : ByteArray :=
  match cbcEncryptNoPad (fromHex k128) (fromHex iv38a) (fromHex (p ++ tail)) with
  | .ok c => c
  | .error _ => ByteArray.empty

-- PKCS#7: valid padding of 1, 4 and 16 bytes is removed.
#guard okHex (cbcDecrypt (fromHex k128) (fromHex iv38a)
  (encWithTail "000102030405060708090a0b0c0d0e" "01") true) "000102030405060708090a0b0c0d0e"
#guard okHex (cbcDecrypt (fromHex k128) (fromHex iv38a)
  (encWithTail "68656c6c6f2c20776f726c64" "04040404") true) "68656c6c6f2c20776f726c64"
#guard okHex (cbcDecrypt (fromHex k128) (fromHex iv38a)
  (encWithTail p38a "10101010101010101010101010101010") true) p38a
-- PKCS#7: inconsistent pad bytes, pad byte 0, pad byte > 16 are rejected.
#guard isErr (cbcDecrypt (fromHex k128) (fromHex iv38a)
  (encWithTail "68656c6c6f2c20776f726c64" "04030404") true)
#guard isErr (cbcDecrypt (fromHex k128) (fromHex iv38a)
  (encWithTail "000102030405060708090a0b0c0d0e" "00") true)
#guard isErr (cbcDecrypt (fromHex k128) (fromHex iv38a)
  (encWithTail "000102030405060708090a0b0c0d0e" "11") true)
-- Without `pad`, the same data decrypts and the tail is kept.
#guard okHex (cbcDecrypt (fromHex k128) (fromHex iv38a)
  (encWithTail "000102030405060708090a0b0c0d0e" "00") false) "000102030405060708090a0b0c0d0e00"
-- Shape errors: empty padded input, partial block, bad IV, bad key length.
#guard isErr (cbcDecrypt (fromHex k128) (fromHex iv38a) ByteArray.empty true)
#guard okHex (cbcDecrypt (fromHex k128) (fromHex iv38a) ByteArray.empty false) ""
#guard isErr (cbcDecrypt (fromHex k128) (fromHex iv38a) (fromHex "00112233") false)
#guard isErr (cbcDecrypt (fromHex k128) (fromHex "0001") (fromHex cCbc128) false)
#guard isErr (cbcDecrypt (fromHex "0001020304") (fromHex iv38a) (fromHex cCbc128) false)
#guard isErr (ecbEncrypt (fromHex k128) (fromHex "00"))

end SafePdf.Core.Crypt.Aes
