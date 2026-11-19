/-!
# SHA-256, SHA-384, SHA-512 (Plan.md §6 Phase 4, task 4.3a; FIPS 180-4)

The SHA-2 hash functions needed by the PDF standard security handler revision 6
(ISO 32000-2 §7.6.4.3.4, Algorithm 2.B): the hash rounds use SHA-256, SHA-384 and SHA-512.

Plan.md §6 Phase 4 asks for the smallest trusted implementation, checked against published
test vectors; a correctness proof is out of scope. Every loop runs over a `Std.Range` (no
`partial`, no `while`) and every byte or table access is bounds-checked with a default
(`b[i]?.getD 0`, `Array.getD`), never `!`-indexed.

SHA-256 works on `UInt32` words and 64-byte blocks (FIPS 180-4 §6.2); SHA-512 on `UInt64`
words and 128-byte blocks (§6.4); SHA-384 is SHA-512 with other initial values, truncated to
48 bytes (§6.5). Cost is linear: the message is padded once, each block is expanded into
its message schedule and mixed.
-/

namespace SafePdf.Core.Crypt.Sha2

/-- Pads a message as FIPS 180-4 §5.1: a `0x80` byte, zeros, then the bit length as a
`lenBytes`-byte big-endian number, so the size becomes a multiple of `block`. Used with
`(block, lenBytes) = (64, 8)` for SHA-256 and `(128, 16)` for SHA-384/512. -/
def pad (msg : ByteArray) (block lenBytes : Nat) : ByteArray := Id.run do
  let used := msg.size % block + 1 + lenBytes
  let zeros := (block - used % block) % block
  let mut out := ByteArray.emptyWithCapacity (msg.size + 1 + zeros + lenBytes)
  out := out ++ msg
  out := out.push 0x80
  for _ in [0:zeros] do
    out := out.push 0
  let bits := msg.size * 8
  for k in [0:lenBytes] do
    out := out.push (bits >>> (8 * (lenBytes - 1 - k))).toUInt8
  return out

/-! ## SHA-256 -/

/-- The 64 SHA-256 round constants (FIPS 180-4 §4.2.2). -/
def k256 : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The SHA-256 initial hash value (FIPS 180-4 §5.3.3). -/
def iv256 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Right rotation of a 32-bit word by `n` bits (`0 < n < 32`). -/
@[inline] def rotr32 (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The big-endian 32-bit word at byte offset `i` (out-of-range bytes read as 0). -/
@[inline] def be32 (b : ByteArray) (i : Nat) : UInt32 :=
  ((b[i]?.getD 0).toUInt32 <<< 24) ||| ((b[i+1]?.getD 0).toUInt32 <<< 16) |||
    ((b[i+2]?.getD 0).toUInt32 <<< 8) ||| (b[i+3]?.getD 0).toUInt32

/-- Processes the 64-byte block at byte offset `off` of `msg` (FIPS 180-4 §6.2.2). The state
`h` holds eight words. -/
def compress256 (h : Array UInt32) (msg : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    w := w.push (be32 msg (off + 4 * t))
  for t in [16:64] do
    let x15 := w.getD (t - 15) 0
    let x2 := w.getD (t - 2) 0
    let s0 := rotr32 x15 7 ^^^ rotr32 x15 18 ^^^ (x15 >>> 3)
    let s1 := rotr32 x2 17 ^^^ rotr32 x2 19 ^^^ (x2 >>> 10)
    w := w.push (s1 + w.getD (t - 7) 0 + s0 + w.getD (t - 16) 0)
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  let mut f := h.getD 5 0
  let mut g := h.getD 6 0
  let mut hh := h.getD 7 0
  for t in [0:64] do
    let bs1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + bs1 + ch + k256.getD t 0 + w.getD t 0
    let bs0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := bs0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h.getD 0 0 + a, h.getD 1 0 + b, h.getD 2 0 + c, h.getD 3 0 + d,
    h.getD 4 0 + e, h.getD 5 0 + f, h.getD 6 0 + g, h.getD 7 0 + hh]

/-- Serializes the first `n` words of `h` big-endian (`n` defaults to all eight). -/
def words32Be (h : Array UInt32) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (4 * n)
  for i in [0:n] do
    let w := h.getD i 0
    out := (((out.push (w >>> 24).toUInt8).push (w >>> 16).toUInt8).push (w >>> 8).toUInt8).push
      w.toUInt8
  return out

/-- The SHA-256 digest of `msg` (FIPS 180-4 §6.2): 32 bytes. -/
def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let p := pad msg 64 8
  let mut h := iv256
  for blk in [0:p.size / 64] do
    h := compress256 h p (64 * blk)
  return words32Be h 8

/-! ## SHA-512 and SHA-384 -/

/-- The 80 SHA-512 round constants (FIPS 180-4 §4.2.3). -/
def k512 : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- The SHA-512 initial hash value (FIPS 180-4 §5.3.5). -/
def iv512 : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The SHA-384 initial hash value (FIPS 180-4 §5.3.4). -/
def iv384 : Array UInt64 := #[
  0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
  0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

/-- Right rotation of a 64-bit word by `n` bits (`0 < n < 64`). -/
@[inline] def rotr64 (x n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- The big-endian 64-bit word at byte offset `i` (out-of-range bytes read as 0). -/
@[inline] def be64 (b : ByteArray) (i : Nat) : UInt64 :=
  ((be32 b i).toUInt64 <<< 32) ||| (be32 b (i + 4)).toUInt64

/-- Processes the 128-byte block at byte offset `off` of `msg` (FIPS 180-4 §6.4.2). The
state `h` holds eight words. -/
def compress512 (h : Array UInt64) (msg : ByteArray) (off : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.mkEmpty 80
  for t in [0:16] do
    w := w.push (be64 msg (off + 8 * t))
  for t in [16:80] do
    let x15 := w.getD (t - 15) 0
    let x2 := w.getD (t - 2) 0
    let s0 := rotr64 x15 1 ^^^ rotr64 x15 8 ^^^ (x15 >>> 7)
    let s1 := rotr64 x2 19 ^^^ rotr64 x2 61 ^^^ (x2 >>> 6)
    w := w.push (s1 + w.getD (t - 7) 0 + s0 + w.getD (t - 16) 0)
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  let mut f := h.getD 5 0
  let mut g := h.getD 6 0
  let mut hh := h.getD 7 0
  for t in [0:80] do
    let bs1 := rotr64 e 14 ^^^ rotr64 e 18 ^^^ rotr64 e 41
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + bs1 + ch + k512.getD t 0 + w.getD t 0
    let bs0 := rotr64 a 28 ^^^ rotr64 a 34 ^^^ rotr64 a 39
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := bs0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h.getD 0 0 + a, h.getD 1 0 + b, h.getD 2 0 + c, h.getD 3 0 + d,
    h.getD 4 0 + e, h.getD 5 0 + f, h.getD 6 0 + g, h.getD 7 0 + hh]

/-- Serializes the first `n` words of `h` big-endian. -/
def words64Be (h : Array UInt64) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (8 * n)
  for i in [0:n] do
    let w := h.getD i 0
    for k in [0:8] do
      out := out.push (w >>> (8 * (7 - k)).toUInt64).toUInt8
  return out

/-- The SHA-512 compression run over a whole message, from initial value `iv`. -/
def sha512Core (iv : Array UInt64) (msg : ByteArray) : Array UInt64 := Id.run do
  let p := pad msg 128 16
  let mut h := iv
  for blk in [0:p.size / 128] do
    h := compress512 h p (128 * blk)
  return h

/-- The SHA-512 digest of `msg` (FIPS 180-4 §6.4): 64 bytes. -/
def sha512 (msg : ByteArray) : ByteArray := words64Be (sha512Core iv512 msg) 8

/-- The SHA-384 digest of `msg` (FIPS 180-4 §6.5): 48 bytes, the first six words of the
SHA-512 computation from the SHA-384 initial value. -/
def sha384 (msg : ByteArray) : ByteArray := words64Be (sha512Core iv384 msg) 6

/-! ## Test vectors (FIPS 180-4 / NIST CSRC examples) -/

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

/-- Whether `f s` equals the hex digest `h`. -/
private def check (f : ByteArray → ByteArray) (s : ByteArray) (h : String) : Bool :=
  (f s).data == (fromHex h).data

/-- The deterministic test message `(7 i + 3) mod 256`, `i < n`. -/
private def seqBytes (n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun i => ((7 * i + 3) % 256).toUInt8⟩

/-- The 448-bit two-block example message of FIPS 180-4 (SHA-256). -/
private def m448 : ByteArray := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8

/-- The 896-bit example message of FIPS 180-4 (SHA-384/512). -/
private def m896 : ByteArray :=
  ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
    "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu").toUTF8

#guard (fromHex "00 0aFf10").data == #[0x00, 0x0a, 0xff, 0x10]
#guard m448.size == 56 && m896.size == 112
#guard check sha256 "".toUTF8 "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard check sha256 "abc".toUTF8
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard check sha256 m448 "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard check sha256 m896 "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
#guard check sha384 "".toUTF8 ("38b060a751ac96384cd9327eb1b1e36a21fdb71114be0743" ++
  "4c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b")
#guard check sha384 "abc".toUTF8 ("cb00753f45a35e8bb5a03d699ac65007272c32ab0eded163" ++
  "1a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7")
#guard check sha384 m896 ("09330c33f71147e83d192fc782cd1b4753111b173b3b05d2" ++
  "2fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039")
#guard check sha512 "".toUTF8 ("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce" ++
  "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
#guard check sha512 "abc".toUTF8 ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
  "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
#guard check sha512 m896 ("8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018" ++
  "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")
-- Block-boundary lengths (reference: Python `hashlib`).
#guard check sha256 (seqBytes 55) "e7313d333c272e639f790978283f9eb392e843d0f29b7016828bb1daa4aac70b"
#guard check sha256 (seqBytes 63) "81c80242132f230c3bd41b3e63bbcff16107339549214a99614ff26664625055"
#guard check sha256 (seqBytes 64) "39e3d7b6b5d075d37d053ad89b24b41bef4f3c29760c84447cab3f3be1882241"
#guard check sha256 (seqBytes 200)
  "2c7e18c942ef065b526a2d4e5546283749cd3ddfb51d8fc71f42717363685f46"
#guard check sha384 (seqBytes 111) ("341388a9dc2275074e90cf394323761919761c805fd9e370" ++
  "977c9966a0e8c81a52135f02577670b0071638a4a26dbc31")
#guard check sha384 (seqBytes 128) ("e8480e9c4dd90f88104a79cbaccec48edbd798a142b4f241" ++
  "d726dc252f1502350e824c7d18dadd59d7d716919fb8f9bf")
#guard check sha512 (seqBytes 111) ("68cffa6d0d76f309c9ce0d35280939f8e25990c43b7b086ccdf709be35b07d4d" ++
  "dba599541ff2b1c19d34ea49aeafb9659adb7ac3c0b078bb30a22d57fc6687ef")
#guard check sha512 (seqBytes 112) ("d0865c524d1dddf7c23b799c413f5adcd7caefd3f66a9b49750ec81066012c25" ++
  "a8bcf94ddea6dc525691673097ca40e0101e897fc97218cfdb0704084e2bef4b")
#guard check sha512 (seqBytes 127) ("e0b6a20f1c0c88970a9340152cd5a1c1ecf3d3b8de55102741879438079473540" ++
  "133b812706e5dbec322c8c9523b6fc8c6d16ee626e87ad5fe3d2916afedc369")
#guard check sha512 (seqBytes 128) ("99b16f17aa0b969a5b8f08f367719d516e330ccd2660b6f0688ec031dbc783de" ++
  "50a1cd185a2568dba75070a2403d17d4741d163578515dfd2ff756ddfe4d47b1")
#guard check sha512 (seqBytes 200) ("cca3c0276046ef9f2897bdfc3ec330f77f4959914b1462bd581b232ddb3e9aa9" ++
  "8acf5f5a2b21c7f49d2e43721daa61a2b5cee6af6052dfeb766e66ddb0d1719c")

end SafePdf.Core.Crypt.Sha2
