/-!
# MD5 (Plan.md §6 Phase 4, task 4.3a; RFC 1321)

The MD5 message digest, needed by the PDF standard security handler (ISO 32000-2 §7.6.4):
key derivation for revisions 2–4 (Algorithm 2, including the 50-fold MD5 loop of R3/R4)
and the per-object keys of Algorithm 1.

Plan.md §6 Phase 4 asks for the smallest trusted implementation, checked against published
test vectors; a correctness proof is out of scope. The implementation is total: every loop
runs over a `Std.Range` (no `partial`, no `while`), and every byte access is bounds-checked
with a default (`b[i]?.getD 0`), never `!`-indexed.

Cost is linear: the message is padded once (one copy), then each 64-byte block is read into
sixteen `UInt32` words and mixed with `UInt32` arithmetic.
-/

namespace SafePdf.Core.Crypt.Md5

/-- The 64 additive constants `K[i] = ⌊|sin(i + 1)| · 2³²⌋` of RFC 1321 §3.4. -/
def kTable : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

/-- The per-step left-rotation amounts of RFC 1321 §3.4 (four per round, repeated). -/
def shiftTable : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- Left rotation of a 32-bit word by `n` bits (`0 < n < 32`). -/
@[inline] def rotl (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- The little-endian 32-bit word at byte offset `i` (out-of-range bytes read as 0). -/
@[inline] def le32 (b : ByteArray) (i : Nat) : UInt32 :=
  (b[i]?.getD 0).toUInt32 ||| ((b[i+1]?.getD 0).toUInt32 <<< 8) |||
    ((b[i+2]?.getD 0).toUInt32 <<< 16) ||| ((b[i+3]?.getD 0).toUInt32 <<< 24)

/-- Pads a message as RFC 1321 §3.1–3.2: a `0x80` byte, zeros up to 56 mod 64, then the
bit length modulo 2⁶⁴ as eight little-endian bytes. The result's size is a multiple of 64. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let zeros := (55 + 64 - msg.size % 64) % 64
  let mut out := ByteArray.emptyWithCapacity (msg.size + zeros + 9)
  out := out ++ msg
  out := out.push 0x80
  for _ in [0:zeros] do
    out := out.push 0
  let bits := msg.size * 8
  for k in [0:8] do
    out := out.push (bits >>> (8 * k)).toUInt8
  return out

/-- The MD5 chaining state: four 32-bit words `(A, B, C, D)`. -/
structure State where
  /-- Word A. -/
  a : UInt32
  /-- Word B. -/
  b : UInt32
  /-- Word C. -/
  c : UInt32
  /-- Word D. -/
  d : UInt32

/-- The initial state of RFC 1321 §3.3. -/
def State.init : State := ⟨0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476⟩

/-- Processes the 64-byte block at byte offset `off` of `msg` (RFC 1321 §3.4). -/
def compress (st : State) (msg : ByteArray) (off : Nat) : State := Id.run do
  let mut m : Array UInt32 := Array.mkEmpty 16
  for j in [0:16] do
    m := m.push (le32 msg (off + 4 * j))
  let mut a := st.a
  let mut b := st.b
  let mut c := st.c
  let mut d := st.d
  for i in [0:64] do
    let (f, g) :=
      if i < 16 then ((b &&& c) ||| (~~~b &&& d), i)
      else if i < 32 then ((d &&& b) ||| (~~~d &&& c), (5 * i + 1) % 16)
      else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
      else (c ^^^ (b ||| ~~~d), (7 * i) % 16)
    let f := f + a + kTable.getD i 0 + m.getD g 0
    a := d
    d := c
    c := b
    b := b + rotl f (shiftTable.getD i 1)
  return ⟨st.a + a, st.b + b, st.c + c, st.d + d⟩

/-- Pushes a 32-bit word as four little-endian bytes. -/
@[inline] def pushLe32 (out : ByteArray) (w : UInt32) : ByteArray :=
  ((((out.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push
    (w >>> 24).toUInt8)

/-- Serializes the final state as the 16-byte digest (A, B, C, D, each little-endian). -/
def State.digest (st : State) : ByteArray :=
  pushLe32 (pushLe32 (pushLe32 (pushLe32 (ByteArray.emptyWithCapacity 16) st.a) st.b) st.c) st.d

/-- The MD5 digest of `msg` (RFC 1321): always 16 bytes (`md5_size`). -/
def md5 (msg : ByteArray) : ByteArray := Id.run do
  let p := pad msg
  let mut st := State.init
  for blk in [0:p.size / 64] do
    st := compress st p (64 * blk)
  return st.digest

/-- An MD5 digest is 16 bytes long. -/
theorem md5_size (msg : ByteArray) : (md5 msg).size = 16 := by
  simp [md5, State.digest, pushLe32, ByteArray.size_push]
  rfl

/-! ## Test vectors (RFC 1321 Appendix A.5) -/

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

/-- Whether `md5 s` equals the hex digest `h`. -/
private def check (s : ByteArray) (h : String) : Bool := (md5 s).data == (fromHex h).data

/-- The deterministic test message `(7 i + 3) mod 256`, `i < n`. -/
private def seqBytes (n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun i => ((7 * i + 3) % 256).toUInt8⟩

#guard (fromHex "00 0aFf10").data == #[0x00, 0x0a, 0xff, 0x10]
#guard check "".toUTF8 "d41d8cd98f00b204e9800998ecf8427e"
#guard check "a".toUTF8 "0cc175b9c0f1b6a831c399e269772661"
#guard check "abc".toUTF8 "900150983cd24fb0d6963f7d28e17f72"
#guard check "message digest".toUTF8 "f96b697d7cb7938d525a2f31aaf161d0"
#guard check "abcdefghijklmnopqrstuvwxyz".toUTF8 "c3fcd3d76192e4007dfb496cca67e13b"
#guard check "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toUTF8
  "d174ab98d277d9f5a5611c2c9f419d9f"
#guard check
  "12345678901234567890123456789012345678901234567890123456789012345678901234567890".toUTF8
  "57edf4a22be3c955ac49da2e2107b67a"
-- Block-boundary lengths (reference: Python `hashlib.md5`).
#guard check (seqBytes 55) "52c0e574e1198de5fe3f8f11440dcb1b"
#guard check (seqBytes 63) "a62f6d59e837867693f042f5b8f5a236"
#guard check (seqBytes 64) "7160b8fb5e9e4023d549c3971fbaeead"
#guard check (seqBytes 128) "10b2da1a82f16d99a81a7203fe9f02cb"
#guard check (seqBytes 200) "4c79b81ac94bad7a875519ce6b964c66"

end SafePdf.Core.Crypt.Md5
