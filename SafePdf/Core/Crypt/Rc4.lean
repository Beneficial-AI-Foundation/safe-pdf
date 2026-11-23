/-!
# RC4 (Plan.md §6 Phase 4, task 4.3a; the ARCFOUR stream cipher, RFC 6229 test vectors)

The RC4 stream cipher used by the PDF standard security handler revisions 2–4
(ISO 32000-2 §7.6.3, `/V 1`, `/V 2` and the `/V2` crypt filter), with keys of 5 to 16 bytes.
Encryption and decryption are the same operation: XOR with the keystream.

Plan.md §6 Phase 4 asks for the smallest trusted implementation, checked against published
test vectors; a correctness proof is out of scope. The permutation is an `Array UInt8` of
256 entries indexed by `UInt8` values (so every index is in range); reads use `Array.getD`,
writes `Array.setIfInBounds` — no `!`-indexing. Every loop runs over a `Std.Range`.

## Key length

* A key of 1–256 bytes is used as RC4 specifies (the key-scheduling step reads
  `key[i mod keylen]` for `i < 256`, so bytes past 256 are never used).
* An **empty key** is not an error: it schedules as the one-byte key `0x00` (equivalently,
  any all-zero key). The PDF handler never derives an empty key — its key length is
  `max(5, min(16, n + 5))` bytes — so this only fixes the meaning of a degenerate call.
-/

namespace SafePdf.Core.Crypt.Rc4

/-- The RC4 key-scheduling algorithm: the permutation of `0 … 255` determined by `key`. -/
def schedule (key : ByteArray) : Array UInt8 := Id.run do
  let mut s : Array UInt8 := (Array.range 256).map (·.toUInt8)
  let len := key.size
  let mut j : UInt8 := 0
  for i in [0:256] do
    let si := s.getD i 0
    let k := if len = 0 then 0 else key[i % len]?.getD 0
    j := j + si + k
    let sj := s.getD j.toNat 0
    s := (s.setIfInBounds i sj).setIfInBounds j.toNat si
  return s

/-- RC4 of `data` under `key`: `data` XOR the keystream. The same call encrypts and decrypts.
The output has the size of `data`. -/
def rc4 (key data : ByteArray) : ByteArray := Id.run do
  let mut s := schedule key
  let mut i : UInt8 := 0
  let mut j : UInt8 := 0
  let mut out := ByteArray.emptyWithCapacity data.size
  for n in [0:data.size] do
    i := i + 1
    let si := s.getD i.toNat 0
    j := j + si
    let sj := s.getD j.toNat 0
    s := (s.setIfInBounds i.toNat sj).setIfInBounds j.toNat si
    let k := s.getD (si + sj).toNat 0
    out := out.push ((data[n]?.getD 0) ^^^ k)
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

/-- The first `n` keystream bytes for `key` (RC4 of `n` zero bytes). -/
private def keystream (key : ByteArray) (n : Nat) : ByteArray :=
  rc4 key ⟨Array.replicate n 0⟩

/-- Whether the keystream bytes `off … off + 15` for the hex `key` equal the hex `h`. -/
private def checkKs (key : String) (off : Nat) (h : String) : Bool :=
  ((keystream (fromHex key) (off + 16)).extract off (off + 16)).data == (fromHex h).data

/-- Whether `rc4 key pt` equals the hex `h`. -/
private def check (key pt : String) (h : String) : Bool :=
  (rc4 key.toUTF8 pt.toUTF8).data == (fromHex h).data

#guard (fromHex "00 0aFf10").data == #[0x00, 0x0a, 0xff, 0x10]
-- The schedule is a permutation.
#guard ((schedule "Key".toUTF8).qsort (· < ·)) == (Array.range 256).map (·.toUInt8)
-- RFC 6229 §2, 40-bit key 0x0102030405, offsets 0 and 16.
#guard checkKs "0102030405" 0 "b2396305f03dc027ccc3524a0a1118a8"
#guard checkKs "0102030405" 16 "6982944f18fc82d589c403a47a0d0919"
-- RFC 6229 §2, 128-bit key 0x0102…10, offsets 0 and 16.
#guard checkKs "0102030405060708090a0b0c0d0e0f10" 0 "9ac7cc9a609d1ef7b2932899cde41b97"
#guard checkKs "0102030405060708090a0b0c0d0e0f10" 16 "5248c4959014126a6e8a84f11d1a9e1c"
-- Classic ARCFOUR examples.
#guard check "Key" "Plaintext" "bbf316e8d940af0ad3"
#guard check "Wiki" "pedia" "1021bf0420"
#guard check "Secret" "Attack at dawn" "45a01f645fc35b383552544b9bf5"
-- Decryption is encryption.
#guard (rc4 "Key".toUTF8 (rc4 "Key".toUTF8 "Plaintext".toUTF8)).data == "Plaintext".toUTF8.data
-- The empty key schedules as the key 0x00.
#guard (rc4 ByteArray.empty "abc".toUTF8).data == (rc4 (fromHex "00") "abc".toUTF8).data
#guard (rc4 "k".toUTF8 ByteArray.empty).size == 0

end SafePdf.Core.Crypt.Rc4
