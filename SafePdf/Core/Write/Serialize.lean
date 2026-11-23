import SafePdf.Core.Print
import SafePdf.Core.Xref

/-!
# Serializer for incremental updates (Plan.md §4 S8/C7, §6 Phase 9 "Persistence"; task 9.5a)

The byte-level pieces of an incremental update (ISO 32000-2 §7.5.6): indirect objects, a
classic cross-reference section with its trailer, the rows of a cross-reference stream
(§7.5.8), and the `startxref` / `%%EOF` tail. Everything is a pure, total function to
`List UInt8` (small: an update holds a handful of objects).

**No new object printer.** Direct objects are written by the Phase 1 printer
`Core.Print.printObj` (task 1.7), whose round trip `parse (print o) = o` is proved
(`Spec.RoundTripCore.parseObject_print`, milestone M1). `serialize` is that printer;
`Spec.Write.serialize_roundtrip` restates the theorem for it.

## Byte layout

* S1. Indirect object: `n g obj` LF, the printed object, LF `endobj` LF (§7.3.10). A stream
  object (used only for the cross-reference stream): `n g obj` LF, the printed dictionary,
  LF `stream` CR LF, the raw data, LF `endstream` LF `endobj` LF (§7.3.8: `stream` is followed
  by CR LF; the EOL before `endstream` is not counted in `/Length`).
* S2. Classic section (§7.5.4): `xref` LF, then per subsection `start count` LF and
  `count` entries of exactly 20 bytes `oooooooooo ggggg n` CR LF (offset zero-padded to ten
  digits, generation to five), then `trailer` LF, the printed trailer dictionary, LF.
* S3. Tail (§7.5.5): `startxref` LF, the offset, LF `%%EOF` LF.
* S4. Subsections are the maximal runs of consecutive object numbers of a sorted list
  (`runs`).
* S5. Cross-reference stream rows (§7.5.8.3): one row per entry, fields `[1, w2, 2]` bytes,
  big-endian: type `1`, the offset in `w2` bytes (`byteWidth` of the largest offset), the
  generation in two bytes.
-/

namespace SafePdf.Core.Write.Serialize

open SafePdf

/-- **The object serializer**: the Phase 1 printer (`Core.Print.printObj`). Its round trip
through the strict parser is `Spec.RoundTripCore.parseObject_print`. -/
def serialize (o : PdfObject) : List UInt8 := Print.printObj o

/-- ASCII bytes of a string literal (only used with ASCII literals). -/
def ascii (s : String) : List UInt8 := s.toUTF8.toList

/-- Decimal digits of a natural number (the printer's `natDigits`). -/
def dec (n : Nat) : List UInt8 := Print.natDigits n

/-- Decimal digits of `n`, left-padded with `0` to at least `w` digits. -/
def decPad (w n : Nat) : List UInt8 :=
  List.replicate (w - (dec n).length) 48 ++ dec n

/-- Line feed. -/
def lf : List UInt8 := [10]

/-- S1. An indirect object `num gen obj … endobj` holding a direct object. -/
def indirect (num gen : Nat) (o : PdfObject) : List UInt8 :=
  dec num ++ [32] ++ dec gen ++ ascii " obj\n" ++ serialize o ++ ascii "\nendobj\n"

/-- S1. A stream object `num gen obj << … >> stream … endstream endobj` with raw `data`. -/
def streamObj (num gen : Nat) (d : Dict) (data : List UInt8) : List UInt8 :=
  dec num ++ [32] ++ dec gen ++ ascii " obj\n" ++ serialize (.dict d) ++
    ascii "\nstream\r\n" ++ data ++ ascii "\nendstream\nendobj\n"

/-- S2. One 20-byte in-use entry: ten offset digits, SP, five generation digits, SP, `n`,
CR LF. Offsets above 10 digits do not fit (the parser rejects them; never produced for
inputs within `Limits.maxInputBytes`). -/
def inUseEntry (off gen : Nat) : List UInt8 :=
  decPad 10 off ++ [32] ++ decPad 5 gen ++ [32, 110, 13, 10]

/-- S4. Group a list of `(number, value)` pairs, sorted by number, into maximal runs of
consecutive numbers: `(first number, values)`. -/
def runs {α : Type} : List (Nat × α) → List (Nat × List α)
  | [] => []
  | (n, a) :: rest =>
    match runs rest with
    | (m, as) :: rs => if m = n + 1 then (n, a :: as) :: rs else (n, [a]) :: (m, as) :: rs
    | [] => [(n, [a])]

/-- S2. The subsections of a classic section for sorted in-use entries
`(num, offset, gen)`. -/
def subsections (es : List (Nat × Nat × Nat)) : List UInt8 :=
  (runs es).flatMap fun (start, xs) =>
    dec start ++ [32] ++ dec xs.length ++ lf ++ xs.flatMap fun (off, gen) => inUseEntry off gen

/-- S2. A classic cross-reference section with its trailer dictionary. -/
def xrefTable (es : List (Nat × Nat × Nat)) (trailer : Dict) : List UInt8 :=
  ascii "xref\n" ++ subsections es ++ ascii "trailer\n" ++ serialize (.dict trailer) ++ lf

/-- S3. The file tail pointing at the section at `off`. -/
def tail (off : Nat) : List UInt8 := ascii "startxref\n" ++ dec off ++ ascii "\n%%EOF\n"

/-- S5. Bytes needed to hold `n` big-endian (at least 1). -/
def byteWidth (n : Nat) : Nat :=
  if n < 256 then 1 else byteWidth (n / 256) + 1
termination_by n
decreasing_by omega

/-- S5. `n` as `w` big-endian bytes (high bytes beyond `w` are dropped). -/
def beBytes (w n : Nat) : List UInt8 :=
  (List.range w).reverse.map fun i => UInt8.ofNat (n / 256 ^ i % 256)

/-- S5. The rows of a cross-reference stream for sorted in-use entries `(num, offset, gen)`
with offset width `w2`. -/
def streamRows (w2 : Nat) (es : List (Nat × Nat × Nat)) : List UInt8 :=
  es.flatMap fun (_, off, gen) => [1] ++ beBytes w2 off ++ beBytes 2 gen

/-- S5. The `/Index` array of a cross-reference stream: `[start count …]` per run. -/
def streamIndex (es : List (Nat × Nat × Nat)) : List PdfObject :=
  (runs es).flatMap fun (start, xs) => [.int start, .int xs.length]

/-! ## Compile-time checks -/

section Tests

#guard inUseEntry 1234 0 == ascii "0000001234 00000 n\r\n"
#guard (inUseEntry 1234 7).length == 20
#guard decPad 5 65535 == ascii "65535"
#guard runs [(3, 'a'), (4, 'b'), (7, 'c'), (8, 'd'), (10, 'e')] ==
  [(3, ['a', 'b']), (7, ['c', 'd']), (10, ['e'])]
#guard subsections [(5, 17, 0), (6, 40, 2)] ==
  ascii "5 2\n0000000017 00000 n\r\n0000000040 00002 n\r\n"
#guard byteWidth 0 == 1 && byteWidth 255 == 1 && byteWidth 256 == 2 && byteWidth 65536 == 3
#guard beBytes 3 0x012345 == [0x01, 0x23, 0x45]
#guard beBytes 2 7 == [0, 7]
#guard streamRows 2 [(9, 0x1234, 0)] == [1, 0x12, 0x34, 0, 0]
#guard streamIndex [(3, 1, 0), (4, 2, 0), (9, 3, 0)] == [.int 3, .int 2, .int 9, .int 1]
#guard indirect 12 0 (.dict [(Name.ofString "A", .int 1)]) == ascii "12 0 obj\n<< /A 1 >>\nendobj\n"
#guard tail 99 == ascii "startxref\n99\n%%EOF\n"

end Tests

end SafePdf.Core.Write.Serialize
