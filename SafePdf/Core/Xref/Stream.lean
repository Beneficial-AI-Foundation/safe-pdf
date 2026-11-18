import SafePdf.Core.Xref
import SafePdf.Core.Filter.Flate
import SafePdf.Core.Filter.Predictor

/-!
# Cross-reference streams

Plan.md §5.2, §4 S2/S3/S6, §6 Phase 2; ISO 32000-2 §7.5.8 (cross-reference streams).

Task 2.4a. Since PDF 1.5 a cross-reference section may be a stream object
`n g obj << /Type /XRef /Size … /W [w1 w2 w3] … >> stream … endstream endobj` whose decoded
data is a table of fixed-width binary rows. Its dictionary doubles as the trailer
(§7.5.8.2). `parseXrefStream` reads one such section at a byte offset and returns the same
`XrefSection × Trailer` that `Core.Xref.parseXrefTable` returns for a classic table, so the
`/Prev` chain (`Core.Xref.Chain`) can walk both kinds.

## Byte grammar (strict path)

* XS1. The offset must hold a digit (the object number of `n g obj`; no leading whitespace),
  and `Core.ObjParse.parseIndirect` must read a *stream* object there. Its `/Length` must be
  a direct integer (§7.5.8.2: the xref stream's own `/Length` shall not be indirect);
  `parseIndirect` already rejects an indirect `/Length` (`unsupported`).
* XS2. `/Type` must be the name `XRef`. The dictionary must be a valid trailer
  (`Trailer.ofDict`: `/Size`, and `/Prev`, `/Root` typed when present).
* XS3. `/W` is an array of exactly three non-negative integers, each at most 8 (bytes per
  field; wider fields are `unsupported`), not all zero.
* XS4. `/Index` is an array of an even number of non-negative integers `[s1 c1 s2 c2 …]`
  (subsections: first object number, count); absent means `[0 Size]`. Every subsection must
  lie below `/Size` (`s + c ≤ Size`); the total count must be `≤ limits.maxObjects`
  (else `limitExceeded .objects`).
* XS5. `/Filter` is absent, `/FlateDecode` or `[/FlateDecode]`; other filters are
  `unsupported`. With Flate, the data is inflated (`Filter.Flate.flateDecode`, output bounded
  by `limits.maxDecodedStreamBytes`) and then the predictor of `/DecodeParms`
  (`Filter.Predictor.Params.ofDict`, a dictionary or a one-element array) is undone. Without a
  filter, `/DecodeParms` is ignored.
* XS6. The decoded length must equal `(Σ counts) × (w1 + w2 + w3)` exactly.
* XS7. Each row is three big-endian unsigned fields. A zero-width field reads as 0, except
  that a zero-width type field means type 1 (§7.5.8.3). Type 0 → `free f2 f3`; type 1 →
  `inUse f2 f3` with `f2 < bytes.size`; type 2 → `compressed f2 f3` with `f2 < /Size` and
  `f2 ≠` the entry's own object number (an object stream cannot contain itself); any other
  type is "a reference to the null object" (§7.5.8.3), recorded as `free 0 0`. Generations
  of types 0 and 1 must be `≤ 65535`.
* XS8. An object number may occur at most once in the section (S6; overlapping `/Index`
  subsections are an error), as for classic tables.

`/XRefStm` in an xref stream's own dictionary is not followed: it is a key of the classic
trailer of a hybrid file (§7.5.8.4), handled by `Core.Xref.Chain`.

## Totality

The row loop is structural in the row count, the subsection loop structural in the
`/Index` list, field reads structural in the field width (`≤ 8`). Nothing is dereferenced.
-/

namespace SafePdf.Core.Xref.Stream

open SafePdf SafePdf.Core.Xref

/-! ## Dictionary keys -/

/-- Key `/Type`. -/
def nameType : Name := Name.ofString "Type"
/-- Name `XRef`. -/
def nameXRef : Name := Name.ofString "XRef"
/-- Key `/W`. -/
def nameW : Name := Name.ofString "W"
/-- Key `/Index`. -/
def nameIndex : Name := Name.ofString "Index"
/-- Key `/Filter`. -/
def nameFilter : Name := Name.ofString "Filter"
/-- Name `FlateDecode`. -/
def nameFlate : Name := Name.ofString "FlateDecode"
/-- Key `/DecodeParms`. -/
def nameDecodeParms : Name := Name.ofString "DecodeParms"

/-- The widest supported `/W` field, in bytes. -/
def maxFieldWidth : Nat := 8

/-! ## Dictionary entries -/

/-- A non-negative integer of a `/W` or `/Index` array. -/
def natOf : PdfObject → Option Nat
  | .int i => if 0 ≤ i then some i.toNat else none
  | _ => none

/-- `/W` (XS3): three field widths, each `≤ maxFieldWidth`, not all zero. -/
def widths (d : Dict) (at_ : Nat) : Except Error (Nat × Nat × Nat) :=
  match d.get? nameW with
  | some (.array [a, b, c]) =>
    match natOf a, natOf b, natOf c with
    | some w1, some w2, some w3 =>
      if maxFieldWidth < w1 ∨ maxFieldWidth < w2 ∨ maxFieldWidth < w3 then
        .error (.unsupported s!"xref stream /W field width above {maxFieldWidth}")
      else if w1 + w2 + w3 = 0 then .error (.malformed at_ "xref stream /W is all zero")
      else .ok (w1, w2, w3)
    | _, _, _ => .error (.malformed at_ "xref stream /W entry is not a non-negative integer")
  | some _ => .error (.malformed at_ "xref stream /W is not an array of three integers")
  | none => .error (.malformed at_ "xref stream without /W")

/-- The pairs of an `/Index` array. -/
def pairs : List PdfObject → Option (List (Nat × Nat))
  | [] => some []
  | a :: b :: rest =>
    match natOf a, natOf b, pairs rest with
    | some s, some c, some ps => some ((s, c) :: ps)
    | _, _, _ => none
  | [_] => none

/-- `/Index` (XS4): the subsections, defaulting to `[0 Size]`. -/
def index (d : Dict) (size at_ : Nat) : Except Error (List (Nat × Nat)) :=
  match d.get? nameIndex with
  | none => .ok [(0, size)]
  | some (.array xs) =>
    match pairs xs with
    | some ps => .ok ps
    | none => .error (.malformed at_ "xref stream /Index is not pairs of non-negative integers")
  | some _ => .error (.malformed at_ "xref stream /Index is not an array")

/-- `/Filter` (XS5): whether the data is Flate-compressed. -/
def isFlate (d : Dict) (at_ : Nat) : Except Error Bool :=
  match d.get? nameFilter with
  | none => .ok false
  | some (.array []) => .ok false
  | some (.name n) =>
    if n = nameFlate then .ok true else .error (.unsupported "xref stream filter other than /FlateDecode")
  | some (.array [.name n]) =>
    if n = nameFlate then .ok true else .error (.unsupported "xref stream filter other than /FlateDecode")
  | some (.array _) => .error (.unsupported "xref stream with a filter chain")
  | some _ => .error (.malformed at_ "xref stream /Filter is not a name")

/-- `/DecodeParms` (XS5): the predictor parameters (defaults when absent). -/
def params (d : Dict) (at_ : Nat) : Except Error Filter.Predictor.Params :=
  match d.get? nameDecodeParms with
  | none => Filter.Predictor.Params.ofDict []
  | some (.dict p) => Filter.Predictor.Params.ofDict p
  | some (.array [.dict p]) => Filter.Predictor.Params.ofDict p
  | some (.array [.null]) => Filter.Predictor.Params.ofDict []
  | some _ => .error (.malformed at_ "xref stream /DecodeParms is not a dictionary")

/-- The decoded data of the stream (XS5). -/
def decodeData (limits : Limits) (d : Dict) (raw : ByteArray) (at_ : Nat) :
    Except Error ByteArray := do
  if ← isFlate d at_ then
    let p ← params d at_
    let inflated ← Filter.Flate.flateDecode limits raw
    Filter.Predictor.decode p inflated
  else .ok raw

/-! ## Rows -/

/-- Big-endian unsigned value of the `k` bytes at `p` (missing bytes read as 0; the caller
checks the length first). -/
def be (data : ByteArray) (p acc : Nat) : Nat → Nat
  | 0 => acc
  | k + 1 => be data (p + 1) (acc * 256 + (data[p]?.getD 0).toNat) k

/-- The entry of object `n` from the three fields of its row (XS7). -/
def mkEntry (bytesSize size n t f2 f3 at_ : Nat) : Except Error XrefEntry :=
  if t = 0 then
    if f3 ≤ 65535 then .ok (.free f2 f3)
    else .error (.malformed at_ s!"xref stream: generation above 65535 for object {n}")
  else if t = 1 then
    if bytesSize ≤ f2 then
      .error (.malformed at_ s!"xref stream: offset of object {n} beyond end of input")
    else if f3 ≤ 65535 then .ok (.inUse f2 f3)
    else .error (.malformed at_ s!"xref stream: generation above 65535 for object {n}")
  else if t = 2 then
    if size ≤ f2 then
      .error (.malformed at_ s!"xref stream: object stream of object {n} not below /Size")
    else if f2 = n then
      .error (.malformed at_ s!"xref stream: object {n} lies in its own object stream")
    else .ok (.compressed f2 f3)
  else .ok (.free 0 0)

/-- The field widths of a section. -/
structure Widths where
  /-- Type field width. -/
  w1 : Nat
  /-- Second field width. -/
  w2 : Nat
  /-- Third field width. -/
  w3 : Nat

/-- Read `k` rows for objects `n, n+1, …` starting at byte `p` of `data`, prepending the
entries to `acc` (XS7). -/
def rows (bytesSize size at_ : Nat) (data : ByteArray) (w : Widths) (n p : Nat) :
    Nat → List (Nat × XrefEntry) → Except Error (List (Nat × XrefEntry))
  | 0, acc => .ok acc
  | k + 1, acc =>
    let t := if w.w1 = 0 then 1 else be data p 0 w.w1
    let f2 := be data (p + w.w1) 0 w.w2
    let f3 := be data (p + w.w1 + w.w2) 0 w.w3
    match mkEntry bytesSize size n t f2 f3 at_ with
    | .error e => .error e
    | .ok e => rows bytesSize size at_ data w (n + 1) (p + w.w1 + w.w2 + w.w3) k ((n, e) :: acc)

/-- Read all subsections (XS4, XS7); `p` is the byte position of the next row. -/
def subsections (bytesSize size at_ : Nat) (data : ByteArray) (w : Widths) (p : Nat) :
    List (Nat × Nat) → List (Nat × XrefEntry) → Except Error (List (Nat × XrefEntry))
  | [], acc => .ok acc
  | (s, c) :: rest, acc =>
    match rows bytesSize size at_ data w s p c acc with
    | .error e => .error e
    | .ok acc' =>
      subsections bytesSize size at_ data w (p + c * (w.w1 + w.w2 + w.w3)) rest acc'

/-! ## Entry point -/

/-- **Entry point.** The cross-reference stream whose `n g obj` starts at `off` (XS1–XS8):
its section and its dictionary read as a trailer. Offsets are range-checked, not
dereferenced. -/
def parseXrefStream (limits : Limits) (bytes : ByteArray) (off : Nat) :
    Except Error (XrefSection × Trailer) := do
  if !digitAt bytes off then
    throw (.malformed off "expected an xref keyword or an xref stream object")
  let (io, _) ← ObjParse.parseIndirect limits bytes off
  let st ← match io.body with
    | .stream st => pure st
    | .obj _ => throw (.malformed off "xref section is not a stream")
  let d := st.dict
  if d.get? nameType != some (.name nameXRef) then
    throw (.malformed off "xref stream without /Type /XRef")
  let tr ← Trailer.ofDict d off
  let (w1, w2, w3) ← widths d off
  let subs ← index d tr.size off
  if subs.any (fun sc => tr.size < sc.1 + sc.2) then
    throw (.malformed off "xref stream /Index subsection not below /Size")
  let total := (subs.map Prod.snd).sum
  if limits.maxObjects < total then throw (.limitExceeded .objects)
  let data ← decodeData limits d st.data off
  if data.size != total * (w1 + w2 + w3) then
    throw (.malformed off s!"xref stream data has {data.size} bytes, expected {total * (w1 + w2 + w3)}")
  let acc ← subsections bytes.size tr.size off data ⟨w1, w2, w3⟩ 0 subs []
  match mkSection acc with
  | none => throw (.malformed off "duplicate object number in cross-reference stream")
  | some sec => pure (sec, tr)

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"

/-- Test helper: the entries of the stream at `off`, or the error. -/
private def ps (b : ByteArray) (off : Nat) : Sum String (List (Nat × XrefEntry) × Option Nat) :=
  match parseXrefStream Limits.default b off with
  | .ok (sec, tr) => .inr (sec.entries, tr.prev?)
  | .error e => .inl (errS e)

/-- Test helper: an uncompressed xref stream object with the given dictionary extras and
row bytes. -/
private def xs (pre : String) (extra : String) (rowBytes : List UInt8) : ByteArray :=
  (pre ++ s!"1 0 obj\n<< /Type /XRef {extra} /Length {rowBytes.length} >>\nstream\n").toUTF8 ++
    ByteArray.mk rowBytes.toArray ++ "\nendstream\nendobj\n".toUTF8

-- three rows, /W [1 2 1]: free, in-use at 10 gen 0, compressed in 5 index 3
#guard ps (xs "" "/Size 6 /Index [0 3] /W [1 2 1]" [0, 0, 0, 255, 1, 0, 10, 0, 2, 0, 5, 3]) 0 ==
  .inr ([(0, .free 0 255), (1, .inUse 10 0), (2, .compressed 5 3)], none)
-- /Index [4 2]: object numbers 4, 5; /Prev is read
#guard ps (xs "" "/Size 6 /Index [4 2] /Prev 0 /W [1 2 1]" [1, 0, 10, 0, 1, 0, 20, 7]) 0 ==
  .inr ([(4, .inUse 10 0), (5, .inUse 20 7)], some 0)
-- zero-width type field: type 1
#guard ps (xs "" "/Size 2 /W [0 1 0]" [0, 5]) 0 == .inr ([(0, .inUse 0 0), (1, .inUse 5 0)], none)
-- unknown type: null reference
#guard ps (xs "" "/Size 1 /W [1 1 0]" [7, 9]) 0 == .inr ([(0, .free 0 0)], none)
-- /W field width 9
#guard ps (xs "" "/Size 1 /W [1 9 0]" [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) 0 ==
  .inl "unsupported:xref stream /W field width above 8"
-- decoded length mismatch
#guard ps (xs "" "/Size 2 /W [1 1 0]" [1, 0, 1]) 0 ==
  .inl "malformed@0: xref stream data has 3 bytes, expected 4"
-- duplicate object numbers via overlapping /Index
#guard ps (xs "" "/Size 2 /Index [0 1 0 1] /W [1 1 0]" [1, 0, 1, 1]) 0 ==
  .inl "malformed@0: duplicate object number in cross-reference stream"
-- subsection not below /Size
#guard ps (xs "" "/Size 1 /Index [0 2] /W [1 1 0]" [1, 0, 1, 1]) 0 ==
  .inl "malformed@0: xref stream /Index subsection not below /Size"
-- in-use offset beyond the input; generation above 65535; self-containing object stream
#guard ps (xs "" "/Size 1 /W [1 2 0]" [1, 255, 255]) 0 ==
  .inl "malformed@0: xref stream: offset of object 0 beyond end of input"
#guard ps (xs "" "/Size 1 /W [1 1 3]" [1, 0, 1, 0, 0]) 0 ==
  .inl "malformed@0: xref stream: generation above 65535 for object 0"
#guard ps (xs "" "/Size 3 /W [1 1 1]" [1, 0, 0, 1, 0, 0, 2, 2, 0]) 0 ==
  .inl "malformed@0: xref stream: object 2 lies in its own object stream"
-- not an xref stream: wrong /Type, a non-stream object, no object at all, indirect /Length
#guard ps ("1 0 obj\n<< /Type /ObjStm /Size 1 /W [1 1 0] /Length 2 >>\nstream\n".toUTF8 ++
    ByteArray.mk #[1, 0] ++ "\nendstream\nendobj\n".toUTF8) 0 ==
  .inl "malformed@0: xref stream without /Type /XRef"
#guard ps "1 0 obj\n<< /Type /XRef /Size 1 /W [1 1 0] >>\nendobj\n".toUTF8 0 ==
  .inl "malformed@0: xref section is not a stream"
#guard ps " 1 0 obj".toUTF8 0 ==
  .inl "malformed@0: expected an xref keyword or an xref stream object"
#guard ps ("1 0 obj\n<< /Type /XRef /Size 1 /W [1 1 0] /Length 2 0 R >>\nstream\n".toUTF8 ++
    ByteArray.mk #[1, 0] ++ "\nendstream\nendobj\n".toUTF8) 0 ==
  .inl "unsupported:indirect /Length"
-- unsupported filter
#guard ps (xs "" "/Size 1 /W [1 1 0] /Filter /LZWDecode" [1, 0]) 0 ==
  .inl "unsupported:xref stream filter other than /FlateDecode"

/-- A Flate + PNG-Up (`/Predictor 12 /Columns 5`) xref stream generated with Python's `zlib`
(scratch script, task 2.4a): rows `[0 0 0 0 255]`, `[1 0 0 15 0]`, `[1 0 0 64 0]`,
`[2 0 0 9 0]` for objects 0–3 of `/W [1 3 1]`, each PNG-Up filtered. -/
private def flateRows : List UInt8 :=
  [120, 156, 99, 98, 0, 130, 255, 76, 140, 12, 12, 252, 140, 76, 64, 166, 33, 3, 136, 125,
   146, 1, 0, 23, 140, 2, 20]

#guard ps (xs "" ("/Size 10 /Index [0 4] /W [1 3 1] /Filter /FlateDecode " ++
    "/DecodeParms << /Predictor 12 /Columns 5 >>") flateRows) 0 ==
  .inr ([(0, .free 0 255), (1, .inUse 15 0), (2, .inUse 64 0), (3, .compressed 9 0)], none)

end Tests

end SafePdf.Core.Xref.Stream
