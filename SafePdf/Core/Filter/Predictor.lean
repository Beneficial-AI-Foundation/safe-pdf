import SafePdf.Core.Object
import SafePdf.Core.Error

/-!
# PNG and TIFF predictors for FlateDecode / LZWDecode (Plan.md §6 Phase 3, task 3.2)

ISO 32000-2 §7.4.4.4 ("LZW and Flate predictor functions") lets the `/DecodeParms` of a
`FlateDecode` or `LZWDecode` stream name a *predictor* that was applied before compression;
the reader undoes it after decompression. Table 10 entries:

| Key | Default | Meaning |
|---|---|---|
| `/Predictor` | 1 | 1 none, 2 TIFF predictor 2, 10–15 PNG (the value only says "PNG") |
| `/Colors` | 1 | colour components per sample |
| `/BitsPerComponent` | 8 | 1, 2, 4, 8 or 16 |
| `/Columns` | 1 | samples per row |

Cross-reference streams (task 2.4) use `/Predictor 12` (PNG Up) on Flate output; that is why
this task was pulled forward from Phase 3.

## Rules

* P1. `bytesPerPixel p = max 1 ((colors * bpc + 7) / 8)` and
  `rowBytes p = (colors * bpc * columns + 7) / 8` (PNG spec §9.2: filters work on bytes, the
  left neighbour is one *pixel* back, rounded up to at least one byte).
* P2. PNG (`/Predictor` 10–15): the input is rows of `1 + rowBytes` bytes. The first byte of a
  row is that row's own filter type (PNG spec §9.2, filter method 0: 0 None, 1 Sub, 2 Up,
  3 Average, 4 Paeth); it may differ from row to row whatever the `/Predictor` value. A type
  above 4 is `Error.malformed` at the type byte's offset.
* P3. Unfiltering (PNG spec §9.2–9.4): `x` the filtered byte, `a` the decoded byte `bpp`
  positions to the left in the same row, `b` the decoded byte above, `c` the decoded byte above
  `a`; every missing neighbour (left of the row start, above the first row) is `0`. Arithmetic
  is modulo 256 (`UInt8`); Average uses `⌊(a + b) / 2⌋` computed without overflow; Paeth uses
  the PNG predictor function over integers, ties broken in the order `a`, `b`, `c`.
* P4. **Partial rows are rejected.** If the input length is not a multiple of `1 + rowBytes`,
  the result is `Error.malformed` (offset: the start of the partial row). zlib output for
  well-formed xref streams is always exact; real-world truncated image data is a matter for
  the repair path (Plan.md §5.4) or the image layer, which may pad or drop the tail itself.
* P5. TIFF predictor 2 (`/Predictor 2`): horizontal differencing, no per-row type byte. For
  `bpc = 8`, byte `j` of a row adds the decoded byte `colors` positions to the left (mod 256);
  for `bpc = 16`, samples are big-endian 16-bit and add the sample `colors` positions to the
  left (mod 65536). `bpc` 1, 2, 4 is `Error.unsupported`. The input length must be a multiple
  of `rowBytes` (P4 again).
* P6. `Params.ofDict` reads the four keys (defaults per Table 10; `null` counts as absent).
  A present key must be a non-negative integer. For `/Predictor 1` nothing else is checked
  (the other keys are ignored by the reader, ISO 32000-2 Table 10). Otherwise:
  `/Predictor ∈ {2, 10, …, 15}` else `malformed`; `/BitsPerComponent ∈ {1, 2, 4, 8, 16}`
  else `malformed`; `/Colors ≥ 1` and `/Columns ≥ 1` else `malformed`.
  **Caps (our choice, `unsupported` beyond them):** `/Colors ≤ 32` (the largest component
  count PDF allows for a colour space, DeviceN, ISO 32000-2 Annex C) and
  `/Columns ≤ 2^24`. With both caps a row is at most `32 · 16 · 2^24 / 8 = 2^30` bytes. The
  decoders allocate nothing proportional to `rowBytes` beyond the output, and the output is
  never longer than the input (`decodePng_size_le`), so no further limit is needed (S3).
  Error offsets in `ofDict` are `0` (the dictionary carries no position).

## Design

The PNG decoder walks the rows with an index `r < n = input.size / (rowBytes + 1)`
(`termination_by n - r`). Each row is decoded into a fresh `ByteArray` by `unfilterRow`,
whose inner loop reads the filtered byte, the left neighbour from the row being built and the
upper neighbours from the previous decoded row. Missing bytes read as `0` through
`getD 0`, so the first row uses the empty array as its "previous row" and no index needs a
bound proof. All loops are `def` with `termination_by` (S2).

Proven here:

* `decodePng_exact`, `decodePng_size`, `decodePng_size_le` — the output-length law: success
  implies whole rows, and the output has exactly `rowBytes` bytes per input row.
* `decodeTiff2_size` — TIFF predictor 2 preserves the length.
* `decode_size` — the dispatcher preserves or shrinks the length per predictor.
* `unfilterRow_spec` — the `ByteArray` row decoder equals the list specification
  `unfilterRowSpec` (structural, with left neighbours read by index from the accumulated
  output), following `docs/proof-patterns.md` §1. The per-byte function `unfilterByte`
  (P3) is shared by spec and implementation; the equivalence covers the indexing.
-/

namespace SafePdf.Core.Filter.Predictor

open SafePdf

/-! ## Parameters -/

/-- Predictor parameters from a stream's `/DecodeParms` (ISO 32000-2 Table 10). -/
structure Params where
  /-- `/Predictor`: 1 none, 2 TIFF, 10–15 PNG. -/
  predictor : Nat
  /-- `/Colors`: components per sample. -/
  colors : Nat
  /-- `/BitsPerComponent`: 1, 2, 4, 8 or 16. -/
  bitsPerComponent : Nat
  /-- `/Columns`: samples per row. -/
  columns : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Cap on `/Colors` (P6): DeviceN allows at most 32 colorants (ISO 32000-2 Annex C). -/
def maxColors : Nat := 32

/-- Cap on `/Columns` (P6). -/
def maxColumns : Nat := 1 <<< 24

/-- Read an optional non-negative integer entry with a default (P6). -/
def getNat (d : Dict) (key : String) (dflt : Nat) : Except Error Nat :=
  match d.get? (Name.ofString key) with
  | none => .ok dflt
  | some (.int i) =>
    if i < 0 then .error (.malformed 0 s!"/DecodeParms /{key}: negative value")
    else .ok i.toNat
  | some _ => .error (.malformed 0 s!"/DecodeParms /{key}: expected an integer")

/-- Check the ranges of P6 for a predictor other than 1. -/
def validate (p : Params) : Except Error Params :=
  if !(p.predictor == 2 || (10 ≤ p.predictor && p.predictor ≤ 15)) then
    .error (.malformed 0 s!"/DecodeParms /Predictor {p.predictor} is not 1, 2 or 10-15")
  else if !(p.bitsPerComponent == 1 || p.bitsPerComponent == 2 || p.bitsPerComponent == 4 ||
      p.bitsPerComponent == 8 || p.bitsPerComponent == 16) then
    .error (.malformed 0 s!"/DecodeParms /BitsPerComponent {p.bitsPerComponent} invalid")
  else if p.colors = 0 then
    .error (.malformed 0 "/DecodeParms /Colors must be at least 1")
  else if p.columns = 0 then
    .error (.malformed 0 "/DecodeParms /Columns must be at least 1")
  else if maxColors < p.colors then
    .error (.unsupported s!"/DecodeParms /Colors {p.colors} above cap {maxColors}")
  else if maxColumns < p.columns then
    .error (.unsupported s!"/DecodeParms /Columns {p.columns} above cap {maxColumns}")
  else .ok p

/-- Parse `/DecodeParms` into predictor parameters (P6). -/
def Params.ofDict (d : Dict) : Except Error Params := do
  let predictor ← getNat d "Predictor" 1
  let colors ← getNat d "Colors" 1
  let bpc ← getNat d "BitsPerComponent" 8
  let columns ← getNat d "Columns" 1
  let p : Params := ⟨predictor, colors, bpc, columns⟩
  if predictor = 1 then .ok p else validate p

/-- Bytes per complete pixel, at least 1 (P1). -/
def bytesPerPixel (p : Params) : Nat := max 1 ((p.colors * p.bitsPerComponent + 7) / 8)

/-- Bytes per decoded row (P1). -/
def rowBytes (p : Params) : Nat := (p.colors * p.bitsPerComponent * p.columns + 7) / 8

/-! ## Per-byte unfiltering (P3) -/

/-- The PNG Paeth predictor (PNG spec §9.4), over integers. -/
def paeth (a b c : UInt8) : UInt8 :=
  let p : Int := (a.toNat : Int) + b.toNat - c.toNat
  let pa := (p - a.toNat).natAbs
  let pb := (p - b.toNat).natAbs
  let pc := (p - c.toNat).natAbs
  if pa ≤ pb ∧ pa ≤ pc then a else if pb ≤ pc then b else c

/-- Undo PNG filter type `t ≤ 4` on one byte: `x` filtered byte, `a` left, `b` up,
`c` upper left (P3). Types above 4 never reach this function; they act as None. -/
def unfilterByte (t x a b c : UInt8) : UInt8 :=
  if t = 1 then x + a
  else if t = 2 then x + b
  else if t = 3 then x + UInt8.ofNat ((a.toNat + b.toNat) / 2)
  else if t = 4 then x + paeth a b c
  else x

/-! ## Row specification (lists) -/

/-- Specification loop: `acc` is the decoded prefix of the row (in order), `row` the
filtered bytes still to decode. The left neighbour is `acc[acc.length - bpp]`, the upper
neighbours are read from `prev` by index; missing bytes are `0`. -/
def specGo (bpp : Nat) (t : UInt8) (prev : List UInt8) : List UInt8 → List UInt8 → List UInt8
  | [], acc => acc
  | x :: xs, acc =>
    specGo bpp t prev xs
      (acc ++ [unfilterByte t x
        (if bpp ≤ acc.length then acc[acc.length - bpp]?.getD 0 else 0)
        (prev[acc.length]?.getD 0)
        (if bpp ≤ acc.length then prev[acc.length - bpp]?.getD 0 else 0)])

/-- Specification of one PNG row: `prev` is the previous decoded row (`[]` for the first
row), `row` the filtered bytes without the type byte, `t` the type byte. `none` for an
unknown filter type. -/
def unfilterRowSpec (bpp : Nat) (prev row : List UInt8) (t : UInt8) : Option (List UInt8) :=
  if t ≤ 4 then some (specGo bpp t prev row []) else none

/-! ## PNG implementation -/

/-- The byte at `k`, or `0` past the end. -/
@[inline] def byteAt (bs : ByteArray) (k : Nat) : UInt8 := bs[k]?.getD 0

/-- Decode `rb - i` more bytes of one row into `cur`: the filtered bytes are
`input[inBase + i ..]`, the previous decoded row is `prev`. -/
def unfilterRow (t : UInt8) (bpp : Nat) (prev input : ByteArray) (inBase rb : Nat)
    (i : Nat) (cur : ByteArray) : ByteArray :=
  if i < rb then
    let a := if bpp ≤ i then byteAt cur (i - bpp) else 0
    let c := if bpp ≤ i then byteAt prev (i - bpp) else 0
    unfilterRow t bpp prev input inBase rb (i + 1)
      (cur.push (unfilterByte t (byteAt input (inBase + i)) a (byteAt prev i) c))
  else cur
termination_by rb - i

/-- The row loop over rows `r .. n - 1`; `prev` is the last decoded row, `out` the output. -/
def pngRows (bpp rb : Nat) (input : ByteArray) (n r : Nat) (prev out : ByteArray) :
    Except Error ByteArray :=
  if r < n then
    if byteAt input (r * (rb + 1)) ≤ 4 then
      pngRows bpp rb input n (r + 1)
        (unfilterRow (byteAt input (r * (rb + 1))) bpp prev input (r * (rb + 1) + 1) rb 0
          (ByteArray.emptyWithCapacity rb))
        (out ++ unfilterRow (byteAt input (r * (rb + 1))) bpp prev input (r * (rb + 1) + 1)
          rb 0 (ByteArray.emptyWithCapacity rb))
    else .error (.malformed (r * (rb + 1))
      s!"PNG predictor: filter type {byteAt input (r * (rb + 1))} above 4")
  else .ok out
termination_by n - r

/-- Undo PNG prediction (P2–P4). -/
def decodePng (p : Params) (input : ByteArray) : Except Error ByteArray :=
  if input.size % (rowBytes p + 1) = 0 then
    pngRows (bytesPerPixel p) (rowBytes p) input (input.size / (rowBytes p + 1)) 0
      ByteArray.empty
      (ByteArray.emptyWithCapacity ((input.size / (rowBytes p + 1)) * rowBytes p))
  else
    .error (.malformed (input.size - input.size % (rowBytes p + 1))
      "PNG predictor: partial final row")

/-! ## TIFF predictor 2 (P5) -/

/-- 8-bit horizontal differencing over the whole input; `rb` row bytes, `bpp = colors`. -/
def tiff8 (bpp rb : Nat) (input : ByteArray) (j : Nat) (out : ByteArray) : ByteArray :=
  if j < input.size then
    tiff8 bpp rb input (j + 1)
      (out.push (byteAt input j + (if bpp ≤ j % rb then byteAt out (j - bpp) else 0)))
  else out
termination_by input.size - j

/-- 16-bit big-endian horizontal differencing; `bpp = 2 * colors` bytes per pixel. A lone
trailing byte (excluded by the row check) is copied. -/
def tiff16 (bpp rb : Nat) (input : ByteArray) (j : Nat) (out : ByteArray) : ByteArray :=
  if j < input.size then
    if j + 1 < input.size then
      tiff16 bpp rb input (j + 2)
        ((out.push (UInt8.ofNat (((byteAt input j).toNat * 256 + (byteAt input (j + 1)).toNat +
            (if bpp ≤ j % rb then
              (byteAt out (j - bpp)).toNat * 256 + (byteAt out (j - bpp + 1)).toNat
             else 0)) % 65536 / 256))).push
          (UInt8.ofNat (((byteAt input j).toNat * 256 + (byteAt input (j + 1)).toNat +
            (if bpp ≤ j % rb then
              (byteAt out (j - bpp)).toNat * 256 + (byteAt out (j - bpp + 1)).toNat
             else 0)) % 256)))
    else tiff16 bpp rb input (j + 1) (out.push (byteAt input j))
  else out
termination_by input.size - j

/-- Undo TIFF predictor 2 (P5). -/
def decodeTiff2 (p : Params) (input : ByteArray) : Except Error ByteArray :=
  if input.size % rowBytes p = 0 then
    if p.bitsPerComponent = 8 then
      .ok (tiff8 p.colors (rowBytes p) input 0 (ByteArray.emptyWithCapacity input.size))
    else if p.bitsPerComponent = 16 then
      .ok (tiff16 (2 * p.colors) (rowBytes p) input 0 (ByteArray.emptyWithCapacity input.size))
    else .error (.unsupported
      s!"TIFF predictor 2 with /BitsPerComponent {p.bitsPerComponent}")
  else
    .error (.malformed (input.size - input.size % rowBytes p) "TIFF predictor: partial final row")

/-! ## Dispatch -/

/-- Undo the predictor named by `p.predictor`: 1 identity, 2 TIFF, 10–15 PNG. -/
def decode (p : Params) (input : ByteArray) : Except Error ByteArray :=
  if p.predictor = 1 then .ok input
  else if p.predictor = 2 then decodeTiff2 p input
  else if 10 ≤ p.predictor ∧ p.predictor ≤ 15 then decodePng p input
  else .error (.malformed 0 s!"/DecodeParms /Predictor {p.predictor} is not 1, 2 or 10-15")

/-! ## Output-length law -/

/-- An array created with a capacity is empty. -/
theorem size_emptyWithCapacity (n : Nat) : (ByteArray.emptyWithCapacity n).size = 0 := rfl

/-- The row loop appends exactly `rb - i` bytes. -/
theorem unfilterRow_size (t : UInt8) (bpp : Nat) (prev input : ByteArray) (inBase rb i : Nat)
    (cur : ByteArray) :
    (unfilterRow t bpp prev input inBase rb i cur).size = cur.size + (rb - i) := by
  fun_induction unfilterRow t bpp prev input inBase rb i cur with
  | case1 i cur hi a c ih => rw [ih, ByteArray.size_push]; omega
  | case2 i cur hi => omega

/-- One decoded row has exactly `rb` bytes. -/
theorem unfilterRow_size_zero (t : UInt8) (bpp : Nat) (prev input : ByteArray)
    (inBase rb : Nat) :
    (unfilterRow t bpp prev input inBase rb 0 (ByteArray.emptyWithCapacity rb)).size = rb := by
  rw [unfilterRow_size, size_emptyWithCapacity]; omega

/-- The PNG row loop outputs `rb` bytes per remaining row. -/
theorem pngRows_size (bpp rb : Nat) (input : ByteArray) (n r : Nat) (prev out o : ByteArray)
    (h : pngRows bpp rb input n r prev out = .ok o) : o.size = out.size + (n - r) * rb := by
  fun_induction pngRows bpp rb input n r prev out with
  | case1 r prev out hr ht ih =>
    rw [ih h, ByteArray.size_append, unfilterRow_size_zero, Nat.add_assoc]
    have hnr : n - r = (n - (r + 1)) + 1 := by omega
    rw [hnr, Nat.succ_mul, Nat.add_comm rb]
  | case2 r prev out hr ht => simp at h
  | case3 r prev out hr =>
    simp only [Except.ok.injEq] at h
    subst h
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hr)]; simp

/-- **Exact rows.** A successful PNG decode had a whole number of rows (P4). -/
theorem decodePng_exact (p : Params) (input out : ByteArray) (h : decodePng p input = .ok out) :
    input.size % (rowBytes p + 1) = 0 := by
  unfold decodePng at h
  split at h
  · assumption
  · simp at h

/-- **Output-length law.** A successful PNG decode yields `rowBytes p` bytes per input row
of `rowBytes p + 1` bytes. -/
theorem decodePng_size (p : Params) (input out : ByteArray) (h : decodePng p input = .ok out) :
    out.size = (input.size / (rowBytes p + 1)) * rowBytes p := by
  unfold decodePng at h
  split at h
  · rw [pngRows_size _ _ _ _ _ _ _ _ h, size_emptyWithCapacity]; simp
  · simp at h

/-- PNG decoding never grows the data (no amplification, S3). -/
theorem decodePng_size_le (p : Params) (input out : ByteArray)
    (h : decodePng p input = .ok out) : out.size ≤ input.size := by
  rw [decodePng_size p input out h]
  have h1 : (input.size / (rowBytes p + 1)) * rowBytes p ≤
      (input.size / (rowBytes p + 1)) * (rowBytes p + 1) :=
    Nat.mul_le_mul_left _ (Nat.le_succ _)
  have h2 := Nat.div_mul_le_self input.size (rowBytes p + 1)
  omega

/-- The 8-bit TIFF loop appends one byte per remaining input byte. -/
theorem tiff8_size (bpp rb : Nat) (input : ByteArray) (j : Nat) (out : ByteArray) :
    (tiff8 bpp rb input j out).size = out.size + (input.size - j) := by
  fun_induction tiff8 bpp rb input j out with
  | case1 j out hj ih => simp only [dite_eq_ite] at ih; rw [ih, ByteArray.size_push]; omega
  | case2 j out hj => omega

/-- The 16-bit TIFF loop appends one byte per remaining input byte. -/
theorem tiff16_size (bpp rb : Nat) (input : ByteArray) (j : Nat) (out : ByteArray) :
    (tiff16 bpp rb input j out).size = out.size + (input.size - j) := by
  fun_induction tiff16 bpp rb input j out with
  | case1 j out hj hj1 ih => simp only [dite_eq_ite] at ih; rw [ih, ByteArray.size_push, ByteArray.size_push]; omega
  | case2 j out hj hj1 ih => rw [ih, ByteArray.size_push]; omega
  | case3 j out hj => omega

/-- **TIFF predictor 2 preserves the length.** -/
theorem decodeTiff2_size (p : Params) (input out : ByteArray)
    (h : decodeTiff2 p input = .ok out) : out.size = input.size := by
  unfold decodeTiff2 at h
  split at h
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h; rw [tiff8_size, size_emptyWithCapacity]; omega
    · split at h
      · simp only [Except.ok.injEq] at h
        subst h; rw [tiff16_size, size_emptyWithCapacity]; omega
      · simp at h
  · simp at h

/-- A successful TIFF decode had a whole number of rows (P5). -/
theorem decodeTiff2_exact (p : Params) (input out : ByteArray)
    (h : decodeTiff2 p input = .ok out) : input.size % rowBytes p = 0 := by
  unfold decodeTiff2 at h
  split at h
  · assumption
  · simp at h

/-- **Dispatcher length law.** Predictor 1 and 2 preserve the length; PNG (10–15) follows
`decodePng_size`. In every case the output is no longer than the input. -/
theorem decode_size (p : Params) (input out : ByteArray) (h : decode p input = .ok out) :
    (p.predictor ≤ 2 ∧ out.size = input.size) ∨
    (10 ≤ p.predictor ∧ p.predictor ≤ 15 ∧ input.size % (rowBytes p + 1) = 0 ∧
      out.size = (input.size / (rowBytes p + 1)) * rowBytes p) := by
  unfold decode at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; left; omega
  · split at h
    · left; exact ⟨by omega, decodeTiff2_size p input out h⟩
    · split at h
      · right
        exact ⟨by omega, by omega, decodePng_exact p input out h, decodePng_size p input out h⟩
      · simp at h

/-- The dispatcher never grows the data (S3). -/
theorem decode_size_le (p : Params) (input out : ByteArray) (h : decode p input = .ok out) :
    out.size ≤ input.size := by
  unfold decode at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; omega
  · split at h
    · rw [decodeTiff2_size p input out h]; omega
    · split at h
      · exact decodePng_size_le p input out h
      · simp at h

/-! ## Row equivalence: implementation = specification -/

/-- `ByteArray` lookup agrees with lookup in the underlying array. -/
theorem getElem?_data (bs : ByteArray) (k : Nat) : bs[k]? = bs.data[k]? := by
  by_cases h : k < bs.size
  · rw [getElem?_pos bs k h, getElem?_pos bs.data k (by simpa using h)]; rfl
  · rw [getElem?_neg bs k h, getElem?_neg bs.data k (by simpa using h)]

/-- `byteAt` is list lookup with default `0`. -/
theorem byteAt_eq (bs : ByteArray) (k : Nat) : byteAt bs k = bs.data.toList[k]?.getD 0 := by
  simp [byteAt, getElem?_data]

/-- The specification row has one byte per filtered byte. -/
theorem specGo_length (bpp : Nat) (t : UInt8) (prev row acc : List UInt8) :
    (specGo bpp t prev row acc).length = acc.length + row.length := by
  induction row generalizing acc with
  | nil => simp [specGo]
  | cons x xs ih => simp only [specGo, ih, List.length_append, List.length_cons]; simp; omega

/-- Generalised row equivalence: from position `i` with the decoded prefix `cur`. -/
theorem unfilterRow_eq_specGo (t : UInt8) (bpp : Nat) (prev input : ByteArray)
    (inBase rb i : Nat) (cur : ByteArray) (hcur : cur.size = i) (hin : inBase + rb ≤ input.size) :
    (unfilterRow t bpp prev input inBase rb i cur).data.toList =
      specGo bpp t prev.data.toList
        (((input.data.toList.drop inBase).take rb).drop i) cur.data.toList := by
  fun_induction unfilterRow t bpp prev input inBase rb i cur with
  | case1 i cur hi a c ih =>
    have hlen : i < ((input.data.toList.drop inBase).take rb).length := by
      rw [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
      omega
    rw [List.drop_eq_getElem_cons hlen, specGo, ih (by rw [ByteArray.size_push]; omega)]
    congr 1
    simp only [ByteArray.data_push, Array.toList_push, a, c, byteAt_eq, Array.length_toList,
      ByteArray.size_data, hcur]
    congr 3
    have hb : inBase + i < input.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; omega
    rw [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem hb]
    rfl
  | case2 i cur hi =>
    have : ((input.data.toList.drop inBase).take rb).drop i = [] := by
      rw [List.drop_eq_nil_iff, List.length_take, List.length_drop, Array.length_toList,
        ByteArray.size_data]
      omega
    rw [this, specGo]

/-- **Row equivalence.** For a known filter type the `ByteArray` row decoder agrees with
`unfilterRowSpec` on the row's `rb` filtered bytes, which start at `inBase`. -/
theorem unfilterRow_spec (t : UInt8) (bpp : Nat) (prev input : ByteArray) (inBase rb : Nat)
    (ht : t ≤ 4) (hin : inBase + rb ≤ input.size) :
    unfilterRowSpec bpp prev.data.toList ((input.data.toList.drop inBase).take rb) t =
      some (unfilterRow t bpp prev input inBase rb 0 (ByteArray.emptyWithCapacity rb)).data.toList := by
  rw [unfilterRowSpec, ite_eq_left_of_eq_true _ _ (eq_true ht), unfilterRow_eq_specGo t bpp prev input inBase rb 0 _ rfl hin]
  rfl

/-- An unknown filter type is rejected by the specification, as by `decodePng`. -/
theorem unfilterRowSpec_none (bpp : Nat) (prev row : List UInt8) (t : UInt8) (ht : 4 < t) :
    unfilterRowSpec bpp prev row t = none := by
  simp [unfilterRowSpec]
  exact ht

/-! ## Tests

PNG vectors were generated by a Python stdlib script implementing PNG filtering (PNG spec §9):
random rows were filtered with the listed type per row, and decoding must give the original
rows back. TIFF vectors likewise by horizontal differencing. -/

/-- Test helper: decoded bytes, or `none` on error. -/
def okList (r : Except Error ByteArray) : Option (List UInt8) :=
  match r with
  | .ok o => some o.data.toList
  | .error _ => none

/-- Test helper: whether the result is an error of the `malformed` kind. -/
def isMalformed {α : Type} (r : Except Error α) : Bool :=
  match r with
  | .error (.malformed _ _) => true
  | _ => false

/-- Test helper: whether the result is an error of the `unsupported` kind. -/
def isUnsupported {α : Type} (r : Except Error α) : Bool :=
  match r with
  | .error (.unsupported _) => true
  | _ => false

/-- Test helper: PNG decoding of `input` gives `expected` (also through `decode`). -/
def pngOk (p : Params) (input expected : List UInt8) : Bool :=
  okList (decodePng p ⟨input.toArray⟩) == some expected &&
    okList (decode p ⟨input.toArray⟩) == some expected

/-- Test helper: TIFF decoding of `input` gives `expected` (also through `decode`). -/
def tiffOk (p : Params) (input expected : List UInt8) : Bool :=
  okList (decodeTiff2 p ⟨input.toArray⟩) == some expected &&
    okList (decode p ⟨input.toArray⟩) == some expected

-- type 0 on every row: colors 3, bpc 8, columns 4, row types [0, 0, 0]
#guard pngOk ⟨12, 3, 8, 4⟩
  [0, 39, 109, 74, 155, 121, 254, 12, 19, 51, 166, 169, 29, 0, 240, 189, 0, 64, 4, 248, 103, 147, 103, 228, 41, 171, 0, 61, 18, 57, 81, 224, 10, 220, 25, 19, 180, 116, 83]
  [39, 109, 74, 155, 121, 254, 12, 19, 51, 166, 169, 29, 240, 189, 0, 64, 4, 248, 103, 147, 103, 228, 41, 171, 61, 18, 57, 81, 224, 10, 220, 25, 19, 180, 116, 83]
-- type 1 on every row: colors 3, bpc 8, columns 4, row types [1, 1, 1]
#guard pngOk ⟨12, 3, 8, 4⟩
  [1, 239, 158, 252, 102, 251, 46, 187, 251, 75, 131, 20, 179, 1, 124, 205, 148, 94, 86, 96, 42, 57, 240, 79, 210, 59, 1, 67, 133, 24, 87, 197, 172, 130, 25, 78, 222, 160, 149]
  [239, 158, 252, 85, 153, 42, 16, 148, 117, 147, 168, 40, 124, 205, 148, 218, 35, 244, 4, 92, 228, 83, 46, 31, 67, 133, 24, 154, 74, 196, 28, 99, 18, 250, 3, 167]
-- type 2 on every row: colors 3, bpc 8, columns 4, row types [2, 2, 2]
#guard pngOk ⟨12, 3, 8, 4⟩
  [2, 184, 251, 245, 127, 165, 119, 115, 196, 192, 189, 99, 65, 2, 251, 194, 81, 255, 91, 136, 155, 115, 64, 152, 62, 148, 2, 192, 44, 135, 172, 163, 223, 71, 132, 155, 213, 202, 109]
  [184, 251, 245, 127, 165, 119, 115, 196, 192, 189, 99, 65, 179, 189, 70, 126, 0, 255, 14, 55, 0, 85, 161, 213, 115, 233, 205, 42, 163, 222, 85, 187, 155, 42, 107, 66]
-- type 3 on every row: colors 3, bpc 8, columns 4, row types [3, 3, 3]
#guard pngOk ⟨12, 3, 8, 4⟩
  [3, 134, 247, 187, 126, 180, 180, 253, 234, 16, 55, 164, 181, 3, 45, 191, 111, 10, 45, 225, 246, 177, 234, 121, 74, 147, 3, 181, 100, 162, 92, 209, 135, 223, 171, 10, 37, 1, 99]
  [134, 247, 187, 193, 47, 17, 93, 1, 24, 101, 164, 193, 112, 58, 204, 162, 97, 79, 117, 226, 29, 230, 13, 2, 237, 129, 8, 35, 66, 178, 43, 61, 113, 173, 38, 156]
-- type 4 on every row: colors 3, bpc 8, columns 4, row types [4, 4, 4]
#guard pngOk ⟨12, 3, 8, 4⟩
  [4, 92, 118, 33, 215, 232, 232, 213, 32, 154, 178, 52, 187, 4, 168, 68, 228, 7, 83, 86, 47, 31, 208, 6, 116, 189, 4, 61, 43, 135, 40, 87, 15, 196, 100, 213, 83, 178, 201]
  [92, 118, 33, 51, 94, 9, 8, 126, 163, 186, 178, 94, 4, 186, 5, 11, 13, 91, 55, 44, 115, 192, 242, 27, 65, 229, 140, 105, 100, 155, 45, 200, 112, 19, 164, 228]
-- mixed types: colors 3, bpc 8, columns 4, row types [4, 1, 2, 3, 0, 4]
#guard pngOk ⟨12, 3, 8, 4⟩
  [4, 137, 78, 109, 105, 76, 210, 27, 35, 164, 57, 197, 182, 1, 151, 121, 1, 78, 213, 75, 51, 40, 139, 100, 181, 43, 2, 143, 23, 66, 181, 114, 174, 162, 123, 50, 128, 158, 128, 3, 56, 105, 145, 195, 250, 236, 238, 95, 169, 10, 139, 69, 0, 143, 37, 117, 228, 144, 214, 8, 62, 203, 188, 31, 40, 4, 121, 141, 96, 213, 166, 104, 31, 21, 144, 108, 20, 45]
  [137, 78, 109, 242, 154, 63, 13, 189, 227, 70, 130, 153, 151, 121, 1, 229, 78, 76, 24, 118, 215, 124, 43, 2, 38, 144, 67, 154, 192, 250, 186, 241, 9, 252, 201, 130, 75, 177, 178, 53, 178, 194, 101, 48, 14, 186, 7, 141, 143, 37, 117, 228, 144, 214, 8, 62, 203, 188, 31, 40, 8, 178, 213, 100, 88, 62, 39, 83, 206, 40, 82, 85]
-- bpc 16, colors 3: colors 3, bpc 16, columns 2, row types [1, 4, 3, 2]
#guard pngOk ⟨12, 3, 16, 2⟩
  [1, 90, 66, 209, 228, 197, 93, 5, 80, 124, 253, 71, 223, 4, 1, 71, 218, 89, 132, 83, 153, 180, 142, 242, 171, 34, 3, 7, 45, 243, 207, 77, 148, 168, 10, 0, 95, 215, 208, 2, 70, 15, 204, 138, 95, 185, 237, 135, 152, 248, 246, 127]
  [90, 66, 209, 228, 197, 93, 95, 146, 77, 225, 12, 60, 91, 137, 171, 61, 73, 176, 248, 70, 219, 47, 183, 210, 52, 113, 72, 237, 113, 236, 62, 101, 145, 237, 107, 175, 122, 128, 20, 119, 208, 165, 43, 236, 41, 229, 97, 46]
-- bpc 1: colors 1, bpc 1, columns 10, row types [1, 2, 4, 3]
#guard pngOk ⟨12, 1, 1, 10⟩
  [1, 15, 125, 2, 167, 69, 4, 125, 167, 3, 85, 124]
  [15, 140, 182, 209, 51, 218, 110, 32]
-- bpc 4, colors 2: colors 2, bpc 4, columns 5, row types [3, 4, 1]
#guard pngOk ⟨12, 2, 4, 5⟩
  [3, 241, 159, 184, 133, 99, 4, 36, 82, 220, 144, 83, 1, 233, 91, 181, 237, 163]
  [241, 23, 195, 230, 214, 21, 103, 159, 83, 166, 233, 68, 249, 230, 137]
-- TIFF 2, bpc 8, colors 3, columns 3
#guard tiffOk ⟨2, 3, 8, 3⟩
  [184, 42, 152, 92, 90, 134, 235, 200, 17, 204, 106, 111, 74, 48, 170, 206, 22, 14, 2, 33, 31, 95, 64, 214, 198, 193, 149]
  [184, 42, 152, 20, 132, 30, 255, 76, 47, 204, 106, 111, 22, 154, 25, 228, 176, 39, 2, 33, 31, 97, 97, 245, 39, 34, 138]
-- TIFF 2, bpc 16, colors 2, columns 3
#guard tiffOk ⟨2, 2, 16, 3⟩
  [45, 84, 197, 99, 74, 146, 248, 7, 143, 3, 223, 158, 221, 153, 167, 105, 134, 72, 56, 109, 127, 133, 189, 63]
  [45, 84, 197, 99, 119, 230, 189, 106, 6, 233, 157, 8, 221, 153, 167, 105, 99, 225, 223, 214, 227, 102, 157, 21]

-- xref-stream-like: /Columns 4 /Predictor 12, every row PNG Up (`02 xx xx xx xx`).
#guard pngOk ⟨12, 1, 8, 4⟩
  [2, 1, 0, 16, 0,  2, 0, 0, 5, 0,  2, 0, 1, 0xFF, 1]
  [1, 0, 16, 0,  1, 0, 21, 0,  1, 1, 20, 1]
-- empty input: no rows, empty output
#guard pngOk ⟨12, 1, 8, 4⟩ [] []
-- filter type 5 is rejected
#guard isMalformed (decodePng ⟨12, 1, 8, 4⟩ ⟨#[2, 1, 2, 3, 4, 5, 1, 2, 3, 4]⟩)
-- partial final row is rejected
#guard isMalformed (decodePng ⟨12, 1, 8, 4⟩ ⟨#[2, 1, 2, 3, 4, 2, 1]⟩)
#guard isMalformed (decodeTiff2 ⟨2, 1, 8, 4⟩ ⟨#[1, 2, 3, 4, 5]⟩)
-- TIFF with bpc below 8 is unsupported
#guard isUnsupported (decodeTiff2 ⟨2, 1, 4, 4⟩ ⟨#[1, 2]⟩)
-- predictor 1 is the identity
#guard okList (decode ⟨1, 1, 8, 1⟩ ⟨#[9, 8, 7]⟩) == some [9, 8, 7]
-- invalid predictor value in the dispatcher
#guard isMalformed (decode ⟨3, 1, 8, 1⟩ ⟨#[9, 8, 7]⟩)
-- spec rejects unknown types, accepts known ones
#guard unfilterRowSpec 1 [] [1, 2] 5 == none
#guard unfilterRowSpec 1 [] [1, 2] 1 == some [1, 3]
#guard unfilterRowSpec 1 [10, 20] [1, 2] 2 == some [11, 22]

-- Params.ofDict: defaults, values, errors
#guard (match Params.ofDict [] with | .ok p => p == ⟨1, 1, 8, 1⟩ | .error _ => false)
#guard (match Params.ofDict [(Name.ofString "Predictor", .int 12),
    (Name.ofString "Columns", .int 5)] with
  | .ok p => p == ⟨12, 1, 8, 5⟩ | .error _ => false)
#guard (match Params.ofDict [(Name.ofString "Predictor", .int 15),
    (Name.ofString "Colors", .int 3), (Name.ofString "BitsPerComponent", .int 16),
    (Name.ofString "Columns", .int 100)] with
  | .ok p => p == ⟨15, 3, 16, 100⟩ && rowBytes p == 600 && bytesPerPixel p == 6
  | .error _ => false)
-- null counts as absent
#guard (match Params.ofDict [(Name.ofString "Columns", .null)] with
  | .ok p => p == ⟨1, 1, 8, 1⟩ | .error _ => false)
#guard isMalformed (Params.ofDict [(Name.ofString "Predictor", .int 3)])
#guard isMalformed (Params.ofDict [(Name.ofString "Predictor", .int 16)])
#guard isMalformed (Params.ofDict [(Name.ofString "Predictor", .int (-1))])
#guard isMalformed (Params.ofDict [(Name.ofString "Predictor", PdfObject.nameOf "Up")])
#guard isMalformed (Params.ofDict [(Name.ofString "Predictor", .int 12),
  (Name.ofString "BitsPerComponent", .int 3)])
#guard isMalformed (Params.ofDict [(Name.ofString "Predictor", .int 12),
  (Name.ofString "Colors", .int 0)])
#guard isMalformed (Params.ofDict [(Name.ofString "Predictor", .int 2),
  (Name.ofString "Columns", .int 0)])
#guard isUnsupported (Params.ofDict [(Name.ofString "Predictor", .int 12),
  (Name.ofString "Colors", .int 33)])
#guard isUnsupported (Params.ofDict [(Name.ofString "Predictor", .int 12),
  (Name.ofString "Columns", .int 16777217)])
-- /Predictor 1 ignores the other keys' ranges
#guard (match Params.ofDict [(Name.ofString "BitsPerComponent", .int 3)] with
  | .ok p => p.predictor == 1 | .error _ => false)
-- bpp and row size for sub-byte components
#guard rowBytes ⟨12, 1, 1, 10⟩ == 2 && bytesPerPixel ⟨12, 1, 1, 10⟩ == 1
#guard rowBytes ⟨12, 3, 4, 3⟩ == 5 && bytesPerPixel ⟨12, 3, 4, 3⟩ == 2

end SafePdf.Core.Filter.Predictor
