import SafePdf.Core.Xref
import SafePdf.Core.Xref.ObjStmDecode
import SafePdf.Core.Xref.Length

/-!
# Object streams (Plan.md §5.2, task 2.4b)

ISO 32000-2 §7.5.7: an object stream is a stream object (`/Type /ObjStm`) whose decoded data
holds `/N` direct objects. The first `/First` bytes are a header of `N` pairs
`objnum offset` (offsets relative to `/First`, in increasing order); the objects follow.
Cross-reference streams point at such objects with type-2 entries
`XrefEntry.compressed objStm index`.

Plan.md §5.2: "Object streams: an object inside an object stream may not itself be the
stream's container — rank argument on (generation of container, offset)." Here the rank is
simply the entry kind: an `inUse` entry has rank 0, a `compressed` one rank 1, and the
container of a compressed object must have rank 0 (§7.5.7: "the stream object itself shall
not be stored in an object stream"; generation 0). So the container chain has length exactly
one and `fetchCompressed` is not recursive at all (`fetchCompressed_no_recursion`).

## Rules

O1–O5 (dictionary, filters, header, offsets, objects) are in `Core.Xref.ObjStmDecode`
(`decodeObjStm`, `getObject`, `findObject`; split out in task 2.14 so that
`Core.Xref.Length` can follow a `/Length` into an object stream). This module adds:

* O6. `fetchCompressed lookup limits bytes fuel num`: the entry of `num` must be
  `compressed c idx` with `c ≠ num` (else `Error.cycle`); the entry of `c` must be
  `inUse off 0` (a compressed container is "nested", an error: `Error.cycle` when it is
  `compressed num _`, the two-object cycle, else `malformed`); the object at `off` is parsed with
  `Length.parseIndirectResolved` (indirect `/Length` resolved with `fuel`), its header must be
  `c 0` and its body a stream; it is decoded by O1–O4; `findObject os num` must equal `idx`
  (the xref index and the stream header agree); then O5 with `k = idx`.

Error offsets for header and object errors are positions in the *decoded* data; dictionary
errors use offset 0, container errors the container's file offset.

## Theorems

* Totality by construction: `fetchCompressed` is not recursive (the `/Length` of its
  container is resolved by `Length.resolveLength`, bounded by its fuel).
* Decoding theorems (`decodeObjStm_*`, `getObject_depth`): `Core.Xref.ObjStmDecode`.
* `fetchCompressed_depth`: depth at most `limits.maxObjectDepth`.
* `fetchCompressed_self`, `fetchCompressed_nested`: a self-container or a compressed
  container is an error; `fetchCompressed_self_cycle`, `fetchCompressed_mutual_cycle`: for a
  self-container and for two object streams containing each other it is `Error.cycle`.
* `fetchCompressed_no_recursion`, `fetchCompressed_rank`: success implies the chain
  `num ↦ compressed c ↦ inUse off 0` with `c ≠ num` (rank 1 → rank 0).
* `fetchCompressed_work`: at most one container parse and one decode
  (`fetchCompressedTrace` counts them; `fetchCompressed` is its result).
-/

namespace SafePdf.Core.Xref.ObjStm

open SafePdf
open SafePdf.Core.Xref (XrefEntry)

/-! ## Fetching a compressed object (O6) -/

/-- An instrumented result: container parses and decodes performed, and the result. -/
structure Trace where
  /-- Number of `Length.parseIndirectResolved` calls on a container. -/
  parses : Nat
  /-- Number of `decodeObjStm` calls. -/
  decodes : Nat
  /-- The fetched object or an error. -/
  result : Except Error PdfObject

/-- `fetchCompressed` with its work counted (rule O6). Not recursive. -/
def fetchCompressedTrace (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel num : Nat) : Trace :=
  match lookup num with
  | some (.compressed c idx) =>
    if c = num then ⟨0, 0, .error (.cycle 0 s!"object {num} is its own object stream")⟩
    else
      match lookup c with
      | some (.inUse off g) =>
        if g = 0 then
          match Length.parseIndirectResolved lookup limits bytes fuel off with
          | .error e => ⟨1, 0, .error e⟩
          | .ok (io, _) =>
            if io.num = c ∧ io.gen = 0 then
              match io.body with
              | .obj _ =>
                ⟨1, 0, .error (.malformed off "object stream container is not a stream")⟩
              | .stream st =>
                match decodeObjStm limits st with
                | .error e => ⟨1, 1, .error e⟩
                | .ok os =>
                  if findObject os num = some idx then ⟨1, 1, getObject os limits idx⟩
                  else ⟨1, 1, .error (.malformed off
                    s!"object {num} is not at index {idx} of object stream {c}")⟩
            else ⟨1, 0, .error (.malformed off
              "object header does not match the cross-reference entry")⟩
        else ⟨0, 0, .error (.malformed off s!"object stream {c} has a non-zero generation")⟩
      | some (.compressed c' _) =>
        ⟨0, 0, .error (if c' = num then
          .cycle 0 s!"object streams {num} and {c} contain each other"
          else .malformed 0 s!"object stream {c} is itself in an object stream")⟩
      | some (.free _ _) => ⟨0, 0, .error (.malformed 0 s!"object stream {c} is free")⟩
      | none => ⟨0, 0, .error (.malformed 0 s!"object stream {c} is not in the xref")⟩
  | _ => ⟨0, 0, .error (.malformed 0 s!"object {num} is not in an object stream")⟩

/-- **Entry point.** Object `num`, stored in an object stream according to `lookup` (rule
O6). `fuel` bounds indirect `/Length` resolution of the container (callers pass the object
count). -/
def fetchCompressed (lookup : Nat → Option XrefEntry) (limits : Limits) (bytes : ByteArray)
    (fuel num : Nat) : Except Error PdfObject :=
  (fetchCompressedTrace lookup limits bytes fuel num).result

/-! ## Theorems -/

/-- **Rank lemma / non-recursion** (Plan.md §5.2): a successful fetch went through exactly one
container `c ≠ num` whose entry is `inUse off 0`; a container is never itself compressed, so
the container chain has length one and no recursion is needed. -/
theorem fetchCompressed_no_recursion {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed lookup limits bytes fuel num = .ok o) :
    ∃ c idx off, lookup num = some (.compressed c idx) ∧ c ≠ num ∧
      lookup c = some (.inUse off 0) := by
  unfold fetchCompressed fetchCompressedTrace at h
  split at h
  · rename_i c idx hl
    split at h
    · cases h
    · rename_i hne
      split at h
      · rename_i off g hc
        split at h
        · rename_i hg
          subst hg
          exact ⟨c, idx, off, hl, hne, hc⟩
        · cases h
      · cases h
      · cases h
      · cases h
  · cases h

/-- The rank of an entry: 1 for an object in an object stream, 0 otherwise. -/
def entryRank : Option XrefEntry → Nat
  | some (.compressed _ _) => 1
  | _ => 0

/-- **Rank decreases**: on success the container's rank is strictly below the object's. -/
theorem fetchCompressed_rank {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed lookup limits bytes fuel num = .ok o) :
    ∃ c idx, lookup num = some (.compressed c idx) ∧
      entryRank (lookup c) < entryRank (lookup num) := by
  obtain ⟨c, idx, off, h1, _, h2⟩ := fetchCompressed_no_recursion h
  exact ⟨c, idx, h1, by simp [entryRank, h1, h2]⟩

/-- **Self-container**: an object claiming to live in an object stream with its own number
is an error. -/
theorem fetchCompressed_self (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num idx : Nat) (h : lookup num = some (.compressed num idx)) :
    ∃ e, fetchCompressed lookup limits bytes fuel num = .error e := by
  simp [fetchCompressed, fetchCompressedTrace, h]

/-- **Self-container is a cycle** (task 2.13): the error of `fetchCompressed_self` is
`Error.cycle`. -/
theorem fetchCompressed_self_cycle (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num idx : Nat) (h : lookup num = some (.compressed num idx)) :
    fetchCompressed lookup limits bytes fuel num =
      .error (.cycle 0 s!"object {num} is its own object stream") := by
  simp [fetchCompressed, fetchCompressedTrace, h]

/-- **Two object streams containing each other are a cycle** (task 2.13): `num` lies in
`c ≠ num` and `c` lies in `num`. -/
theorem fetchCompressed_mutual_cycle (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num c idx idx' : Nat)
    (h : lookup num = some (.compressed c idx)) (hc : lookup c = some (.compressed num idx'))
    (hne : c ≠ num) :
    fetchCompressed lookup limits bytes fuel num =
      .error (.cycle 0 s!"object streams {num} and {c} contain each other") := by
  simp [fetchCompressed, fetchCompressedTrace, h, hc, hne]

/-- **Nested container**: a container that is itself in an object stream is an error. -/
theorem fetchCompressed_nested (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num c idx c' idx' : Nat)
    (h : lookup num = some (.compressed c idx)) (hc : lookup c = some (.compressed c' idx')) :
    ∃ e, fetchCompressed lookup limits bytes fuel num = .error e := by
  by_cases hcn : c = num
  · subst hcn; exact fetchCompressed_self lookup limits bytes fuel c idx h
  · simp [fetchCompressed, fetchCompressedTrace, h, hc, hcn]

/-- **Work bound**: at most one container parse and one object-stream decode. -/
theorem fetchCompressed_work (lookup : Nat → Option XrefEntry) (limits : Limits)
    (bytes : ByteArray) (fuel num : Nat) :
    (fetchCompressedTrace lookup limits bytes fuel num).parses ≤ 1 ∧
    (fetchCompressedTrace lookup limits bytes fuel num).decodes ≤ 1 := by
  unfold fetchCompressedTrace
  repeat' split
  all_goals simp

/-- **Depth bound** for fetched objects. -/
theorem fetchCompressed_depth {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel num : Nat} {o : PdfObject}
    (h : fetchCompressed lookup limits bytes fuel num = .ok o) :
    o.depth ≤ limits.maxObjectDepth := by
  unfold fetchCompressed fetchCompressedTrace at h
  repeat' split at h
  all_goals first | cases h | exact getObject_depth h

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}:{m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o w => s!"cycle@{o}:{w}"


/-- Test helper: `fetchCompressed` summarised. -/
private def fc (lookup : Nat → Option XrefEntry) (b : ByteArray) (num : Nat) :
    Sum String PdfObject :=
  match fetchCompressed lookup Limits.default b 100 num with
  | .ok o => .inr o
  | .error e => .inl (errS e)

/-- Test helper: lookup from an explicit list of entries. -/
private def mkLookup (l : List (Nat × XrefEntry)) : Nat → Option XrefEntry :=
  fun n => l.lookup n

/-- `raw3` (see `ObjStmDecode`) compressed with Python's `zlib.compress`. -/
private def z3 : ByteArray := ⟨#[120, 156, 51, 52, 80, 48, 80, 48, 52, 4, 35, 35, 5, 67, 75, 5,
  27, 27, 5, 125, 71, 5, 67, 5, 59, 59, 174, 104, 67, 5, 35, 5, 227, 88, 46, 141, 140, 76, 77,
  46, 0, 153, 183, 7, 166]⟩


private def dictA : PdfObject := .dict [(Name.ofString "A", .int 1)]
private def arr123 : PdfObject := .array [.int 1, .int 2, .int 3]
private def strHi : PdfObject := .string "hi".toUTF8.toList


/-- A file holding object stream `20 0 obj` (Flate, the three objects of `raw3`) at offset 0. -/
private def file20 : ByteArray :=
  "20 0 obj\n<< /Type /ObjStm /N 3 /First 17 /Filter /FlateDecode /Length 45 >>\nstream\n".toUTF8
    ++ z3 ++ "\nendstream\nendobj\n".toUTF8

/-- Lookup for `file20`: objects 10–12 in stream 20. -/
private def lookup20 : Nat → Option XrefEntry :=
  mkLookup [(20, .inUse 0 0), (10, .compressed 20 0), (11, .compressed 20 1),
    (12, .compressed 20 2), (13, .compressed 20 1), (30, .compressed 31 0), (31, .compressed 20 0),
    (40, .compressed 41 0), (41, .inUse 0 0)]

-- valid fetches through the xref
#guard fc lookup20 file20 10 == .inr dictA
#guard fc lookup20 file20 11 == .inr arr123
#guard fc lookup20 file20 12 == .inr strHi
#guard (fetchCompressedTrace lookup20 Limits.default file20 100 12).parses == 1
#guard (fetchCompressedTrace lookup20 Limits.default file20 100 12).decodes == 1
-- xref index and stream header disagree (13 claims index 1, which holds object 11)
#guard fc lookup20 file20 13 == .inl "malformed@0:object 13 is not at index 1 of object stream 20"
-- nested container: 30 is in 31, which is itself in 20
#guard fc lookup20 file20 30 == .inl "malformed@0:object stream 31 is itself in an object stream"
-- two object streams containing each other: a cycle (task 2.13)
#guard fc (mkLookup [(50, .compressed 51 0), (51, .compressed 50 0)]) file20 50 ==
  .inl "cycle@0:object streams 50 and 51 contain each other"
-- container header mismatch: entry 41 points at `20 0 obj`
#guard fc lookup20 file20 40 ==
  .inl "malformed@0:object header does not match the cross-reference entry"
-- not compressed / missing
#guard (fc lookup20 file20 20).isLeft
#guard (fc lookup20 file20 99).isLeft
-- an uncompressed container, with an indirect /Length
#guard fc (mkLookup [(1, .inUse 0 0), (2, .inUse 87 0), (7, .compressed 1 0)])
  ("1 0 obj\n<< /Type /ObjStm /N 1 /First 4 /Length 2 0 R >>\nstream\n7 0 42\nendstream\nendobj\n"
    ++ "2 0 obj 6 endobj\n").toUTF8 7 == .inr (.int 42)

/-- Bytes of `Tests/adversarial/objstm-self-container.pdf` (378 B, SHA-256 `91dcdb06…41ea`):
the xref stream (object 4 at offset 223) marks object 5 as type 2 in object stream 5. -/
private def selfContainerPdf : ByteArray := ⟨#[
  37, 80, 68, 70, 45, 49, 46, 55, 10, 37, 226, 227, 207, 211, 10, 49, 32, 48, 32, 111, 98, 106,
  10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103, 32, 47, 80, 97,
  103, 101, 115, 32, 50, 32, 48, 32, 82, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 50, 32,
  48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 115, 32,
  47, 75, 105, 100, 115, 32, 91, 51, 32, 48, 32, 82, 93, 32, 47, 67, 111, 117, 110, 116, 32, 49,
  32, 62, 62, 10, 101, 110, 100, 111, 98, 106, 10, 51, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32,
  47, 84, 121, 112, 101, 32, 47, 80, 97, 103, 101, 32, 47, 80, 97, 114, 101, 110, 116, 32, 50,
  32, 48, 32, 82, 32, 47, 77, 101, 100, 105, 97, 66, 111, 120, 32, 91, 48, 32, 48, 32, 54, 49,
  50, 32, 55, 57, 50, 93, 32, 47, 82, 111, 116, 97, 116, 101, 32, 53, 32, 48, 32, 82, 32, 47, 82,
  101, 115, 111, 117, 114, 99, 101, 115, 32, 60, 60, 32, 62, 62, 32, 62, 62, 10, 101, 110, 100,
  111, 98, 106, 10, 52, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47,
  88, 82, 101, 102, 32, 47, 83, 105, 122, 101, 32, 54, 32, 47, 87, 32, 91, 49, 32, 52, 32, 50,
  93, 32, 47, 82, 111, 111, 116, 32, 49, 32, 48, 32, 82, 32, 47, 76, 101, 110, 103, 116, 104, 32,
  52, 50, 32, 62, 62, 10, 115, 116, 114, 101, 97, 109, 10, 0, 0, 0, 0, 0, 255, 255, 1, 0, 0, 0,
  15, 0, 0, 1, 0, 0, 0, 64, 0, 0, 1, 0, 0, 0, 121, 0, 0, 1, 0, 0, 0, 223, 0, 0, 2, 0, 0, 0, 5, 0,
  0, 10, 101, 110, 100, 115, 116, 114, 101, 97, 109, 10, 101, 110, 100, 111, 98, 106, 10, 115,
  116, 97, 114, 116, 120, 114, 101, 102, 10, 50, 50, 51, 10, 37, 37, 69, 79, 70, 10
]⟩

/-- Lookup decoded by hand from the file's xref stream (`/W [1 4 2]`, `/Size 6`). -/
private def selfContainerLookup : Nat → Option XrefEntry :=
  mkLookup [(0, .free 0 65535), (1, .inUse 15 0), (2, .inUse 64 0), (3, .inUse 121 0),
    (4, .inUse 223 0), (5, .compressed 5 0)]

#guard selfContainerPdf.size == 378
#guard fc selfContainerLookup selfContainerPdf 5 ==
  .inl "cycle@0:object 5 is its own object stream"
#guard (fetchCompressedTrace selfContainerLookup Limits.default selfContainerPdf 6 5).parses == 0
-- pointing object 5 at the xref stream instead: a container that is not /Type /ObjStm
#guard fc (mkLookup [(4, .inUse 223 0), (5, .compressed 4 0)]) selfContainerPdf 5 ==
  .inl "malformed@0:object stream: /Type is not /ObjStm"

end Tests

end SafePdf.Core.Xref.ObjStm