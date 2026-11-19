import SafePdf.Core.Xref
import SafePdf.Core.ObjParse
import SafePdf.Core.Lex
import SafePdf.Core.Filter.Flate
import SafePdf.Core.Filter.Predictor

/-!
# Object streams: decoding (Plan.md §5.2, tasks 2.4b, 2.14)

ISO 32000-2 §7.5.7: an object stream is a stream object (`/Type /ObjStm`) whose decoded data
holds `/N` direct objects. The first `/First` bytes are a header of `N` pairs
`objnum offset` (offsets relative to `/First`, in increasing order); the objects follow.

This module holds the decoding of an already parsed object stream (rules O1–O5 of
`Core.Xref.ObjStm`). Task 2.14 split it out of `Core.Xref.ObjStm` so that
`Core.Xref.Length` can decode an object stream while resolving an indirect `/Length` whose
value lives in one (`Core.Xref.ObjStm` imports `Core.Xref.Length` for its container's own
`/Length`). Names stay in the namespace `SafePdf.Core.Xref.ObjStm`.

## Rules

* O1. `decodeObjStm`: `/Type /ObjStm`; `/N` an integer `≥ 0` (above `limits.maxObjects` is
  `Error.limitExceeded .objects`); `/First` an integer `≥ 0`, at most the decoded size;
  `/Extends`, if present, a reference (recorded, not followed).
* O2. Data: no `/Filter` (or `[]`) is raw; `/FlateDecode` (or `[/FlateDecode]`) is inflated
  with `Filter.Flate.flateDecode limits`, then `/DecodeParms` (a dictionary or a one-element
  array) is applied with `Filter.Predictor`; any other filter or filter chain is
  `Error.unsupported`.
* O3. Header: exactly `N` pairs of non-negative integers, lexed by `Lex.next` from the decoded
  bytes `[0, /First)` only, and nothing else in that range.
* O4. Offsets strictly increasing; `/First + offset <` decoded size for every pair; object
  numbers `≥ 1`; object numbers pairwise distinct (S6). These are carried by `ObjStm` as
  proof fields, so `decodeObjStm_offsets_sorted` etc. hold by construction.
* O5. `getObject os limits k`: `ObjParse.parseObject` at `/First + off_k`; the object must end
  at or before the next object's start (`/First + off_{k+1}`, or the end of the data), and
  only white space or comments may follow it in its slice: objects in object streams are
  direct objects (no `n g obj` wrapper, no `stream`), generation implicitly 0.

Error offsets for header and object errors are positions in the *decoded* data; dictionary
errors use offset 0.

## Theorems

* Totality by construction: no recursion except `parsePairs` (structural on the pair count).
* `decodeObjStm_offsets_sorted`, `decodeObjStm_bounds`, `decodeObjStm_nums_pos`,
  `decodeObjStm_nums_nodup`, `decodeObjStm_first_le`, `decodeObjStm_count_le`.
* `getObject_depth`: depth at most `limits.maxObjectDepth`.
-/

namespace SafePdf.Core.Xref.ObjStm

open SafePdf
open SafePdf.Core.Xref (XrefEntry)
open SafePdf.Core.ObjParse (errAt lexErr)

/-! ## Strictly ascending lists -/

/-- Adjacent elements strictly ascending (linear-time check). -/
def adjLt : List Nat → Bool
  | a :: b :: rest => decide (a < b) && adjLt (b :: rest)
  | _ => true

/-- Adjacent-strict implies pairwise strict. -/
theorem pairwise_of_adjLt : (l : List Nat) → adjLt l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [adjLt, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_adjLt (b :: rest) h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst hx; exact h.1
    · exact Nat.lt_trans h.1 ((List.pairwise_cons.mp ih).1 x hx)

/-- Distinctness check in `O(n log n)`: sort, then compare neighbours. -/
def numsDistinct (nums : List Nat) : Bool :=
  adjLt (nums.mergeSort (fun a b => decide (a ≤ b)))

/-- `numsDistinct` is sound. -/
theorem nodup_of_numsDistinct (nums : List Nat) (h : numsDistinct nums = true) : nums.Nodup := by
  have hp := pairwise_of_adjLt _ h
  have hn : (nums.mergeSort (fun a b => decide (a ≤ b))).Nodup := hp.imp Nat.ne_of_lt
  exact (List.mergeSort_perm nums _).nodup_iff.mp hn

/-! ## The decoded object stream -/

/-- A decoded object stream (ISO 32000-2 §7.5.7) with its header invariants (O4). -/
structure ObjStm where
  /-- `/First`: offset of the first object in `data`. -/
  first : Nat
  /-- `/Extends`, if present: the reference `(num, gen)` to another object stream. -/
  extends? : Option (Nat × Nat)
  /-- The decoded stream data. -/
  data : ByteArray
  /-- The header pairs `(object number, offset relative to first)`, in header order. -/
  entries : List (Nat × Nat)
  /-- `/First` lies within the data. -/
  first_le : first ≤ data.size
  /-- Offsets strictly increasing (§7.5.7). -/
  sorted : (entries.map Prod.snd).Pairwise (· < ·)
  /-- Every object starts inside the data. -/
  bounded : ∀ e ∈ entries, first + e.2 < data.size
  /-- Object numbers are at least 1. -/
  numPos : ∀ e ∈ entries, 1 ≤ e.1
  /-- Object numbers are distinct (S6). -/
  distinct : (entries.map Prod.fst).Nodup

/-- Check the invariants of O4 and build the `ObjStm`. -/
def mkObjStm (first : Nat) (ext : Option (Nat × Nat)) (data : ByteArray)
    (entries : List (Nat × Nat)) : Except Error ObjStm :=
  if hf : first ≤ data.size then
    if hs : adjLt (entries.map Prod.snd) = true then
      if hb : entries.all (fun e => decide (first + e.2 < data.size)) = true then
        if hp : entries.all (fun e => decide (1 ≤ e.1)) = true then
          if hn : numsDistinct (entries.map Prod.fst) = true then
            .ok { first, extends? := ext, data, entries
                  first_le := hf
                  sorted := pairwise_of_adjLt _ hs
                  bounded := fun e he => of_decide_eq_true (List.all_eq_true.mp hb e he)
                  numPos := fun e he => of_decide_eq_true (List.all_eq_true.mp hp e he)
                  distinct := nodup_of_numsDistinct _ hn }
          else .error (.malformed 0 "object stream: duplicate object number")
        else .error (.malformed 0 "object stream: object number 0")
      else .error (.malformed 0 "object stream: object offset beyond the data")
    else .error (.malformed 0 "object stream: offsets not increasing")
  else .error (.malformed 0 "object stream: /First beyond the decoded data")

/-! ## Dictionary entries (O1, O2) -/

/-- `/Type` must be `/ObjStm`. -/
def checkType (d : Dict) : Except Error Unit :=
  match d.get? (Name.ofString "Type") with
  | some (.name n) =>
    if n = Name.ofString "ObjStm" then .ok ()
    else .error (.malformed 0 "object stream: /Type is not /ObjStm")
  | _ => .error (.malformed 0 "object stream: /Type is not /ObjStm")

/-- `/N`: an integer, `0 ≤ N ≤ limits.maxObjects`. -/
def getCount (limits : Limits) (d : Dict) : Except Error Nat :=
  match d.get? (Name.ofString "N") with
  | some (.int n) =>
    if n < 0 then .error (.malformed 0 "object stream: negative /N")
    else if n.toNat ≤ limits.maxObjects then .ok n.toNat
    else .error (.limitExceeded .objects)
  | _ => .error (.malformed 0 "object stream: /N missing or not an integer")

/-- `/First`: a non-negative integer. -/
def getFirst (d : Dict) : Except Error Nat :=
  match d.get? (Name.ofString "First") with
  | some (.int n) =>
    if n < 0 then .error (.malformed 0 "object stream: negative /First") else .ok n.toNat
  | _ => .error (.malformed 0 "object stream: /First missing or not an integer")

/-- `/Extends`: absent, or a reference (recorded, not followed). -/
def getExtends (d : Dict) : Except Error (Option (Nat × Nat)) :=
  match d.get? (Name.ofString "Extends") with
  | none => .ok none
  | some (.ref n g) => .ok (some (n, g))
  | some _ => .error (.malformed 0 "object stream: /Extends is not a reference")

/-- The single filter name, if any: `/F`, `[/F]`, absent or `[]`; chains are unsupported. -/
def filterName (d : Dict) : Except Error (Option Name) :=
  match d.get? (Name.ofString "Filter") with
  | none => .ok none
  | some (.name n) => .ok (some n)
  | some (.array []) => .ok none
  | some (.array [.name n]) => .ok (some n)
  | some _ => .error (.unsupported "object stream: filter chain")

/-- The predictor parameters dictionary: absent, a dictionary, or a one-element array. -/
def decodeParms (d : Dict) : Except Error Dict :=
  match d.get? (Name.ofString "DecodeParms") with
  | none => .ok []
  | some (.dict p) => .ok p
  | some (.array []) => .ok []
  | some (.array [.null]) => .ok []
  | some (.array [.dict p]) => .ok p
  | some _ => .error (.malformed 0 "object stream: /DecodeParms is not a dictionary")

/-- Decode the stream data (O2). -/
def decodeData (limits : Limits) (d : Dict) (raw : ByteArray) : Except Error ByteArray :=
  match filterName d with
  | .error e => .error e
  | .ok none => .ok raw
  | .ok (some n) =>
    if n = Name.ofString "FlateDecode" then
      match Filter.Flate.flateDecode limits raw with
      | .error e => .error e
      | .ok out =>
        match decodeParms d with
        | .error e => .error e
        | .ok parms =>
          match Filter.Predictor.Params.ofDict parms with
          | .error e => .error e
          | .ok p => Filter.Predictor.decode p out
    else .error (.unsupported "object stream: filter other than /FlateDecode")

/-! ## Header (O3) -/

/-- Read `k` more pairs `objnum offset` from the header bytes at `pos`, then require the end
of the header. Structural on `k`. -/
def parsePairs (hdr : ByteArray) : Nat → Nat → List (Nat × Nat) →
    Except Error (List (Nat × Nat))
  | 0, pos, acc =>
    match Lex.next hdr pos with
    | .ok none => .ok acc.reverse
    | .ok (some _) => .error (errAt hdr pos "object stream: header longer than /N pairs")
    | .error e => .error (lexErr e)
  | k + 1, pos, acc =>
    match Lex.next hdr pos with
    | .ok (some (.int n, q)) =>
      match Lex.next hdr q with
      | .ok (some (.int off, q2)) =>
        if 0 ≤ n ∧ 0 ≤ off then parsePairs hdr k q2 ((n.toNat, off.toNat) :: acc)
        else .error (errAt hdr pos "object stream: negative number in header")
      | .error e => .error (lexErr e)
      | .ok _ => .error (errAt hdr q "object stream: expected an offset in header")
    | .error e => .error (lexErr e)
    | .ok _ => .error (errAt hdr pos "object stream: expected an object number in header")

/-- **Entry point.** Decode an object stream (rules O1–O4). Does not follow `/Extends`. -/
def decodeObjStm (limits : Limits) (st : Stream) : Except Error ObjStm :=
  match checkType st.dict, getCount limits st.dict, getFirst st.dict, getExtends st.dict with
  | .ok (), .ok n, .ok first, .ok ext =>
    match decodeData limits st.dict st.data with
    | .error e => .error e
    | .ok data =>
      if first ≤ data.size then
        match parsePairs (data.extract 0 first) n 0 [] with
        | .error e => .error e
        | .ok entries => mkObjStm first ext data entries
      else .error (.malformed 0 "object stream: /First beyond the decoded data")
  | .error e, _, _, _ => .error e
  | _, .error e, _, _ => .error e
  | _, _, .error e, _ => .error e
  | _, _, _, .error e => .error e

/-! ## Objects (O5) -/

/-- End of the slice of the `k`-th object: the next object's start, or the end of the data. -/
def sliceEnd (os : ObjStm) (k : Nat) : Nat :=
  match os.entries[k + 1]? with
  | some (_, off') => os.first + off'
  | none => os.data.size

/-- **Entry point.** The `k`-th object of the stream (rule O5); generation implicitly 0. -/
def getObject (os : ObjStm) (limits : Limits) (k : Nat) : Except Error PdfObject :=
  match os.entries[k]? with
  | none => .error (.malformed 0 s!"object stream: index {k} out of range")
  | some (_, off) =>
    match ObjParse.parseObject limits os.data (os.first + off) with
    | .error e => .error e
    | .ok (o, r) =>
      if r ≤ sliceEnd os k then
        if sliceEnd os k ≤ Lex.skipWs os.data r false then .ok o
        else .error (.malformed r "object stream: data after the object (not a direct object)")
      else .error (.malformed r "object stream: object runs past the next object's offset")

/-- The index of object number `num` in the header, if present (unique, by `os.distinct`). -/
def findObject (os : ObjStm) (num : Nat) : Option Nat :=
  os.entries.findIdx? (fun e => e.1 == num)

/-! ## Theorems -/

/-- **Sorted offsets** (§7.5.7 "in increasing order"), by construction. -/
theorem decodeObjStm_offsets_sorted {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : (os.entries.map Prod.snd).Pairwise (· < ·) :=
  os.sorted

/-- **Header bounds**: every object starts inside the decoded data. -/
theorem decodeObjStm_bounds {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : ∀ e ∈ os.entries, os.first + e.2 < os.data.size :=
  os.bounded

/-- `/First` lies within the decoded data. -/
theorem decodeObjStm_first_le {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : os.first ≤ os.data.size :=
  os.first_le

/-- Object numbers in the header are at least 1. -/
theorem decodeObjStm_nums_pos {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : ∀ e ∈ os.entries, 1 ≤ e.1 :=
  os.numPos

/-- Object numbers in the header are distinct (S6). -/
theorem decodeObjStm_nums_nodup {limits : Limits} {st : Stream} {os : ObjStm}
    (_h : decodeObjStm limits st = .ok os) : (os.entries.map Prod.fst).Nodup :=
  os.distinct

/-- `parsePairs` reads exactly `k` pairs. -/
theorem parsePairs_length (hdr : ByteArray) :
    (k pos : Nat) → (acc l : List (Nat × Nat)) → parsePairs hdr k pos acc = .ok l →
    l.length = k + acc.length
  | 0, pos, acc, l, h => by
    unfold parsePairs at h
    split at h
    · cases h; simp
    · cases h
    · cases h
  | k + 1, pos, acc, l, h => by
    unfold parsePairs at h
    split at h
    · split at h
      · split at h
        · have := parsePairs_length hdr k _ _ l h
          simp at this; omega
        · cases h
      · cases h
      · cases h
    · cases h
    · cases h

/-- `getCount` respects `limits.maxObjects`. -/
theorem getCount_le {limits : Limits} {d : Dict} {n : Nat} (h : getCount limits d = .ok n) :
    n ≤ limits.maxObjects := by
  unfold getCount at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h; assumption
      · cases h
  · cases h

/-- `mkObjStm` keeps the entries it was given. -/
theorem mkObjStm_entries {first : Nat} {ext : Option (Nat × Nat)} {data : ByteArray}
    {entries : List (Nat × Nat)} {os : ObjStm} (h : mkObjStm first ext data entries = .ok os) :
    os.entries = entries := by
  unfold mkObjStm at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- **Count bound**: at most `limits.maxObjects` objects (exactly `/N`). -/
theorem decodeObjStm_count_le {limits : Limits} {st : Stream} {os : ObjStm}
    (h : decodeObjStm limits st = .ok os) : os.entries.length ≤ limits.maxObjects := by
  unfold decodeObjStm at h
  split at h
  · next n first ext _ hn _ _ =>
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · next entries he =>
          have h1 := parsePairs_length _ _ _ _ _ he
          have h2 := mkObjStm_entries h
          have h3 := getCount_le hn
          rw [h2, h1]
          simpa using h3
      · cases h
  all_goals cases h

/-- **Depth bound**: an object from an object stream nests at most `limits.maxObjectDepth`. -/
theorem getObject_depth {os : ObjStm} {limits : Limits} {k : Nat} {o : PdfObject}
    (h : getObject os limits k = .ok o) : o.depth ≤ limits.maxObjectDepth := by
  unfold getObject at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hp
      split at h
      · split at h
        · cases h; exact ObjParse.parseObject_depth hp
        · cases h
      · cases h

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}:{m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o w => s!"cycle@{o}:{w}"

/-- Test helper: a stream from string keys. -/
private def mkSt (d : List (String × PdfObject)) (data : ByteArray) : Stream :=
  ⟨d.map (fun e => (Name.ofString e.1, e.2)), data⟩

/-- Test helper: `/Type /ObjStm /N n /First f` plus extra entries. -/
private def osDict (n first : Int) (extra : List (String × PdfObject) := []) :
    List (String × PdfObject) :=
  [("Type", PdfObject.nameOf "ObjStm"), ("N", .int n), ("First", .int first)] ++ extra

/-- Test helper: `decodeObjStm` summarised as its header entries. -/
private def dec (st : Stream) : Sum String (List (Nat × Nat)) :=
  match decodeObjStm Limits.default st with
  | .ok os => .inr os.entries
  | .error e => .inl (errS e)

/-- Test helper: decode, then fetch object `k`. -/
private def obj (st : Stream) (k : Nat) : Sum String PdfObject :=
  match decodeObjStm Limits.default st with
  | .ok os =>
    match getObject os Limits.default k with
    | .ok o => .inr o
    | .error e => .inl (errS e)
  | .error e => .inl (errS e)

/-- Three objects, uncompressed: header `10 0 11 11 12 19 `, `/First 17`. -/
private def raw3 : ByteArray := "10 0 11 11 12 19 << /A 1 >>\n[1 2 3]\n(hi)\n".toUTF8

/-- `raw3` compressed with Python's `zlib.compress` (scratch script, stdlib only). -/
private def z3 : ByteArray := ⟨#[120, 156, 51, 52, 80, 48, 80, 48, 52, 4, 35, 35, 5, 67, 75, 5,
  27, 27, 5, 125, 71, 5, 67, 5, 59, 59, 174, 104, 67, 5, 35, 5, 227, 88, 46, 141, 140, 76, 77,
  46, 0, 153, 183, 7, 166]⟩

/-- `raw3` padded with spaces to 44 bytes, PNG Up predictor (`/Columns 4`), then
`zlib.compress`. -/
private def zp : ByteArray := ⟨#[120, 156, 1, 55, 0, 200, 255, 2, 49, 48, 32, 48, 2, 239, 1, 17,
  240, 2, 17, 0, 239, 17, 2, 1, 239, 17, 8, 2, 238, 28, 11, 231, 2, 15, 5, 228, 17, 2, 241, 253,
  30, 217, 2, 59, 243, 226, 40, 2, 197, 2, 61, 216, 2, 8, 53, 12, 31, 2, 226, 184, 183, 247,
  190, 201, 18, 129]⟩

private def flate : List (String × PdfObject) := [("Filter", PdfObject.nameOf "FlateDecode")]

private def dictA : PdfObject := .dict [(Name.ofString "A", .int 1)]
private def arr123 : PdfObject := .array [.int 1, .int 2, .int 3]
private def strHi : PdfObject := .string "hi".toUTF8.toList

-- N = 3, raw
#guard dec (mkSt (osDict 3 17) raw3) == .inr [(10, 0), (11, 11), (12, 19)]
#guard obj (mkSt (osDict 3 17) raw3) 0 == .inr dictA
#guard obj (mkSt (osDict 3 17) raw3) 1 == .inr arr123
#guard obj (mkSt (osDict 3 17) raw3) 2 == .inr strHi
#guard obj (mkSt (osDict 3 17) raw3) 3 == .inl "malformed@0:object stream: index 3 out of range"
-- N = 3, Flate (also as a one-element filter array), and Flate + PNG predictor
#guard dec (mkSt (osDict 3 17 flate) z3) == .inr [(10, 0), (11, 11), (12, 19)]
#guard obj (mkSt (osDict 3 17 flate) z3) 2 == .inr strHi
#guard obj (mkSt (osDict 3 17 [("Filter", .array [PdfObject.nameOf "FlateDecode"])]) z3) 1 ==
  .inr arr123
#guard obj (mkSt (osDict 3 17 (flate ++ [("DecodeParms", .dict [(Name.ofString "Predictor",
  .int 12), (Name.ofString "Columns", .int 4)])])) zp) 2 == .inr strHi
-- N = 1 and N = 0
#guard dec (mkSt (osDict 1 4) "7 0 42".toUTF8) == .inr [(7, 0)]
#guard obj (mkSt (osDict 1 4) "7 0 42".toUTF8) 0 == .inr (.int 42)
#guard dec (mkSt (osDict 0 0) ByteArray.empty) == .inr []
#guard obj (mkSt (osDict 0 0) ByteArray.empty) 0 ==
  .inl "malformed@0:object stream: index 0 out of range"
-- /Extends is recorded
#guard (match decodeObjStm Limits.default
    (mkSt (osDict 1 4 [("Extends", .ref 9 0)]) "7 0 42".toUTF8) with
  | .ok os => os.extends? == some (9, 0)
  | .error _ => false)
-- decreasing offsets
#guard dec (mkSt (osDict 2 10) "10 5 11 0 42 43".toUTF8) ==
  .inl "malformed@0:object stream: offsets not increasing"
-- /First beyond the data; offset beyond the data
#guard dec (mkSt (osDict 3 100) raw3) ==
  .inl "malformed@0:object stream: /First beyond the decoded data"
#guard dec (mkSt (osDict 1 4) "7 9 42".toUTF8) ==
  .inl "malformed@0:object stream: object offset beyond the data"
-- object spilling past the next offset
#guard obj (mkSt (osDict 2 10) "10 0 11 3 [1 2 3]\n42".toUTF8) 0 ==
  .inl "malformed@17:object stream: object runs past the next object's offset"
#guard obj (mkSt (osDict 2 10) "10 0 11 8 [1 2 3]\n42".toUTF8) 1 == .inr (.int 42)
-- not a direct object: `n g obj` wrapper, `stream`
#guard obj (mkSt (osDict 1 4) "5 0 5 0 obj 1 endobj".toUTF8) 0 ==
  .inl "malformed@5:object stream: data after the object (not a direct object)"
#guard obj (mkSt (osDict 1 4) "5 0 << >> stream".toUTF8) 0 ==
  .inl "malformed@9:object stream: data after the object (not a direct object)"
-- duplicate object numbers; object number 0; header too short / too long
#guard dec (mkSt (osDict 2 10) "10 0 10 2 1 2".toUTF8) ==
  .inl "malformed@0:object stream: duplicate object number"
#guard dec (mkSt (osDict 1 4) "0 0 42".toUTF8) ==
  .inl "malformed@0:object stream: object number 0"
#guard (dec (mkSt (osDict 2 4) "7 0 42".toUTF8)).isLeft
#guard (dec (mkSt (osDict 1 8) "7 0 8 1 42".toUTF8)).isLeft
-- dictionary checks
#guard dec (mkSt [("Type", PdfObject.nameOf "XRef"), ("N", .int 0), ("First", .int 0)]
  ByteArray.empty) == .inl "malformed@0:object stream: /Type is not /ObjStm"
#guard dec (mkSt (osDict (-1) 0) ByteArray.empty) == .inl "malformed@0:object stream: negative /N"
#guard dec (mkSt (osDict 8388608 0) ByteArray.empty) == .inl "limit:SafePdf.LimitKind.objects"
#guard dec (mkSt (osDict 0 0 [("Filter", PdfObject.nameOf "ASCIIHexDecode")]) ByteArray.empty) ==
  .inl "unsupported:object stream: filter other than /FlateDecode"
#guard (dec (mkSt (osDict 3 17 flate) raw3)).isLeft

end Tests

end SafePdf.Core.Xref.ObjStm
