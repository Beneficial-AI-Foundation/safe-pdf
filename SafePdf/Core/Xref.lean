import SafePdf.Core.Object
import SafePdf.Core.Lex
import SafePdf.Core.ObjParse
import SafePdf.Core.Error
import SafePdf.Core.Limits

/-!
# Classic cross-reference tables and trailers

Plan.md §5.2, §6 Phase 2; ISO 32000-2 §7.5.4–7.5.5.

Task 2.1 of the file-structure layer: one classic cross-reference section (`xref` … `trailer`
dictionary) and the `startxref` pointer at the end of the file. Offsets are read and range
checked here but never dereferenced. The `/Prev` chain (2.2), indirect `/Length` (2.3), xref
streams (2.4), newest-revision-wins (2.5) and repair (2.6) build on these types.

## Byte grammar (strict path)

* X1. `findStartxref`: the last `startxref` keyword whose first byte lies in the final
  `window` bytes (default 1024); then at least one whitespace byte; then 1–10 decimal digits
  (the offset, `< bytes.size`); then optional whitespace, `%%EOF`, and only whitespace up to
  the end of input (ISO 32000-2 §7.5.5). Anything else after `%%EOF` is an error.
* X2. A section starts with the bytes `xref` exactly at the given position, followed by a
  whitespace byte (§7.5.4).
* X3. Between lines, whitespace bytes are skipped. A line starting with `trailer` ends the
  table; otherwise it must be a subsection header: 1–10 digits (first object number), one or
  more SP, 1–10 digits (count), optional SPs, an EOL (CR LF, CR or LF).
* X4. Directly after the header come exactly `count` entries of exactly 20 bytes each:
  `nnnnnnnnnn SP ggggg SP k e1 e2` with ten offset digits, five generation digits,
  `k ∈ {n, f}` and a two-byte EOL `e1 e2 ∈ {SP CR, SP LF, CR LF}` (§7.5.4). `entrySpec` is the
  list-level specification; `entryAt` reads the same record from a `ByteArray` and
  `entryAt_eq` proves they agree.
* X5. Range checks: generation `≤ 65535`; an in-use offset `< bytes.size`; a subsection whose
  `count` entries do not fit in the input is an error before any entry is read; the running
  entry total stays `≤ limits.maxObjects` (else `limitExceeded .objects`); object numbers stay
  `≤ limits.maxObjects`.
* X6. After `trailer`, one object (via `Core.ObjParse.parseObject`) which must be a dictionary
  with a non-negative integer `/Size`; `/Prev`, `/XRefStm` (non-negative integers) and `/Root`
  (a reference) are type checked when present (§7.5.5). A `null` value counts as absent.
* X7. Within one section an object number may occur at most once (S6); the entries are
  returned sorted by object number.

## Design for the later tasks

`XrefSection` is a strictly ascending `List (Nat × XrefEntry)` that carries its sortedness
proof, so 2.2/2.5 can merge revisions with a linear merge and keep "one entry per object
number" as a type invariant. `XrefEntry.compressed` is the type-2 entry of xref streams
(§7.5.8.3); classic tables never produce it. `Trailer` keeps the raw dictionary next to the
typed, validated fields.

## Totality

Every loop is bounded: `entries` is structural in the entry count (and the count is checked
against the remaining bytes first), `sections`, `skipWhite`, `spacesAt` recurse on
`bytes.size - pos` with progress proven (`header_pos`), digit runs and the backward
`startxref` scan are structural in a fuel bounded by 10 and by `window`. No offsets are
followed.
-/

namespace SafePdf.Core.Xref

open SafePdf

/-! ## Types -/

/-- One cross-reference entry (ISO 32000-2 §7.5.4, §7.5.8.3). -/
inductive XrefEntry where
  /-- A free entry: next free object number and the generation to use on reuse. -/
  | free (nextFree : Nat) (gen : Nat)
  /-- An in-use entry: byte offset of `n g obj` and the generation number. -/
  | inUse (offset : Nat) (gen : Nat)
  /-- An object stored in an object stream (xref streams only, task 2.4): the object number
  of the containing stream and the index within it. Never produced by classic tables. -/
  | compressed (objStm : Nat) (index : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Adjacent keys strictly ascending: the executable check behind `XrefSection.sorted`. -/
def strictAsc : List (Nat × XrefEntry) → Bool
  | a :: b :: rest => decide (a.1 < b.1) && strictAsc (b :: rest)
  | _ => true

/-- One cross-reference section: entries keyed by object number, strictly ascending (hence
at most one entry per object number, S6). -/
structure XrefSection where
  /-- `(object number, entry)`, strictly ascending by object number. -/
  entries : List (Nat × XrefEntry)
  /-- The sortedness invariant. -/
  sorted : entries.Pairwise (fun a b => a.1 < b.1)

/-- The trailer of a section (ISO 32000-2 §7.5.5): the dictionary and its typed entries. -/
structure Trailer where
  /-- The trailer dictionary as parsed. -/
  dict : Dict
  /-- `/Size`: one more than the highest object number in the file. -/
  size : Nat
  /-- `/Prev`: offset of the previous section, if any (followed by task 2.2). -/
  prev? : Option Nat
  /-- `/Root`: the catalog reference `(num, gen)`, if present. -/
  root? : Option (Nat × Nat)
  /-- `/XRefStm`: offset of the hybrid-file xref stream, if any (task 2.4/2.5). -/
  xrefStm? : Option Nat
  /-- Whether `/Encrypt` is present (encrypted files are unsupported by the strict path). -/
  encrypted : Bool
  deriving Repr

/-! ## Byte helpers -/

/-- Bytes of `xref`. -/
def kwXref : List UInt8 := [120, 114, 101, 102]
/-- Bytes of `trailer`. -/
def kwTrailer : List UInt8 := [116, 114, 97, 105, 108, 101, 114]
/-- Bytes of `startxref`. -/
def kwStartxref : List UInt8 := [115, 116, 97, 114, 116, 120, 114, 101, 102]
/-- Bytes of `%%EOF`. -/
def kwEOF : List UInt8 := [37, 37, 69, 79, 70]

/-- Whether `pat` occurs in `bytes` at position `p`. -/
def matchAt (bytes : ByteArray) (p : Nat) : List UInt8 → Bool
  | [] => true
  | c :: cs => bytes[p]? == some c && matchAt bytes (p + 1) cs

/-- Skip whitespace bytes (ISO 32000-2 §7.2.3) from `p`. -/
def skipWhite (bytes : ByteArray) (p : Nat) : Nat :=
  if h : p < bytes.size then
    if Lex.isWhite bytes[p] then skipWhite bytes (p + 1) else p
  else p
termination_by bytes.size - p

/-- Skip SP bytes from `p`. -/
def spacesAt (bytes : ByteArray) (p : Nat) : Nat :=
  if h : p < bytes.size then
    if bytes[p] == 32 then spacesAt bytes (p + 1) else p
  else p
termination_by bytes.size - p

/-- Whether the byte at `p` is a decimal digit. -/
def digitAt (bytes : ByteArray) (p : Nat) : Bool :=
  match bytes[p]? with
  | some b => Lex.isDigit b
  | none => false

/-- Read at most `fuel` decimal digits from `p`, accumulating into `acc`; returns the value
and the position after the digits. -/
def digitsAt (bytes : ByteArray) (p acc : Nat) : Nat → Nat × Nat
  | 0 => (acc, p)
  | f + 1 =>
    match bytes[p]? with
    | some b =>
      if Lex.isDigit b then digitsAt bytes (p + 1) (acc * 10 + (b.toNat - 48)) f else (acc, p)
    | none => (acc, p)

/-- An unsigned integer of 1–10 digits at `p` (not followed by an 11th digit): the value and
the position after it. -/
def natAt (bytes : ByteArray) (p : Nat) : Option (Nat × Nat) :=
  match digitsAt bytes p 0 10 with
  | (v, e) => if p < e && !digitAt bytes e then some (v, e) else none

/-- An end-of-line marker at `p` (CR LF, CR or LF): the position after it. -/
def eolAt (bytes : ByteArray) (p : Nat) : Option Nat :=
  if bytes[p]? = some 13 then
    if bytes[p + 1]? = some 10 then some (p + 2) else some (p + 1)
  else if bytes[p]? = some 10 then some (p + 1)
  else none

/-! ## The 20-byte entry (X4) -/

/-- The value of a list of decimal digits, or `none` if some byte is not a digit. -/
def digitsVal : List UInt8 → Nat → Option Nat
  | [], acc => some acc
  | b :: bs, acc => if Lex.isDigit b then digitsVal bs (acc * 10 + (b.toNat - 48)) else none

/-- The two-byte entry EOL: `SP CR`, `SP LF` or `CR LF` (§7.5.4). -/
def eolOk (e1 e2 : UInt8) : Bool :=
  (e1 == 32 && (e2 == 13 || e2 == 10)) || (e1 == 13 && e2 == 10)

/-- Decode the fields of an entry: ten offset digits `o`, separator `s1`, five generation
digits `g`, separator `s2`, kind `k` and EOL `e1 e2`. -/
def entryFields (o : List UInt8) (s1 : UInt8) (g : List UInt8) (s2 k e1 e2 : UInt8) :
    Option XrefEntry :=
  if s1 == 32 && s2 == 32 && eolOk e1 e2 then
    match digitsVal o 0, digitsVal g 0 with
    | some off, some gen =>
      if k == 110 then some (.inUse off gen)
      else if k == 102 then some (.free off gen)
      else none
    | _, _ => none
  else none

/-- **Spec** of one entry (X4): exactly 20 bytes `nnnnnnnnnn ggggg k e1e2`; any other length
is `none`. -/
def entrySpec (l : List UInt8) : Option XrefEntry :=
  match l with
  | [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, s1, g0, g1, g2, g3, g4, s2, k, e1, e2] =>
    entryFields [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9] s1 [g0, g1, g2, g3, g4] s2 k e1 e2
  | _ => none

/-- **Impl** of one entry: the 20-byte record at `p` of `bytes`, read by index. -/
def entryAt (bytes : ByteArray) (p : Nat) : Option XrefEntry :=
  if h : p + 20 ≤ bytes.size then
    entryFields
      [bytes[p], bytes[p + 1], bytes[p + 2], bytes[p + 3], bytes[p + 4], bytes[p + 5],
        bytes[p + 6], bytes[p + 7], bytes[p + 8], bytes[p + 9]]
      bytes[p + 10]
      [bytes[p + 11], bytes[p + 12], bytes[p + 13], bytes[p + 14], bytes[p + 15]]
      bytes[p + 16] bytes[p + 17] bytes[p + 18] bytes[p + 19]
  else none

/-- Range check of an entry in a classic table of an input of `size` bytes (X5). -/
def entryOk (size : Nat) : XrefEntry → Bool
  | .free _ g => decide (g ≤ 65535)
  | .inUse o g => decide (o < size) && decide (g ≤ 65535)
  | .compressed _ _ => false

/-! ## Subsections and sections (X3–X5, X7) -/

/-- A subsection header at `q` (X3): first object number, count, and the position after the
header's EOL. -/
def header (bytes : ByteArray) (q : Nat) : Option (Nat × Nat × Nat) :=
  match natAt bytes q with
  | none => none
  | some (start, e1) =>
    if bytes[e1]? = some 32 then
      match natAt bytes (spacesAt bytes e1) with
      | none => none
      | some (count, e2) =>
        match eolAt bytes (spacesAt bytes e2) with
        | none => none
        | some e3 => some (start, count, e3)
    else none

/-- Read `k` consecutive entries at `p`, for object numbers `num, num + 1, …`, onto the
reversed accumulator `acc`. -/
def entries (bytes : ByteArray) (p num : Nat) :
    Nat → List (Nat × XrefEntry) → Except Error (List (Nat × XrefEntry))
  | 0, acc => .ok acc
  | k + 1, acc =>
    match entryAt bytes p with
    | none => .error (.malformed p "malformed cross-reference entry")
    | some e =>
      if entryOk bytes.size e then entries bytes (p + 20) (num + 1) k ((num, e) :: acc)
      else .error (.malformed p "cross-reference entry out of range")

/-- `spacesAt` never moves backwards. -/
theorem le_spacesAt (bytes : ByteArray) (p : Nat) : p ≤ spacesAt bytes p := by
  fun_induction spacesAt bytes p <;> omega

/-- `skipWhite` never moves backwards. -/
theorem le_skipWhite (bytes : ByteArray) (p : Nat) : p ≤ skipWhite bytes p := by
  fun_induction skipWhite bytes p <;> omega

/-- `skipWhite` stays within the input when it starts within it. -/
theorem skipWhite_le (bytes : ByteArray) (p : Nat) (h : p ≤ bytes.size) :
    skipWhite bytes p ≤ bytes.size := by
  fun_induction skipWhite bytes p <;> omega

/-- Progress of `natAt`. -/
theorem natAt_pos {bytes : ByteArray} {p v e : Nat} (h : natAt bytes p = some (v, e)) :
    p < e := by
  unfold natAt at h
  split at h
  rename_i v' e' _
  by_cases hc : (p < e' && !digitAt bytes e') = true
  · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  · simp [hc] at h

/-- Progress of `eolAt`. -/
theorem eolAt_pos {bytes : ByteArray} {p e : Nat} (h : eolAt bytes p = some e) : p < e := by
  unfold eolAt at h
  split at h
  · split at h <;> (simp at h; omega)
  · split at h
    · simp at h; omega
    · simp at h

/-- Progress of `header`: the position after the header lies after `q`. -/
theorem header_pos {bytes : ByteArray} {q start count e : Nat}
    (h : header bytes q = some (start, count, e)) : q < e := by
  unfold header at h
  split at h
  · simp at h
  · rename_i start' e1 h1
    have := natAt_pos h1
    split at h
    · split at h
      · simp at h
      · rename_i count' e2 h2
        have := natAt_pos h2
        have := le_spacesAt bytes e1
        have := le_spacesAt bytes e2
        split at h
        · simp at h
        · rename_i e3 h3
          have := eolAt_pos h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega
    · simp at h

/-- The subsection loop at a line start `q` (X3–X5). `total = acc.length` is the number of
entries read so far. Returns the reversed entries and the position after `trailer`. -/
def sections (limits : Limits) (bytes : ByteArray) (q total : Nat)
    (acc : List (Nat × XrefEntry)) : Except Error (List (Nat × XrefEntry) × Nat) :=
  if matchAt bytes q kwTrailer then .ok (acc, q + 7)
  else
    match header bytes q with
    | none => .error (.malformed q "expected a subsection header or trailer")
    | some (start, count, e) =>
      if limits.maxObjects < total + count then .error (.limitExceeded .objects)
      else if limits.maxObjects + 1 < start + count then
        .error (.malformed q "subsection exceeds the object-number limit")
      else if _hs : bytes.size < e + 20 * count then
        .error (.malformed e "subsection extends past end of input")
      else
        match entries bytes e start count acc with
        | .error err => .error err
        | .ok acc' =>
          -- `q < e` always holds (`header_pos`); the guard keeps the definition simple.
          if _hq : q < e then
            sections limits bytes (skipWhite bytes (e + 20 * count)) (total + count) acc'
          else .error (.malformed q "internal: no progress")
termination_by bytes.size - q
decreasing_by
  have := le_skipWhite bytes (e + 20 * count)
  omega

/-- Build a section from the collected entries: sort by object number (stable merge sort),
then require strictly ascending numbers; a duplicate yields `none` (X7, S6). -/
def ofSorted (s : List (Nat × XrefEntry)) : Option XrefSection :=
  if h : strictAsc s = true then
    some ⟨s, by
      induction s with
      | nil => exact List.Pairwise.nil
      | cons a l ih =>
        cases l with
        | nil => exact List.pairwise_singleton _ _
        | cons b rest =>
          simp only [strictAsc, Bool.and_eq_true, decide_eq_true_eq] at h
          have ih' := ih h.2
          refine List.Pairwise.cons ?_ ih'
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h.1
          · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih' hx)⟩
  else none

/-- Sort the collected entries and build the section (X7). -/
def mkSection (acc : List (Nat × XrefEntry)) : Option XrefSection :=
  ofSorted (acc.mergeSort (fun a b => decide (a.1 ≤ b.1)))

/-! ## Trailer (X6) -/

/-- Key `/Size`. -/
def nameSize : Name := Name.ofString "Size"
/-- Key `/Prev`. -/
def namePrev : Name := Name.ofString "Prev"
/-- Key `/Root`. -/
def nameRoot : Name := Name.ofString "Root"
/-- Key `/XRefStm`. -/
def nameXRefStm : Name := Name.ofString "XRefStm"
/-- Key `/Encrypt`. -/
def nameEncrypt : Name := Name.ofString "Encrypt"

/-- An optional non-negative integer entry of `d`. -/
def natField (d : Dict) (k : Name) (at_ : Nat) (what : String) : Except Error (Option Nat) :=
  match Dict.get? d k with
  | none => .ok none
  | some (.int i) =>
    if 0 ≤ i then .ok (some i.toNat) else .error (.malformed at_ s!"negative {what}")
  | some _ => .error (.malformed at_ s!"{what} is not an integer")

/-- An optional reference entry of `d`. -/
def refField (d : Dict) (k : Name) (at_ : Nat) (what : String) :
    Except Error (Option (Nat × Nat)) :=
  match Dict.get? d k with
  | none => .ok none
  | some (.ref n g) => .ok (some (n, g))
  | some _ => .error (.malformed at_ s!"{what} is not a reference")

/-- Validate a trailer dictionary found at offset `at_` (X6). -/
def Trailer.ofDict (d : Dict) (at_ : Nat) : Except Error Trailer := do
  let size? ← natField d nameSize at_ "/Size"
  let prev? ← natField d namePrev at_ "/Prev"
  let root? ← refField d nameRoot at_ "/Root"
  let xrefStm? ← natField d nameXRefStm at_ "/XRefStm"
  match size? with
  | none => .error (.malformed at_ "trailer without /Size")
  | some size =>
    .ok { dict := d, size, prev?, root?, xrefStm?,
          encrypted := (Dict.get? d nameEncrypt).isSome }

/-! ## Entry points -/

/-- The trailer dictionary after the `trailer` keyword ending at `t`, and the section. -/
def finish (limits : Limits) (bytes : ByteArray) (pos t : Nat)
    (acc : List (Nat × XrefEntry)) : Except Error (XrefSection × Trailer × Nat) :=
  match ObjParse.parseObject limits bytes t with
  | .error e => .error e
  | .ok (.dict d, r) =>
    match Trailer.ofDict d t with
    | .error e => .error e
    | .ok tr =>
      match mkSection acc with
      | none => .error (.malformed pos "duplicate object number in cross-reference section")
      | some sec => .ok (sec, tr, r)
  | .ok _ => .error (.malformed t "trailer is not a dictionary")

/-- **Entry point.** The classic cross-reference section starting at `pos` (keyword `xref`)
and its trailer (X2–X7). Returns the section, the trailer and the position after the trailer
dictionary. Offsets are range-checked, not dereferenced. -/
def parseXrefTable (limits : Limits) (bytes : ByteArray) (pos : Nat) :
    Except Error (XrefSection × Trailer × Nat) :=
  if matchAt bytes pos kwXref && (bytes[pos + 4]?.map Lex.isWhite == some true) then
    match sections limits bytes (skipWhite bytes (pos + 4)) 0 [] with
    | .error e => .error e
    | .ok (acc, t) => finish limits bytes pos t acc
  else .error (.malformed pos "expected xref keyword")

/-- Search backwards for `pat` at positions `i, i - 1, …`, at most `k` positions. -/
def scanBack (bytes : ByteArray) (pat : List UInt8) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, k + 1 =>
    if matchAt bytes i pat then some i
    else if i = 0 then none
    else scanBack bytes pat (i - 1) k

/-- The `startxref` offset with a configurable search window (X1). -/
def findStartxrefIn (window : Nat) (bytes : ByteArray) : Except Error Nat :=
  match scanBack bytes kwStartxref (bytes.size - 9) (window - 8) with
  | none => .error (.malformed bytes.size "startxref not found")
  | some i =>
    if i + 9 < skipWhite bytes (i + 9) then
      match natAt bytes (skipWhite bytes (i + 9)) with
      | none => .error (.malformed (i + 9) "expected an offset after startxref")
      | some (off, e) =>
        if matchAt bytes (skipWhite bytes e) kwEOF then
          if skipWhite bytes (skipWhite bytes e + 5) = bytes.size then
            if off < bytes.size then .ok off
            else .error (.malformed (i + 9) "startxref offset beyond end of input")
          else .error (.malformed (skipWhite bytes (skipWhite bytes e + 5)) "data after %%EOF")
        else .error (.malformed (skipWhite bytes e) "expected %%EOF")
    else .error (.malformed (i + 9) "expected whitespace after startxref")

/-- **Entry point.** The offset after the last `startxref` in the final `window` bytes
(default 1024), followed by `%%EOF` and only whitespace (X1). -/
def findStartxref (bytes : ByteArray) (window : Nat := 1024) : Except Error Nat :=
  findStartxrefIn window bytes

/-! ## Spec agreement for the 20-byte entry -/

/-- `entrySpec` of a list whose length is not 20 is `none`. -/
theorem entrySpec_of_length_ne {l : List UInt8} (h : l.length ≠ 20) : entrySpec l = none := by
  unfold entrySpec
  split
  · simp at h
  · rfl

/-- One step of the `ByteArray`-to-list bridge. -/
theorem drop_cons {bytes : ByteArray} {p : Nat} (h : p < bytes.size) :
    bytes.data.toList.drop p = bytes[p] :: bytes.data.toList.drop (p + 1) :=
  List.drop_eq_getElem_cons (by simpa using h)

/-- **The `ByteArray` entry reader agrees with the list spec** on the 20 bytes at `p`
(no hypothesis on `p`: past the end both sides are `none`). -/
theorem entryAt_eq (bytes : ByteArray) (p : Nat) :
    entryAt bytes p = entrySpec ((bytes.data.toList.drop p).take 20) := by
  unfold entryAt
  by_cases h : p + 20 ≤ bytes.size
  · simp only [h, ↓reduceDIte]
    rw [drop_cons (p := p) (by omega), drop_cons (p := p + 1) (by omega),
      drop_cons (p := p + 1 + 1) (by omega), drop_cons (p := p + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (by omega),
      drop_cons (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (by omega),
      drop_cons
        (p := p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (by omega)]
    rfl
  · simp only [h, ↓reduceDIte]
    refine (entrySpec_of_length_ne ?_).symm
    simp
    omega

/-! ## Invariants -/

/-- `entries` keeps every entry range-checked and adds exactly `k` entries. -/
theorem entries_ok {bytes : ByteArray} {p num k : Nat} {acc acc' : List (Nat × XrefEntry)}
    (h : entries bytes p num k acc = .ok acc')
    (hacc : ∀ x ∈ acc, entryOk bytes.size x.2 = true) :
    (∀ x ∈ acc', entryOk bytes.size x.2 = true) ∧ acc'.length = acc.length + k := by
  induction k generalizing p num acc with
  | zero =>
    simp only [entries, Except.ok.injEq] at h
    subst h
    exact ⟨hacc, rfl⟩
  | succ k ih =>
    simp only [entries] at h
    split at h
    · simp at h
    · rename_i e _
      by_cases he : entryOk bytes.size e = true
      · simp only [he, ↓reduceIte] at h
        have hacc2 : ∀ x ∈ (num, e) :: acc, entryOk bytes.size x.2 = true := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact he
          · exact hacc x hx
        have := ih h hacc2
        refine ⟨this.1, ?_⟩
        rw [this.2]
        simp
        omega
      · simp [he] at h

/-- A nonempty `matchAt` succeeds only inside the input. -/
theorem matchAt_le {bytes : ByteArray} {p : Nat} {c : UInt8} {cs : List UInt8}
    (h : matchAt bytes p (c :: cs) = true) : p + (c :: cs).length ≤ bytes.size := by
  induction cs generalizing p c with
  | nil =>
    simp only [matchAt, Bool.and_true, beq_iff_eq] at h
    rcases Nat.lt_or_ge p bytes.size with hp | hp
    · simp; omega
    · rw [getElem?_neg bytes p (by omega)] at h; simp at h
  | cons d ds ih =>
    rw [matchAt, Bool.and_eq_true] at h
    have h1 := ih (p := p + 1) (c := d) h.2
    simp at h1 ⊢
    omega

/-- Invariant of the subsection loop: range-checked entries, at most `limits.maxObjects` of
them, and the returned position lies after `q` and within the input. -/
theorem sections_ok {limits : Limits} {bytes : ByteArray} {q total : Nat}
    {acc acc' : List (Nat × XrefEntry)} {r : Nat}
    (h : sections limits bytes q total acc = .ok (acc', r))
    (ht : total = acc.length) (hle : acc.length ≤ limits.maxObjects)
    (hacc : ∀ x ∈ acc, entryOk bytes.size x.2 = true) :
    (∀ x ∈ acc', entryOk bytes.size x.2 = true) ∧ acc'.length ≤ limits.maxObjects ∧
      q < r ∧ r ≤ bytes.size := by
  induction q, total, acc using sections.induct limits bytes with
  | case1 q total acc hm =>
    rw [sections] at h
    simp only [hm, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := matchAt_le (c := 116) (cs := [114, 97, 105, 108, 101, 114]) hm
    simp at this
    exact ⟨hacc, hle, by omega, by omega⟩
  | case2 q total acc hm hh =>
    rw [sections] at h
    simp [hm, hh] at h
  | case3 q total acc hm start count e hh hlim =>
    rw [sections] at h
    simp [hm, hh, hlim] at h
  | case4 q total acc hm start count e hh hlim hnum =>
    rw [sections] at h
    simp [hm, hh, hlim, hnum] at h
  | case5 q total acc hm start count e hh hlim hnum hsz =>
    rw [sections] at h
    simp [hm, hh, hlim, hnum, hsz] at h
  | case6 q total acc hm start count e hh hlim hnum hsz err he =>
    rw [sections] at h
    simp [hm, hh, hlim, hnum, hsz, he] at h
  | case8 q total acc hm start count e hh hlim hnum hsz acc2 he hq =>
    exact absurd (header_pos hh) hq
  | case7 q total acc hm start count e hh hlim hnum hsz acc2 he hq ih =>
    rw [sections] at h
    simp only [hm, hh, hlim, hnum, hsz, he, hq, Bool.false_eq_true, ↓reduceIte,
      ↓reduceDIte] at h
    have hent := entries_ok he hacc
    have hw := le_skipWhite bytes (e + 20 * count)
    have := ih h (by omega) (by omega) hent.1
    exact ⟨this.1, this.2.1, by omega, this.2.2.2⟩

/-! ## Main theorems -/

/-- Every section has pairwise distinct object numbers (S6 within a section). -/
theorem XrefSection.keys_nodup (sec : XrefSection) : (sec.entries.map Prod.fst).Nodup := by
  have h := sec.sorted
  unfold List.Nodup
  rw [List.pairwise_map]
  exact h.imp (fun hab => Nat.ne_of_lt hab)

/-- `ofSorted` keeps the list as it is. -/
theorem ofSorted_entries {s : List (Nat × XrefEntry)} {sec : XrefSection}
    (h : ofSorted s = some sec) : sec.entries = s := by
  unfold ofSorted at h
  split at h
  · cases h; rfl
  · simp at h

/-- `mkSection` keeps exactly the collected entries (it only reorders them). -/
theorem mkSection_mem {acc : List (Nat × XrefEntry)} {sec : XrefSection}
    (h : mkSection acc = some sec) (x : Nat × XrefEntry) : x ∈ sec.entries ↔ x ∈ acc := by
  rw [ofSorted_entries h, List.mem_mergeSort]

/-- `mkSection` keeps the number of entries. -/
theorem mkSection_length {acc : List (Nat × XrefEntry)} {sec : XrefSection}
    (h : mkSection acc = some sec) : sec.entries.length = acc.length := by
  rw [ofSorted_entries h, List.length_mergeSort]

/-- What a successful `finish` guarantees. -/
theorem finish_ok {limits : Limits} {bytes : ByteArray} {pos t : Nat}
    {acc : List (Nat × XrefEntry)} {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : finish limits bytes pos t acc = .ok (sec, tr, r)) :
    mkSection acc = some sec ∧ t < r ∧ r ≤ bytes.size := by
  unfold finish at h
  split at h
  · simp at h
  · rename_i d r' hp
    have hpos := ObjParse.parseObject_pos hp
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i sec' hs
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        exact ⟨hs, hpos⟩
  · simp at h

/-- What a successful `parseXrefTable` consists of. -/
theorem parseXrefTable_ok {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : parseXrefTable limits bytes pos = .ok (sec, tr, r)) :
    ∃ acc t, sections limits bytes (skipWhite bytes (pos + 4)) 0 [] = .ok (acc, t) ∧
      finish limits bytes pos t acc = .ok (sec, tr, r) := by
  unfold parseXrefTable at h
  split at h
  · split at h
    · simp at h
    · rename_i acc t hs
      exact ⟨acc, t, hs, h⟩
  · simp at h

/-- The collected entries of a successful parse, with the loop invariant. -/
theorem parseXrefTable_entries {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : parseXrefTable limits bytes pos = .ok (sec, tr, r)) :
    (∀ x ∈ sec.entries, entryOk bytes.size x.2 = true) ∧
      sec.entries.length ≤ limits.maxObjects ∧ pos < r ∧ r ≤ bytes.size := by
  obtain ⟨acc, t, hs, hf⟩ := parseXrefTable_ok h
  have hl := sections_ok hs rfl (Nat.zero_le _) (by simp)
  have hfin := finish_ok hf
  have hw := le_skipWhite bytes (pos + 4)
  refine ⟨fun x hx => hl.1 x ((mkSection_mem hfin.1 x).mp hx), ?_, by omega, hfin.2.2⟩
  rw [mkSection_length hfin.1]
  exact hl.2.1

/-- **(a)** Every in-use offset in a successfully parsed section lies inside the input. -/
theorem parseXrefTable_inUse_lt {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : parseXrefTable limits bytes pos = .ok (sec, tr, r)) {n o g : Nat}
    (hm : (n, XrefEntry.inUse o g) ∈ sec.entries) : o < bytes.size := by
  have := (parseXrefTable_entries h).1 _ hm
  simp only [entryOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- Every generation number in a successfully parsed section is at most 65535, and no entry
is `compressed`. -/
theorem parseXrefTable_gen_le {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : parseXrefTable limits bytes pos = .ok (sec, tr, r)) {x : Nat × XrefEntry}
    (hm : x ∈ sec.entries) :
    match x.2 with
    | .free _ g => g ≤ 65535
    | .inUse _ g => g ≤ 65535
    | .compressed _ _ => False := by
  have := (parseXrefTable_entries h).1 _ hm
  revert this
  cases x.2 <;> simp [entryOk]

/-- **(b)** A successfully parsed section has at most `limits.maxObjects` entries. -/
theorem parseXrefTable_length_le {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : parseXrefTable limits bytes pos = .ok (sec, tr, r)) :
    sec.entries.length ≤ limits.maxObjects :=
  (parseXrefTable_entries h).2.1

/-- **(c)** No object number occurs twice in a successfully parsed section (S6). -/
theorem parseXrefTable_nodup {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (_h : parseXrefTable limits bytes pos = .ok (sec, tr, r)) :
    (sec.entries.map Prod.fst).Nodup :=
  sec.keys_nodup

/-- **(d)** Progress: the returned position lies after `pos` and within the input. -/
theorem parseXrefTable_pos {limits : Limits} {bytes : ByteArray} {pos : Nat}
    {sec : XrefSection} {tr : Trailer} {r : Nat}
    (h : parseXrefTable limits bytes pos = .ok (sec, tr, r)) : pos < r ∧ r ≤ bytes.size :=
  (parseXrefTable_entries h).2.2

/-- The `startxref` offset lies inside the input. -/
theorem findStartxref_lt {bytes : ByteArray} {window off : Nat}
    (h : findStartxref bytes window = .ok off) : off < bytes.size := by
  unfold findStartxref findStartxrefIn at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · split at h
          · split at h
            · simp only [Except.ok.injEq] at h
              omega
            · simp at h
          · simp at h
        · simp at h
    · simp at h

/-! ## Tests -/

section Tests

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o _ => s!"malformed@{o}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o _ => s!"cycle@{o}"

/-- Test helper: `parseXrefTable` summarised as (entries, /Size, /Root, /Prev, end). -/
private def pxl (lim : Limits) (b : ByteArray) (pos : Nat) :
    Sum String (List (Nat × XrefEntry) × Nat × Option (Nat × Nat) × Option Nat × Nat) :=
  match parseXrefTable lim b pos with
  | .ok (sec, tr, r) => .inr (sec.entries, tr.size, tr.root?, tr.prev?, r)
  | .error e => .inl (errS e)

/-- Test helper: `pxl` with default limits on a string at position `pos`. -/
private def px (s : String) (pos : Nat := 0) :=
  pxl Limits.default s.toUTF8 pos

/-- Test helper: `findStartxref` summarised. -/
private def fsx (s : String) (window : Nat := 1024) : Sum String Nat :=
  match findStartxref s.toUTF8 window with
  | .ok n => .inr n
  | .error e => .inl (errS e)

/-- Test helper: `n` spaces, used as padding so that offsets fall inside the input. -/
private def pad (n : Nat) : String := "".pushn ' ' n

/-- The tail of `Tests/adversarial/minimal-valid.pdf` from byte 404 (its `xref` keyword). -/
private def minimalTail : String :=
  "xref\n0 6\n0000000000 65535 f \n0000000015 00000 n \n0000000064 00000 n \n" ++
  "0000000121 00000 n \n0000000247 00000 n \n0000000334 00000 n \n" ++
  "trailer\n<< /Size 6 /Root 1 0 R >>\nstartxref\n404\n%%EOF\n"

/-- The same layout as `minimal-valid.pdf` (587 bytes) with the first 404 bytes blanked. -/
private def minimal : String := pad 404 ++ minimalTail

-- X4 entry spec on literal records, and agreement with the reader
#guard entrySpec "0000000015 00000 n \n".toUTF8.data.toList == some (.inUse 15 0)
#guard entrySpec "0000000000 65535 f\r\n".toUTF8.data.toList == some (.free 0 65535)
#guard entrySpec "0000000000 65535 f \r".toUTF8.data.toList == some (.free 0 65535)
#guard entrySpec "0000000015 00000 n\n\n".toUTF8.data.toList == none
#guard entrySpec "0000000015 00000 x \n".toUTF8.data.toList == none
#guard entrySpec "000000001a 00000 n \n".toUTF8.data.toList == none
#guard entrySpec "0000000015 00000 n \n ".toUTF8.data.toList == none
#guard entryAt "  0000000015 00000 n \n".toUTF8 2 == some (.inUse 15 0)
#guard entryAt "0000000015 00000 n ".toUTF8 0 == none
-- X1: startxref
#guard minimal.toUTF8.size == 587
#guard fsx minimal == .inr 404
#guard fsx (minimal ++ "\r\n  \n") == .inr 404
#guard fsx (minimal ++ "junk") == .inl "malformed@587"
#guard fsx (pad 404 ++ "startxref\n404\n") == .inl "malformed@418"
#guard fsx (pad 404 ++ "startxref\n404\n%%EO") == .inl "malformed@418"
#guard fsx (pad 404 ++ "startxref\n999\n%%EOF") == .inl "malformed@413"
#guard fsx (pad 404 ++ "startxref404\n%%EOF") == .inl "malformed@413"
#guard fsx (pad 404 ++ "startxref\n\n%%EOF") == .inl "malformed@413"
#guard fsx "%%EOF" == .inl "malformed@5"
#guard fsx "" == .inl "malformed@0"
-- the last startxref wins; the window bounds the search
#guard fsx (pad 404 ++ "startxref\n1\n%%EOF\nstartxref\n2\n%%EOF\n") == .inr 2
#guard fsx (pad 404 ++ "startxref\n1\n%%EOF" ++ pad 2000) == .inl "malformed@2421"
#guard fsx (pad 404 ++ "startxref\n1\n%%EOF" ++ pad 2000) 4096 == .inr 1
-- X2–X7: the minimal table
#guard px minimal 404 == .inr ([(0, .free 0 65535), (1, .inUse 15 0), (2, .inUse 64 0),
  (3, .inUse 121 0), (4, .inUse 247 0), (5, .inUse 334 0)], 6, some (1, 0), none, 566)
#guard px minimal 403 == .inl "malformed@403"
#guard px minimal 405 == .inl "malformed@405"
-- multiple subsections (out of order), blank lines, header with trailing SP and CR LF
#guard px (pad 100 ++ "xref\r\n7 2 \r\n0000000010 00000 n\r\n0000000020 00001 n\r\n\r\n" ++
    "0 1\n0000000000 65535 f \n3 1\n0000000030 00000 n \ntrailer <</Size 9 /Prev 5>>") 100 ==
  .inr ([(0, .free 0 65535), (3, .inUse 30 0), (7, .inUse 10 0), (8, .inUse 20 1)], 9, none,
    some 5, 229)
-- the three entry EOLs; a bad EOL
#guard px (pad 50 ++ "xref\n1 3\n0000000001 00000 n \r0000000002 00000 n \n" ++
    "0000000003 00000 n\r\ntrailer<</Size 4>>") 50 ==
  .inr ([(1, .inUse 1 0), (2, .inUse 2 0), (3, .inUse 3 0)], 4, none, none, 137)
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n\n\ntrailer<</Size 2>>") 50 ==
  .inl "malformed@59"
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n\r\rtrailer<</Size 2>>") 50 ==
  .inl "malformed@59"
-- count larger than the table: the subsection does not fit in the input
#guard px (pad 50 ++ "xref\n1 1000\n0000000001 00000 n \ntrailer<</Size 2>>") 50 ==
  .inl "malformed@62"
-- count that fits in the bytes but runs into the trailer
#guard px (pad 50 ++ "xref\n1 2\n0000000001 00000 n \ntrailer<</Size 2>>    ") 50 ==
  .inl "malformed@79"
-- header numbers: more than 10 digits, missing count
#guard px "xref\n00000000001 1\n0000000000 00000 n \ntrailer<</Size 2>>" == .inl "malformed@5"
#guard px "xref\n1\n0000000000 00000 n \ntrailer<</Size 2>>" == .inl "malformed@5"
-- entry total and object numbers against limits.maxObjects
#guard pxl { maxObjects := 2 } (pad 50 ++ "xref\n0 3\n0000000000 65535 f \n" ++
    "0000000001 00000 n \n0000000002 00000 n \ntrailer<</Size 3>>").toUTF8 50 ==
  .inl "limit:SafePdf.LimitKind.objects"
#guard pxl { maxObjects := 2 } (pad 50 ++ "xref\n0 1\n0000000000 65535 f \n" ++
    "1 1\n0000000001 00000 n \n2 1\n0000000002 00000 n \ntrailer<</Size 3>>").toUTF8 50 ==
  .inl "limit:SafePdf.LimitKind.objects"
#guard pxl { maxObjects := 2 } (pad 50 ++ "xref\n5 1\n0000000001 00000 n \n" ++
    "trailer<</Size 6>>").toUTF8 50 == .inl "malformed@55"
-- duplicate object number within one section (S6)
#guard px (pad 50 ++ "xref\n1 2\n0000000001 00000 n \n0000000002 00000 n \n" ++
    "2 1\n0000000003 00000 n \ntrailer<</Size 3>>") 50 == .inl "malformed@50"
-- offsets beyond the input, generation beyond 65535
#guard px (pad 50 ++ "xref\n1 1\n0000000999 00000 n \ntrailer<</Size 2>>") 50 ==
  .inl "malformed@59"
#guard px (pad 50 ++ "xref\n1 1\n0000000999 00000 f \ntrailer<</Size 2>>") 50 ==
  .inr ([(1, .free 999 0)], 2, none, none, 97)
#guard px (pad 50 ++ "xref\n1 1\n0000000001 65536 n \ntrailer<</Size 2>>") 50 ==
  .inl "malformed@59"
-- missing trailer, trailer not a dictionary, trailer entries mistyped
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n \n") 50 == .inl "malformed@79"
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n \nstartxref\n50\n%%EOF") 50 ==
  .inl "malformed@79"
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n \ntrailer [1]") 50 == .inl "malformed@86"
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n \ntrailer<</Root 1 0 R>>") 50 ==
  .inl "malformed@86"
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n \ntrailer<</Size -1>>") 50 ==
  .inl "malformed@86"
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n \ntrailer<</Size 2 /Root 1>>") 50 ==
  .inl "malformed@86"
#guard px (pad 50 ++ "xref\n1 1\n0000000001 00000 n \ntrailer<</Size 2 /Prev null>>") 50 ==
  .inr ([(1, .inUse 1 0)], 2, none, none, 108)
-- an empty table
#guard px "xref\ntrailer<</Size 1>>" == .inr ([], 1, none, none, 23)
-- typed trailer fields
#guard (match parseXrefTable Limits.default (pad 50 ++ "xref\n0 1\n0000000000 65535 f \n" ++
    "trailer<</Size 1 /XRefStm 7 /Encrypt 3 0 R>>").toUTF8 50 with
  | .ok (_, tr, _) => tr.xrefStm? == some 7 && tr.encrypted
  | .error _ => false)

end Tests

end SafePdf.Core.Xref
