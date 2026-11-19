import SafePdf.Core.Xref
import SafePdf.Core.Xref.Length

/-!
# Repair path: rebuilding a cross-reference table by scanning

Plan.md §5.4 (the repair path), §4 S2/S3/S7/C4, §6 Phase 2; Caradoc's strict/relaxed parser
pair (Plan.md §2).

When the strict path fails (no `startxref`, a broken or missing xref table, wrong offsets),
real readers fall back to scanning the file for `N G obj` headers. This module is that
fallback. It is **proven total and bounded** (S2, S3) but not proven "correct": there is no
spec for garbage. Its output is an ordinary `Core.Xref.XrefSection` and `Core.Xref.Trailer`,
which must pass the same strict validation downstream as a strictly parsed file, and the
document built from it is flagged `repaired := true` (S7, by the caller).

## Algorithm

* R1. `scanObjects`: a byte-level scan (not the lexer, which binary stream data would fool).
  At each position `p` that is the start of input or follows a whitespace or delimiter byte,
  try to match `digits SP+ digits SP+ obj` followed by a whitespace byte, a delimiter or the
  end of input (`headerAt`), with `1 ≤ num` and `gen ≤ 65535`, each number 1–10 digits.
* R2. After a header, `Core.ObjParse.parseIndirect` is tried at `p`; on success the scan jumps
  past `endobj` (so the data of a stream that parses is never scanned for headers), otherwise
  it resumes at `p + 1`. Either way the next position is `> p`. A header is recorded whether
  or not its object parses (strict validation downstream decides).
* R2'. At most `limits.maxRepairFailures` (default 256) attempts may fail; after that,
  headers are still recorded but no longer parsed. The same budget applies to the trailer scan.
* R2''. When `parseIndirect` fails only because a stream `/Length` is indirect
  (`unsupported "indirect /Length"`), the same attempt retries once with
  `Core.Xref.Length.parseIndirectResolved` against `headerTable` (the newest header per object
  number, from a parse-free byte scan of the whole file; fuel = the table size). So a stream
  with an indirect `/Length` is jumped over too, and fake headers inside its data are not
  reported. The retry is charged to the same attempt (task 2.10).
* R3. The last occurrence of each object number wins (later = newer in incremental files):
  the hits are collected newest first, stably sorted by object number, and the first of each
  run is kept (`keepAsc`). The result is capped at `limits.maxObjects` entries.
* R4. `findTrailers`: every `trailer` keyword (at a boundary, followed by a whitespace or
  delimiter byte) whose next object is a dictionary, newest last (a dictionary that parses is
  jumped over). `repairTrailer` takes the
  newest one with a `/Root` reference; if there is none, it synthesizes `/Root` from the
  newest scanned object whose dictionary has `/Type /Catalog`. `/Size` is the larger of the
  dictionary's `/Size` and (highest scanned object number + 1); `/Prev` and `/XRefStm` are
  dropped (the scan replaces every revision).
* R5. `repair`: the section `0 → free 0 65535` plus `n → inUse offset gen` for every scanned
  object, and the trailer. Errors only when nothing usable is found: no object, or neither a
  trailer with `/Root` nor a catalog object.

## Bounds (S2, S3)

All loops recurse on `bytes.size - p` with strict progress (S2). The scan makes at most one
attempt (`attempt`: a `parseIndirect`, plus at most one indirect-`/Length` retry, R2'') per
header, at strictly increasing positions, so at most `bytes.size` attempts
(`scanAttempts_le`; the retry is charged to the attempt it belongs to, so the bound keeps its
constant), of which at most `limits.maxRepairFailures` fail
(`scanFailures_le`); it reports at most `min maxObjects bytes.size` objects
(`scanObjects_length_le`), each at a genuine header inside the input (`scanObjects_header`,
`scanObjects_offset_lt`), with distinct object numbers (`scanObjects_keys_nodup`).

Time (S3, informal; the cost model is not formalized): a successful attempt reads only the
bytes it then jumps over, so successes cost `O(bytes.size)` in total; a failed attempt may
read to the end of the input without moving the scan, so failures cost
`O(limits.maxRepairFailures · bytes.size)`; everything else is `O(1)` per byte plus an
`O(k log k)` sort of the `k ≤ bytes.size` hits. Without the budget, `k` headers inside one
unterminated string would cost `O(k · bytes.size)`. A retry (R2'') costs one more parse of
the stream object plus at most `t` parses of `/Length` objects, `t` the header-table size
(`Core.Xref.Length.resolveLength_calls_le`); the table itself is built once, lazily (a
`Thunk`, only when some retry needs it), in `O(bytes.size + k log k)`. A failed retry counts
as a failure against the budget; successful retries are not otherwise budgeted, so a file of
many streams sharing one long `/Length` chain costs up to `O(k · t)` length-object parses.

## Conservativity (C4), to be stated with task 2.5

C4 needs the full strict pipeline (task 2.5, `strictParse`). Its statement will be: for every
`bytes` on which `strictParse limits bytes = .ok doc`, the document obtained through
`repair limits bytes` (resolving every object through the repaired section, then the same
strict validation) equals `doc` up to `repaired := true`. On a strictly valid file the newest
definition of each object number is the one the merged xref points to, and the scan finds
the same header at the same offset; free and compressed entries need the xref-stream case
(2.4) and the "object-stream members" lookup to be handled before C4 can be proven.
-/

namespace SafePdf.Repair

open SafePdf
open SafePdf.Core
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)

/-! ## Header recognition (R1) -/

/-- Whether position `p` may start a header: the start of input, or the previous byte is a
whitespace or delimiter byte (this includes line starts). -/
def boundaryAt (bytes : ByteArray) (p : Nat) : Bool :=
  match p with
  | 0 => true
  | q + 1 =>
    match bytes[q]? with
    | some b => Lex.isWhite b || Lex.isDelim b
    | none => false

/-- Whether a keyword ending at `p` is properly terminated: a whitespace byte, a delimiter, or
the end of input. -/
def endOk (bytes : ByteArray) (p : Nat) : Bool :=
  match bytes[p]? with
  | some b => Lex.isWhite b || Lex.isDelim b
  | none => true

/-- The tail of a header after the object number `num` ending at `e1`: `SP+ gen SP+ obj`. -/
def headerTail (bytes : ByteArray) (num e1 : Nat) : Option (Nat × Nat) :=
  match Xref.natAt bytes (Xref.spacesAt bytes e1) with
  | none => none
  | some (gen, e2) =>
    if e1 < Xref.spacesAt bytes e1 && e2 < Xref.spacesAt bytes e2 &&
        Xref.matchAt bytes (Xref.spacesAt bytes e2) ObjParse.kwObj &&
        endOk bytes (Xref.spacesAt bytes e2 + 3) && decide (1 ≤ num) && decide (gen ≤ 65535)
    then some (num, gen)
    else none

/-- An object header `num SP+ gen SP+ obj` at exactly `p` (R1): `(num, gen)`. -/
def headerAt (bytes : ByteArray) (p : Nat) : Option (Nat × Nat) :=
  match Xref.natAt bytes p with
  | none => none
  | some (num, e1) => headerTail bytes num e1

/-! ## Header table for indirect `/Length` (R2'') -/

/-- Order hits by object number (stable: equal numbers keep their order). -/
def keyLe (a b : Nat × Nat × Nat) : Bool := decide (a.1 ≤ b.1)

/-- Keep a hit only if its object number is at least `b`, then raise the bound past it. On a
list sorted by object number this keeps the first hit of each number. -/
def keepAsc : List (Nat × Nat × Nat) → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | x :: xs, b => if b ≤ x.1 then x :: keepAsc xs (x.1 + 1) else keepAsc xs b

/-- Every header `(num, gen, offset)` at a boundary from `p` on, onto `acc` (newest first). A
plain byte scan: nothing is parsed, so headers inside stream data are included. -/
def headerLoop (bytes : ByteArray) (p : Nat) (acc : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat) :=
  if _h : p < bytes.size then
    if boundaryAt bytes p then
      match headerAt bytes p with
      | some (num, gen) => headerLoop bytes (p + 1) ((num, gen, p) :: acc)
      | none => headerLoop bytes (p + 1) acc
    else headerLoop bytes (p + 1) acc
  else acc
termination_by bytes.size - p

/-- The newest header per object number, ascending by object number: the table an indirect
`/Length` is resolved against during the scan (as the inspector's objects view does). -/
def headerTable (bytes : ByteArray) : Array (Nat × Nat × Nat) :=
  (keepAsc ((headerLoop bytes 0 []).mergeSort keyLe) 1).toArray

/-- Lookup of an object number in a `headerTable` (binary search), as an in-use entry. -/
def tableLookup (t : Array (Nat × Nat × Nat)) (n : Nat) : Option XrefEntry :=
  match t.binSearch (n, 0, 0) (fun a b => a.1 < b.1) with
  | some (_, g, off) => some (.inUse off g)
  | none => none

/-- One parse attempt at header offset `p` (R2, R2''): `ObjParse.parseIndirect`; if it fails
only because a stream `/Length` is indirect, one retry with
`Core.Xref.Length.parseIndirectResolved` against the header table `tbl` (fuel: the table
size). Returns the end of the object on success. The retry is part of the same attempt. -/
def attempt (limits : Limits) (bytes : ByteArray) (tbl : Thunk (Array (Nat × Nat × Nat)))
    (p : Nat) : Option Nat :=
  match ObjParse.parseIndirect limits bytes p with
  | .ok (_, r) => some r
  | .error (.unsupported what) =>
    if what == "indirect /Length" then
      match Xref.Length.parseIndirectResolved (tableLookup tbl.get) limits bytes tbl.get.size p
      with
      | .ok (_, r) => some r
      | .error _ => none
    else none
  | .error _ => none

/-! ## The scan (R2) -/

/-! At most `limits.maxRepairFailures` `parseIndirect` (and trailer `parseObject`) attempts may
fail during one scan; afterwards headers are still recorded but no longer parsed (R2'). A
failed attempt may read up to the end of the input without moving the scan forward, so this
budget is what makes the worst-case time `O(bytes.size · limits.maxRepairFailures)` instead of
quadratic in the number of headers (e.g. thousands of headers nested inside one unterminated
string). -/

/-- The scan loop from `p`. `acc` holds the hits `(num, gen, offset)` found so far, newest
first; `n` counts the `parseIndirect` attempts and `fails` the failed ones. Returns the hits,
the attempts and the failures. -/
def scanLoop (limits : Limits) (bytes : ByteArray) (tbl : Thunk (Array (Nat × Nat × Nat)))
    (p : Nat) (acc : List (Nat × Nat × Nat)) (n fails : Nat) : List (Nat × Nat × Nat) × Nat × Nat :=
  if _h : p < bytes.size then
    if boundaryAt bytes p then
      match headerAt bytes p with
      | some (num, gen) =>
        if fails < limits.maxRepairFailures then
          match attempt limits bytes tbl p with
          | some r =>
            scanLoop limits bytes tbl (max r (p + 1)) ((num, gen, p) :: acc) (n + 1) fails
          | none =>
            scanLoop limits bytes tbl (p + 1) ((num, gen, p) :: acc) (n + 1) (fails + 1)
        else scanLoop limits bytes tbl (p + 1) ((num, gen, p) :: acc) n fails
      | none => scanLoop limits bytes tbl (p + 1) acc n fails
    else scanLoop limits bytes tbl (p + 1) acc n fails
  else (acc, n, fails)
termination_by bytes.size - p

/-- The raw scan: every header hit (newest first), the number of `parseIndirect` attempts and
the number of failed attempts. -/
def scanRaw (limits : Limits) (bytes : ByteArray) : List (Nat × Nat × Nat) × Nat × Nat :=
  scanLoop limits bytes (Thunk.mk fun _ => headerTable bytes) 0 [] 0 0

/-- **Work measure.** The number of `parseIndirect` attempts the scan makes. -/
def scanAttempts (limits : Limits) (bytes : ByteArray) : Nat :=
  (scanRaw limits bytes).2.1

/-- **Work measure.** The number of failed `parseIndirect` attempts. -/
def scanFailures (limits : Limits) (bytes : ByteArray) : Nat :=
  (scanRaw limits bytes).2.2

/-! ## Newest wins (R3) -/

/-- **Entry point.** The `(num, gen, offset)` of every `num gen obj` header found by the
repair scan, the newest per object number, ascending by object number, at most
`limits.maxObjects` of them (R1–R3). -/
def scanObjects (limits : Limits) (bytes : ByteArray) : List (Nat × Nat × Nat) :=
  (keepAsc ((scanRaw limits bytes).1.mergeSort keyLe) 1).take limits.maxObjects

/-! ## Trailers (R4) -/

/-- Scan for `trailer` dictionaries from `p`; `acc` newest first. A dictionary that parses is
jumped over; at most `limits.maxRepairFailures` attempts may fail (as in `scanLoop`). -/
def trailerLoop (limits : Limits) (bytes : ByteArray) (p : Nat) (acc : List Dict)
    (fails : Nat) : List Dict :=
  if _h : p < bytes.size then
    if boundaryAt bytes p && Xref.matchAt bytes p Xref.kwTrailer && endOk bytes (p + 7) &&
        decide (fails < limits.maxRepairFailures) then
      match ObjParse.parseObject limits bytes (p + 7) with
      | .ok (.dict d, r) => trailerLoop limits bytes (max r (p + 1)) (d :: acc) fails
      | _ => trailerLoop limits bytes (p + 1) acc (fails + 1)
    else trailerLoop limits bytes (p + 1) acc fails
  else acc.reverse
termination_by bytes.size - p

/-- **Entry point.** Every `trailer << … >>` dictionary in the file, newest last (R4). -/
def findTrailers (limits : Limits) (bytes : ByteArray) : List Dict :=
  trailerLoop limits bytes 0 [] 0

/-- Key `/Type`. -/
def nameType : Name := Name.ofString "Type"

/-- Name `/Catalog`. -/
def nameCatalog : Name := Name.ofString "Catalog"

/-- The `/Root` reference of a dictionary, if it is one. -/
def rootOf (d : Dict) : Option (Nat × Nat) :=
  match Dict.get? d Xref.nameRoot with
  | some (.ref n g) => some (n, g)
  | _ => none

/-- The `/Size` of a dictionary when it is a non-negative integer, else 0. -/
def sizeOf (d : Dict) : Nat :=
  match Dict.get? d Xref.nameSize with
  | some (.int i) => i.toNat
  | _ => 0

/-- Whether a dictionary has `/Type /Catalog`. -/
def isCatalog (d : Dict) : Bool :=
  match Dict.get? d nameType with
  | some (.name n) => n == nameCatalog
  | _ => false

/-- Whether the scanned object at `off` is a catalog dictionary. -/
def catalogAt (limits : Limits) (bytes : ByteArray) (off : Nat) : Bool :=
  match ObjParse.parseIndirect limits bytes off with
  | .ok (⟨_, _, .obj (.dict d)⟩, _) => isCatalog d
  | _ => false

/-- The newest (largest offset) catalog object among the in-use `entries`, as
`(num, gen)`. -/
def findCatalog (limits : Limits) (bytes : ByteArray) (entries : List (Nat × XrefEntry)) :
    Option (Nat × Nat) :=
  let best := entries.foldl (fun (acc : Option (Nat × Nat × Nat)) e =>
    match e with
    | (k, .inUse off g) =>
      if catalogAt limits bytes off then
        match acc with
        | some y => if y.2.2 < off then some (k, g, off) else acc
        | none => some (k, g, off)
      else acc
    | _ => acc) none
  best.map (fun x => (x.1, x.2.1))

/-- One more than the highest object number in `entries`. -/
def scanSize (entries : List (Nat × XrefEntry)) : Nat :=
  entries.foldl (fun m e => max m (e.1 + 1)) 0

/-- The typed trailer for dictionary `d`, catalog reference `root`, and `/Size` `size`. -/
def mkTrailer (d : Dict) (root : Nat × Nat) (size : Nat) : Trailer :=
  { dict := d, size, prev? := none, root? := some root, xrefStm? := none,
    encrypted := (Dict.get? d Xref.nameEncrypt).isSome }

/-- **Entry point.** The repaired trailer (R4): the newest `trailer` dictionary with a
`/Root` reference, else one synthesized from the newest catalog object among the in-use
`entries`. -/
def repairTrailer (limits : Limits) (bytes : ByteArray) (entries : List (Nat × XrefEntry)) :
    Option Trailer :=
  match (findTrailers limits bytes).reverse.findSome?
      (fun d => (rootOf d).map (fun r => (d, r))) with
  | some (d, root) => some (mkTrailer d root (max (sizeOf d) (scanSize entries)))
  | none =>
    match findCatalog limits bytes entries with
    | some (n, g) =>
      some (mkTrailer [(Xref.nameSize, .int (scanSize entries)), (Xref.nameRoot, .ref n g)]
        (n, g) (scanSize entries))
    | none => none

/-! ## The repaired section (R5) -/

/-- Scanned hits as in-use xref entries. -/
def toEntries (objs : List (Nat × Nat × Nat)) : List (Nat × XrefEntry) :=
  objs.map (fun x => (x.1, XrefEntry.inUse x.2.2 x.2.1))

/-- Every hit kept by `keepAsc xs b` has object number `≥ b`. -/
theorem keepAsc_ge (xs : List (Nat × Nat × Nat)) (b : Nat) :
    ∀ y ∈ keepAsc xs b, b ≤ y.1 := by
  induction xs generalizing b with
  | nil => simp [keepAsc]
  | cons x xs ih =>
    intro y hy
    unfold keepAsc at hy
    split at hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · assumption
      · have := ih _ y hy; omega
    · exact ih b y hy

/-- `keepAsc` produces strictly ascending object numbers. -/
theorem keepAsc_sorted (xs : List (Nat × Nat × Nat)) (b : Nat) :
    (keepAsc xs b).Pairwise (fun a c => a.1 < c.1) := by
  induction xs generalizing b with
  | nil => simp [keepAsc]
  | cons x xs ih =>
    unfold keepAsc
    split
    · refine List.Pairwise.cons ?_ (ih _)
      intro y hy
      have := keepAsc_ge xs (x.1 + 1) y hy
      omega
    · exact ih b

/-- `keepAsc` only drops hits. -/
theorem keepAsc_sublist (xs : List (Nat × Nat × Nat)) (b : Nat) :
    List.Sublist (keepAsc xs b) xs := by
  induction xs generalizing b with
  | nil => simp [keepAsc]
  | cons x xs ih =>
    unfold keepAsc
    split
    · exact (ih _).cons_cons x
    · exact (ih b).cons x

/-- Every object number reported by `scanObjects` is at least 1. -/
theorem scanObjects_num_pos (limits : Limits) (bytes : ByteArray) :
    ∀ x ∈ scanObjects limits bytes, 1 ≤ x.1 := by
  intro x hx
  exact keepAsc_ge _ 1 x (List.mem_of_mem_take hx)

/-- **(d)** `scanObjects` is strictly ascending by object number. -/
theorem scanObjects_sorted (limits : Limits) (bytes : ByteArray) :
    (scanObjects limits bytes).Pairwise (fun a c => a.1 < c.1) :=
  (keepAsc_sorted _ 1).sublist (List.take_sublist _ _)

/-- **(d)** The object numbers reported by `scanObjects` are pairwise distinct. -/
theorem scanObjects_keys_nodup (limits : Limits) (bytes : ByteArray) :
    ((scanObjects limits bytes).map Prod.fst).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  exact (scanObjects_sorted limits bytes).imp (fun h => Nat.ne_of_lt h)

/-- The repaired section: `0 → free 0 65535`, then every scanned object as in use. Sorted
(hence one entry per object number, S6) by construction. -/
def scanSection (limits : Limits) (bytes : ByteArray) : XrefSection :=
  ⟨(0, .free 0 65535) :: toEntries (scanObjects limits bytes), by
    refine List.Pairwise.cons ?_ ?_
    · intro y hy
      unfold toEntries at hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact scanObjects_num_pos limits bytes x hx
    · unfold toEntries
      rw [List.pairwise_map]
      exact scanObjects_sorted limits bytes⟩

/-- The repair path for an already scanned section: an error when it holds no object, else
the section and the repaired trailer. -/
def repairWith (limits : Limits) (bytes : ByteArray) (sec : XrefSection) :
    Except Error (XrefSection × Trailer) :=
  if sec.entries.length ≤ 1 then .error (.malformed 0 "repair: no indirect object found")
  else
    match repairTrailer limits bytes sec.entries with
    | none => .error (.malformed 0 "repair: no trailer with /Root and no catalog object")
    | some tr => .ok (sec, tr)

/-- **Entry point.** The repair path (R5): a cross-reference section rebuilt by scanning, and
a trailer. An error only when nothing usable is found. -/
def repair (limits : Limits) (bytes : ByteArray) : Except Error (XrefSection × Trailer) :=
  repairWith limits bytes (scanSection limits bytes)

/-! ## Bounds of the scan loop -/

/-- Loop invariant of `scanLoop`: at most one hit per remaining byte; at most one attempt
per hit; the failure count never passes `limits.maxRepairFailures`; every new hit is a header
at an offset inside the input. -/
theorem scanLoop_spec (limits : Limits) (bytes : ByteArray)
    (tbl : Thunk (Array (Nat × Nat × Nat))) (p : Nat) (acc : List (Nat × Nat × Nat))
    (n fails : Nat) :
    (scanLoop limits bytes tbl p acc n fails).1.length ≤ acc.length + (bytes.size - p) ∧
    (scanLoop limits bytes tbl p acc n fails).2.1 + acc.length ≤
      n + (scanLoop limits bytes tbl p acc n fails).1.length ∧
    (fails ≤ limits.maxRepairFailures →
      (scanLoop limits bytes tbl p acc n fails).2.2 ≤ limits.maxRepairFailures) ∧
    ∀ x ∈ (scanLoop limits bytes tbl p acc n fails).1,
      x ∈ acc ∨ (x.2.2 < bytes.size ∧ headerAt bytes x.2.2 = some (x.1, x.2.1)) := by
  fun_induction scanLoop limits bytes tbl p acc n fails
  case case1 p acc n fails h _ num gen hh _ r _ ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    simp only [List.length_cons] at ih1 ih2
    refine ⟨by omega, by omega, ih3, ?_⟩
    intro x hx
    rcases ih4 x hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr ⟨h, hh⟩
      · exact Or.inl hx
    · exact Or.inr hx
  case case2 p acc n fails h _ num gen hh hf _ ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    simp only [List.length_cons] at ih1 ih2
    refine ⟨by omega, by omega, fun _ => ih3 (by omega), ?_⟩
    intro x hx
    rcases ih4 x hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr ⟨h, hh⟩
      · exact Or.inl hx
    · exact Or.inr hx
  case case3 p acc n fails h _ num gen hh _ ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    simp only [List.length_cons] at ih1 ih2
    refine ⟨by omega, by omega, ih3, ?_⟩
    intro x hx
    rcases ih4 x hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr ⟨h, hh⟩
      · exact Or.inl hx
    · exact Or.inr hx
  case case4 p acc n fails h _ _ ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    exact ⟨by omega, ih2, ih3, ih4⟩
  case case5 p acc n fails h _ ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    exact ⟨by omega, ih2, ih3, ih4⟩
  case case6 p acc n fails h =>
    dsimp only
    exact ⟨by omega, by omega, id, fun x hx => Or.inl hx⟩

/-- **(b)** `scanObjects` reports at most `min limits.maxObjects bytes.size` objects. -/
theorem scanObjects_length_le (limits : Limits) (bytes : ByteArray) :
    (scanObjects limits bytes).length ≤ min limits.maxObjects bytes.size := by
  obtain ⟨h1, _, _, _⟩ := scanLoop_spec limits bytes (Thunk.mk fun _ => headerTable bytes) 0 [] 0 0
  simp only [List.length_nil] at h1
  have hk := (keepAsc_sublist ((scanRaw limits bytes).1.mergeSort keyLe) 1).length_le
  rw [List.length_mergeSort] at hk
  unfold scanObjects
  rw [List.length_take]
  unfold scanRaw at hk ⊢
  omega

/-- **(c)** Every object reported by `scanObjects` starts with a header (R1) at an offset
inside the input. -/
theorem scanObjects_header (limits : Limits) (bytes : ByteArray) :
    ∀ x ∈ scanObjects limits bytes,
      x.2.2 < bytes.size ∧ headerAt bytes x.2.2 = some (x.1, x.2.1) := by
  intro x hx
  have hm := (keepAsc_sublist _ 1).subset (List.mem_of_mem_take hx)
  rw [List.mem_mergeSort] at hm
  obtain ⟨_, _, _, h3⟩ := scanLoop_spec limits bytes (Thunk.mk fun _ => headerTable bytes) 0 [] 0 0
  rcases h3 x hm with h | h
  · simp at h
  · exact h

/-- **(e) Work bound.** The scan makes at most `bytes.size` `parseIndirect` attempts (at most
one per header, at strictly increasing positions). -/
theorem scanAttempts_le (limits : Limits) (bytes : ByteArray) :
    scanAttempts limits bytes ≤ bytes.size := by
  obtain ⟨h1, h2, _, _⟩ := scanLoop_spec limits bytes (Thunk.mk fun _ => headerTable bytes) 0 [] 0 0
  unfold scanAttempts scanRaw
  simp only [List.length_nil] at h1 h2
  omega

/-- **(e) Work bound.** At most `limits.maxRepairFailures` of those attempts fail. -/
theorem scanFailures_le (limits : Limits) (bytes : ByteArray) :
    scanFailures limits bytes ≤ limits.maxRepairFailures := by
  obtain ⟨_, _, h3, _⟩ := scanLoop_spec limits bytes (Thunk.mk fun _ => headerTable bytes) 0 [] 0 0
  unfold scanFailures scanRaw
  exact h3 (Nat.zero_le _)

/-- **(c)** Every offset reported by `scanObjects` is `< bytes.size`. -/
theorem scanObjects_offset_lt (limits : Limits) (bytes : ByteArray) :
    ∀ x ∈ scanObjects limits bytes, x.2.2 < bytes.size :=
  fun x hx => (scanObjects_header limits bytes x hx).1

/-! ## Properties of `repair` -/

/-- A successful `repair` returns the scanned section and a trailer with a `/Root`. -/
theorem repair_ok {limits : Limits} {bytes : ByteArray} {sec : XrefSection} {tr : Trailer}
    (h : repair limits bytes = .ok (sec, tr)) :
    sec = scanSection limits bytes ∧ tr.root?.isSome := by
  unfold repair repairWith at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i tr' htr
      cases h
      refine ⟨rfl, ?_⟩
      unfold repairTrailer at htr
      split at htr
      · cases htr; rfl
      · split at htr
        · cases htr; rfl
        · cases htr

/-- **(c) for `repair`.** Every in-use offset of a repaired section is `< bytes.size`. -/
theorem repair_offset_lt {limits : Limits} {bytes : ByteArray} {sec : XrefSection}
    {tr : Trailer} (h : repair limits bytes = .ok (sec, tr)) :
    ∀ k o g, (k, XrefEntry.inUse o g) ∈ sec.entries → o < bytes.size := by
  intro k o g hm
  rw [(repair_ok h).1] at hm
  simp only [scanSection, List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false,
    false_or] at hm
  unfold toEntries at hm
  rcases List.mem_map.mp hm with ⟨x, hx, he⟩
  simp only [Prod.mk.injEq, XrefEntry.inUse.injEq] at he
  rw [← he.2.1]
  exact scanObjects_offset_lt limits bytes x hx

/-- **(b) for `repair`.** A repaired section has at most `min maxObjects bytes.size + 1`
entries (the scanned objects and entry 0). -/
theorem repair_length_le {limits : Limits} {bytes : ByteArray} {sec : XrefSection}
    {tr : Trailer} (h : repair limits bytes = .ok (sec, tr)) :
    sec.entries.length ≤ min limits.maxObjects bytes.size + 1 := by
  rw [(repair_ok h).1]
  simp only [scanSection, List.length_cons, toEntries, List.length_map]
  have := scanObjects_length_le limits bytes
  omega

/-- **(d) for `repair`.** A repaired section has one entry per object number (S6). -/
theorem repair_keys_nodup {limits : Limits} {bytes : ByteArray} {sec : XrefSection}
    {tr : Trailer} (_h : repair limits bytes = .ok (sec, tr)) :
    (sec.entries.map Prod.fst).Nodup :=
  sec.keys_nodup

/-! ## Tests -/

section Tests

/-- `Tests/adversarial/minimal-valid.pdf` (587 bytes, SHA-256 `051e3308…4d84`), embedded as a
byte literal by a one-off script so the file itself is never opened here. -/
private def minimalBytes : ByteArray := ⟨#[
  37, 80, 68, 70, 45, 49, 46, 55, 10, 37, 226, 227, 207, 211, 10, 49, 32, 48, 32, 111,
  98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 67, 97, 116, 97, 108, 111, 103,
  32, 47, 80, 97, 103, 101, 115, 32, 50, 32, 48, 32, 82, 32, 62, 62, 10, 101, 110, 100,
  111, 98, 106, 10, 50, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101,
  32, 47, 80, 97, 103, 101, 115, 32, 47, 75, 105, 100, 115, 32, 91, 51, 32, 48, 32, 82,
  93, 32, 47, 67, 111, 117, 110, 116, 32, 49, 32, 62, 62, 10, 101, 110, 100, 111, 98, 106,
  10, 51, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 80,
  97, 103, 101, 32, 47, 80, 97, 114, 101, 110, 116, 32, 50, 32, 48, 32, 82, 32, 47, 77,
  101, 100, 105, 97, 66, 111, 120, 32, 91, 48, 32, 48, 32, 54, 49, 50, 32, 55, 57, 50,
  93, 32, 47, 67, 111, 110, 116, 101, 110, 116, 115, 32, 52, 32, 48, 32, 82, 32, 47, 82,
  101, 115, 111, 117, 114, 99, 101, 115, 32, 60, 60, 32, 47, 70, 111, 110, 116, 32, 60, 60,
  32, 47, 70, 49, 32, 53, 32, 48, 32, 82, 32, 62, 62, 32, 62, 62, 32, 62, 62, 10,
  101, 110, 100, 111, 98, 106, 10, 52, 32, 48, 32, 111, 98, 106, 10, 60, 60, 32, 32, 47,
  76, 101, 110, 103, 116, 104, 32, 51, 54, 32, 62, 62, 10, 115, 116, 114, 101, 97, 109, 10,
  66, 84, 32, 47, 70, 49, 32, 50, 52, 32, 84, 102, 32, 55, 50, 32, 55, 48, 48, 32,
  84, 100, 32, 40, 72, 101, 108, 108, 111, 41, 32, 84, 106, 32, 69, 84, 10, 101, 110, 100,
  115, 116, 114, 101, 97, 109, 10, 101, 110, 100, 111, 98, 106, 10, 53, 32, 48, 32, 111, 98,
  106, 10, 60, 60, 32, 47, 84, 121, 112, 101, 32, 47, 70, 111, 110, 116, 32, 47, 83, 117,
  98, 116, 121, 112, 101, 32, 47, 84, 121, 112, 101, 49, 32, 47, 66, 97, 115, 101, 70, 111,
  110, 116, 32, 47, 72, 101, 108, 118, 101, 116, 105, 99, 97, 32, 62, 62, 10, 101, 110, 100,
  111, 98, 106, 10, 120, 114, 101, 102, 10, 48, 32, 54, 10, 48, 48, 48, 48, 48, 48, 48,
  48, 48, 48, 32, 54, 53, 53, 51, 53, 32, 102, 32, 10, 48, 48, 48, 48, 48, 48, 48,
  48, 49, 53, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48, 48, 48, 48,
  48, 54, 52, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48, 48, 48, 48,
  49, 50, 49, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48, 48, 48, 48,
  50, 52, 55, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 48, 48, 48, 48, 48, 48, 48,
  51, 51, 52, 32, 48, 48, 48, 48, 48, 32, 110, 32, 10, 116, 114, 97, 105, 108, 101, 114,
  10, 60, 60, 32, 47, 83, 105, 122, 101, 32, 54, 32, 47, 82, 111, 111, 116, 32, 49, 32,
  48, 32, 82, 32, 62, 62, 10, 115, 116, 97, 114, 116, 120, 114, 101, 102, 10, 52, 48, 52,
  10, 37, 37, 69, 79, 70, 10
]⟩

/-- Test helper: an error summary. -/
private def errS : Error → String
  | .malformed o m => s!"malformed@{o}: {m}"
  | .limitExceeded k => s!"limit:{reprStr k}"
  | .unsupported w => s!"unsupported:{w}"
  | .cycle o w => s!"cycle@{o}: {w}"

/-- Test helper: `repair` summarised as (entries, /Size, /Root). -/
private def rp (b : ByteArray) (lim : Limits := Limits.default) :
    Sum String (List (Nat × XrefEntry) × Nat × Option (Nat × Nat)) :=
  match repair lim b with
  | .ok (sec, tr) => .inr (sec.entries, tr.size, tr.root?)
  | .error e => .inl (errS e)

/-- Test helper: `rp` on a string. -/
private def rps (s : String) := rp s.toUTF8

/-- Test helper: the strict entries of a table at `pos`, or `[]`. -/
private def strictEntries (b : ByteArray) (pos : Nat) : List (Nat × XrefEntry) :=
  match Xref.parseXrefTable Limits.default b pos with
  | .ok (sec, _, _) => sec.entries
  | .error _ => []

/-- The six entries of `minimal-valid.pdf`. -/
private def minimalEntries : List (Nat × XrefEntry) :=
  [(0, .free 0 65535), (1, .inUse 15 0), (2, .inUse 64 0), (3, .inUse 121 0),
    (4, .inUse 247 0), (5, .inUse 334 0)]

-- the file itself: strict and repaired agree
#guard minimalBytes.size == 587
#guard Xref.findStartxref minimalBytes matches .ok 404
#guard strictEntries minimalBytes 404 == minimalEntries
#guard rp minimalBytes == .inr (strictEntries minimalBytes 404, 6, some (1, 0))
#guard scanObjects Limits.default minimalBytes ==
  [(1, 0, 15), (2, 0, 64), (3, 0, 121), (4, 0, 247), (5, 0, 334)]
-- the stream object (4) is skipped by the jump: one attempt per object
#guard scanAttempts Limits.default minimalBytes == 5
#guard findTrailers Limits.default minimalBytes ==
  [[(Xref.nameSize, .int 6), (Xref.nameRoot, .ref 1 0)]]
-- xref table deleted (bytes 404..532), trailer and a now-wrong startxref kept
#guard rp (minimalBytes.extract 0 404 ++ minimalBytes.extract 533 587) ==
  .inr (minimalEntries, 6, some (1, 0))
-- xref table with wrong offsets: strict accepts the (range-valid) garbage, repair fixes it
#guard (Xref.findStartxref (minimalBytes.extract 0 404 ++ ("xref\n0 6\n" ++
    "0000000000 65535 f \n0000000001 00000 n \n0000000002 00000 n \n" ++
    "0000000003 00000 n \n0000000004 00000 n \n0000000005 00000 n \n").toUTF8 ++
    minimalBytes.extract 533 587)) matches .ok 404
#guard rp (minimalBytes.extract 0 404 ++ ("xref\n0 6\n" ++
    "0000000000 65535 f \n0000000001 00000 n \n0000000002 00000 n \n" ++
    "0000000003 00000 n \n0000000004 00000 n \n0000000005 00000 n \n").toUTF8 ++
    minimalBytes.extract 533 587) == .inr (minimalEntries, 6, some (1, 0))
-- startxref garbage: strict fails, repair is unaffected
#guard (Xref.findStartxref (minimalBytes.extract 0 566 ++ "startxref\nzz\n%%EOF\n".toUTF8))
  matches .error _
#guard rp (minimalBytes.extract 0 566 ++ "startxref\nzz\n%%EOF\n".toUTF8) ==
  .inr (minimalEntries, 6, some (1, 0))
-- no trailer at all: /Root synthesized from the /Type /Catalog object, /Size = 5 + 1
#guard rp (minimalBytes.extract 0 404) == .inr (minimalEntries, 6, some (1, 0))
-- truncated in the middle of the stream object: objects 1-3 still found (4's header too)
#guard rp (minimalBytes.extract 0 280) ==
  .inr ([(0, .free 0 65535), (1, .inUse 15 0), (2, .inUse 64 0), (3, .inUse 121 0),
    (4, .inUse 247 0)], 5, some (1, 0))

/-- A stream whose (binary) data contains a fake object header on its own line. -/
private def fakeInStream (len : Nat) : String :=
  "%PDF-1.7\n1 0 obj\n<< /Type /Catalog >>\nendobj\n" ++
  s!"2 0 obj\n<< /Length {len} >>\nstream\n" ++
  "\x00\x01\n9 0 obj\n(x)\nendobj\n\x7f" ++
  "\nendstream\nendobj\n"

-- the data is 23 bytes; with the right /Length the jump skips the fake `9 0 obj`
#guard "\x00\x01\n9 0 obj\n(x)\nendobj\n\x7f".toUTF8.size == 23
#guard scanObjects Limits.default (fakeInStream 23).toUTF8 == [(1, 0, 9), (2, 0, 45)]
#guard rps (fakeInStream 23) == .inr ([(0, .free 0 65535), (1, .inUse 9 0), (2, .inUse 45 0)],
  3, some (1, 0))
-- with a wrong /Length the stream does not parse, so the scan looks inside (documented
-- limitation: only parseable objects are jumped over)
#guard (scanObjects Limits.default (fakeInStream 99).toUTF8).map (·.1) == [1, 2, 9]

/-- `fakeInStream`, but the stream's `/Length` is `3 0 R`, defined after the stream as
`3 0 obj <len> endobj`; `lenRef` is the reference written in the stream dictionary. -/
private def fakeInIndirect (lenRef : String) (len : Nat) : String :=
  "%PDF-1.7\n1 0 obj\n<< /Type /Catalog >>\nendobj\n" ++
  s!"2 0 obj\n<< /Length {lenRef} >>\nstream\n" ++
  "\x00\x01\n9 0 obj\n(x)\nendobj\n\x7f" ++
  s!"\nendstream\nendobj\n3 0 obj\n{len}\nendobj\n"

-- R2'': parseIndirect alone rejects the stream (indirect /Length) ...
#guard (match ObjParse.parseIndirect Limits.default (fakeInIndirect "3 0 R" 23).toUTF8 45 with
  | .error (.unsupported w) => w == "indirect /Length"
  | _ => false)
-- ... the retry resolves `3 0 R` through the header table, so the stream is jumped over and
-- the fake `9 0 obj` inside its data is no longer reported (task 2.10)
#guard (scanObjects Limits.default (fakeInIndirect "3 0 R" 23).toUTF8).map (·.1) == [1, 2, 3]
-- the retry is charged to the attempt it belongs to: 3 attempts for 3 real headers, none failed
#guard scanAttempts Limits.default (fakeInIndirect "3 0 R" 23).toUTF8 == 3
#guard scanFailures Limits.default (fakeInIndirect "3 0 R" 23).toUTF8 == 0
-- a wrong resolved length, or a self-referential /Length (Bogk), still fails: the scan looks
-- inside, and the failed retry counts as one failure
#guard (scanObjects Limits.default (fakeInIndirect "3 0 R" 99).toUTF8).map (·.1) == [1, 2, 3, 9]
#guard (scanObjects Limits.default (fakeInIndirect "2 0 R" 23).toUTF8).map (·.1) == [1, 2, 3, 9]
#guard scanFailures Limits.default (fakeInIndirect "2 0 R" 23).toUTF8 == 1
-- the header table: newest header per object number, fake headers included
#guard (headerTable (fakeInIndirect "3 0 R" 23).toUTF8).toList.map (·.1) == [1, 2, 3, 9]
#guard tableLookup (headerTable (fakeInIndirect "3 0 R" 23).toUTF8) 3 ==
  some (.inUse ((fakeInIndirect "3 0 R" 23).utf8ByteSize - 18) 0)
#guard tableLookup (headerTable (fakeInIndirect "3 0 R" 23).toUTF8) 4 == none

-- incremental update: object 3 redefined after the first %%EOF; the newest definition wins
#guard rp (minimalBytes ++ ("3 0 obj\n<< /Type /Page /Parent 2 0 R >>\nendobj\n" ++
    "xref\n0 1\n0000000000 65535 f \n3 1\n0000000587 00000 n \n" ++
    "trailer\n<< /Size 6 /Root 1 0 R /Prev 404 >>\nstartxref\n633\n%%EOF\n").toUTF8) ==
  .inr ([(0, .free 0 65535), (1, .inUse 15 0), (2, .inUse 64 0), (3, .inUse 587 0),
    (4, .inUse 247 0), (5, .inUse 334 0)], 6, some (1, 0))
-- newest trailer with /Root wins; an older /Size larger than the scan is kept
#guard rps ("1 0 obj 1 endobj\n2 0 obj 2 endobj\ntrailer << /Size 9 /Root 1 0 R >>\n" ++
    "trailer << /Size 3 /Root 2 0 R >>\ntrailer << /Size 50 >>") ==
  .inr ([(0, .free 0 65535), (1, .inUse 0 0), (2, .inUse 17 0)], 3, some (2, 0))
-- generation numbers, extra spaces, header after a delimiter; not after a regular byte
#guard scanObjects Limits.default "x]7  2 obj null endobj a8 0 obj null endobj".toUTF8 ==
  [(7, 2, 2)]
-- headers that are not: object 0, generation > 65535, 11 digits, no space, no `obj` end
#guard scanObjects Limits.default ("0 0 obj null endobj 1 65536 obj 1 endobj " ++
    "12345678901 0 obj 1 0obj 1 0 objx 1 0 obj").toUTF8 == [(1, 0, 75)]

/-- `k` copies of `1 0 obj (`: every header opens a string that never closes. -/
private def nestedStrings (k : Nat) : ByteArray :=
  ((List.replicate k "1 0 obj (").foldl (· ++ ·) "").toUTF8

-- R2': headers inside an unterminated string. Every attempt fails (and would read to the
-- end); after limits.maxRepairFailures failures the scan stops parsing but still records headers
#guard scanAttempts Limits.default (nestedStrings 300) == 256
#guard scanFailures Limits.default (nestedStrings 300) == 256
#guard (scanRaw Limits.default (nestedStrings 300)).1.length == 300
-- below the budget every header is attempted
#guard scanAttempts Limits.default (nestedStrings 10) == 10
-- the budget is `limits.maxRepairFailures`
#guard scanAttempts { maxRepairFailures := 3 } (nestedStrings 10) == 3
#guard (scanRaw { maxRepairFailures := 3 } (nestedStrings 10)).1.length == 10
#guard scanAttempts { maxRepairFailures := 0 } (nestedStrings 10) == 0

-- the object cap: limits.maxObjects keeps the lowest object numbers
#guard rp minimalBytes { maxObjects := 2 } ==
  .inr ([(0, .free 0 65535), (1, .inUse 15 0), (2, .inUse 64 0)], 6, some (1, 0))
-- nothing usable: no objects; objects but no catalog and no trailer with /Root
#guard rps "" == .inl "malformed@0: repair: no indirect object found"
#guard rps "%PDF-1.7\ngarbage 1 0 R\n" == .inl "malformed@0: repair: no indirect object found"
#guard rps "1 0 obj\n<< /A 1 >>\nendobj\ntrailer << /Size 2 >>" ==
  .inl "malformed@0: repair: no trailer with /Root and no catalog object"
-- a cyclic /Prev chain is irrelevant to the scan (it never follows offsets)
#guard rp (minimalBytes.extract 0 404 ++ ("xref\n0 1\n0000000000 65535 f \n" ++
    "trailer\n<< /Size 6 /Root 1 0 R /Prev 404 >>\nstartxref\n404\n%%EOF\n").toUTF8) ==
  .inr (minimalEntries, 6, some (1, 0))

end Tests

end SafePdf.Repair
