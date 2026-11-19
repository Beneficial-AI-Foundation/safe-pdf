import SafePdf.Core.Xref
import SafePdf.Core.Xref.Chain
import SafePdf.Core.Xref.Length
import SafePdf.Core.Xref.ObjStm
import SafePdf.Repair

/-!
# Opening a document: strict path, repair fallback, object resolution (task 2.11)

Plan.md §4 (S6 unambiguous interpretation, S7 local, visible failure), §5.4 (strict → repair →
strict validation, `repaired := true`), §6 Phase 2 (milestone M2).

## Opening (`openFile`)

* P1. **Strict path** (`strictOpen`): `Chain.loadChain` (the `startxref` → `/Prev` chain of
  classic tables and xref streams, cycle-free by construction) → `Chain.mergeChain` (newest
  entry wins per object number, S6). Every merged object number must be below the newest
  trailer's `/Size` (`checkSize`, task 2.12; else the strict path fails and repair runs). The
  trailer is the newest revision's. Then `validate`.
* P2. **Validation** (`validate`): the trailer has `/Root`, and `getObject` of that reference
  is a dictionary (not a stream, not `null`).
* P3. **Repair** (`repairOpen`): if the strict path fails at any step (chain or validation)
  other than with a cycle (P5),
  `SafePdf.Repair.repair` rebuilds a section by scanning, and the same `validate` runs on it.
  The result has `repaired := true` (S7) and `revisions := 0` (no xref chain was used).
* P4. If repair fails too, `openFile` returns the **strict** error: it is the primary
  diagnosis (what is wrong with the file as written); the repair error ("no object found")
  is usually less informative.
* P5. **Cycles are final** (task 2.13; §6 Phase 2 M2 "Bogk-style cyclic files all rejected in
  bounded time"): if the strict error is an `Error.cycle` (a revisited `/Prev` or `/XRefStm`
  offset in `Chain.loadChain`, an object in its own object stream in the xref stream or in
  `ObjStm.fetchCompressed`, a cyclic `/Length` in `Length.resolveLength`), `openFile` returns
  it without trying repair. This includes cycles found while *validating the root* (P2):
  they are strict-path findings about the file as written, and the repair path, which
  re-reads the same objects through a scanned section, would at best rediscover the same
  cycle and at worst "succeed" by picking a different object, silently accepting the attack.
  Other strict errors (broken offsets, missing keywords) still fall back to repair (P3).

## Object resolution (`OpenDoc.getObject`)

* G1. The entry of `num` in the merged section (binary search on `OpenDoc.index`, an array
  copy of the sorted entries).
* G2. `inUse off g`: if `g` differs from the requested generation the object does not exist
  (null, G4). Otherwise `Length.parseIndirectResolved` at `off` (indirect `/Length` resolved
  with fuel = number of entries); the header must be `num g` (else `malformed`).
* G3. `compressed c i`: the requested generation must be 0 (else null, G4); then
  `ObjStm.fetchCompressed` with fuel = number of entries (one container, never nested).
* G4. `free`, absent, or a generation mismatch: `null` — ISO 32000-2 §7.3.10, "an indirect
  reference to an undefined object shall not be considered an error … treated as a reference
  to the null object" (docs/deviations-from-spec.md D-001).

Encrypted files (`trailer.encrypted`) open: the xref and dictionary structure is not
encrypted; strings and stream data stay encrypted until Phase 4 (task 4.3).

## Theorems

* Totality: by construction (no recursion except the binary search, `termination_by`).
* `openFile_repaired`: `repaired = false` ⇒ `loadChain` succeeded, the section is its merge,
  the trailer is the newest one (S7: a non-repaired document came from the strict path).
* `openFile_strict`: when the strict path succeeds, `openFile` returns it (repair never
  overrides a strictly valid file).
* `openFile_cycle`: when the strict path fails with a cycle error, `openFile` returns that
  error (rule P5); `openFile_loadChain_cycle`: in particular a cycle error of
  `Chain.loadChain`.
* `openFile_root`: an opened document's root is present and resolves to a dictionary.
* `strictOpen_lt_size`: a strictly opened document's object numbers are below its trailer's
  `/Size` (`Spec.Unambiguous.openFile_lt_size` lifts it to `openFile`).
* `getObject_depth`: every object returned nests at most `limits.maxObjectDepth`.
* `getObject_work`: one `getObject` performs at most one top-level object parse
  (`parseIndirectResolved` or a container parse inside `fetchCompressed`) and at most one
  object-stream decode; each `/Length` chain inside costs at most `fuel` object parses
  (`Length.resolveLength_calls_le`). That `parseIndirectResolved` runs at most one
  `resolveLength` is by inspection of `Length.lengthDict` (it is not instrumented).
-/

namespace SafePdf.Core.Open

open SafePdf
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)

/-! ## The opened document -/

/-- An opened document: the input, one merged cross-reference section and the trailer.
(The section field is `xref`: `section` is a Lean keyword.) -/
structure OpenDoc where
  /-- The whole input. -/
  bytes : ByteArray
  /-- The merged cross-reference section (strict) or the scanned one (repaired). -/
  xref : XrefSection
  /-- The newest trailer (strict) or the repaired trailer. -/
  trailer : Trailer
  /-- Number of xref sections in the chain (strict); `0` for a repaired document. -/
  revisions : Nat
  /-- `true` iff the document was built by the repair path (S7). -/
  repaired : Bool
  /-- `xref.entries` as an array, for binary search. -/
  index : Array (Nat × XrefEntry)
  /-- `index` is exactly the entry list. -/
  index_eq : index = xref.entries.toArray

/-- Build an `OpenDoc` (computes the index). -/
def OpenDoc.mk' (bytes : ByteArray) (xref : XrefSection) (trailer : Trailer) (revisions : Nat)
    (repaired : Bool) : OpenDoc :=
  ⟨bytes, xref, trailer, revisions, repaired, xref.entries.toArray, rfl⟩

/-- Binary search for object number `n` in `a[lo:hi]` (ascending keys). -/
def bsearch (a : Array (Nat × XrefEntry)) (n lo hi : Nat) : Option XrefEntry :=
  if lo < hi then
    match a[(lo + hi) / 2]? with
    | none => none
    | some (k, e) =>
      if k = n then some e
      else if k < n then bsearch a n ((lo + hi) / 2 + 1) hi
      else bsearch a n lo ((lo + hi) / 2)
  else none
termination_by hi - lo
decreasing_by all_goals omega

/-- The entry of object number `n` (rule G1). -/
def OpenDoc.lookup (d : OpenDoc) (n : Nat) : Option XrefEntry :=
  bsearch d.index n 0 d.index.size

/-- Number of cross-reference entries: the fuel for `/Length` resolution. -/
def OpenDoc.objectCount (d : OpenDoc) : Nat := d.index.size

/-- The null body returned for undefined objects (rule G4). -/
def nullBody : IndirectBody := .obj .null

/-- `getObject` with its work counted: top-level parses (`parseIndirectResolved` of the
object itself, or the container parse inside `fetchCompressed`), object-stream decodes, and
the result (rules G1–G4). -/
structure Trace where
  /-- Top-level object parses. -/
  parses : Nat
  /-- Object-stream decodes. -/
  decodes : Nat
  /-- The object or an error. -/
  result : Except Error IndirectBody

/-- `getObject` with its work counted. -/
def OpenDoc.getObjectTrace (d : OpenDoc) (limits : Limits) (num gen : Nat) : Trace :=
  match d.lookup num with
  | some (.inUse off g) =>
    if g = gen then
      match Xref.Length.parseIndirectResolved d.lookup limits d.bytes d.objectCount off with
      | .error e => ⟨1, 0, .error e⟩
      | .ok (io, _) =>
        if io.num = num ∧ io.gen = gen then ⟨1, 0, .ok io.body⟩
        else ⟨1, 0, .error (.malformed off
          s!"object header {io.num} {io.gen} does not match the xref entry {num} {gen}")⟩
    else ⟨0, 0, .ok nullBody⟩
  | some (.compressed _ _) =>
    if gen = 0 then
      let t := Xref.ObjStm.fetchCompressedTrace d.lookup limits d.bytes d.objectCount num
      ⟨t.parses, t.decodes, t.result.map IndirectBody.obj⟩
    else ⟨0, 0, .ok nullBody⟩
  | some (.free _ _) => ⟨0, 0, .ok nullBody⟩
  | none => ⟨0, 0, .ok nullBody⟩

/-- **Entry point.** Object `num gen` of the document (rules G1–G4): its body, `null` for
an undefined object (ISO 32000-2 §7.3.10), or an error. -/
def OpenDoc.getObject (d : OpenDoc) (limits : Limits) (num gen : Nat) :
    Except Error IndirectBody :=
  (d.getObjectTrace limits num gen).result

/-! ## Opening -/

/-- Strict validation (rule P2): `/Root` present and resolving to a dictionary. -/
def validate (limits : Limits) (d : OpenDoc) : Except Error OpenDoc :=
  match d.trailer.root? with
  | none => .error (.malformed 0 "trailer has no /Root")
  | some (n, g) =>
    match d.getObject limits n g with
    | .error e => .error e
    | .ok (.obj (.dict _)) => .ok d
    | .ok (.obj .null) => .error (.malformed 0 s!"/Root {n} {g} R is not defined")
    | .ok _ => .error (.malformed 0 s!"/Root {n} {g} R is not a dictionary")

/-- The document of a loaded chain (newest revision first), before validation. -/
def ofChain (bytes : ByteArray) : List Core.Xref.Chain.Revision → Except Error OpenDoc
  | [] => .error (.malformed 0 "no cross-reference section")
  | revs@((_, tr, _) :: _) =>
    .ok (OpenDoc.mk' bytes (Core.Xref.Chain.mergeChain revs) tr revs.length false)

/-- **`/Size` check** (rule P1, ISO 32000-2 §7.5.5; task 2.12): every object number of the
merged chain must be below the `/Size` of the newest trailer (which, per §7.5.6, counts the
objects of the whole file). `loadChain` checks this for xref streams against their own `/Size`
but not for classic tables. An empty chain passes. -/
def checkSize : List Core.Xref.Chain.Revision → Except Error Unit
  | [] => .ok ()
  | r :: rest =>
    if (Core.Xref.Chain.mergeChain (r :: rest)).entries.all (fun x => decide (x.1 < r.2.1.size))
    then .ok ()
    else .error (.malformed r.2.2 "cross-reference object number not below the trailer /Size")

/-- The strict path (rules P1, P2): load the chain, check object numbers against the newest
`/Size` (`checkSize`; a failure sends the file to the repair path), merge, validate. -/
def strictOpen (limits : Limits) (bytes : ByteArray) : Except Error OpenDoc :=
  match Core.Xref.Chain.loadChain limits bytes with
  | .error e => .error e
  | .ok revs =>
    match checkSize revs with
    | .error e => .error e
    | .ok () =>
      match ofChain bytes revs with
      | .error e => .error e
      | .ok d => validate limits d

/-- The repair path (rule P3): scanned section, same validation, `repaired := true`. -/
def repairOpen (limits : Limits) (bytes : ByteArray) : Except Error OpenDoc :=
  match SafePdf.Repair.repair limits bytes with
  | .error e => .error e
  | .ok (sec, tr) => validate limits (OpenDoc.mk' bytes sec tr 0 true)

/-- **Entry point.** Open a document: the strict path; on a cycle error (`Error.cycle`,
rule P5) that error; else the repair path; if both fail, the strict error (rule P4). -/
def openFile (limits : Limits) (bytes : ByteArray) : Except Error OpenDoc :=
  match strictOpen limits bytes with
  | .ok d => .ok d
  | .error e =>
    if e.isCycle then .error e
    else
      match repairOpen limits bytes with
      | .ok d => .ok d
      | .error _ => .error e

/-! ## Theorems -/

/-- `validate` returns its argument unchanged on success. -/
theorem validate_eq {limits : Limits} {d d' : OpenDoc} (h : validate limits d = .ok d') :
    d' = d := by
  unfold validate at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- On success, `validate` checked the root: present and a dictionary. -/
theorem validate_root {limits : Limits} {d d' : OpenDoc} (h : validate limits d = .ok d') :
    ∃ n g dict, d.trailer.root? = some (n, g) ∧
      d.getObject limits n g = .ok (.obj (.dict dict)) := by
  unfold validate at h
  split at h
  · cases h
  · rename_i n g hr
    split at h
    · cases h
    · rename_i dict hg
      exact ⟨n, g, dict, hr, hg⟩
    · cases h
    · cases h

/-- **The strict path, unfolded.** A strictly opened document comes from a chain that loads,
passes `checkSize`, and validates. -/
theorem strictOpen_ok {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : strictOpen limits bytes = .ok d) :
    ∃ revs, Core.Xref.Chain.loadChain limits bytes = .ok revs ∧ checkSize revs = .ok () ∧
      ofChain bytes revs = .ok d ∧ validate limits d = .ok d := by
  unfold strictOpen at h
  split at h
  · cases h
  · rename_i revs hl
    split at h
    · cases h
    · rename_i hc
      split at h
      · cases h
      · rename_i d1 hd
        have := validate_eq h
        subst this
        exact ⟨revs, hl, hc, hd, h⟩

/-- What `checkSize` guarantees: every merged object number is below the newest `/Size`. -/
theorem checkSize_ok {r : Core.Xref.Chain.Revision} {rest : List Core.Xref.Chain.Revision}
    (h : checkSize (r :: rest) = .ok ()) :
    ∀ x ∈ (Core.Xref.Chain.mergeChain (r :: rest)).entries, x.1 < r.2.1.size := by
  by_cases hall : (Core.Xref.Chain.mergeChain (r :: rest)).entries.all
      (fun x => decide (x.1 < r.2.1.size)) = true
  · intro x hx
    have := List.all_eq_true.mp hall x hx
    simpa using this
  · simp only [checkSize, hall, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-- **Strict documents respect `/Size`.** In a strictly opened document every object number
of the cross-reference section is below the trailer's `/Size`. -/
theorem strictOpen_lt_size {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : strictOpen limits bytes = .ok d) : ∀ x ∈ d.xref.entries, x.1 < d.trailer.size := by
  obtain ⟨revs, -, hc, hd, -⟩ := strictOpen_ok h
  unfold ofChain at hd
  split at hd
  · cases hd
  · rename_i sec tr off rest
    cases hd
    exact checkSize_ok hc

/-- Every repaired document is flagged as such. -/
theorem repairOpen_repaired {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : repairOpen limits bytes = .ok d) : d.repaired = true := by
  unfold repairOpen at h
  split at h
  · cases h
  · rw [validate_eq h]; rfl

/-- **S7: repaired documents are flagged.** A document with `repaired = false` came from the
strict path: `loadChain` succeeded with a non-empty chain, the section is the merge of the
chain, the trailer is the newest revision's and `revisions` is the chain length. -/
theorem openFile_repaired {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : openFile limits bytes = .ok d) (hr : d.repaired = false) :
    ∃ revs, Core.Xref.Chain.loadChain limits bytes = .ok revs ∧
      d.xref = Core.Xref.Chain.mergeChain revs ∧
      d.revisions = revs.length ∧
      ∃ sec off rest, revs = (sec, d.trailer, off) :: rest := by
  unfold openFile at h
  split at h
  · rename_i d0 hs
    cases h
    obtain ⟨revs, hl, -, hc, -⟩ := strictOpen_ok hs
    unfold ofChain at hc
    split at hc
    · cases hc
    · rename_i sec tr off rest
      cases hc
      exact ⟨_, hl, rfl, rfl, sec, off, rest, rfl⟩
  · split at h
    · cases h
    · split at h
      · cases h
        rename_i d1 hrep
        rw [repairOpen_repaired hrep] at hr
        cases hr
      · cases h

/-- **Strict first.** When the strict path succeeds, `openFile` returns exactly its result:
repair never overrides a strictly valid file. -/
theorem openFile_strict {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : strictOpen limits bytes = .ok d) : openFile limits bytes = .ok d := by
  simp [openFile, h]

/-- **Cycles are final** (rule P5, task 2.13; M2 "Bogk-style cyclic files all rejected"):
when the strict path fails with a cycle error, `openFile` returns exactly that error; the
repair path is not tried. -/
theorem openFile_cycle {limits : Limits} {bytes : ByteArray} {e : Error}
    (h : strictOpen limits bytes = .error e) (hc : e.isCycle = true) :
    openFile limits bytes = .error e := by
  simp [openFile, h, hc]

/-- **`/Prev`, `/XRefStm` and xref-stream cycles are final.** A cycle error of
`Chain.loadChain` is the result of `openFile`. -/
theorem openFile_loadChain_cycle {limits : Limits} {bytes : ByteArray} {e : Error}
    (h : Core.Xref.Chain.loadChain limits bytes = .error e) (hc : e.isCycle = true) :
    openFile limits bytes = .error e :=
  openFile_cycle (by simp [strictOpen, h]) hc

/-- **A cycle error never yields a document.** If the strict path fails with a cycle error,
`openFile` returns no document, repaired or not. -/
theorem openFile_cycle_not_ok {limits : Limits} {bytes : ByteArray} {e : Error} {d : OpenDoc}
    (h : strictOpen limits bytes = .error e) (hc : e.isCycle = true) :
    openFile limits bytes ≠ .ok d := by
  rw [openFile_cycle h hc]; exact fun h' => by cases h'

/-- **Root validated.** An opened document's `/Root` is present and resolves to a
dictionary. -/
theorem openFile_root {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : openFile limits bytes = .ok d) :
    ∃ n g dict, d.trailer.root? = some (n, g) ∧
      d.getObject limits n g = .ok (.obj (.dict dict)) := by
  unfold openFile at h
  split at h
  · rename_i d0 hs
    cases h
    obtain ⟨-, -, -, -, hv⟩ := strictOpen_ok hs
    exact validate_root hv
  · split at h
    · cases h
    · split at h
      · cases h
        rename_i d1 hrep
        unfold repairOpen at hrep
        split at hrep
        · cases hrep
        · have := validate_eq hrep
          subst this
          exact validate_root hrep
      · cases h

/-- Nesting depth of an indirect body: a stream counts as its dictionary. -/
def bodyDepth : IndirectBody → Nat
  | .obj o => o.depth
  | .stream s => (PdfObject.dict s.dict).depth

/-- `ObjParse.parseIndirectBodyWith` returns bodies within the depth limit, for every length
resolver (a stream's dictionary is the parsed one, `ObjParse.parseStreamBodyWith_ok`). -/
theorem parseIndirectBodyWith_depth {len : ObjParse.LengthResolver} {limits : Limits}
    {bytes : ByteArray} {p : Nat} {b : IndirectBody} {r : Nat}
    (h : ObjParse.parseIndirectBodyWith len limits bytes p = .ok (b, r)) :
    bodyDepth b ≤ limits.maxObjectDepth := by
  unfold ObjParse.parseIndirectBodyWith at h
  split at h
  · cases h
  · rename_i o r1 h1
    have hd := ObjParse.parseObject_depth h1
    split at h
    · cases h
    · split at h
      · cases h; exact hd
      · split at h
        · split at h
          · rename_i d _
            split at h
            · rename_i s r3 hs
              cases h
              obtain ⟨_, _, _, _, _, _, hsd⟩ := ObjParse.parseStreamBodyWith_ok hs
              simp only [bodyDepth, hsd]; exact hd
            · cases h
          · cases h
        · cases h
    · cases h

/-- `Length.parseIndirectResolved` returns bodies within the depth limit. -/
theorem parseIndirectResolved_depth {lookup : Nat → Option XrefEntry} {limits : Limits}
    {bytes : ByteArray} {fuel pos : Nat} {io : IndirectObject} {r : Nat}
    (h : Xref.Length.parseIndirectResolved lookup limits bytes fuel pos = .ok (io, r)) :
    bodyDepth io.body ≤ limits.maxObjectDepth := by
  unfold Xref.Length.parseIndirectResolved at h
  split at h
  · cases h
  · split at h
    · rename_i b r' hb
      cases h
      exact parseIndirectBodyWith_depth hb
    · cases h

/-- **Depth bound.** Every body `getObject` returns nests at most `limits.maxObjectDepth`. -/
theorem getObject_depth {d : OpenDoc} {limits : Limits} {num gen : Nat} {b : IndirectBody}
    (h : d.getObject limits num gen = .ok b) : bodyDepth b ≤ limits.maxObjectDepth := by
  unfold OpenDoc.getObject OpenDoc.getObjectTrace at h
  split at h
  · split at h
    · split at h
      · cases h
      · rename_i io r hp
        split at h
        · cases h; exact parseIndirectResolved_depth hp
        · cases h
    · cases h; simp [nullBody, bodyDepth, PdfObject.depth]
  · split at h
    · simp only at h
      cases hf : (Xref.ObjStm.fetchCompressedTrace d.lookup limits d.bytes d.objectCount num).result
      · rw [hf] at h; cases h
      · rename_i o
        rw [hf] at h
        cases h
        exact Xref.ObjStm.fetchCompressed_depth (by unfold Xref.ObjStm.fetchCompressed; exact hf)
    · cases h; simp [nullBody, bodyDepth, PdfObject.depth]
  · cases h; simp [nullBody, bodyDepth, PdfObject.depth]
  · cases h; simp [nullBody, bodyDepth, PdfObject.depth]

/-- **Work bound.** One `getObject` performs at most one top-level object parse and at most
one object-stream decode. (Inside a parse, each indirect `/Length` chain costs at most
`d.objectCount` further parses: `Length.resolveLength_calls_le`.) -/
theorem getObject_work (d : OpenDoc) (limits : Limits) (num gen : Nat) :
    (d.getObjectTrace limits num gen).parses ≤ 1 ∧
    (d.getObjectTrace limits num gen).decodes ≤ 1 := by
  unfold OpenDoc.getObjectTrace
  split
  · split
    · split
      · simp
      · split <;> simp
    · simp
  · split
    · exact Xref.ObjStm.fetchCompressed_work _ _ _ _ _
    · simp
  · simp
  · simp

/-- **Length-chain bound** in `getObject`'s fuel: resolving an indirect `/Length` while
fetching from `d` parses at most `d.objectCount` objects. -/
theorem getObject_length_calls_le (d : OpenDoc) (limits : Limits) (visiting : List Nat)
    (ref : Nat × Nat) :
    Xref.Length.resolveLengthCalls d.lookup limits d.bytes d.objectCount visiting ref ≤
      d.objectCount :=
  Xref.Length.resolveLength_calls_le _ _ _ _ _ _

/-! ## Tests -/

section Tests

/-- Test helper: summary of an open result. -/
private def os (b : ByteArray) : String :=
  match openFile Limits.default b with
  | .ok d => s!"ok repaired={d.repaired} revs={d.revisions} n={d.objectCount}"
  | .error (.malformed _ m) => s!"err {m}"
  | .error (.cycle o m) => s!"cycle@{o} {m}"
  | .error _ => "err"

/-- A minimal valid file with a correct xref table. -/
private def minimal : String :=
  "%PDF-1.4\n" ++
  "1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n" ++
  "2 0 obj\n<< /Type /Pages /Kids [] /Count 0 >>\nendobj\n"

/-- `minimal` with an xref table at the right offset. -/
private def minimalValid : ByteArray :=
  let body := minimal
  let x := body.utf8ByteSize
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  (body ++ "xref\n0 3\n0000000000 65535 f \n" ++ row 9 ++ row 58 ++
    "trailer\n<< /Size 3 /Root 1 0 R >>\nstartxref\n" ++ toString x ++ "\n%%EOF\n").toUTF8

/-- `minimal` with an xref table whose `/Prev` is its own offset (a one-element cycle). -/
private def minimalPrevSelf : ByteArray :=
  let body := minimal
  let x := body.utf8ByteSize
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  (body ++ "xref\n0 3\n0000000000 65535 f \n" ++ row 9 ++ row 58 ++
    s!"trailer\n<< /Size 3 /Root 1 0 R /Prev {x} >>\nstartxref\n" ++ toString x ++
    "\n%%EOF\n").toUTF8

/-- `minimal` with a broken `startxref`. -/
private def minimalBroken : ByteArray :=
  (minimal ++ "trailer\n<< /Size 3 /Root 1 0 R >>\nstartxref\n9999\n%%EOF\n").toUTF8

/-- Test helper: is the result the null body? -/
private def isNull : Except Error IndirectBody → Bool
  | .ok (.obj .null) => true
  | _ => false

-- Strict open of a valid file.
#guard os minimalValid == "ok repaired=false revs=1 n=3"

-- A broken xref is repaired.
#guard os minimalBroken == "ok repaired=true revs=0 n=3"

-- A `/Prev` cycle is final: no repair (rule P5), although the scan would find the objects.
#guard os minimalPrevSelf == "cycle@110 xref /Prev cycle"
#guard (match repairOpen Limits.default minimalPrevSelf with
  | .ok _ => true
  | .error _ => false)
/-- `minimalValid` whose trailer says `/Size 2` while the table lists objects 0–2. -/
private def minimalOverSize : ByteArray :=
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  (minimal ++ "xref\n0 3\n0000000000 65535 f \n" ++ row 9 ++ row 58 ++
    "trailer\n<< /Size 2 /Root 1 0 R >>\nstartxref\n" ++ toString minimal.utf8ByteSize ++
    "\n%%EOF\n").toUTF8

-- Object numbers not below /Size: the strict path fails `checkSize`, repair opens it (2.12).
#guard (match strictOpen Limits.default minimalOverSize with
  | .error (.malformed _ m) => m == "cross-reference object number not below the trailer /Size"
  | _ => false)
#guard os minimalOverSize == "ok repaired=true revs=0 n=3"

-- Garbage: the strict error is reported.
#guard os "%PDF-1.4\nhello\n".toUTF8 == "err startxref not found"

-- Undefined and free objects resolve to null; the catalog resolves.
#guard (match openFile Limits.default minimalValid with
  | .ok d =>
    isNull (d.getObject Limits.default 7 0) && isNull (d.getObject Limits.default 0 0) &&
    isNull (d.getObject Limits.default 1 5) &&
    (match d.getObject Limits.default 2 0 with
     | .ok (.obj (.dict _)) => true
     | _ => false)
  | .error _ => false)

end Tests

end SafePdf.Core.Open
