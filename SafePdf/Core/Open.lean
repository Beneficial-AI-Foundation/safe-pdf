import SafePdf.Core.Xref
import SafePdf.Core.Xref.Chain
import SafePdf.Core.Xref.Length
import SafePdf.Core.Xref.ObjStm
import SafePdf.Repair
import SafePdf.Core.Crypt

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
  is usually less informative. Exception (rule E3): a repair-path `Error.encryption`.
* P5. **Cycles are final** (and so are encryption-setup errors, rule E2) (task 2.13; §6 Phase 2 M2 "Bogk-style cyclic files all rejected in
  bounded time"): if the strict error is an `Error.cycle` (a revisited `/Prev` or `/XRefStm`
  offset in `Chain.loadChain`, an object in its own object stream in the xref stream or in
  `ObjStm.fetchCompressed`, a cyclic `/Length` in `Length.resolveLength`, also through an
  object stream since task 2.14), `openFile` returns
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
  with fuel = number of entries, also when a `/Length` lives in an object stream, task 2.14);
  the header must be `num g` (else `malformed`).
* G3. `compressed c i`: the requested generation must be 0 (else null, G4); then
  `ObjStm.fetchCompressed` with fuel = number of entries (one container, never nested).
* G4. `free`, absent, or a generation mismatch: `null` — ISO 32000-2 §7.3.10, "an indirect
  reference to an undefined object shall not be considered an error … treated as a reference
  to the null object" (docs/deviations-from-spec.md D-001).

## Encryption (task 4.3b, Plan.md §6 Phase 4, ISO 32000-2 §7.6)

* E1. `OpenDoc.withCrypt` runs on every candidate document before validation (in `ofChain`
  for the strict path, in `repairOpen` for the repair path): a trailer with `/Encrypt` gets
  its decryption state `crypt` (`Crypt.setup`: parse the handler, derive the file key for the
  empty user password). The encryption dictionary is direct in the trailer or an indirect
  object outside object streams (§7.5.7), fetched raw.
* E2. A `withCrypt` failure (unsupported handler or revision, non-empty user password,
  malformed or unresolvable `/Encrypt`) is an `Error.encryption` (`Crypt.setupError`; task
  4.6 replaced the message-prefix tagging of 4.3b by this constructor) and **final** like a
  cycle (`Error.isFinal`, `openFile_final`, `openFile_setup_final`): repair is not tried.
* E3. (Task 4.6.) On the repair path the same `withCrypt` runs on the repaired trailer, which
  keeps the file's `/Encrypt` and `/ID` (`Repair` rule R4': from the newest `trailer`
  dictionary or cross-reference stream dictionary that has one, also when the trailer is
  synthesized). So a repaired encrypted file is decrypted, or fails with `Error.encryption`
  (e.g. `/Encrypt` names an object the scan did not find); it never opens undecrypted. When
  both paths fail and the repair path's error is `Error.encryption`, `openFile` reports that
  error instead of the strict one (`bothFailed`, `openFile_repair_encryption`).
* G5. `getObject` decrypts what it returns (`OpenDoc.decrypt` → `Crypt.decryptBody`): strings
  everywhere and stream data, except the encryption dictionary, xref streams and the other
  §7.6.2 exceptions (`Core.Crypt`, rule C7). An object in an object stream is not decrypted:
  its container's data is, before decoding (`OpenDoc.pre`, the `ObjStm.Pre` pass, rule O7);
  `getObjectB` / `Session` use the same pass, so they stay equal to `getObject`.
* A container decoded while resolving an indirect `/Length` that lives in an object stream
  (`Length.resolveLength`, rule L6) passes through the same `OpenDoc.pre` (task 4.6), so such
  a `/Length` in an encrypted file resolves.

## Theorems

* Totality: by construction (no recursion except the binary search, `termination_by`).
* `openFile_repaired`: `repaired = false` ⇒ `loadChain` succeeded, the section is its merge,
  the trailer is the newest one (S7: a non-repaired document came from the strict path).
* `openFile_strict`: when the strict path succeeds, `openFile` returns it (repair never
  overrides a strictly valid file).
* `openFile_final`, `openFile_setup_final`, `openFile_repair_encryption`: final errors
  (`Error.isFinal`) skip repair; a repair-path encryption error is reported (rules E2, E3).
* `openFile_cycle`: when the strict path fails with a cycle error, `openFile` returns that
  error (rule P5); `openFile_loadChain_cycle`: in particular a cycle error of
  `Chain.loadChain`.
* `openFile_root`: an opened document's root is present and resolves to a dictionary.
* `strictOpen_lt_size`: a strictly opened document's object numbers are below its trailer's
  `/Size` (`Spec.Unambiguous.openFile_lt_size` lifts it to `openFile`).
* `getObject_depth`: every object returned nests at most `limits.maxObjectDepth` (decryption
  preserves depth: `decrypt_depth`).
* `withCrypt_ok`: only the decryption state changes at open; `withCrypt_plain`,
  `decrypt_none`: an unencrypted document gets no state and `getObject` decrypts nothing.
  (Every theorem of this module keeps its statement; the `CacheExact` hypotheses and
  conclusions now name the document's pre-pass `d.pre`, and `ofChain` takes `limits`.)
* `getObject_work`: one `getObject` performs at most one top-level object parse
  (`parseIndirectResolved` or a container parse inside `fetchCompressed`) and at most one
  object-stream decode; each `/Length` chain inside, including hops through object streams
  (task 2.14), costs at most `fuel` object parses and container decodes
  (`Length.resolveLength_calls_le`). That `parseIndirectResolved` runs at most one
  `resolveLength` is by inspection of `Length.lengthDict` (it is not instrumented).

## Budgeted opening and sessions (task 3.13, Plan.md §3 S3)

`openFileB limits budget bytes` is `openFile` with the decodes it performs charged against a
`Filter.Budget`: the xref streams of the chain (`Chain.loadChainB`) and the object-stream
decode of the root validation (`validateB` → `getObjectB` → `ObjStm.fetchCompressedB`).
`OpenDoc.getObjectB` fetches with a budget and an `ObjStm.Cache`, so each object stream is
decoded (and charged) once per cache. `Session` bundles a document, its budget and its cache;
`Session.open` starts from `Budget.init limits`. The unbudgeted functions above are unchanged.

* `openFileB_le`, `getObjectB_le`, `Session.getObject_le`: the budget never grows.
* `getObjectB_cost`, `validateB_cost`, `strictOpenB_eq`: a fetch costs at most one
  `decodeAllowance`; the strict open at most `maxRevisions + 1` of them.
* `openFileB_strict`, `openFileB_cycle`, `openFileB_loadChain_cycle`, `openFileB_root`,
  `openFileB_repaired`: rules P1–P5 for the budgeted path.
* `getObjectB_eq`, `openFileB_eq`, `Session.getObject_eq`, `Session.open_eq`: **with enough
  budget left the budgeted functions return exactly what the unbudgeted ones return**
  (`(maxRevisions + 2) · decodeAllowance` to open, one `decodeAllowance` per fetch), and the
  cache stays exact (`ObjStm.CacheExact`). No monotonicity of the decoders is needed
  (`Filter.decodeStreamB_eq`).
* `getObjectB_depth`: depth bound.

**Not charged** (bounded per call only): object-stream decodes made while resolving an
indirect `/Length` that lives in an object stream (`Length.resolveLength`, rule L6, inside
`Length.parseIndirectResolved`, also for a container's own `/Length`): at most
`d.objectCount` decodes per fetch (`Length.resolveLength_calls_le`), each allocating at most
`maxFilters · maxDecodedStreamBytes` bytes. Charging them needs a budgeted `Length` resolver.
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
  /-- The decryption state of an encrypted document (task 4.3b; `none` when unencrypted). -/
  crypt : Option Crypt.State
  /-- `xref.entries` as an array, for binary search. -/
  index : Array (Nat × XrefEntry)
  /-- `index` is exactly the entry list. -/
  index_eq : index = xref.entries.toArray

/-- Build an `OpenDoc` (computes the index; no decryption state, see `OpenDoc.withCrypt`). -/
def OpenDoc.mk' (bytes : ByteArray) (xref : XrefSection) (trailer : Trailer) (revisions : Nat)
    (repaired : Bool) : OpenDoc :=
  ⟨bytes, xref, trailer, revisions, repaired, none, xref.entries.toArray, rfl⟩

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

/-- Decrypt the body of object `num gen` (rule G5): the identity for an unencrypted document,
else `Crypt.decryptBody`. -/
def OpenDoc.decrypt (d : OpenDoc) (num gen : Nat) (b : IndirectBody) : Except Error IndirectBody :=
  match d.crypt with
  | none => .ok b
  | some st => Crypt.decryptBody st num gen b

/-- The object-stream pre-pass of `d` (rule G5): decrypt the container's data
(`Crypt.decryptContainer`) of an encrypted document, the identity otherwise. -/
def OpenDoc.pre (d : OpenDoc) : Xref.ObjStm.Pre :=
  match d.crypt with
  | none => Xref.ObjStm.Pre.id
  | some st => ⟨fun c s => Crypt.decryptContainer st c s,
      fun _ _ _ h => (Crypt.decryptContainer_size_le h).1⟩

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
      match Xref.Length.parseIndirectResolved d.lookup limits d.bytes d.objectCount off d.pre with
      | .error e => ⟨1, 0, .error e⟩
      | .ok (io, _) =>
        if io.num = num ∧ io.gen = gen then ⟨1, 0, d.decrypt num gen io.body⟩
        else ⟨1, 0, .error (.malformed off
          s!"object header {io.num} {io.gen} does not match the xref entry {num} {gen}")⟩
    else ⟨0, 0, .ok nullBody⟩
  | some (.compressed _ _) =>
    if gen = 0 then
      let t := Xref.ObjStm.fetchCompressedTrace d.pre d.lookup limits d.bytes d.objectCount num
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

/-- The encryption dictionary of an encrypted document (rule E1): direct in the trailer, or an
indirect object that is not in an object stream (ISO 32000-2 §7.5.7), fetched with
`getObject`; with its reference. -/
def OpenDoc.encryptDict (d : OpenDoc) (limits : Limits) :
    Except Error (Dict × Option (Nat × Nat)) :=
  match Dict.get? d.trailer.dict Xref.nameEncrypt with
  | some (.dict e) => .ok (e, none)
  | some (.ref n g) =>
    match d.lookup n with
    | some (.compressed _ _) =>
      .error (.malformed 0 "/Encrypt: in an object stream (ISO 32000-2 §7.5.7)")
    | _ =>
      match d.getObject limits n g with
      | .ok (.obj (.dict e)) => .ok (e, some (n, g))
      | .ok _ => .error (.malformed 0 s!"/Encrypt: {n} {g} R is not a dictionary")
      | .error e => .error e
  | _ => .error (.malformed 0 "/Encrypt: not a dictionary or a reference")

/-- **Decryption state at open** (rules E1, E2, task 4.3b): for a document whose trailer has
`/Encrypt`, parse the encryption dictionary, derive the file key for the empty user password
(`Crypt.setup`) and store the state; any failure (unsupported handler, non-empty user
password, malformed dictionary) is the error. An unencrypted document is returned as is
(`withCrypt_plain`). Only `crypt` changes (`withCrypt_ok`). -/
def OpenDoc.withCrypt (d : OpenDoc) (limits : Limits) : Except Error OpenDoc :=
  if d.trailer.encrypted then
    match d.encryptDict limits with
    | .error e => .error (Crypt.setupError e)
    | .ok (enc, ref) =>
      match Crypt.setup enc d.trailer.dict ref with
      | .error e => .error e
      | .ok st => .ok { d with crypt := some st }
  else .ok d

/-- `withCrypt` changes nothing but the decryption state. -/
theorem withCrypt_ok {d d' : OpenDoc} {limits : Limits} (h : d.withCrypt limits = .ok d') :
    ∃ c, d' = { d with crypt := c } := by
  unfold OpenDoc.withCrypt at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨d.crypt, rfl⟩

/-- **Unencrypted documents are untouched**: without `/Encrypt`, `withCrypt` is the identity
(so `getObject` decrypts nothing when `d.crypt = none`, `decrypt_none`). -/
theorem withCrypt_plain {d : OpenDoc} {limits : Limits} (h : d.trailer.encrypted = false) :
    d.withCrypt limits = .ok d := by
  simp [OpenDoc.withCrypt, h]

/-- Without a decryption state, `decrypt` is the identity. -/
theorem decrypt_none {d : OpenDoc} (h : d.crypt = none) (num gen : Nat) (b : IndirectBody) :
    d.decrypt num gen b = .ok b := by
  simp [OpenDoc.decrypt, h]

/-- The document of a loaded chain (newest revision first), with its decryption state
(`withCrypt`), before validation. -/
def ofChain (limits : Limits) (bytes : ByteArray) :
    List Core.Xref.Chain.Revision → Except Error OpenDoc
  | [] => .error (.malformed 0 "no cross-reference section")
  | revs@((_, tr, _) :: _) =>
    (OpenDoc.mk' bytes (Core.Xref.Chain.mergeChain revs) tr revs.length false).withCrypt limits

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
      match ofChain limits bytes revs with
      | .error e => .error e
      | .ok d => validate limits d

/-- The repair path (rule P3): scanned section, decryption state (`withCrypt`), same
validation, `repaired := true`. -/
def repairOpen (limits : Limits) (bytes : ByteArray) : Except Error OpenDoc :=
  match SafePdf.Repair.repair limits bytes with
  | .error e => .error e
  | .ok (sec, tr) =>
    match (OpenDoc.mk' bytes sec tr 0 true).withCrypt limits with
    | .error e => .error e
    | .ok d => validate limits d

/-- The error of `openFile` when both paths fail (rule P4): the strict error `e`, unless the
repair path failed with an encryption error `e'` (rule E3: the file is encrypted and cannot
be decrypted; that is the diagnosis, whatever broke its cross-reference data). -/
def bothFailed (e e' : Error) : Error := if e'.isEncryption then e' else e

/-- **Entry point.** Open a document: the strict path; on a final error (`Error.isFinal`: a
cycle, rule P5, or an encryption-setup error, rule E2) that error; else the repair path; if
both fail, the strict error, or the repair path's encryption error (rules P4, E3). -/
def openFile (limits : Limits) (bytes : ByteArray) : Except Error OpenDoc :=
  match strictOpen limits bytes with
  | .ok d => .ok d
  | .error e =>
    if e.isFinal then .error e
    else
      match repairOpen limits bytes with
      | .ok d => .ok d
      | .error e' => .error (bothFailed e e')

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
      ofChain limits bytes revs = .ok d ∧ validate limits d = .ok d := by
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
    obtain ⟨c, rfl⟩ := withCrypt_ok hd
    exact checkSize_ok hc

/-- **The repair path, unfolded.** A repaired document is a scanned section with its
decryption state that validates. -/
theorem repairOpen_ok {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : repairOpen limits bytes = .ok d) :
    ∃ sec tr, SafePdf.Repair.repair limits bytes = .ok (sec, tr) ∧
      (OpenDoc.mk' bytes sec tr 0 true).withCrypt limits = .ok d ∧ validate limits d = .ok d := by
  unfold repairOpen at h
  split at h
  · cases h
  · rename_i sec tr hr
    split at h
    · cases h
    · rename_i d0 hw
      have := validate_eq h
      subst this
      exact ⟨sec, tr, hr, hw, h⟩

/-- Every repaired document is flagged as such. -/
theorem repairOpen_repaired {limits : Limits} {bytes : ByteArray} {d : OpenDoc}
    (h : repairOpen limits bytes = .ok d) : d.repaired = true := by
  obtain ⟨sec, tr, -, hw, -⟩ := repairOpen_ok h
  obtain ⟨c, rfl⟩ := withCrypt_ok hw
  rfl

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
      obtain ⟨c, rfl⟩ := withCrypt_ok hc
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
  simp [openFile, Error.isFinal, h, hc]

/-- **Final errors are final** (rules P5, E2): when the strict path fails with a final error
(`Error.isFinal`), `openFile` returns exactly that error; the repair path is not tried. -/
theorem openFile_final {limits : Limits} {bytes : ByteArray} {e : Error}
    (h : strictOpen limits bytes = .error e) (hc : e.isFinal = true) :
    openFile limits bytes = .error e := by
  simp [openFile, h, hc]

/-- **Encryption-setup errors are final** (rule E2, tasks 4.3b, 4.6): when the strict path
fails with an `Error.encryption` (unsupported handler, non-empty user password, malformed
`/Encrypt`), `openFile` returns exactly that error; the repair path is not tried. -/
theorem openFile_setup_final {limits : Limits} {bytes : ByteArray} {e : Error}
    (h : strictOpen limits bytes = .error e) (hc : e.isEncryption = true) :
    openFile limits bytes = .error e :=
  openFile_final h (by simp [Error.isFinal, hc])

/-- **An encryption error of the repair path is reported** (rule E3, task 4.6): when the
strict path fails with a non-final error and the repair path fails with an encryption error,
`openFile` returns the repair path's error. -/
theorem openFile_repair_encryption {limits : Limits} {bytes : ByteArray} {e e' : Error}
    (h : strictOpen limits bytes = .error e) (hf : e.isFinal = false)
    (hr : repairOpen limits bytes = .error e') (he : e'.isEncryption = true) :
    openFile limits bytes = .error e' := by
  simp [openFile, h, hf, hr, bothFailed, he]

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
        obtain ⟨-, -, -, -, hv⟩ := repairOpen_ok hrep
        exact validate_root hv
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
theorem parseIndirectResolved_depth {pre : Xref.ObjStm.Pre} {lookup : Nat → Option XrefEntry}
    {limits : Limits} {bytes : ByteArray} {fuel pos : Nat} {io : IndirectObject} {r : Nat}
    (h : Xref.Length.parseIndirectResolved lookup limits bytes fuel pos pre = .ok (io, r)) :
    bodyDepth io.body ≤ limits.maxObjectDepth := by
  unfold Xref.Length.parseIndirectResolved at h
  split at h
  · cases h
  · split at h
    · rename_i b r' hb
      cases h
      exact parseIndirectBodyWith_depth hb
    · cases h

/-- **Decryption preserves depth** (task 4.3b): `decrypt` changes only string bytes and
stream data. -/
theorem decrypt_depth {d : OpenDoc} {num gen : Nat} {b b' : IndirectBody}
    (h : d.decrypt num gen b = .ok b') : bodyDepth b' = bodyDepth b := by
  unfold OpenDoc.decrypt at h
  split at h
  · cases h; rfl
  · rcases Crypt.decryptBody_shape h with ⟨o, o', rfl, rfl, hd⟩ | ⟨s, s', rfl, rfl, hd⟩
    · exact hd
    · exact hd

/-- **Depth bound.** Every body `getObject` returns nests at most `limits.maxObjectDepth`
(decrypted or not, `decrypt_depth`). -/
theorem getObject_depth {d : OpenDoc} {limits : Limits} {num gen : Nat} {b : IndirectBody}
    (h : d.getObject limits num gen = .ok b) : bodyDepth b ≤ limits.maxObjectDepth := by
  unfold OpenDoc.getObject OpenDoc.getObjectTrace at h
  split at h
  · split at h
    · split at h
      · cases h
      · rename_i io r hp
        split at h
        · rw [decrypt_depth h]; exact parseIndirectResolved_depth hp
        · cases h
    · cases h; simp [nullBody, bodyDepth, PdfObject.depth]
  · split at h
    · simp only at h
      cases hf : (Xref.ObjStm.fetchCompressedTrace d.pre d.lookup limits d.bytes d.objectCount num).result
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
`d.objectCount` further parses, object-stream containers included:
`Length.resolveLength_calls_le`.) -/
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
    · exact Xref.ObjStm.fetchCompressed_work _ _ _ _ _ _
    · simp
  · simp
  · simp

/-- **Length-chain bound** in `getObject`'s fuel: resolving an indirect `/Length` while
fetching from `d` parses at most `d.objectCount` objects (length objects and object-stream
containers, task 2.14). -/
theorem getObject_length_calls_le (d : OpenDoc) (limits : Limits) (visiting : List Nat)
    (ref : Nat × Nat) :
    Xref.Length.resolveLengthCalls d.pre d.lookup limits d.bytes d.objectCount visiting ref ≤
      d.objectCount :=
  Xref.Length.resolveLength_calls_le _ _ _ _ _ _ _

/-! ## Budgeted opening and sessions (task 3.13)

The budgeted twins of `getObject`, `validate`, `strictOpen`, `repairOpen` and `openFile`
thread a `Filter.Budget` and an object-stream `ObjStm.Cache`. The unbudgeted functions and
their theorems stay as they are (other layers and the specs use them); the theorems below
relate the two. -/

open SafePdf.Core.Filter (Budget)
open SafePdf.Core.Xref.ObjStm (Cache CacheExact)

/-- The most one budgeted fetch or one xref-stream parse of `d` can charge. -/
def OpenDoc.allowance (d : OpenDoc) (limits : Limits) : Nat :=
  Core.Xref.Chain.decodeAllowance limits d.bytes

/-- **Budgeted object resolution** (rules G1–G4, task 3.13): an object in an object stream is
fetched by `ObjStm.fetchCompressedB` (container decode charged, decoded once per cache);
anything else as by `getObject`. Returns the result, the budget and the cache. -/
def OpenDoc.getObjectB (d : OpenDoc) (limits : Limits) (budget : Budget) (cache : Cache)
    (num gen : Nat) : (Except Error IndirectBody) × Budget × Cache :=
  match d.lookup num with
  | some (.compressed _ _) =>
    if gen = 0 then
      let r := Xref.ObjStm.fetchCompressedB d.pre d.lookup limits d.bytes d.objectCount num budget cache
      (r.1.map IndirectBody.obj, r.2.1, r.2.2)
    else (.ok nullBody, budget, cache)
  | _ => (d.getObject limits num gen, budget, cache)

/-- `getObjectB` never increases the budget. -/
theorem getObjectB_le (d : OpenDoc) (limits : Limits) (budget : Budget) (cache : Cache)
    (num gen : Nat) : (d.getObjectB limits budget cache num gen).2.1.remaining ≤ budget.remaining := by
  unfold OpenDoc.getObjectB
  split
  · split
    · exact Xref.ObjStm.fetchCompressedB_le _ _ _ _ _ _ _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- **Cost of one fetch**: at most `d.allowance limits` (one container decode). -/
theorem getObjectB_cost (d : OpenDoc) (limits : Limits) (budget : Budget) (cache : Cache)
    (num gen : Nat) : budget.remaining ≤ (d.getObjectB limits budget cache num gen).2.1.remaining +
      d.allowance limits := by
  unfold OpenDoc.getObjectB OpenDoc.allowance Core.Xref.Chain.decodeAllowance
  split
  · split
    · exact Xref.ObjStm.fetchCompressedB_cost _ _ _ _ _ _ _ _
    · exact Nat.le_add_right _ _
  · exact Nat.le_add_right _ _

/-- **Budget large enough ⇒ same object** (task 3.13): with an exact cache and at least
`d.allowance limits` left, `getObjectB` returns exactly what `getObject` returns and the cache
stays exact. -/
theorem getObjectB_eq {d : OpenDoc} {limits : Limits} {budget : Budget} {cache : Cache}
    {num gen : Nat} (hc : CacheExact d.pre d.lookup limits d.bytes d.objectCount cache)
    (h : d.allowance limits ≤ budget.remaining) :
    (d.getObjectB limits budget cache num gen).1 = d.getObject limits num gen ∧
    CacheExact d.pre d.lookup limits d.bytes d.objectCount (d.getObjectB limits budget cache num gen).2.2 := by
  unfold OpenDoc.getObjectB
  split
  · rename_i c i hl
    split
    · rename_i hg
      obtain ⟨he, hc'⟩ := Xref.ObjStm.fetchCompressedB_eq (num := num) hc h
      refine ⟨?_, hc'⟩
      simp only [OpenDoc.getObject, OpenDoc.getObjectTrace, hl, hg, ↓reduceIte, he]
      rfl
    · rename_i hg
      refine ⟨?_, hc⟩
      simp [OpenDoc.getObject, OpenDoc.getObjectTrace, hl, hg]
  · exact ⟨rfl, hc⟩

/-- **Depth bound** for `getObjectB`. -/
theorem getObjectB_depth {d : OpenDoc} {limits : Limits} {budget : Budget} {cache : Cache}
    {num gen : Nat} {b : IndirectBody} (h : (d.getObjectB limits budget cache num gen).1 = .ok b) :
    bodyDepth b ≤ limits.maxObjectDepth := by
  unfold OpenDoc.getObjectB at h
  split at h
  · split at h
    · simp only at h
      cases hf : (Xref.ObjStm.fetchCompressedB d.pre d.lookup limits d.bytes d.objectCount num budget
          cache).1 with
      | error e => rw [hf] at h; cases h
      | ok o =>
        rw [hf] at h
        cases h
        exact Xref.ObjStm.fetchCompressedB_depth hf
    · cases h; simp [nullBody, bodyDepth, PdfObject.depth]
  · exact getObject_depth h

/-- Budgeted validation (rule P2): the root is fetched with `getObjectB`. -/
def validateB (limits : Limits) (budget : Budget) (cache : Cache) (d : OpenDoc) :
    (Except Error OpenDoc) × Budget × Cache :=
  match d.trailer.root? with
  | none => (.error (.malformed 0 "trailer has no /Root"), budget, cache)
  | some (n, g) =>
    let r := d.getObjectB limits budget cache n g
    (match r.1 with
     | .error e => .error e
     | .ok (.obj (.dict _)) => .ok d
     | .ok (.obj .null) => .error (.malformed 0 s!"/Root {n} {g} R is not defined")
     | .ok _ => .error (.malformed 0 s!"/Root {n} {g} R is not a dictionary"), r.2.1, r.2.2)

/-- `validateB` never increases the budget. -/
theorem validateB_le (limits : Limits) (budget : Budget) (cache : Cache) (d : OpenDoc) :
    (validateB limits budget cache d).2.1.remaining ≤ budget.remaining := by
  unfold validateB
  split
  · exact Nat.le_refl _
  · exact getObjectB_le _ _ _ _ _ _

/-- Cost of `validateB`: at most one fetch. -/
theorem validateB_cost (limits : Limits) (budget : Budget) (cache : Cache) (d : OpenDoc) :
    budget.remaining ≤ (validateB limits budget cache d).2.1.remaining + d.allowance limits := by
  unfold validateB
  split
  · exact Nat.le_add_right _ _
  · exact getObjectB_cost _ _ _ _ _ _

/-- `validateB` returns its argument unchanged on success. -/
theorem validateB_eq_self {limits : Limits} {budget : Budget} {cache : Cache} {d d' : OpenDoc}
    (h : (validateB limits budget cache d).1 = .ok d') : d' = d := by
  unfold validateB at h
  split at h
  · cases h
  · simp only at h
    split at h <;> first | (cases h; rfl) | cases h

/-- On success, `validateB` checked the root: present and a dictionary (fetched with the
budget and cache it was given). -/
theorem validateB_root {limits : Limits} {budget : Budget} {cache : Cache} {d d' : OpenDoc}
    (h : (validateB limits budget cache d).1 = .ok d') :
    ∃ n g dict, d.trailer.root? = some (n, g) ∧
      (d.getObjectB limits budget cache n g).1 = .ok (.obj (.dict dict)) := by
  unfold validateB at h
  split at h
  · cases h
  · rename_i n g hr
    simp only at h
    split at h
    · cases h
    · rename_i dict hg
      exact ⟨n, g, dict, hr, hg⟩
    · cases h
    · cases h

/-- Budget large enough ⇒ `validateB` is `validate`, and the cache stays exact. -/
theorem validateB_eq {limits : Limits} {budget : Budget} {cache : Cache} {d : OpenDoc}
    (hc : CacheExact d.pre d.lookup limits d.bytes d.objectCount cache)
    (h : d.allowance limits ≤ budget.remaining) :
    (validateB limits budget cache d).1 = validate limits d ∧
    CacheExact d.pre d.lookup limits d.bytes d.objectCount (validateB limits budget cache d).2.2 := by
  unfold validateB validate
  split
  · exact ⟨rfl, hc⟩
  · rename_i n g hr
    obtain ⟨he, hc'⟩ := getObjectB_eq (num := n) (gen := g) hc h
    refine ⟨?_, hc'⟩
    simp only
    rw [he]

/-- The budgeted strict path (rules P1, P2): `Chain.loadChainB`, `checkSize`, merge,
`validateB` (with an empty cache). Returns the result, the budget and the cache. -/
def strictOpenB (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    (Except Error OpenDoc) × Budget × Cache :=
  match Core.Xref.Chain.loadChainB limits budget bytes with
  | (.error e, b1) => (.error e, b1, [])
  | (.ok revs, b1) =>
    match checkSize revs with
    | .error e => (.error e, b1, [])
    | .ok () =>
      match ofChain limits bytes revs with
      | .error e => (.error e, b1, [])
      | .ok d => validateB limits b1 [] d

/-- The budgeted repair path (rule P3), with an empty cache. -/
def repairOpenB (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    (Except Error OpenDoc) × Budget × Cache :=
  match SafePdf.Repair.repair limits bytes with
  | .error e => (.error e, budget, [])
  | .ok (sec, tr) =>
    match (OpenDoc.mk' bytes sec tr 0 true).withCrypt limits with
    | .error e => (.error e, budget, [])
    | .ok d => validateB limits budget [] d

/-- **Budgeted entry point** (task 3.13): `openFile` with the xref-stream decodes of the chain
and the object-stream decode of the root validation charged against `budget`. The cache of the
strict attempt is dropped when repair runs (it belongs to another cross-reference section).
Returns the result, the budget left and the cache of the returned document. -/
def openFileB (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    (Except Error OpenDoc) × Budget × Cache :=
  match strictOpenB limits budget bytes with
  | (.ok d, b1, c1) => (.ok d, b1, c1)
  | (.error e, b1, _) =>
    if e.isFinal then (.error e, b1, [])
    else
      match repairOpenB limits b1 bytes with
      | (.ok d, b2, c2) => (.ok d, b2, c2)
      | (.error e', b2, _) => (.error (bothFailed e e'), b2, [])

/-- `strictOpenB` never increases the budget. -/
theorem strictOpenB_le (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    (strictOpenB limits budget bytes).2.1.remaining ≤ budget.remaining := by
  unfold strictOpenB
  have h1 := Core.Xref.Chain.loadChainB_le limits budget bytes
  rcases hl : Core.Xref.Chain.loadChainB limits budget bytes with ⟨r1, b1⟩
  rw [hl] at h1
  simp only at h1
  rcases r1 with e | revs
  · exact h1
  · simp only
    split
    · exact h1
    · split
      · exact h1
      · exact Nat.le_trans (validateB_le _ _ _ _) h1

/-- `repairOpenB` never increases the budget. -/
theorem repairOpenB_le (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    (repairOpenB limits budget bytes).2.1.remaining ≤ budget.remaining := by
  unfold repairOpenB
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · exact validateB_le _ _ _ _

/-- **The budgeted repair path, unfolded**: a scanned section with its decryption state,
validated with the budget it was given and an empty cache. -/
theorem repairOpenB_ok {limits : Limits} {budget : Budget} {bytes : ByteArray} {d : OpenDoc}
    (h : (repairOpenB limits budget bytes).1 = .ok d) :
    ∃ sec tr, SafePdf.Repair.repair limits bytes = .ok (sec, tr) ∧
      (OpenDoc.mk' bytes sec tr 0 true).withCrypt limits = .ok d ∧
      (validateB limits budget [] d).1 = .ok d := by
  unfold repairOpenB at h
  split at h
  · cases h
  · rename_i sec tr hr
    split at h
    · cases h
    · rename_i d0 hw
      have := validateB_eq_self h
      subst this
      exact ⟨sec, tr, hr, hw, h⟩

/-- **Budget monotone**: `openFileB` never increases the budget. -/
theorem openFileB_le (limits : Limits) (budget : Budget) (bytes : ByteArray) :
    (openFileB limits budget bytes).2.1.remaining ≤ budget.remaining := by
  unfold openFileB
  have h1 := strictOpenB_le limits budget bytes
  rcases hs : strictOpenB limits budget bytes with ⟨r1, b1, c1⟩
  rw [hs] at h1
  simp only at h1
  rcases r1 with e | d
  · simp only
    split
    · exact h1
    · have h2 := repairOpenB_le limits b1 bytes
      rcases hr : repairOpenB limits b1 bytes with ⟨r2, b2, c2⟩
      rw [hr] at h2
      simp only at h2
      rcases r2 with e' | d' <;> exact Nat.le_trans h2 h1
  · exact h1

/-- **Strict first** (budgeted): when the budgeted strict path succeeds, `openFileB` returns
it. -/
theorem openFileB_strict {limits : Limits} {budget : Budget} {bytes : ByteArray} {d : OpenDoc}
    (h : (strictOpenB limits budget bytes).1 = .ok d) :
    (openFileB limits budget bytes).1 = .ok d := by
  unfold openFileB
  rcases hs : strictOpenB limits budget bytes with ⟨r1, b1, c1⟩
  rw [hs] at h
  simp only at h
  subst h
  rfl

/-- **Cycles are final** (budgeted, rule P5): when the budgeted strict path fails with a
cycle error, `openFileB` returns exactly that error; repair is not tried. -/
theorem openFileB_cycle {limits : Limits} {budget : Budget} {bytes : ByteArray} {e : Error}
    (h : (strictOpenB limits budget bytes).1 = .error e) (hc : e.isCycle = true) :
    (openFileB limits budget bytes).1 = .error e := by
  unfold openFileB
  rcases hs : strictOpenB limits budget bytes with ⟨r1, b1, c1⟩
  rw [hs] at h
  simp only at h
  subst h
  simp [Error.isFinal, hc]

/-- **`/Prev`, `/XRefStm` and xref-stream cycles are final** (budgeted). -/
theorem openFileB_loadChain_cycle {limits : Limits} {budget : Budget} {bytes : ByteArray}
    {e : Error} (h : (Core.Xref.Chain.loadChainB limits budget bytes).1 = .error e)
    (hc : e.isCycle = true) : (openFileB limits budget bytes).1 = .error e := by
  apply openFileB_cycle _ hc
  unfold strictOpenB
  rcases hl : Core.Xref.Chain.loadChainB limits budget bytes with ⟨r1, b1⟩
  rw [hl] at h
  simp only at h
  subst h
  rfl

/-- **Root validated** (budgeted): an opened document's `/Root` is present and resolves to a
dictionary (fetched from an empty cache with the budget left at validation). -/
theorem openFileB_root {limits : Limits} {budget : Budget} {bytes : ByteArray} {d : OpenDoc}
    (h : (openFileB limits budget bytes).1 = .ok d) :
    ∃ n g dict b, d.trailer.root? = some (n, g) ∧
      (d.getObjectB limits b [] n g).1 = .ok (.obj (.dict dict)) := by
  unfold openFileB at h
  rcases hs : strictOpenB limits budget bytes with ⟨r1, b1, c1⟩
  rw [hs] at h
  rcases r1 with e | d0
  · simp only at h
    split at h
    · cases h
    · rcases hr : repairOpenB limits b1 bytes with ⟨r2, b2, c2⟩
      rw [hr] at h
      rcases r2 with e' | d1
      · cases h
      · simp only [Except.ok.injEq] at h
        subst h
        have hr1 : (repairOpenB limits b1 bytes).1 = .ok d1 := by rw [hr]
        obtain ⟨-, -, -, -, hv⟩ := repairOpenB_ok hr1
        obtain ⟨n, g, dict, h1, h2⟩ := validateB_root hv
        exact ⟨n, g, dict, b1, h1, h2⟩
  · simp only [Except.ok.injEq] at h
    subst h
    unfold strictOpenB at hs
    rcases hl : Core.Xref.Chain.loadChainB limits budget bytes with ⟨r0, b0⟩
    rw [hl] at hs
    rcases r0 with e | revs
    · cases hs
    · simp only at hs
      split at hs
      · cases hs
      · split at hs
        · cases hs
        · rename_i d2 _
          have hv : (validateB limits b0 [] d2).1 = .ok d0 := by rw [hs]
          have := validateB_eq_self hv
          subst this
          obtain ⟨n, g, dict, h1, h2⟩ := validateB_root hv
          exact ⟨n, g, dict, b0, h1, h2⟩

/-- **S7, budgeted**: a document with `repaired = false` came from the budgeted strict path:
`loadChainB` succeeded, the section is the merge of the chain, the trailer the newest one. -/
theorem openFileB_repaired {limits : Limits} {budget : Budget} {bytes : ByteArray} {d : OpenDoc}
    (h : (openFileB limits budget bytes).1 = .ok d) (hr : d.repaired = false) :
    ∃ revs, (Core.Xref.Chain.loadChainB limits budget bytes).1 = .ok revs ∧
      d.xref = Core.Xref.Chain.mergeChain revs ∧
      d.revisions = revs.length ∧
      ∃ sec off rest, revs = (sec, d.trailer, off) :: rest := by
  unfold openFileB at h
  rcases hs : strictOpenB limits budget bytes with ⟨r1, b1, c1⟩
  rw [hs] at h
  rcases r1 with e | d0
  · simp only at h
    split at h
    · cases h
    · rcases hrp : repairOpenB limits b1 bytes with ⟨r2, b2, c2⟩
      rw [hrp] at h
      rcases r2 with e' | d1
      · cases h
      · simp only [Except.ok.injEq] at h
        subst h
        have hr1 : (repairOpenB limits b1 bytes).1 = .ok d1 := by rw [hrp]
        obtain ⟨_, _, -, hw, -⟩ := repairOpenB_ok hr1
        obtain ⟨c, rfl⟩ := withCrypt_ok hw
        cases hr
  · simp only [Except.ok.injEq] at h
    subst h
    unfold strictOpenB at hs
    rcases hl : Core.Xref.Chain.loadChainB limits budget bytes with ⟨r0, b0⟩
    rw [hl] at hs
    rcases r0 with e | revs
    · cases hs
    · simp only at hs
      split at hs
      · cases hs
      · split at hs
        · cases hs
        · rename_i d2 hd
          have hv := congrArg Prod.fst hs
          simp only at hv
          have := validateB_eq_self hv
          subst this
          unfold ofChain at hd
          split at hd
          · cases hd
          · obtain ⟨c, rfl⟩ := withCrypt_ok hd
            exact ⟨_, rfl, rfl, rfl, _, _, _, rfl⟩

/-- An opened document (unbudgeted) never comes with a non-empty cache requirement: the empty
cache is exact for every document. -/
theorem cacheExact_nil (d : OpenDoc) (limits : Limits) :
    CacheExact d.pre d.lookup limits d.bytes d.objectCount [] :=
  Xref.ObjStm.cacheExact_nil _ _ _ _ _

/-- Budget large enough ⇒ `strictOpenB` is `strictOpen`; it costs at most
`(maxRevisions + 1) · decodeAllowance`, and its cache is exact for the document. -/
theorem strictOpenB_eq {limits : Limits} {budget : Budget} {bytes : ByteArray}
    (h : (limits.maxRevisions + 1) * Core.Xref.Chain.decodeAllowance limits bytes ≤
      budget.remaining) :
    (strictOpenB limits budget bytes).1 = strictOpen limits bytes ∧
    budget.remaining ≤ (strictOpenB limits budget bytes).2.1.remaining +
      (limits.maxRevisions + 1) * Core.Xref.Chain.decodeAllowance limits bytes ∧
    ∀ d, (strictOpenB limits budget bytes).1 = .ok d →
      CacheExact d.pre d.lookup limits d.bytes d.objectCount (strictOpenB limits budget bytes).2.2 := by
  have hK : limits.maxRevisions * Core.Xref.Chain.decodeAllowance limits bytes ≤
      budget.remaining := by
    rw [Nat.succ_mul] at h; omega
  have he := Core.Xref.Chain.loadChainB_eq hK
  have hc := Core.Xref.Chain.loadChainB_cost limits budget bytes
  unfold strictOpenB strictOpen
  rcases hl : Core.Xref.Chain.loadChainB limits budget bytes with ⟨r1, b1⟩
  rw [hl] at he hc
  simp only at he hc
  rw [← he]
  rw [Nat.succ_mul] at h ⊢
  rcases r1 with e | revs
  · refine ⟨rfl, by simp only; omega, fun d hd => by cases hd⟩
  · simp only
    split
    · refine ⟨rfl, by simp only; omega, fun d hd => by cases hd⟩
    · split
      · refine ⟨rfl, by simp only; omega, fun d hd => by cases hd⟩
      · rename_i d hd
        have hbytes : d.bytes = bytes := by
          unfold ofChain at hd; split at hd
          · cases hd
          · obtain ⟨c, rfl⟩ := withCrypt_ok hd; rfl
        have hal : d.allowance limits ≤ b1.remaining := by
          unfold OpenDoc.allowance; rw [hbytes]; omega
        obtain ⟨hv, hcx⟩ := validateB_eq (cacheExact_nil d limits) hal
        have hvc := validateB_cost limits b1 [] d
        refine ⟨hv, ?_, fun d' hd' => ?_⟩
        · unfold OpenDoc.allowance at hvc; rw [hbytes] at hvc; omega
        · have := validateB_eq_self hd'
          subst this
          exact hcx

/-- Budget large enough ⇒ `repairOpenB` is `repairOpen`, and its cache is exact for the
document. -/
theorem repairOpenB_eq {limits : Limits} {budget : Budget} {bytes : ByteArray}
    (h : Core.Xref.Chain.decodeAllowance limits bytes ≤ budget.remaining) :
    (repairOpenB limits budget bytes).1 = repairOpen limits bytes ∧
    ∀ d, (repairOpenB limits budget bytes).1 = .ok d →
      CacheExact d.pre d.lookup limits d.bytes d.objectCount (repairOpenB limits budget bytes).2.2 := by
  unfold repairOpenB repairOpen
  split
  · exact ⟨rfl, fun d hd => by cases hd⟩
  · rename_i sec tr _
    split
    · exact ⟨rfl, fun d hd => by cases hd⟩
    · rename_i d0 hw
      have hb : d0.bytes = bytes := by obtain ⟨c, rfl⟩ := withCrypt_ok hw; rfl
      have hal : d0.allowance limits ≤ budget.remaining := by
        unfold OpenDoc.allowance; rw [hb]; exact h
      obtain ⟨hv, hcx⟩ := validateB_eq (cacheExact_nil d0 limits) hal
      refine ⟨hv, fun d hd => ?_⟩
      have := validateB_eq_self hd
      subst this
      exact hcx

/-- **Budget large enough ⇒ same document** (task 3.13): with at least
`(maxRevisions + 2) · decodeAllowance limits bytes` left (the chain, the strict root
validation and the repaired root validation), `openFileB` returns exactly what `openFile`
returns, and the cache it returns is exact for the document (so later `getObjectB` calls with
enough budget return what `getObject` returns, `getObjectB_eq`). -/
theorem openFileB_eq {limits : Limits} {budget : Budget} {bytes : ByteArray}
    (h : (limits.maxRevisions + 2) * Core.Xref.Chain.decodeAllowance limits bytes ≤
      budget.remaining) :
    (openFileB limits budget bytes).1 = openFile limits bytes ∧
    ∀ d, (openFileB limits budget bytes).1 = .ok d →
      CacheExact d.pre d.lookup limits d.bytes d.objectCount (openFileB limits budget bytes).2.2 := by
  have h2 : (limits.maxRevisions + 2) * Core.Xref.Chain.decodeAllowance limits bytes =
      (limits.maxRevisions + 1) * Core.Xref.Chain.decodeAllowance limits bytes +
        Core.Xref.Chain.decodeAllowance limits bytes := by
    rw [show limits.maxRevisions + 2 = (limits.maxRevisions + 1) + 1 by omega, Nat.succ_mul]
  have h1 : (limits.maxRevisions + 1) * Core.Xref.Chain.decodeAllowance limits bytes ≤
      budget.remaining := by omega
  obtain ⟨he, hc, hx⟩ := strictOpenB_eq h1
  unfold openFileB openFile
  rcases hs : strictOpenB limits budget bytes with ⟨r1, b1, c1⟩
  rw [hs] at he hc hx
  simp only at he hc hx
  rw [← he]
  rcases r1 with e | d
  · simp only
    split
    · exact ⟨rfl, fun d hd => by cases hd⟩
    · have hb1 : Core.Xref.Chain.decodeAllowance limits bytes ≤ b1.remaining := by omega
      obtain ⟨hre, hrx⟩ := repairOpenB_eq (bytes := bytes) hb1
      rcases hr : repairOpenB limits b1 bytes with ⟨r2, b2, c2⟩
      rw [hr] at hre hrx
      simp only at hre hrx
      rw [← hre]
      rcases r2 with e' | d'
      · exact ⟨rfl, fun d hd => by cases hd⟩
      · refine ⟨rfl, fun d hd => ?_⟩
        simp only [Except.ok.injEq] at hd
        subst hd
        exact hrx d' rfl
  · exact ⟨rfl, fun d' hd' => by
      simp only [Except.ok.injEq] at hd'
      subst hd'
      exact hx d rfl⟩

/-! ### Sessions -/

/-- **An open document with its budget** (task 3.13): the document, what is left of the
decoded-bytes budget (`Filter.Budget`), and the decoded object streams (`ObjStm.Cache`).
Fetch objects with `Session.getObject`; decode streams with `Filter.decodeStreamB` from
`budget`, storing the budget back. -/
structure Session where
  /-- The opened document. -/
  doc : OpenDoc
  /-- What is left of `limits.maxDecodedTotalBytes`. -/
  budget : Budget
  /-- Object streams decoded so far. -/
  cache : Cache

/-- **Open a session**: `openFileB` from the full budget `Budget.init limits`. -/
def Session.open (limits : Limits) (bytes : ByteArray) : Except Error Session :=
  match openFileB limits (Budget.init limits) bytes with
  | (.ok d, b, c) => .ok ⟨d, b, c⟩
  | (.error e, _, _) => .error e

/-- A session for an already opened document: the full budget, an empty cache. -/
def Session.ofDoc (limits : Limits) (d : OpenDoc) : Session := ⟨d, Budget.init limits, []⟩

/-- **Budgeted fetch** in a session: `getObjectB` with the session's budget and cache. -/
def Session.getObject (s : Session) (limits : Limits) (num gen : Nat) :
    (Except Error IndirectBody) × Session :=
  let r := s.doc.getObjectB limits s.budget s.cache num gen
  (r.1, ⟨s.doc, r.2.1, r.2.2⟩)

/-- A session fetch never increases the budget and keeps the document. -/
theorem Session.getObject_le (s : Session) (limits : Limits) (num gen : Nat) :
    (s.getObject limits num gen).2.budget.remaining ≤ s.budget.remaining ∧
    (s.getObject limits num gen).2.doc = s.doc :=
  ⟨getObjectB_le _ _ _ _ _ _, rfl⟩

/-- An exact session: its cache holds only exact decodes. -/
def Session.Exact (s : Session) (limits : Limits) : Prop :=
  CacheExact s.doc.pre s.doc.lookup limits s.doc.bytes s.doc.objectCount s.cache

/-- **A session fetch is `getObject`** when the session is exact and at least one decode's
worth of budget is left; the session stays exact. -/
theorem Session.getObject_eq {s : Session} {limits : Limits} {num gen : Nat}
    (hx : s.Exact limits) (h : s.doc.allowance limits ≤ s.budget.remaining) :
    (s.getObject limits num gen).1 = s.doc.getObject limits num gen ∧
    (s.getObject limits num gen).2.Exact limits :=
  getObjectB_eq hx h

/-- A fresh session of an opened document is exact. -/
theorem Session.ofDoc_exact (limits : Limits) (d : OpenDoc) : (Session.ofDoc limits d).Exact limits :=
  cacheExact_nil d limits

/-- **Opening a session with the default budget**: whenever the full budget covers
`(maxRevisions + 2) · decodeAllowance`, `Session.open` opens exactly the document `openFile`
opens, and the session is exact. -/
theorem Session.open_eq {limits : Limits} {bytes : ByteArray}
    (h : (limits.maxRevisions + 2) * Core.Xref.Chain.decodeAllowance limits bytes ≤
      limits.maxDecodedTotalBytes) :
    (∀ s, Session.open limits bytes = .ok s → openFile limits bytes = .ok s.doc ∧ s.Exact limits) ∧
    (∀ e, Session.open limits bytes = .error e → openFile limits bytes = .error e) := by
  obtain ⟨he, hx⟩ := openFileB_eq (budget := Budget.init limits) (bytes := bytes) h
  unfold Session.open
  rcases ho : openFileB limits (Budget.init limits) bytes with ⟨r, b, c⟩
  rw [ho] at he hx
  simp only at he hx
  rcases r with e | d
  · refine ⟨fun s hs => ?_, fun e' he' => ?_⟩
    · simp only at hs; cases hs
    · simp only [Except.error.injEq] at he'
      subst he'
      exact he.symm
  · refine ⟨fun s hs => ?_, fun e' he' => ?_⟩
    · simp only [Except.ok.injEq] at hs
      subst hs
      exact ⟨he.symm, hx d rfl⟩
    · simp only at he'; cases he'

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

/-! ### Budgeted opening (task 3.13) -/

/-- Test helper: summary of a budgeted open from a budget of `n` bytes. -/
private def osb (n : Nat) (b : ByteArray) : String :=
  match openFileB Limits.default ⟨n⟩ b with
  | (.ok d, bud, c) => s!"ok repaired={d.repaired} left={bud.remaining} cached={c.length}"
  | (.error (.cycle o m), bud, _) => s!"cycle@{o} {m} left={bud.remaining}"
  | (.error _, bud, _) => s!"err left={bud.remaining}"

-- classic tables decode nothing: the budget is untouched, even an empty one
#guard osb 100 minimalValid == "ok repaired=false left=100 cached=0"
#guard osb 0 minimalValid == "ok repaired=false left=0 cached=0"
#guard osb 100 minimalBroken == "ok repaired=true left=100 cached=0"
#guard osb 100 minimalPrevSelf == "cycle@110 xref /Prev cycle left=100"
-- a session fetch of an undefined object is null and free
#guard (match Session.open Limits.default minimalValid with
  | .ok s =>
    let (r, s') := s.getObject Limits.default 7 0
    isNull r && s'.budget == s.budget
  | .error _ => false)

end Tests

end SafePdf.Core.Open
