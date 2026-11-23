import SafePdf.Core.Write.Serialize
import SafePdf.Core.Doc
import SafePdf.Core.Crypt.Md5
import SafePdf.Core.Write.Encrypt

/-!
# Incremental-update writer (Plan.md §4 S8/C7, §6 Phase 9 "Persistence"; task 9.5a)

`writeAnnots limits doc marks` appends annotation objects to an opened document as an
**incremental update** (ISO 32000-2 §7.5.6): the result is `doc.file.bytes ++ update`, the
original bytes untouched (S8). `marks` lists, per page index, already-built annotation
dictionaries (task 9.5b builds `/Highlight` and `/Text` ones). The update holds:

* the new annotation objects, numbered from the old trailer's `/Size` upwards (W3);
* superseded annotation objects under their own numbers, and page `/Annots` without removed
  references (W11, task 9.5g; `writeUpdate`);
* each affected page dictionary, rewritten under its own object number and generation with
  `/Annots` extended (W4);
* auxiliary stream objects passed by the caller, e.g. appearance streams (W9, task 9.5b);
* a cross-reference section for exactly these objects and a trailer with `/Prev` = the old
  `startxref` offset, `/Size` grown, the other entries carried over (W5–W7);
* the `startxref` / `%%EOF` tail.

## Rules and decisions

* W1. **Strictly opened input only.** A repaired document (`repaired = true`)
  is refused (`Error.unsupported`): its cross-reference chain is broken, so a `/Prev` to it
  would extend a file that the strict parser does not accept. (Task 9.5a also refused
  encrypted documents; task 9.5f lifted that, rule W10. A document with `/Encrypt` in the
  trailer but no decryption state is still refused: it cannot occur after a strict open.)
* W10. **Encrypted documents** (task 9.5f): the written objects are encrypted with the
  document's own security handler and file key (`Core.Write.Encrypt`, rules E1-E7: per-object
  key by Algorithm 1, RC4 / AES-128 / AES-256 by `/StrF` and `/StmF`, an AES IV derived by
  SHA-256 from the caller's `ivSeed` — fresh OS randomness in the viewer, task 12.4 — since the
  core itself has no randomness; every theorem of `Spec.Write` holds for every seed). The plan keeps both forms: the
  plaintext objects (`Plan.objects`, `Plan.aux` — what the reader must see) and the written
  ones (`Plan.wire`, `Plan.auxWire`). An auxiliary stream's `/Length` is that of its written
  data, so its decrypted body is `auxBody` (with `/Length` = `Encrypt.encLen`). The trailer
  keeps `/Encrypt` and the first `/ID` string (the file key depends on it, W6, W7); the
  update's xref stream is never encrypted. The self-check (W8) re-opens the result, which
  decrypts every written object, and compares with the plaintext — so the C7 theorems hold
  for encrypted documents as stated — and checks that the result's decryption state has the
  original's file key and methods (`sameCrypt`) and, since task 9.5e2, that it is the
  original's state in every field (`sameState`: the whole handler incl. `/EncryptMetadata`
  and the crypt filters, the key, the `/Encrypt` object, the `/Perms` result). The writer
  copies `/Encrypt` into the update's trailer verbatim (W6), so the check holds for every
  correct write; it is what lets `Spec.Write.c7Value'` cover a direct trailer `/Encrypt`
  and a superseded (W11) indirect one without a side condition.
* W2. The page indices of `marks` are distinct and in range; each annotation dictionary is
  canonical with in-range references (the printer's round-trip hypotheses,
  `Spec.RoundTripCore.parseObject_print`) and nests within `limits.maxObjectDepth`.
* W3. Annotation `k` (in `marks` order, over all pages) gets object number `size + k`,
  generation 0, where `size` is the newest trailer's `/Size`. The new `/Size` must stay within
  `limits.maxObjects + 1` (else `limitExceeded .objects`).
* W4. **`/Annots` is rewritten on the page, never in a shared array object.** The page's old
  annotation list is its `/Annots` value: a direct array, or an indirect reference to an
  array (resolved one level, as `Core.Annot.collect` does); absent or `null` is empty. The
  rewritten page dictionary is the old one with `/Annots` set (in place, or appended when
  absent) to a **direct** array: the old elements followed by references to the new
  annotations. An indirect `/Annots` array object is left as it was (it may be shared with
  other pages; rewriting the page is always local). A page stored in an object stream is
  written as an ordinary object (generation 0, as its entry implies).
* W5. **Cross-reference kind follows the original's newest section** (the one at
  `startxref`): a classic table (also for a hybrid file, §7.5.8.4: the update's classic
  trailer has no `/XRefStm`; the old hybrid table and its stream stay in the chain through
  `/Prev`) gets a classic section; an xref stream gets an uncompressed xref stream (no
  `/Filter`; `/W [1 w 2]`, `/Index` runs, an entry for itself), so that a reader which only
  knows xref streams for that file — or a strict reader that rejects a classic section after
  an xref-stream file — still reads it.
* W6. **Trailer.** Classic: `/Size`, then every entry of the old trailer except `/Size`,
  `/Prev` and `/XRefStm`, then `/Prev`. Xref stream: `/Type /XRef`, `/Size`, `/Index`, `/W`,
  then `/Root`, `/Info`, `/ID`, `/Encrypt` (task 9.5f) of the old trailer (the other keys of an xref-stream
  dictionary describe that stream, §7.5.8.2), then `/Prev` and `/Length`.
* W7. **`/ID`** (§14.4): when the old trailer has `/ID [a b]` of two strings, the first is kept
  and the second becomes the MD5 of `b` followed by the bytes of the new objects (a
  deterministic stand-in for "a new value when the file is updated"; no clock or randomness
  in the core). `/Info` is carried over unchanged (no `/ModDate` update).
* W9. **Auxiliary streams** (task 9.5b): besides the annotation dictionaries the caller may
  pass stream objects (`AuxStream`: a dictionary and raw data), e.g. the annotations'
  appearance streams (`/AP /N`). Stream `j` gets object number `size + annotCount + j`,
  generation 0 (after all annotations, before an xref stream), so the caller, which knows
  `size` (the trailer's `/Size`) and how many annotations it passes, can reference it from
  its annotation dictionaries. The writer sets the stream's `/Length` (`setKey`); the
  dictionary must satisfy the W2 conditions. They are written as stream objects (S1), listed
  in the section, and checked by the self-check (W8) to fetch back exactly.
* W8. **Self-check.** The writer re-parses its own result before returning it, with the same
  strict parser the viewer uses: the chain of `bytes ++ update` must load as the new section
  followed by the old chain (`checkChain`: `startxref` at or after the old end of file, the
  section parses with exactly the expected object numbers, no `/XRefStm`, `/Prev` = the old
  `startxref`, room for one more revision), and `Open.openFile` must open it strictly and
  return every written object exactly (`checkObjects`). On failure the writer returns
  `Error.malformed` instead of bytes. `Spec.Write` derives the conservativity theorem C7 from
  these checks.

* W11. **Removal and supersession** (task 9.5g; `writeUpdate`): the general entry point takes,
  per page (`PageEdit`), references to **remove** from the page's annotation list and
  dictionaries to **add**, and a list of **supersessions** `(num, gen, dict)`: an existing
  object re-emitted under its own number and generation with a new dictionary (ISO 32000-2
  §7.5.6: the newest cross-reference entry for a number wins; the old object stays in the
  earlier revision, which is normal for incremental updates). Conditions (else
  `Error.malformed`): every removed reference occurs in the page's old annotation list; the
  superseded numbers are distinct, below the old `/Size`, not the object of any page, and
  their old object is a dictionary under exactly that generation; the new dictionaries
  satisfy W2. The rewritten page's `/Annots` is the old list without the removed references
  (`PagePlan.kept`: a filter, so every other element — superseded ones included — keeps its
  relative position) followed by the new references. A page whose annotations are only
  superseded is not rewritten (its references do not change). Superseded objects are written
  after the pages' objects and take no new numbers (W3 and W9 count only added annotations).
  Encryption (W10) uses the superseded object's own number and generation. The self-check
  (W8) fetches every superseded object back. `writeAnnots` is `writeUpdate` with add-only
  page edits and no supersessions, so every 9.5a/9.5b/9.5f statement about it keeps its form.

Everything is pure and total (structural recursion only).
-/

namespace SafePdf.Core.Write.Incremental

open SafePdf
open SafePdf.Core.Open (OpenDoc)
open SafePdf.Core.Xref (XrefEntry XrefSection Trailer)
open SafePdf.Core.Write.Serialize

/-! ## Names -/

/-- Key `/Annots`. -/
def nameAnnots : Name := Name.ofString "Annots"
/-- Key `/ID`. -/
def nameID : Name := Name.ofString "ID"
/-- Key `/Info`. -/
def nameInfo : Name := Name.ofString "Info"
/-- Key `/Length`. -/
def nameLength : Name := Name.ofString "Length"

/-! ## Dictionaries -/

/-- Set key `k` to `v`: replace the first entry with key `k`, or append one. -/
def setKey (d : Dict) (k : Name) (v : PdfObject) : Dict :=
  match d with
  | [] => [(k, v)]
  | (k', v') :: rest => if k' = k then (k, v) :: rest else (k', v') :: setKey rest k v

/-- After `setKey`, looking up `k` gives `v`. -/
theorem lookup_setKey (d : Dict) (k : Name) (v : PdfObject) :
    Dict.lookup (setKey d k v) k = some v := by
  induction d with
  | nil => simp [setKey, Dict.lookup]
  | cons e rest ih =>
    obtain ⟨k', v'⟩ := e
    unfold setKey
    split
    · simp [Dict.lookup]
    · rename_i hk
      simp only [Dict.lookup, hk, ↓reduceIte]
      exact ih

/-- `setKey` leaves every other key alone. -/
theorem lookup_setKey_ne (d : Dict) {k k' : Name} (v : PdfObject) (h : k' ≠ k) :
    Dict.lookup (setKey d k v) k' = Dict.lookup d k' := by
  induction d with
  | nil => simp [setKey, Dict.lookup, Ne.symm h]
  | cons e rest ih =>
    obtain ⟨k₀, v₀⟩ := e
    unfold setKey
    split
    · rename_i hk
      subst hk
      simp [Dict.lookup, Ne.symm h]
    · simp only [Dict.lookup]
      split
      · rfl
      · exact ih

/-! ## Annotation lists -/

/-- The annotation list of a page dictionary `pd` of `d` (rule W4): the `/Annots` array,
direct or behind one indirect reference; absent or `null` is empty. -/
def annotItems (d : OpenDoc) (limits : Limits) (pd : Dict) : Except Error (List PdfObject) :=
  match Dict.get? pd nameAnnots with
  | none => .ok []
  | some (.array xs) => .ok xs
  | some (.ref n g) =>
    match d.getObject limits n g with
    | .ok (.obj (.array xs)) => .ok xs
    | .ok (.obj .null) => .ok []
    | .ok _ => .error (.malformed 0 s!"/Annots {n} {g} R is not an array")
    | .error e => .error e
  | some _ => .error (.malformed 0 "/Annots is not an array")

/-- **The annotations of page object `num gen`** in `d`: its dictionary's annotation list
(`annotItems`). The C7 statement is phrased with this function. -/
def annotsOf (d : OpenDoc) (limits : Limits) (num gen : Nat) : Except Error (List PdfObject) :=
  match d.getObject limits num gen with
  | .ok (.obj (.dict pd)) => annotItems d limits pd
  | .ok _ => .error (.malformed 0 s!"page {num} {gen} is not a dictionary")
  | .error e => .error e

/-! ## The plan -/

/-- Annotations to add: per page index, the annotation dictionaries, in order. -/
abbrev Marks := List (Nat × List Dict)

/-- An auxiliary stream object written with the annotations (rule W9): its dictionary
(`/Length` is set by the writer) and its raw data. -/
structure AuxStream where
  /-- The stream dictionary (without `/Length`, or with any value: it is overwritten). -/
  dict : Dict
  /-- The raw stream data (no filter is applied). -/
  data : List UInt8
  deriving Repr, Inhabited, DecidableEq

/-- The dictionary written for an auxiliary stream: `/Length` set to the data length. -/
def AuxStream.fullDict (a : AuxStream) : Dict := setKey a.dict nameLength (.int a.data.length)

/-- The body the strict parser must return for an auxiliary stream. -/
def AuxStream.body (a : AuxStream) : IndirectBody := .stream ⟨a.fullDict, ⟨a.data.toArray⟩⟩

/-- The body the strict parser must return for an auxiliary stream of a document with
decryption state `st` (rule W10): the stream's dictionary with `/Length` set to the length of
the *written* data (`Encrypt.encLen`), and its plaintext data. -/
def auxBody (st : Option Crypt.State) (a : AuxStream) : IndirectBody :=
  .stream ⟨setKey a.dict nameLength (.int (Encrypt.encLen st a.dict a.data.length)),
    ⟨a.data.toArray⟩⟩

/-- Without encryption, `auxBody` is the stream's own body (rule W9). -/
theorem auxBody_none (a : AuxStream) : auxBody none a = a.body := rfl

/-- Number auxiliary streams consecutively from `n` (rule W9). -/
def numberAux : Nat → List AuxStream → List (Nat × AuxStream)
  | _, [] => []
  | n, a :: as => (n, a) :: numberAux (n + 1) as

/-- Number dictionaries consecutively from `n`. -/
def numberFrom : Nat → List Dict → List (Nat × Dict)
  | _, [] => []
  | n, m :: ms => (n, m) :: numberFrom (n + 1) ms

/-- The changes to one page (rule W11): references to remove from its annotation list, and
annotation dictionaries to add. -/
structure PageEdit where
  /-- The page index. -/
  index : Nat
  /-- References `(num, gen)` to remove from the page's annotation list. -/
  remove : List (Nat × Nat) := []
  /-- Annotation dictionaries to add, in order. -/
  add : List Dict := []
  deriving Repr, Inhabited

/-- The changes of an update, page by page (rule W11). -/
abbrev Edits := List PageEdit

/-- A supersession (rule W11): object number, generation, and the new dictionary. -/
abbrev Supersede := Nat × Nat × Dict

/-- The page edit of an add-only page (`writeAnnots`). -/
def PageEdit.ofMarks (pm : Nat × List Dict) : PageEdit := ⟨pm.1, [], pm.2⟩

/-- The reference objects of `(num, gen)` pairs. -/
def refObjs (rs : List (Nat × Nat)) : List PdfObject := rs.map fun r => .ref r.1 r.2

/-- What happens to one page. -/
structure PagePlan where
  /-- The page index in `marks`. -/
  index : Nat
  /-- The page object number. -/
  num : Nat
  /-- The page generation. -/
  gen : Nat
  /-- The original page dictionary. -/
  dict : Dict
  /-- Its original annotation list (`annotItems`). -/
  old : List PdfObject
  /-- The new annotations with their object numbers. -/
  annots : List (Nat × Dict)
  /-- The references removed from the annotation list (rule W11; empty for `writeAnnots`). -/
  removed : List PdfObject := []

/-- References to the new annotations of a page. -/
def PagePlan.refs (pp : PagePlan) : List PdfObject := pp.annots.map fun a => .ref a.1 0

/-- The old annotations that stay (rule W11): the old list without the removed references,
in their order. -/
def PagePlan.kept (pp : PagePlan) : List PdfObject :=
  pp.old.filter fun o => decide (o ∉ pp.removed)

/-- The rewritten page dictionary (rules W4, W11). -/
def PagePlan.newDict (pp : PagePlan) : Dict :=
  setKey pp.dict nameAnnots (.array (pp.kept ++ pp.refs))

/-- The objects written for a page: its annotations, then the page. -/
def PagePlan.objects (pp : PagePlan) : List (Nat × Nat × PdfObject) :=
  pp.annots.map (fun a => (a.1, 0, .dict a.2)) ++ [(pp.num, pp.gen, .dict pp.newDict)]

/-- An annotation dictionary the printer writes back exactly (rule W2). -/
def markOk (limits : Limits) (m : Dict) : Bool :=
  (PdfObject.dict m).isCanonical && Print.refsInRange (.dict m) &&
    decide ((PdfObject.dict m).depth ≤ limits.maxObjectDepth)

/-- Plan one page edit (rules W4, W11): look the page up, read its dictionary and
annotation list, check that the removed references occur in it, number the new annotations
from `next`. -/
def planEditPage (limits : Limits) (doc : Doc.Doc) (next : Nat) (pe : PageEdit) :
    Except Error PagePlan :=
  match doc.pages[pe.index]? with
  | none => .error (.malformed 0 s!"page index {pe.index} out of range")
  | some p =>
    if pe.add.all (markOk limits) then
      match doc.file.getObject limits p.num p.gen with
      | .ok (.obj (.dict pd)) =>
        match annotItems doc.file limits pd with
        | .ok old =>
          if (refObjs pe.remove).all (fun r => decide (r ∈ old)) then
            .ok { index := pe.index, num := p.num, gen := p.gen, dict := pd, old,
                  annots := numberFrom next pe.add, removed := refObjs pe.remove }
          else .error (.malformed 0 s!"a removed annotation is not on page index {pe.index}")
        | .error e => .error e
      | .ok _ => .error (.malformed 0 s!"page {p.num} {p.gen} is not a dictionary")
      | .error e => .error e
    else .error (.malformed 0 "annotation dictionary is not canonical or nests too deep")

/-- Plan all page edits; annotation numbers continue from `next`. -/
def planEditPages (limits : Limits) (doc : Doc.Doc) : Nat → Edits → Except Error (List PagePlan)
  | _, [] => .ok []
  | next, pe :: rest =>
    match planEditPage limits doc next pe with
    | .error e => .error e
    | .ok pp =>
      match planEditPages limits doc (next + pe.add.length) rest with
      | .error e => .error e
      | .ok pps => .ok (pp :: pps)

/-- Plan one page of `writeAnnots` (an add-only `PageEdit`). -/
def planPage (limits : Limits) (doc : Doc.Doc) (next : Nat) (pm : Nat × List Dict) :
    Except Error PagePlan :=
  planEditPage limits doc next (PageEdit.ofMarks pm)

/-- Plan all pages of `writeAnnots`; annotation numbers continue from `next`. -/
def planPages (limits : Limits) (doc : Doc.Doc) (next : Nat) (marks : Marks) :
    Except Error (List PagePlan) :=
  planEditPages limits doc next (marks.map PageEdit.ofMarks)

/-- Whether a supersession is acceptable (rule W11): below `size`, not a page object, its new
dictionary passes W2, and its old object is a dictionary under that generation. -/
def supOk (limits : Limits) (doc : Doc.Doc) (size : Nat) (s : Supersede) : Bool :=
  decide (s.1 < size) && doc.pages.all (fun p => p.num != s.1) && markOk limits s.2.2 &&
    match doc.file.getObject limits s.1 s.2.1 with
    | .ok (.obj (.dict _)) => true
    | _ => false

/-- The whole update, before layout. -/
structure Plan where
  /-- The original `startxref` offset (the new `/Prev`). -/
  start : Nat
  /-- Whether the update's section is an xref stream (rule W5). -/
  stream : Bool
  /-- The original trailer's `/Size`. -/
  size : Nat
  /-- The pages to rewrite. -/
  pages : List PagePlan
  /-- The original trailer dictionary. -/
  trailer : Dict
  /-- The auxiliary streams with their object numbers (rule W9). -/
  aux : List (Nat × AuxStream) := []
  /-- The superseded objects: number, generation, new dictionary (rule W11). -/
  sups : List Supersede := []
  /-- The document's decryption state (rule W10; `none` when unencrypted). -/
  crypt : Option Crypt.State := none
  /-- The objects as written (encrypted under `crypt`; rule W10), in write order. -/
  wire : List (Nat × Nat × PdfObject) := []
  /-- The auxiliary streams as written: number, dictionary with `/Length`, data (rule W10). -/
  auxWire : List (Nat × Dict × List UInt8) := []

/-- The superseded objects as `(num, gen, object)` (rule W11). -/
def supObjects (sups : List Supersede) : List (Nat × Nat × PdfObject) :=
  sups.map fun s => (s.1, s.2.1, .dict s.2.2)

/-- The objects of the update, in write order: the pages' objects, then the superseded
objects (rule W11). -/
def Plan.objects (p : Plan) : List (Nat × Nat × PdfObject) :=
  p.pages.flatMap PagePlan.objects ++ supObjects p.sups

/-- The number of new annotation objects. -/
def Plan.annotCount (p : Plan) : Nat := (p.pages.map fun pp => pp.annots.length).sum

/-- The object number of the update's xref stream (rule W5; unused for a classic section). -/
def Plan.xrefNum (p : Plan) : Nat := p.size + p.annotCount + p.aux.length

/-- The new `/Size`. -/
def Plan.newSize (p : Plan) : Nat := p.xrefNum + (if p.stream then 1 else 0)

/-- The bodies the strict parser must return for the auxiliary streams (rule W10). -/
def Plan.auxExpected (p : Plan) : List (Nat × IndirectBody) :=
  p.aux.map fun a => (a.1, auxBody p.crypt a.2)

/-- One object as written (rule W10): encrypted under `st`, if any. -/
def wireObject (st : Option Crypt.State) (seed : ByteArray) (o : Nat × Nat × PdfObject) :
    Except Error (Nat × Nat × PdfObject) :=
  match st with
  | none => .ok o
  | some s =>
    match Encrypt.encryptObject s o.1 o.2.1 o.2.2 seed with
    | .ok o' => .ok (o.1, o.2.1, o')
    | .error e => .error e

/-- One auxiliary stream as written (rules W9, W10): dictionary (strings encrypted under `st`)
with `/Length` of the written data, and the (encrypted) data. -/
def wireAux (st : Option Crypt.State) (seed : ByteArray) (a : Nat × AuxStream) :
    Except Error (Nat × Dict × List UInt8) :=
  match st with
  | none => .ok (a.1, a.2.fullDict, a.2.data)
  | some s =>
    match Encrypt.encryptStream s a.1 0 a.2.dict a.2.data seed with
    | .ok (d, data) => .ok (a.1, setKey d nameLength (.int data.length), data)
    | .error e => .error e

/-- **Planning** (rules W1–W3, W9–W11): checks the input and reads the pages. `ivSeed`
feeds the AES IVs of an encrypted document (rule W10, `Encrypt` rule E3'). -/
def planUpdate (limits : Limits) (doc : Doc.Doc) (edits : Edits) (sups : List Supersede)
    (aux : List AuxStream := []) (ivSeed : ByteArray := ByteArray.empty) : Except Error Plan :=
  let d := doc.file
  if d.repaired then .error (.unsupported "incremental update of a repaired document")
  else if d.trailer.encrypted && d.crypt.isNone then
    .error (.unsupported "incremental update of an encrypted document without decryption state")
  else if !(edits.map PageEdit.index).Nodup then
    .error (.malformed 0 "a page index occurs twice in the marks")
  else if !aux.all (fun a => markOk limits a.fullDict) then
    .error (.malformed 0 "auxiliary stream dictionary is not canonical or nests too deep")
  else if !(sups.map Prod.fst).Nodup then
    .error (.malformed 0 "an object is superseded twice")
  else if !sups.all (supOk limits doc d.trailer.size) then
    .error (.malformed 0 "a superseded object is not an existing non-page dictionary, or its new dictionary is not canonical")
  else
    match Xref.findStartxref d.bytes with
    | .error e => .error e
    | .ok start =>
      match planEditPages limits doc d.trailer.size edits with
      | .error e => .error e
      | .ok pps =>
        let n0 := d.trailer.size + (pps.map fun pp => pp.annots.length).sum
        let p : Plan := ⟨start, !Xref.matchAt d.bytes start Xref.kwXref, d.trailer.size, pps,
          d.trailer.dict, numberAux n0 aux, sups, d.crypt, [], []⟩
        if limits.maxObjects + 1 < p.newSize then .error (.limitExceeded .objects)
        else
          match p.objects.mapM (wireObject d.crypt ivSeed),
            p.aux.mapM (wireAux d.crypt ivSeed) with
          | .ok w, .ok wa => .ok { p with wire := w, auxWire := wa }
          | .error e, _ => .error e
          | _, .error e => .error e

/-- **Planning for `writeAnnots`** (rules W1–W3, W9): add-only page edits, no supersessions. -/
def plan (limits : Limits) (doc : Doc.Doc) (marks : Marks) (aux : List AuxStream := [])
    (ivSeed : ByteArray := ByteArray.empty) : Except Error Plan :=
  planUpdate limits doc (marks.map PageEdit.ofMarks) [] aux ivSeed

/-! ## Layout -/

/-- Write the objects starting at byte offset `pos`: the entries `(num, offset, gen)` and the
bytes. -/
def emit (pos : Nat) : List (Nat × Nat × PdfObject) → List (Nat × Nat × Nat) × List UInt8
  | [] => ([], [])
  | (n, g, o) :: rest =>
    let b := indirect n g o
    let r := emit (pos + b.length) rest
    ((n, pos, g) :: r.1, b ++ r.2)

/-- Write the auxiliary streams (as written, rule W10) starting at byte offset `pos`
(rule W9). -/
def emitAux (pos : Nat) : List (Nat × Dict × List UInt8) → List (Nat × Nat × Nat) × List UInt8
  | [] => ([], [])
  | (n, d, data) :: rest =>
    let b := streamObj n 0 d data
    let r := emitAux (pos + b.length) rest
    ((n, pos, 0) :: r.1, b ++ r.2)

/-- Sort entries by object number. -/
def sortEntries (es : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  es.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- Rule W7: a new second `/ID` string. -/
def bumpId (d : Dict) (seed : List UInt8) : Dict :=
  match Dict.get? d nameID with
  | some (.array [.string a, .string b]) =>
    setKey d nameID (.array [.string a, .string (Crypt.Md5.md5 ⟨(b ++ seed).toArray⟩).toList])
  | _ => d

/-- Rule W6, classic: the old trailer without `/Size`, `/Prev`, `/XRefStm`. -/
def carriedClassic (d : Dict) : Dict :=
  d.filter fun e => e.1 != Xref.nameSize && e.1 != Xref.namePrev && e.1 != Xref.nameXRefStm

/-- Rule W6, xref stream: `/Root`, `/Info`, `/ID`, `/Encrypt` of the old trailer. -/
def carriedStream (d : Dict) : Dict :=
  d.filter fun e => e.1 == Xref.nameRoot || e.1 == nameInfo || e.1 == nameID ||
    e.1 == Xref.nameEncrypt

/-- The object numbers of the update's section, ascending. -/
def Plan.keys (p : Plan) : List Nat :=
  (p.objects.map (·.1) ++ p.aux.map (·.1) ++ (if p.stream then [p.xrefNum] else [])).mergeSort
    fun a b => decide (a ≤ b)

/-- **The update bytes** for an original of `base` bytes. -/
def update (base : Nat) (p : Plan) : List UInt8 :=
  let objStart := base + 1
  let r0 := emit objStart p.wire
  let ra := emitAux (objStart + r0.2.length) p.auxWire
  let r := (r0.1 ++ ra.1, r0.2 ++ ra.2)
  let xoff := objStart + r.2.length
  if p.stream then
    let es := sortEntries ((p.xrefNum, xoff, 0) :: r.1)
    let w2 := byteWidth xoff
    let data := streamRows w2 es
    let d : Dict :=
      [(Xref.Stream.nameType, .name Xref.Stream.nameXRef), (Xref.nameSize, .int p.newSize),
        (Xref.Stream.nameIndex, .array (streamIndex es)),
        (Xref.Stream.nameW, .array [.int 1, .int w2, .int 2])] ++
      bumpId (carriedStream p.trailer) r.2 ++
      [(Xref.namePrev, .int p.start), (nameLength, .int data.length)]
    lf ++ r.2 ++ streamObj p.xrefNum 0 d data ++ tail xoff
  else
    let es := sortEntries r.1
    let tr : Dict := [(Xref.nameSize, .int p.newSize)] ++
      bumpId (carriedClassic p.trailer) r.2 ++ [(Xref.namePrev, .int p.start)]
    lf ++ r.2 ++ xrefTable es tr ++ tail xoff

/-! ## Self-check (rule W8) -/

/-- The chain check: the result loads as one new section in front of the old chain. -/
def checkChain (limits : Limits) (bytes out : ByteArray) (start : Nat) (keys : List Nat) :
    Bool :=
  match Xref.findStartxref bytes, Xref.Chain.loadChain limits bytes, Xref.findStartxref out with
  | .ok s, .ok revs, .ok off' =>
    decide (s = start) && decide (bytes.size ≤ off') &&
      decide (revs.length + 1 ≤ limits.maxRevisions) &&
      match Xref.Chain.parseSection limits out off' with
      | .ok (sec', tr') =>
        decide (Xref.Chain.hybridStm out off' tr' = none) && decide (tr'.prev? = some start) &&
          decide (sec'.entries.map Prod.fst = keys)
      | .error _ => false
  | _, _, _ => false

/-- Whether a fetch returned exactly the direct object `o`. -/
def bodyIs (r : Except Error IndirectBody) (o : PdfObject) : Bool :=
  match r with
  | .ok b => decide (b = .obj o)
  | .error _ => false

/-- Whether a fetch returned exactly the body `b` (rule W9: an auxiliary stream). -/
def auxIs (r : Except Error IndirectBody) (b : IndirectBody) : Bool :=
  match r with
  | .ok b' => decide (b' = b)
  | .error _ => false

/-- Whether two decryption states agree (rule W10): both absent, or the same file key,
string and stream methods and encryption-dictionary object. -/
def sameCrypt : Option Crypt.State → Option Crypt.State → Bool
  | none, none => true
  | some a, some b =>
    a.fileKey.data == b.fileKey.data && decide (a.handler.strF = b.handler.strF) &&
      decide (a.handler.stmF = b.handler.stmF) && decide (a.encRef = b.encRef)
  | _, _ => false

/-- Whether two security handlers agree in every field (rule W10, task 9.5e2): algorithm,
revision, key length, permissions, the `/O` `/U` `/OE` `/UE` `/Perms` strings,
`/EncryptMetadata`, the stream and string methods and the named crypt filters. -/
def sameHandler (a b : Crypt.Handler) : Bool :=
  decide (a.v = b.v) && decide (a.r = b.r) && decide (a.keyLen = b.keyLen) &&
    decide (a.p = b.p) && decide (a.o.data = b.o.data) && decide (a.u.data = b.u.data) &&
    decide (a.oe.data = b.oe.data) && decide (a.ue.data = b.ue.data) &&
    decide (a.perms.data = b.perms.data) && decide (a.encryptMetadata = b.encryptMetadata) &&
    decide (a.stmF = b.stmF) && decide (a.strF = b.strF) && decide (a.filters = b.filters)

/-- Whether two decryption states are equal in every field (rule W10, task 9.5e2): both
absent, or the same handler (`sameHandler`), file key, encryption-dictionary object and
`/Perms` result. Stronger than `sameCrypt`; the self-check uses both. -/
def sameState : Option Crypt.State → Option Crypt.State → Bool
  | none, none => true
  | some a, some b =>
    sameHandler a.handler b.handler && decide (a.fileKey.data = b.fileKey.data) &&
      decide (a.encRef = b.encRef) && decide (a.permsOk = b.permsOk)
  | _, _ => false

/-- The object check: the result opens strictly with exactly the decryption state `crypt`
of the original (`sameCrypt`, and since task 9.5e2 `sameState`: every field, so the
`/Encrypt` dictionary the result is read with — direct in the update's trailer or an
indirect object — defines the same handler) and returns every written object and every
auxiliary stream (as decrypted bodies, rule W10). -/
def checkObjects (limits : Limits) (out : ByteArray) (objs : List (Nat × Nat × PdfObject))
    (aux : List (Nat × IndirectBody) := []) (crypt : Option Crypt.State := none) : Bool :=
  match Open.openFile limits out with
  | .ok d' => !d'.repaired && objs.all (fun o => bodyIs (d'.getObject limits o.1 o.2.1) o.2.2) &&
      aux.all (fun a => auxIs (d'.getObject limits a.1 0) a.2) && sameCrypt d'.crypt crypt &&
      sameState d'.crypt crypt
  | .error _ => false

/-! ## Entry point -/

/-- The result bytes of a plan: the original followed by the update. -/
def result (bytes : ByteArray) (p : Plan) : ByteArray :=
  bytes ++ ⟨(update bytes.size p).toArray⟩

/-- **General entry point** (Plan.md C7, rule W11). Apply `edits` (per page: references
removed from `/Annots`, annotations added) and `sups` (objects superseded under their own
number and generation) to the opened document `doc` as one incremental update:
`doc.file.bytes ++ update`, self-checked by the strict parser (rule W8). `aux` are extra
stream objects (rule W9). `ivSeed` feeds the AES IVs of an encrypted document (rule W10;
the viewer passes fresh OS randomness, task 12.4). -/
def writeUpdate (limits : Limits) (doc : Doc.Doc) (edits : Edits) (sups : List Supersede)
    (aux : List AuxStream := []) (ivSeed : ByteArray := ByteArray.empty) :
    Except Error ByteArray :=
  match planUpdate limits doc edits sups aux ivSeed with
  | .error e => .error e
  | .ok p =>
    let out := result doc.file.bytes p
    if checkChain limits doc.file.bytes out p.start p.keys &&
      checkObjects limits out p.objects p.auxExpected p.crypt
    then .ok out
    else .error (.malformed doc.file.bytes.size
      "incremental update failed its strict re-parse (internal writer error)")

/-- **Entry point** (Plan.md C7). Append `marks` to the opened document `doc` as an
incremental update: `doc.file.bytes ++ update`, self-checked by the strict parser (rule W8).
`aux` are extra stream objects (rule W9; appearance streams, task 9.5b). It is `writeUpdate`
with add-only page edits and no supersessions (rule W11); `ivSeed` as for `writeUpdate`. -/
def writeAnnots (limits : Limits) (doc : Doc.Doc) (marks : Marks) (aux : List AuxStream := [])
    (ivSeed : ByteArray := ByteArray.empty) : Except Error ByteArray :=
  writeUpdate limits doc (marks.map PageEdit.ofMarks) [] aux ivSeed


end SafePdf.Core.Write.Incremental
