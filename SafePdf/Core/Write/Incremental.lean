import SafePdf.Core.Write.Serialize
import SafePdf.Core.Doc
import SafePdf.Core.Crypt.Md5

/-!
# Incremental-update writer (Plan.md §4 S8/C7, §6 Phase 9 "Persistence"; task 9.5a)

`writeAnnots limits doc marks` appends annotation objects to an opened document as an
**incremental update** (ISO 32000-2 §7.5.6): the result is `doc.file.bytes ++ update`, the
original bytes untouched (S8). `marks` lists, per page index, already-built annotation
dictionaries (task 9.5b builds `/Highlight` and `/Text` ones). The update holds:

* the new annotation objects, numbered from the old trailer's `/Size` upwards (W3);
* each affected page dictionary, rewritten under its own object number and generation with
  `/Annots` extended (W4);
* auxiliary stream objects passed by the caller, e.g. appearance streams (W9, task 9.5b);
* a cross-reference section for exactly these objects and a trailer with `/Prev` = the old
  `startxref` offset, `/Size` grown, the other entries carried over (W5–W7);
* the `startxref` / `%%EOF` tail.

## Rules and decisions

* W1. **Strictly opened, unencrypted input only.** A repaired document (`repaired = true`)
  is refused (`Error.unsupported`): its cross-reference chain is broken, so a `/Prev` to it
  would extend a file that the strict parser does not accept. An encrypted document
  (`/Encrypt` in the trailer or a decryption state) is refused with `Error.unsupported`
  (decision of task 9.5a, recorded in the ledger): encrypting the new objects needs the
  string/stream encryption of every handler (RC4, AES-CBC with a fresh IV per string, which a
  pure core cannot draw) and is left to a follow-up.
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
  then `/Root`, `/Info`, `/ID` of the old trailer (the other keys of an xref-stream
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

/-- Number auxiliary streams consecutively from `n` (rule W9). -/
def numberAux : Nat → List AuxStream → List (Nat × AuxStream)
  | _, [] => []
  | n, a :: as => (n, a) :: numberAux (n + 1) as

/-- Number dictionaries consecutively from `n`. -/
def numberFrom : Nat → List Dict → List (Nat × Dict)
  | _, [] => []
  | n, m :: ms => (n, m) :: numberFrom (n + 1) ms

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

/-- References to the new annotations of a page. -/
def PagePlan.refs (pp : PagePlan) : List PdfObject := pp.annots.map fun a => .ref a.1 0

/-- The rewritten page dictionary (rule W4). -/
def PagePlan.newDict (pp : PagePlan) : Dict :=
  setKey pp.dict nameAnnots (.array (pp.old ++ pp.refs))

/-- The objects written for a page: its annotations, then the page. -/
def PagePlan.objects (pp : PagePlan) : List (Nat × Nat × PdfObject) :=
  pp.annots.map (fun a => (a.1, 0, .dict a.2)) ++ [(pp.num, pp.gen, .dict pp.newDict)]

/-- An annotation dictionary the printer writes back exactly (rule W2). -/
def markOk (limits : Limits) (m : Dict) : Bool :=
  (PdfObject.dict m).isCanonical && Print.refsInRange (.dict m) &&
    decide ((PdfObject.dict m).depth ≤ limits.maxObjectDepth)

/-- Plan one page: look the page up, read its dictionary and annotation list, number the
new annotations from `next`. -/
def planPage (limits : Limits) (doc : Doc.Doc) (next : Nat) (pm : Nat × List Dict) :
    Except Error PagePlan :=
  match doc.pages[pm.1]? with
  | none => .error (.malformed 0 s!"page index {pm.1} out of range")
  | some p =>
    if pm.2.all (markOk limits) then
      match doc.file.getObject limits p.num p.gen with
      | .ok (.obj (.dict pd)) =>
        match annotItems doc.file limits pd with
        | .ok old => .ok ⟨pm.1, p.num, p.gen, pd, old, numberFrom next pm.2⟩
        | .error e => .error e
      | .ok _ => .error (.malformed 0 s!"page {p.num} {p.gen} is not a dictionary")
      | .error e => .error e
    else .error (.malformed 0 "annotation dictionary is not canonical or nests too deep")

/-- Plan all pages; annotation numbers continue from `next`. -/
def planPages (limits : Limits) (doc : Doc.Doc) : Nat → Marks → Except Error (List PagePlan)
  | _, [] => .ok []
  | next, pm :: rest =>
    match planPage limits doc next pm with
    | .error e => .error e
    | .ok pp =>
      match planPages limits doc (next + pm.2.length) rest with
      | .error e => .error e
      | .ok pps => .ok (pp :: pps)

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

/-- The objects of the update, in write order. -/
def Plan.objects (p : Plan) : List (Nat × Nat × PdfObject) := p.pages.flatMap PagePlan.objects

/-- The number of new annotation objects. -/
def Plan.annotCount (p : Plan) : Nat := (p.pages.map fun pp => pp.annots.length).sum

/-- The object number of the update's xref stream (rule W5; unused for a classic section). -/
def Plan.xrefNum (p : Plan) : Nat := p.size + p.annotCount + p.aux.length

/-- The new `/Size`. -/
def Plan.newSize (p : Plan) : Nat := p.xrefNum + (if p.stream then 1 else 0)

/-- **Planning** (rules W1–W3, W9): checks the input and reads the pages. -/
def plan (limits : Limits) (doc : Doc.Doc) (marks : Marks) (aux : List AuxStream := []) :
    Except Error Plan :=
  let d := doc.file
  if d.repaired then .error (.unsupported "incremental update of a repaired document")
  else if d.trailer.encrypted || d.crypt.isSome then
    .error (.unsupported "incremental update of an encrypted document")
  else if !(marks.map Prod.fst).Nodup then
    .error (.malformed 0 "a page index occurs twice in the marks")
  else if !aux.all (fun a => markOk limits a.fullDict) then
    .error (.malformed 0 "auxiliary stream dictionary is not canonical or nests too deep")
  else
    match Xref.findStartxref d.bytes with
    | .error e => .error e
    | .ok start =>
      match planPages limits doc d.trailer.size marks with
      | .error e => .error e
      | .ok pps =>
        let n0 := d.trailer.size + (pps.map fun pp => pp.annots.length).sum
        let p : Plan := ⟨start, !Xref.matchAt d.bytes start Xref.kwXref, d.trailer.size, pps,
          d.trailer.dict, numberAux n0 aux⟩
        if limits.maxObjects + 1 < p.newSize then .error (.limitExceeded .objects)
        else .ok p

/-! ## Layout -/

/-- Write the objects starting at byte offset `pos`: the entries `(num, offset, gen)` and the
bytes. -/
def emit (pos : Nat) : List (Nat × Nat × PdfObject) → List (Nat × Nat × Nat) × List UInt8
  | [] => ([], [])
  | (n, g, o) :: rest =>
    let b := indirect n g o
    let r := emit (pos + b.length) rest
    ((n, pos, g) :: r.1, b ++ r.2)

/-- Write the auxiliary streams starting at byte offset `pos` (rule W9). -/
def emitAux (pos : Nat) : List (Nat × AuxStream) → List (Nat × Nat × Nat) × List UInt8
  | [] => ([], [])
  | (n, a) :: rest =>
    let b := streamObj n 0 a.fullDict a.data
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

/-- Rule W6, xref stream: `/Root`, `/Info`, `/ID` of the old trailer. -/
def carriedStream (d : Dict) : Dict :=
  d.filter fun e => e.1 == Xref.nameRoot || e.1 == nameInfo || e.1 == nameID

/-- The object numbers of the update's section, ascending. -/
def Plan.keys (p : Plan) : List Nat :=
  (p.objects.map (·.1) ++ p.aux.map (·.1) ++ (if p.stream then [p.xrefNum] else [])).mergeSort
    fun a b => decide (a ≤ b)

/-- **The update bytes** for an original of `base` bytes. -/
def update (base : Nat) (p : Plan) : List UInt8 :=
  let objStart := base + 1
  let r0 := emit objStart p.objects
  let ra := emitAux (objStart + r0.2.length) p.aux
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

/-- Whether a fetch returned exactly the auxiliary stream `a` (rule W9). -/
def auxIs (r : Except Error IndirectBody) (a : AuxStream) : Bool :=
  match r with
  | .ok b => decide (b = a.body)
  | .error _ => false

/-- The object check: the result opens strictly and returns every written object and every
auxiliary stream. -/
def checkObjects (limits : Limits) (out : ByteArray) (objs : List (Nat × Nat × PdfObject))
    (aux : List (Nat × AuxStream) := []) : Bool :=
  match Open.openFile limits out with
  | .ok d' => !d'.repaired && objs.all (fun o => bodyIs (d'.getObject limits o.1 o.2.1) o.2.2) &&
      aux.all fun a => auxIs (d'.getObject limits a.1 0) a.2
  | .error _ => false

/-! ## Entry point -/

/-- The result bytes of a plan: the original followed by the update. -/
def result (bytes : ByteArray) (p : Plan) : ByteArray :=
  bytes ++ ⟨(update bytes.size p).toArray⟩

/-- **Entry point** (Plan.md C7). Append `marks` to the opened document `doc` as an
incremental update: `doc.file.bytes ++ update`, self-checked by the strict parser (rule W8).
`aux` are extra stream objects (rule W9; appearance streams, task 9.5b). -/
def writeAnnots (limits : Limits) (doc : Doc.Doc) (marks : Marks) (aux : List AuxStream := []) :
    Except Error ByteArray :=
  match plan limits doc marks aux with
  | .error e => .error e
  | .ok p =>
    let out := result doc.file.bytes p
    if checkChain limits doc.file.bytes out p.start p.keys &&
      checkObjects limits out p.objects p.aux
    then .ok out
    else .error (.malformed doc.file.bytes.size
      "incremental update failed its strict re-parse (internal writer error)")

end SafePdf.Core.Write.Incremental
