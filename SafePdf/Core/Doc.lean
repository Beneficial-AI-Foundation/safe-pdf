import SafePdf.Core.Open

/-!
# Document structure: catalog and page tree (task 4.1)

Plan.md §6 Phase 4 ("Catalog, page tree with inheritance (`Resources`, `MediaBox`, `CropBox`,
`Rotate`); acyclicity proof; `getPage : Document → Fin n → Page` total"), §5.2 ("Page tree:
depth bounded by node count; visited-set on node ids; `/Kids` cycles rejected"), §4 S2
(totality). ISO 32000-2 §7.7.2 (catalog), §7.7.3 (page tree, inheritable attributes),
§14.11.2 (page boxes).

All failure happens at open time (`openDoc`): the result is a `Doc` whose pages are an array,
so `Doc.getPage` is total and trivial.

## The walk

* W1. From the trailer `/Root` (the catalog, a dictionary: `Open.openFile_root`) to its
  `/Pages`, which must be an indirect reference (§7.7.2); otherwise `malformed`.
* W2. **Worklist, preorder.** The walk keeps a stack of entries (object number, generation,
  depth, inherited attributes). Popping an entry whose object number is already **visited**
  is `Error.cycle` (offset: the object's xref offset, else 0). This rejects a `/Kids` cycle
  (an ancestor is visited before its kids are pushed) and also a node reached twice through
  two parents (a DAG): the page list must consist of distinct objects.
* W3. A popped reference that resolves to `null` (free, absent, generation mismatch: D-001) is
  **skipped** and counted in `Doc.skippedKids` (qpdf also ignores dangling kids). It is not
  marked visited.
* W4. **Node kind**, lenient by structure: `/Type /Pages` ⇒ intermediate; `/Type /Page` ⇒
  leaf; no `/Type` name ⇒ intermediate iff `/Kids` is present, else leaf; any other `/Type`
  name (e.g. `/Catalog`) ⇒ `malformed`. A node that is not a dictionary (a stream, a number)
  ⇒ `malformed`.
* W5. **`/Kids`** is resolved one level (it may be a reference to an array); a missing
  `/Kids` on an intermediate node is an empty array; every element must be an indirect
  reference (§7.7.3.2), else `malformed`. Kids are pushed in order before the rest of the
  stack, so pages come out in document order.
* W6. **Bounds.** Depth above `limits.maxObjectDepth` ⇒ `limitExceeded .objectDepth`. The
  number of visited nodes is bounded by fuel `objectCount`; exhausting it with live work left
  ⇒ `limitExceeded .objects` (in a consistent file every live node has its own xref entry, so
  this should not happen; that fact is not proven here). Every node visit costs at most 6
  `getObject` calls (node, `/Kids`, four attributes): the work is `O(objectCount)` fetches.
* W7. **`/Count`** is advisory: the root's `/Count` is kept as `Doc.declaredCount` and a
  mismatch is reported by `Doc.countMismatch`, never as an error.

## Attributes and inheritance (§7.7.3.4)

* A1. `/Resources`, `/MediaBox`, `/CropBox`, `/Rotate` are each resolved **one level** (a
  reference to the value is followed once; a reference that resolves to a stream counts as
  absent). `/Resources` is kept as `Option Dict`; references *inside* it stay unresolved.
* A2. A value of the wrong shape (a `/MediaBox` that is not an array of four numbers, a
  non-dictionary `/Resources`, a non-number `/Rotate`) counts as **absent**, so inheritance
  continues to the ancestor's value.
* A3. **Inheritance**: each attribute is the node's own if present, else the nearest
  ancestor's (`Attrs.merge`, `foldl_merge_mediaBox`).
* A4. **Missing `/MediaBox`** everywhere (it is required): US Letter `[0 0 612 792]`, the
  common practice of viewers; `Page.mediaBoxDefaulted` records it.
* A5. **`/Rotate`** is taken modulo 360 (so `-90` is `270`); a value that is not a multiple of
  90 (or a non-integral real) is treated as `0`, as pdf.js does.
* A6. **Rectangles** are normalized (§7.9.5: any two opposite corners): `llx ≤ urx`,
  `lly ≤ ury`, exact `Decimal`s in canonical form. **`/CropBox`** defaults to the MediaBox and
  is intersected with it (§14.11.2); if the intersection is empty the MediaBox is used.
* A7. `/Contents` is kept unresolved (the page's own value only: it is not inheritable).

Encrypted documents: page-tree keys are names, numbers, references and arrays, which are not
encrypted, so the walk works before string/stream decryption exists (task 4.3b).

## Decoded-bytes accounting (task 3.10, Plan.md §4 S3)

Streams decoded on demand go through `Filter.decodeStreamB`, which charges a `Filter.Budget`
(start: `Filter.Budget.init limits` = `limits.maxDecodedTotalBytes`; rules B1–B5 of
`Core.Filter`). The caller threads the budget through every access of the document (page
contents, and later fonts, images, forms), so the decoded bytes of all of them together stay
within `maxDecodedTotalBytes` or end in `Error.limitExceeded .decodedTotalBytes`.

* D1. `Doc.decodeStreamOf doc limits budget n g` fetches object `n g` and decodes it under
  the budget; a non-stream is `malformed`. A failed fetch charges nothing.
* D2. `/Filter` and `/DecodeParms` are resolved one level first (`resolveStreamDict`: the
  value, or each element of an array; a reference to a stream is `malformed`), since
  `Filter.decodeStream` rejects references.
* D3. `Doc.decodeContentsB doc limits budget page`: the page's `/Contents` (a stream, an array
  of streams, or a reference to such an array; ISO 32000-2 §7.7.3.3) decoded in order and
  returned as separate parts (not concatenated: no extra copy). A reference to a missing
  object is skipped (as W3); a content stream ending in an image codec is `malformed`.

**Not charged yet** (each is bounded per stream, but not against the document budget;
threading the budget through `Open.getObject` and `Xref.Chain.loadChain` changes many
signatures and theorems and is left to a follow-up task):

* Cross-reference streams at open time (`loadChain`): at most `limits.maxRevisions` sections
  are parsed (an `/XRefStm` counts as one), each decoded once, each allocating at most
  `maxFilters · maxDecodedStreamBytes` (`Filter.produced_le_maxFilters`). Total
  `≤ maxRevisions · maxFilters · maxDecodedStreamBytes`.
* Object streams inside `Open.getObject` (the page-tree walk, `resolve`, the fetches of
  D1–D3 themselves): one `getObject` performs at most one top-level object-stream decode
  (`Open.getObject_work`), plus at most `objectCount` container parses while resolving an
  indirect `/Length` (`Open.getObject_length_calls_le`), each of which may decode one object
  stream. So each `getObject` allocates at most
  `(objectCount + 1) · maxFilters · maxDecodedStreamBytes` in object-stream decoding; the
  page-tree walk performs `O(objectCount)` `getObject` calls (rule W6; stated, not proven).
  Decoded object streams are not cached, so this is the bound per call, not per document.

## Theorems

* Totality: by construction (structural recursion on fuel and on the stack).
* `walk_visits_le`: at most `objectCount` nodes are visited; `ofOpen_pages_le`: so at most
  `objectCount` pages.
* `walk_no_repeat`: the visited list and the page object numbers are duplicate-free, and every
  page was visited; `ofOpen_pages_nodup`.
* `loop_cycle`: popping an already visited node is `Error.cycle`; `visitNode_visited`: a node
  is visited before its kids are pushed (so a `/Kids` entry pointing to an ancestor or to the
  node itself is popped while visited).
* `foldl_merge_mediaBox`, `foldl_merge_rotate`: the inherited value is the nearest one along
  the path; `mkPage_mediaBox`.
* `cropBox_sub_media`: every page's CropBox lies inside its MediaBox.
* Budget (task 3.10): `Doc.decodeStreamOf_le`, `Doc.decodeRefsB_le`, `Doc.decodeContentsB_le`
  (the budget never grows); `Doc.decodeStreamOf_charge` (a decoded stream's size plus the
  budget left is at most the budget before); `Doc.decodeStreamOf_size_le` (per-stream bound);
  `Doc.decodeRefsB_total`, `Doc.decodeContentsB_total` (the decoded parts plus the budget
  left are at most the budget before).
-/

set_option autoImplicit false

namespace SafePdf.Core.Doc

open SafePdf
open SafePdf.Core.Open (OpenDoc)

/-! ## Exact coordinates -/

/-- Order on exact decimals: `a ≤ b` by cross-multiplying the scales. -/
def numLe (a b : Decimal) : Bool :=
  decide (a.mantissa * (10 : Int) ^ b.scale ≤ b.mantissa * (10 : Int) ^ a.scale)

/-- `numLe` is reflexive. -/
theorem numLe_refl (a : Decimal) : numLe a a = true := by
  simp [numLe]

/-- `numLe` is total. -/
theorem numLe_of_not {a b : Decimal} (h : numLe a b = false) : numLe b a = true := by
  simp only [numLe, decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢
  exact Int.le_of_lt (Int.not_le.mp h)

/-- The larger of two decimals (by `numLe`). -/
def dmax (x y : Decimal) : Decimal := if numLe x y then y else x

/-- The smaller of two decimals (by `numLe`). -/
def dmin (x y : Decimal) : Decimal := if numLe x y then x else y

/-- `x ≤ max x y`. -/
theorem le_dmax_left (x y : Decimal) : numLe x (dmax x y) = true := by
  unfold dmax; split
  · assumption
  · exact numLe_refl x

/-- `y ≤ max x y`. -/
theorem le_dmax_right (x y : Decimal) : numLe y (dmax x y) = true := by
  unfold dmax; split
  · exact numLe_refl y
  · next h => exact numLe_of_not (Bool.eq_false_iff.mpr h)

/-- `min x y ≤ x`. -/
theorem dmin_le_left (x y : Decimal) : numLe (dmin x y) x = true := by
  unfold dmin; split
  · exact numLe_refl x
  · next h => exact numLe_of_not (Bool.eq_false_iff.mpr h)

/-- `min x y ≤ y`. -/
theorem dmin_le_right (x y : Decimal) : numLe (dmin x y) y = true := by
  unfold dmin; split
  · assumption
  · exact numLe_refl y

/-- `min x y ≤ max x y`. -/
theorem dmin_le_dmax (x y : Decimal) : numLe (dmin x y) (dmax x y) = true := by
  unfold dmin dmax; split
  · assumption
  · next h => exact numLe_of_not (Bool.eq_false_iff.mpr h)

/-! ## Rectangles -/

/-- A normalized rectangle (ISO 32000-2 §7.9.5): lower-left and upper-right corners, exact. -/
structure Rect where
  /-- Lower-left x. -/
  llx : Decimal
  /-- Lower-left y. -/
  lly : Decimal
  /-- Upper-right x. -/
  urx : Decimal
  /-- Upper-right y. -/
  ury : Decimal
  /-- `llx ≤ urx`. -/
  hx : numLe llx urx = true
  /-- `lly ≤ ury`. -/
  hy : numLe lly ury = true

/-- The rectangle with two opposite corners `(a, b)` and `(c, d)`, in any order. -/
def Rect.ofCorners (a b c d : Decimal) : Rect :=
  ⟨dmin a c, dmin b d, dmax a c, dmax b d, dmin_le_dmax a c, dmin_le_dmax b d⟩

/-- `r ⊆ s`: every edge of `r` lies inside `s`. -/
def Rect.sub (r s : Rect) : Bool :=
  numLe s.llx r.llx && numLe s.lly r.lly && numLe r.urx s.urx && numLe r.ury s.ury

/-- `⊆` is reflexive. -/
theorem Rect.sub_refl (r : Rect) : r.sub r = true := by
  simp [Rect.sub, numLe_refl]

/-- The intersection of `c` and `m`, or `m` if it is empty (rule A6). -/
def clip (c m : Rect) : Rect :=
  if h : numLe (dmax c.llx m.llx) (dmin c.urx m.urx) = true ∧
      numLe (dmax c.lly m.lly) (dmin c.ury m.ury) = true then
    ⟨dmax c.llx m.llx, dmax c.lly m.lly, dmin c.urx m.urx, dmin c.ury m.ury, h.1, h.2⟩
  else m

/-- The clipped rectangle lies inside `m`. -/
theorem clip_sub (c m : Rect) : (clip c m).sub m = true := by
  unfold clip; split
  · simp [Rect.sub, le_dmax_right, dmin_le_right]
  · exact Rect.sub_refl m

/-- The page's CropBox: the declared one clipped to the MediaBox, else the MediaBox (A6). -/
def cropOf : Option Rect → Rect → Rect
  | none, m => m
  | some c, m => clip c m

/-- The CropBox lies inside the MediaBox. -/
theorem cropOf_sub (c : Option Rect) (m : Rect) : (cropOf c m).sub m = true := by
  cases c
  · exact Rect.sub_refl m
  · exact clip_sub _ m

/-- US Letter, the default MediaBox (rule A4). -/
def letter : Rect := Rect.ofCorners ⟨0, 0⟩ ⟨0, 0⟩ ⟨612, 0⟩ ⟨792, 0⟩

/-! ## Rotation -/

/-- A page rotation, clockwise in degrees (§7.7.3.3 `/Rotate`). -/
inductive Rotation where
  /-- 0°. -/
  | r0
  /-- 90°. -/
  | r90
  /-- 180°. -/
  | r180
  /-- 270°. -/
  | r270
  deriving DecidableEq, Repr, Inhabited

/-- The rotation of an integer `/Rotate` (rule A5). -/
def rotationOfInt (i : Int) : Rotation :=
  let r := i % 360
  if r = 0 then .r0 else if r = 90 then .r90 else if r = 180 then .r180
  else if r = 270 then .r270 else .r0

/-- The rotation of a resolved `/Rotate` value; `none` if it is not a number (rule A2). -/
def rotateOf : PdfObject → Option Rotation
  | .int i => some (rotationOfInt i)
  | .real r =>
    if r.normalize.scale = 0 then some (rotationOfInt r.normalize.mantissa) else some .r0
  | _ => none

/-! ## Attributes -/

/-- A number as an exact canonical decimal. -/
def numOf : PdfObject → Option Decimal
  | .int i => some ⟨i, 0⟩
  | .real r => some r.normalize
  | _ => none

/-- A rectangle from a resolved value: an array of exactly four numbers (rule A2). -/
def rectOf : PdfObject → Option Rect
  | .array [a, b, c, d] =>
    match numOf a, numOf b, numOf c, numOf d with
    | some a, some b, some c, some d => some (Rect.ofCorners a b c d)
    | _, _, _, _ => none
  | _ => none

/-- The inheritable page attributes of one node, or as inherited (§7.7.3.4). -/
structure Attrs where
  /-- `/Resources`. -/
  resources : Option Dict := none
  /-- `/MediaBox`. -/
  mediaBox : Option Rect := none
  /-- `/CropBox` (unclipped). -/
  cropBox : Option Rect := none
  /-- `/Rotate`. -/
  rotate : Option Rotation := none

/-- Inheritance step (rule A3): the node's own value if present, else the inherited one. -/
def Attrs.merge (inh own : Attrs) : Attrs where
  resources := own.resources.or inh.resources
  mediaBox := own.mediaBox.or inh.mediaBox
  cropBox := own.cropBox.or inh.cropBox
  rotate := own.rotate.or inh.rotate

/-- The xref offset of an object, for error messages (0 if not a plain in-use object). -/
def offsetOf (d : OpenDoc) (n : Nat) : Nat :=
  match d.lookup n with
  | some (.inUse off _) => off
  | _ => 0

/-- Resolve one level (rule A1): a reference is fetched once; a stream counts as `null`. -/
def resolve (d : OpenDoc) (limits : Limits) : PdfObject → Except Error PdfObject
  | .ref n g =>
    match d.getObject limits n g with
    | .error e => .error e
    | .ok (.obj o) => .ok o
    | .ok (.stream _) => .ok .null
  | o => .ok o

/-- The value of key `k`, resolved one level; `null` if absent. -/
def key (d : OpenDoc) (limits : Limits) (nd : Dict) (k : String) : Except Error PdfObject :=
  match Dict.get? nd (Name.ofString k) with
  | none => .ok .null
  | some o => resolve d limits o

/-- The node's own inheritable attributes (rules A1, A2). -/
def attrsOf (d : OpenDoc) (limits : Limits) (nd : Dict) : Except Error Attrs := do
  let r ← key d limits nd "Resources"
  let m ← key d limits nd "MediaBox"
  let c ← key d limits nd "CropBox"
  let t ← key d limits nd "Rotate"
  pure { resources := (match r with | .dict x => some x | _ => none),
         mediaBox := rectOf m, cropBox := rectOf c, rotate := rotateOf t }

/-! ## Pages -/

/-- A page: its object, its effective (inherited, defaulted) attributes. -/
structure Page where
  /-- Object number of the page dictionary. -/
  num : Nat
  /-- Generation of the page dictionary. -/
  gen : Nat
  /-- Effective MediaBox (rule A4 if none was found). -/
  mediaBox : Rect
  /-- Whether `mediaBox` is the Letter default (no `/MediaBox` on the page or an ancestor). -/
  mediaBoxDefaulted : Bool
  /-- Effective CropBox, inside the MediaBox (rule A6). -/
  cropBox : Rect
  /-- Effective rotation (rule A5). -/
  rotate : Rotation
  /-- Effective `/Resources`, resolved one level (rule A1). -/
  resources : Option Dict
  /-- The page's own `/Contents`, unresolved (rule A7). -/
  contents : Option PdfObject
  /-- The CropBox lies inside the MediaBox. -/
  cropBox_sub : cropBox.sub mediaBox = true

/-- The page of a leaf with merged attributes `a`. -/
def mkPage (num gen : Nat) (a : Attrs) (contents : Option PdfObject) : Page where
  num := num
  gen := gen
  mediaBox := a.mediaBox.getD letter
  mediaBoxDefaulted := a.mediaBox.isNone
  cropBox := cropOf a.cropBox (a.mediaBox.getD letter)
  rotate := a.rotate.getD .r0
  resources := a.resources
  contents := contents
  cropBox_sub := cropOf_sub _ _

/-! ## The walk -/

/-- A stack entry: a node to visit, with what it inherits. -/
structure Entry where
  /-- Object number. -/
  num : Nat
  /-- Generation. -/
  gen : Nat
  /-- Depth below the root `/Pages` node. -/
  depth : Nat
  /-- Attributes inherited from the ancestors. -/
  inh : Attrs

/-- The walk state. -/
structure WalkState where
  /-- Nodes still to visit, next first. -/
  stack : List Entry
  /-- Object numbers of the visited nodes, newest first. -/
  visited : List Nat
  /-- Pages found, newest first. -/
  pages : List Page
  /-- References skipped because they resolve to `null` (rule W3). -/
  skipped : Nat

/-- Node kinds (rule W4). -/
inductive Kind where
  /-- An intermediate `/Pages` node. -/
  | inner
  /-- A `/Page` leaf. -/
  | leaf
  /-- Another `/Type`. -/
  | bad
  deriving DecidableEq, Repr

/-- The kind of a node dictionary (rule W4). -/
def kindOf (nd : Dict) : Kind :=
  match Dict.get? nd (Name.ofString "Type") with
  | some (.name n) =>
    if n = Name.ofString "Pages" then .inner
    else if n = Name.ofString "Page" then .leaf
    else .bad
  | _ => if (Dict.get? nd (Name.ofString "Kids")).isSome then .inner else .leaf

/-- The references of a `/Kids` array; `none` if an element is not a reference (W5). -/
def refsOf : List PdfObject → Option (List (Nat × Nat))
  | [] => some []
  | .ref n g :: rest => (refsOf rest).map ((n, g) :: ·)
  | _ :: _ => none

/-- The kids of a resolved `/Kids` value (rule W5). -/
def kidsOf : PdfObject → Option (List (Nat × Nat))
  | .null => some []
  | .array xs => refsOf xs
  | _ => none

/-- Pop the next live entry (rules W2, W3): a visited one is a cycle, a `null` one is
skipped. Returns the entry, its body, the rest of the stack, and the skip count. -/
def popLive (d : OpenDoc) (limits : Limits) (visited : List Nat) :
    List Entry → Nat → Except Error (Option (Entry × IndirectBody × List Entry) × Nat)
  | [], k => .ok (none, k)
  | e :: rest, k =>
    if e.num ∈ visited then .error (.cycle (offsetOf d e.num) "page tree /Kids cycle")
    else
      match d.getObject limits e.num e.gen with
      | .error x => .error x
      | .ok (.obj .null) => popLive d limits visited rest (k + 1)
      | .ok b => .ok (some (e, b, rest), k)

/-- Visit a live node (rules W4–W6): mark it visited, then push its kids or record its
page. `st.stack` is already the rest of the stack. -/
def visitNode (d : OpenDoc) (limits : Limits) (e : Entry) (b : IndirectBody)
    (st : WalkState) : Except Error WalkState :=
  if limits.maxObjectDepth < e.depth then .error (.limitExceeded .objectDepth)
  else
    match b with
    | .obj (.dict nd) =>
      match attrsOf d limits nd with
      | .error x => .error x
      | .ok own =>
        match kindOf nd with
        | .inner =>
          match key d limits nd "Kids" with
          | .error x => .error x
          | .ok ko =>
            match kidsOf ko with
            | none => .error (.malformed (offsetOf d e.num)
                s!"page tree node {e.num}: /Kids is not an array of references")
            | some ks =>
              .ok { st with
                    stack := ks.map (fun r => ⟨r.1, r.2, e.depth + 1, e.inh.merge own⟩) ++
                      st.stack
                    visited := e.num :: st.visited }
        | .leaf =>
          .ok { st with
                visited := e.num :: st.visited
                pages := mkPage e.num e.gen (e.inh.merge own)
                  (Dict.get? nd (Name.ofString "Contents")) :: st.pages }
        | .bad => .error (.malformed (offsetOf d e.num)
            s!"page tree node {e.num} has an unexpected /Type")
    | _ => .error (.malformed (offsetOf d e.num)
        s!"page tree node {e.num} is not a dictionary")

/-- The walk loop: at most `fuel` node visits (rule W6). -/
def loop (d : OpenDoc) (limits : Limits) : Nat → WalkState → Except Error WalkState
  | 0, st =>
    match popLive d limits st.visited st.stack st.skipped with
    | .error x => .error x
    | .ok (none, k) => .ok { st with stack := [], skipped := k }
    | .ok (some _, _) => .error (.limitExceeded .objects)
  | f + 1, st =>
    match popLive d limits st.visited st.stack st.skipped with
    | .error x => .error x
    | .ok (none, k) => .ok { st with stack := [], skipped := k }
    | .ok (some (e, b, rest), k) =>
      match visitNode d limits e b { st with stack := rest, skipped := k } with
      | .error x => .error x
      | .ok st' => loop d limits f st'

/-- The initial state: the root `/Pages` node `n g`, nothing inherited. -/
def initState (n g : Nat) : WalkState := ⟨[⟨n, g, 0, {}⟩], [], [], 0⟩

/-- Walk the page tree rooted at `n g` with fuel `objectCount`. -/
def walk (d : OpenDoc) (limits : Limits) (n g : Nat) : Except Error WalkState :=
  loop d limits d.objectCount (initState n g)

/-! ## The document -/

/-- An opened document with its page tree flattened. -/
structure Doc where
  /-- The opened file. -/
  file : OpenDoc
  /-- The catalog dictionary (§7.7.2). -/
  catalog : Dict
  /-- The root `/Pages` reference. -/
  pagesRef : Nat × Nat
  /-- The pages, in document order. -/
  pages : Array Page
  /-- The root's `/Count`, if it is an integer (advisory, rule W7). -/
  declaredCount : Option Int
  /-- Dangling `/Kids` references skipped (rule W3). -/
  skippedKids : Nat

/-- Number of pages. -/
def Doc.pageCount (doc : Doc) : Nat := doc.pages.size

/-- **Total page access** (Plan.md §6 Phase 4). -/
def Doc.getPage (doc : Doc) (i : Fin doc.pages.size) : Page := doc.pages[i]

/-- Whether the root's `/Count` disagrees with the walked page count (rule W7). -/
def Doc.countMismatch (doc : Doc) : Bool :=
  match doc.declaredCount with
  | some c => c != (doc.pageCount : Int)
  | none => false

/-- The root's `/Count` (advisory). -/
def declaredCountOf (d : OpenDoc) (limits : Limits) (n g : Nat) : Option Int :=
  match d.getObject limits n g with
  | .ok (.obj (.dict pd)) =>
    match Dict.get? pd (Name.ofString "Count") with
    | some (.int c) => some c
    | _ => none
  | _ => none

/-- Build the document of an opened file (rules W1–W7). -/
def ofOpen (limits : Limits) (d : OpenDoc) : Except Error Doc :=
  match d.trailer.root? with
  | none => .error (.malformed 0 "trailer has no /Root")
  | some (rn, rg) =>
    match d.getObject limits rn rg with
    | .error e => .error e
    | .ok (.obj (.dict cat)) =>
      match Dict.get? cat (Name.ofString "Pages") with
      | some (.ref pn pg) =>
        match walk d limits pn pg with
        | .error e => .error e
        | .ok st =>
          .ok { file := d, catalog := cat, pagesRef := (pn, pg),
                pages := st.pages.reverse.toArray,
                declaredCount := declaredCountOf d limits pn pg, skippedKids := st.skipped }
      | _ => .error (.malformed (offsetOf d rn) "catalog /Pages is not an indirect reference")
    | .ok _ => .error (.malformed (offsetOf d rn) "/Root is not a dictionary")

/-- **Entry point.** Open a document and flatten its page tree. -/
def openDoc (limits : Limits) (bytes : ByteArray) : Except Error Doc :=
  match Open.openFile limits bytes with
  | .error e => .error e
  | .ok d => ofOpen limits d

/-! ## Decoded streams under the document budget (task 3.10) -/

open SafePdf.Core.Filter (Budget Decoded okSize)

/-- Resolve one `/Filter` or `/DecodeParms` reference (rule D2): a direct object is kept; a
reference to a stream is `malformed`. -/
def resolveParamRef (d : OpenDoc) (limits : Limits) : PdfObject → Except Error PdfObject
  | .ref n g =>
    match d.getObject limits n g with
    | .error e => .error e
    | .ok (.obj o) => .ok o
    | .ok (.stream _) =>
      .error (.malformed (offsetOf d n) "/Filter or /DecodeParms refers to a stream")
  | o => .ok o

/-- Resolve a `/Filter` or `/DecodeParms` value one level (rule D2): the value itself, or
each element of an array. -/
def resolveParam (d : OpenDoc) (limits : Limits) : PdfObject → Except Error PdfObject
  | .array items =>
    match items.mapM (resolveParamRef d limits) with
    | .error e => .error e
    | .ok xs => .ok (.array xs)
  | o => resolveParamRef d limits o

/-- A stream dictionary with `/Filter` and `/DecodeParms` resolved one level (rule D2). -/
def resolveStreamDict (d : OpenDoc) (limits : Limits) (sd : Dict) : Except Error Dict :=
  sd.mapM fun (kv : Name × PdfObject) =>
    if kv.1 = Name.ofString "Filter" ∨ kv.1 = Name.ofString "DecodeParms" then
      match resolveParam d limits kv.2 with
      | .error e => .error e
      | .ok v => .ok (kv.1, v)
    else .ok kv

/-- Decode a fetched body under the budget (rule D1): a stream is decoded by
`Filter.decodeStreamB` after rule D2; anything else is `malformed` (offset `off`). -/
def decodeBodyB (d : OpenDoc) (limits : Limits) (budget : Budget) (off : Nat) :
    IndirectBody → (Except Error Decoded) × Budget
  | .stream s =>
    match resolveStreamDict d limits s.dict with
    | .error e => (.error e, budget)
    | .ok sd => Filter.decodeStreamB limits budget sd s.data
  | .obj _ => (.error (.malformed off "not a stream"), budget)

/-- **Budgeted stream access** (task 3.10). Fetch object `n g` and decode it as a stream,
charging `budget` (rule D1). -/
def Doc.decodeStreamOf (doc : Doc) (limits : Limits) (budget : Budget) (n g : Nat) :
    (Except Error Decoded) × Budget :=
  match doc.file.getObject limits n g with
  | .error e => (.error e, budget)
  | .ok b => decodeBodyB doc.file limits budget (offsetOf doc.file n) b

/-- The bytes of a content stream: an image-codec result is `malformed` (rule D3). -/
def contentData (off : Nat) : Except Error Decoded → Except Error ByteArray
  | .error e => .error e
  | .ok (.data b) => .ok b
  | .ok (.image _ _ _) => .error (.malformed off "content stream with an image filter")

/-- Decode a `/Contents` array (rule D3), threading the budget. A reference to a missing
object (`null`) is skipped; a non-reference element is `malformed`. -/
def Doc.decodeRefsB (doc : Doc) (limits : Limits) :
    Budget → List PdfObject → (Except Error (List ByteArray)) × Budget
  | b, [] => (.ok [], b)
  | b, .ref n g :: os =>
    match doc.file.getObject limits n g with
    | .error e => (.error e, b)
    | .ok (.obj .null) => doc.decodeRefsB limits b os
    | .ok body =>
      match contentData (offsetOf doc.file n)
          (decodeBodyB doc.file limits b (offsetOf doc.file n) body).1 with
      | .error e => (.error e, (decodeBodyB doc.file limits b (offsetOf doc.file n) body).2)
      | .ok bs =>
        match doc.decodeRefsB limits
            (decodeBodyB doc.file limits b (offsetOf doc.file n) body).2 os with
        | (.error e, q) => (.error e, q)
        | (.ok bss, q) => (.ok (bs :: bss), q)
  | b, _ :: _ =>
    (.error (.malformed 0 "/Contents array element is not an indirect reference"), b)

/-- **Budgeted page contents** (rule D3): the decoded content streams of a page, in order,
not concatenated (the content lexer of phase 5 reads across them). -/
def Doc.decodeContentsB (doc : Doc) (limits : Limits) (budget : Budget) (page : Page) :
    (Except Error (List ByteArray)) × Budget :=
  match page.contents with
  | none => (.ok [], budget)
  | some (.array items) => doc.decodeRefsB limits budget items
  | some (.ref n g) =>
    match doc.file.getObject limits n g with
    | .error e => (.error e, budget)
    | .ok (.obj .null) => (.ok [], budget)
    | .ok (.obj (.array items)) => doc.decodeRefsB limits budget items
    | .ok body =>
      match contentData (offsetOf doc.file n)
          (decodeBodyB doc.file limits budget (offsetOf doc.file n) body).1 with
      | .error e => (.error e, (decodeBodyB doc.file limits budget (offsetOf doc.file n) body).2)
      | .ok bs => (.ok [bs], (decodeBodyB doc.file limits budget (offsetOf doc.file n) body).2)
  | some _ =>
    (.error (.malformed (offsetOf doc.file page.num) "/Contents is not a stream or an array"),
      budget)

/-- The budget never grows in `decodeBodyB`. -/
theorem decodeBodyB_le (d : OpenDoc) (limits : Limits) (budget : Budget) (off : Nat)
    (body : IndirectBody) :
    (decodeBodyB d limits budget off body).2.remaining ≤ budget.remaining := by
  unfold decodeBodyB
  split
  · split
    · exact Nat.le_refl _
    · exact Filter.decodeStreamB_le _ _ _ _ _
  · exact Nat.le_refl _

/-- **Charge law** of `decodeBodyB`. -/
theorem decodeBodyB_charge {d : OpenDoc} {limits : Limits} {budget : Budget} {off : Nat}
    {body : IndirectBody} {r : Decoded} (h : (decodeBodyB d limits budget off body).1 = .ok r) :
    r.bytes.size + (decodeBodyB d limits budget off body).2.remaining ≤ budget.remaining := by
  unfold decodeBodyB at h ⊢
  split at h
  · rename_i s
    cases hs : resolveStreamDict d limits s.dict with
    | error e => simp [hs] at h
    | ok sd =>
      simp only [hs] at h ⊢
      exact Filter.decodeStreamB_charge h
  · cases h

/-- **Budget monotone**: `Doc.decodeStreamOf` never increases the budget. -/
theorem Doc.decodeStreamOf_le (doc : Doc) (limits : Limits) (budget : Budget) (n g : Nat) :
    (doc.decodeStreamOf limits budget n g).2.remaining ≤ budget.remaining := by
  unfold Doc.decodeStreamOf
  split
  · exact Nat.le_refl _
  · exact decodeBodyB_le _ _ _ _ _

/-- **Charge law** (S3): a stream decoded by `Doc.decodeStreamOf` was charged its size. -/
theorem Doc.decodeStreamOf_charge {doc : Doc} {limits : Limits} {budget : Budget} {n g : Nat}
    {r : Decoded} (h : (doc.decodeStreamOf limits budget n g).1 = .ok r) :
    r.bytes.size + (doc.decodeStreamOf limits budget n g).2.remaining ≤ budget.remaining := by
  unfold Doc.decodeStreamOf at h ⊢
  split at h
  · cases h
  · rename_i b hb
    exact decodeBodyB_charge h

/-- **Per-stream bound** for `Doc.decodeStreamOf`. -/
theorem Doc.decodeStreamOf_size_le {doc : Doc} {limits : Limits} {budget : Budget}
    {n g : Nat} {r : Decoded} (h : (doc.decodeStreamOf limits budget n g).1 = .ok r) :
    r.bytes.size ≤ limits.maxDecodedStreamBytes := by
  unfold Doc.decodeStreamOf at h
  split at h
  · cases h
  · unfold decodeBodyB at h
    split at h
    · split at h
      · cases h
      · exact Filter.decodeStreamB_size_le h
    · cases h

/-- `contentData` keeps the bytes of a data result. -/
theorem contentData_ok {off : Nat} {r : Except Error Decoded} {bs : ByteArray}
    (h : contentData off r = .ok bs) : ∃ d, r = .ok d ∧ d.bytes = bs := by
  unfold contentData at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; subst h; exact ⟨_, rfl, rfl⟩
  · cases h

/-- The budget never grows in `Doc.decodeRefsB`. -/
theorem Doc.decodeRefsB_le (doc : Doc) (limits : Limits) :
    (b : Budget) → (items : List PdfObject) →
    (doc.decodeRefsB limits b items).2.remaining ≤ b.remaining
  | b, [] => by simp [Doc.decodeRefsB]
  | b, .ref n g :: os => by
    have hbody := fun body => decodeBodyB_le doc.file limits b (offsetOf doc.file n) body
    unfold Doc.decodeRefsB
    split
    · exact Nat.le_refl _
    · exact Doc.decodeRefsB_le doc limits b os
    · rename_i body _ _
      have h1 := hbody body
      split
      · exact h1
      · have h2 := Doc.decodeRefsB_le doc limits
          (decodeBodyB doc.file limits b (offsetOf doc.file n) body).2 os
        split <;> rename_i hq <;> rw [hq] at h2 <;> dsimp only at h2 ⊢ <;> omega
  | b, .null :: _ | b, .bool _ :: _ | b, .int _ :: _ | b, .real _ :: _ | b, .string _ :: _
  | b, .name _ :: _ | b, .array _ :: _ | b, .dict _ :: _ => by simp [Doc.decodeRefsB]

/-- **Document-wide bound for content arrays**: the decoded parts plus the budget left are
at most the budget before. -/
theorem Doc.decodeRefsB_total (doc : Doc) (limits : Limits) :
    (b : Budget) → (items : List PdfObject) → (parts : List ByteArray) →
    (doc.decodeRefsB limits b items).1 = .ok parts →
    (parts.map ByteArray.size).sum + (doc.decodeRefsB limits b items).2.remaining ≤ b.remaining
  | b, [], parts, h => by
    simp only [Doc.decodeRefsB, Except.ok.injEq] at h ⊢; subst h; simp
  | b, .ref n g :: os, parts, h => by
    unfold Doc.decodeRefsB at h ⊢
    split at h
    · cases h
    · rename_i hg
      exact Doc.decodeRefsB_total doc limits b os parts h
    · rename_i body hnull hg
      split at h
      · cases h
      · rename_i bs hc
        split at h
        · cases h
        · rename_i bss q hq
          simp only [Except.ok.injEq] at h; subst h
          obtain ⟨dd, hdd, hbs⟩ := contentData_ok hc
          have h1 := decodeBodyB_charge hdd
          have h2 := Doc.decodeRefsB_total doc limits _ os bss (by rw [hq])
          rw [hq] at h2
          rw [hbs] at h1
          simp only [List.map_cons, List.sum_cons]
          dsimp only at h2 ⊢
          omega
  | b, .null :: _, _, h | b, .bool _ :: _, _, h | b, .int _ :: _, _, h
  | b, .real _ :: _, _, h | b, .string _ :: _, _, h | b, .name _ :: _, _, h
  | b, .array _ :: _, _, h | b, .dict _ :: _, _, h => by simp [Doc.decodeRefsB] at h

/-- The budget never grows in `Doc.decodeContentsB`. -/
theorem Doc.decodeContentsB_le (doc : Doc) (limits : Limits) (budget : Budget) (page : Page) :
    (doc.decodeContentsB limits budget page).2.remaining ≤ budget.remaining := by
  unfold Doc.decodeContentsB
  split
  · exact Nat.le_refl _
  · exact Doc.decodeRefsB_le _ _ _ _
  · split
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Doc.decodeRefsB_le _ _ _ _
    · rename_i n _ _ _ body _ _ _
      have := decodeBodyB_le doc.file limits budget (offsetOf doc.file n) body
      split <;> exact this
  · exact Nat.le_refl _

/-- **Document-wide bound for a page's contents** (S3): the decoded content streams plus the
budget left are at most the budget before. Threading the budget through every page access
of a document from `Budget.init limits` therefore decodes at most
`limits.maxDecodedTotalBytes` bytes of content in total. -/
theorem Doc.decodeContentsB_total {doc : Doc} {limits : Limits} {budget : Budget} {page : Page}
    {parts : List ByteArray} (h : (doc.decodeContentsB limits budget page).1 = .ok parts) :
    (parts.map ByteArray.size).sum + (doc.decodeContentsB limits budget page).2.remaining ≤
      budget.remaining := by
  unfold Doc.decodeContentsB at h ⊢
  split at h
  · simp only [Except.ok.injEq] at h; subst h; simp
  · exact Doc.decodeRefsB_total doc limits budget _ parts h
  · rename_i n g hc
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h; subst h
      rename_i hg
      simp
    · rename_i items hg
      exact Doc.decodeRefsB_total doc limits budget items parts h
    · rename_i body hn ha hg
      split at h
      · cases h
      · rename_i bs hcd
        simp only [Except.ok.injEq] at h; subst h
        obtain ⟨dd, hdd, hbs⟩ := contentData_ok hcd
        have := decodeBodyB_charge hdd
        rw [hbs] at this
        simpa using this
  · cases h

/-! ## Theorems -/

/-- **CropBox inside MediaBox** (§14.11.2). -/
theorem cropBox_sub_media (p : Page) : p.cropBox.sub p.mediaBox = true := p.cropBox_sub

/-- A page's MediaBox is the merged one, else Letter. -/
theorem mkPage_mediaBox (num gen : Nat) (a : Attrs) (c : Option PdfObject) :
    (mkPage num gen a c).mediaBox = a.mediaBox.getD letter := rfl

/-- **Inheritance law** (§7.7.3.4) for `/MediaBox`: folding `merge` along a root-first path
gives the value of the nearest node that has one, else the initial value. -/
theorem foldl_merge_mediaBox (path : List Attrs) (init : Attrs) :
    (path.foldl Attrs.merge init).mediaBox =
      (path.reverse.findSome? (·.mediaBox)).or init.mediaBox := by
  induction path generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl, ih, List.reverse_cons, List.findSome?_append, Attrs.merge]
    cases h1 : as.reverse.findSome? (·.mediaBox) <;> cases h2 : a.mediaBox <;> simp [h2]

/-- **Inheritance law** for `/Rotate`. -/
theorem foldl_merge_rotate (path : List Attrs) (init : Attrs) :
    (path.foldl Attrs.merge init).rotate =
      (path.reverse.findSome? (·.rotate)).or init.rotate := by
  induction path generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl, ih, List.reverse_cons, List.findSome?_append, Attrs.merge]
    cases h1 : as.reverse.findSome? (·.rotate) <;> cases h2 : a.rotate <;> simp [h2]

/-- A live entry popped by `popLive` is not visited. -/
theorem popLive_fresh {d : OpenDoc} {limits : Limits} {visited : List Nat} :
    ∀ {s : List Entry} {k k' : Nat} {e : Entry} {b : IndirectBody} {rest : List Entry},
      popLive d limits visited s k = .ok (some (e, b, rest), k') → e.num ∉ visited
  | [], _, _, _, _, _, h => by simp [popLive] at h
  | e0 :: s, k, k', e, b, rest, h => by
    unfold popLive at h
    split at h
    · cases h
    · rename_i hn
      split at h
      · cases h
      · exact popLive_fresh h
      · cases h; exact hn

/-- **Cycle ⇒ error.** Popping an entry that is already visited is `Error.cycle`. -/
theorem popLive_cycle {d : OpenDoc} {limits : Limits} {visited : List Nat} {e : Entry}
    {rest : List Entry} {k : Nat} (h : e.num ∈ visited) :
    popLive d limits visited (e :: rest) k =
      .error (.cycle (offsetOf d e.num) "page tree /Kids cycle") := by
  simp [popLive, h]

/-- **Cycle ⇒ error** for the walk: if the next entry is already visited, the walk fails
with `Error.cycle`, whatever the fuel. -/
theorem loop_cycle {d : OpenDoc} {limits : Limits} {f : Nat} {st : WalkState} {e : Entry}
    {rest : List Entry} (hs : st.stack = e :: rest) (h : e.num ∈ st.visited) :
    (loop d limits f st).isOk = false ∧
      loop d limits f st = .error (.cycle (offsetOf d e.num) "page tree /Kids cycle") := by
  have hp := popLive_cycle (d := d) (limits := limits) (rest := rest) (k := st.skipped) h
  cases f <;> simp [loop, hs, hp, Except.isOk, Except.toBool]

/-- What a node visit does to the visited set and the pages: the node becomes visited, and
at most one page, for this node, is added. -/
theorem visitNode_ok {d : OpenDoc} {limits : Limits} {e : Entry} {b : IndirectBody}
    {st st' : WalkState} (h : visitNode d limits e b st = .ok st') :
    st'.visited = e.num :: st.visited ∧
      (st'.pages = st.pages ∨ ∃ p : Page, p.num = e.num ∧ st'.pages = p :: st.pages) := by
  unfold visitNode at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h; exact ⟨rfl, Or.inl rfl⟩
        · cases h; exact ⟨rfl, Or.inr ⟨_, rfl, rfl⟩⟩
        · cases h
    · cases h

/-- **A node is visited before its kids are pushed**: after visiting an intermediate node,
its number is in the visited set, so a `/Kids` entry pointing back to it or to any earlier
visited ancestor is rejected by `loop_cycle` when popped. -/
theorem visitNode_visited {d : OpenDoc} {limits : Limits} {e : Entry} {b : IndirectBody}
    {st st' : WalkState} (h : visitNode d limits e b st = .ok st') :
    e.num ∈ st'.visited ∧ ∀ x ∈ st.visited, x ∈ st'.visited := by
  rw [(visitNode_ok h).1]
  exact ⟨List.mem_cons_self .., fun x hx => List.mem_cons_of_mem _ hx⟩

/-- **Work bound** of the loop: at most `fuel` new nodes are visited. -/
theorem loop_visits_le {d : OpenDoc} {limits : Limits} :
    ∀ {f : Nat} {st st' : WalkState}, loop d limits f st = .ok st' →
      st'.visited.length ≤ st.visited.length + f
  | 0, st, st', h => by
    unfold loop at h
    split at h
    · cases h
    · cases h; simp
    · cases h
  | f + 1, st, st', h => by
    unfold loop at h
    split at h
    · cases h
    · cases h; simp
    · split at h
      · cases h
      · rename_i st1 hv
        have h1 := loop_visits_le h
        have h2 := (visitNode_ok hv).1
        simp only [h2, List.length_cons] at h1
        omega

/-- The walk invariant: the visited set and the page numbers are duplicate-free, and every
page was visited. -/
def Inv (st : WalkState) : Prop :=
  st.visited.Nodup ∧ (st.pages.map Page.num).Nodup ∧ ∀ p ∈ st.pages, p.num ∈ st.visited

/-- A node visit of a fresh node preserves the invariant. -/
theorem visitNode_inv {d : OpenDoc} {limits : Limits} {e : Entry} {b : IndirectBody}
    {st st' : WalkState} (hi : Inv st) (hf : e.num ∉ st.visited)
    (h : visitNode d limits e b st = .ok st') : Inv st' := by
  obtain ⟨hv, hp⟩ := visitNode_ok h
  obtain ⟨hnd, hpn, hsub⟩ := hi
  refine ⟨?_, ?_, ?_⟩
  · rw [hv]; exact List.nodup_cons.2 ⟨hf, hnd⟩
  · rcases hp with hp | ⟨p, hpe, hp⟩
    · rw [hp]; exact hpn
    · rw [hp, List.map_cons]
      refine List.nodup_cons.2 ⟨?_, hpn⟩
      intro hm
      obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hm
      exact hf (hpe ▸ hqe ▸ hsub q hq)
  · intro q hq
    rw [hv]
    rcases hp with hp | ⟨p, hpe, hp⟩
    · rw [hp] at hq; exact List.mem_cons_of_mem _ (hsub q hq)
    · rw [hp] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [hpe]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hsub q hq)

/-- The loop preserves the invariant. -/
theorem loop_inv {d : OpenDoc} {limits : Limits} :
    ∀ {f : Nat} {st st' : WalkState}, Inv st → loop d limits f st = .ok st' → Inv st'
  | 0, st, st', hi, h => by
    unfold loop at h
    split at h
    · cases h
    · cases h; exact hi
    · cases h
  | f + 1, st, st', hi, h => by
    unfold loop at h
    split at h
    · cases h
    · cases h; exact hi
    · rename_i e b rest k hpop
      split at h
      · cases h
      · rename_i st1 hv
        exact loop_inv (visitNode_inv (st := { st with stack := rest, skipped := k }) hi (popLive_fresh hpop) hv) h

/-- **Visit bound** (Plan.md §5.2): the walk visits at most `objectCount` nodes. -/
theorem walk_visits_le {d : OpenDoc} {limits : Limits} {n g : Nat} {st : WalkState}
    (h : walk d limits n g = .ok st) : st.visited.length ≤ d.objectCount := by
  have := loop_visits_le h
  simpa [initState] using this

/-- **No repeats**: no node is visited twice, the pages are distinct objects, and every page
was visited. -/
theorem walk_no_repeat {d : OpenDoc} {limits : Limits} {n g : Nat} {st : WalkState}
    (h : walk d limits n g = .ok st) : Inv st :=
  loop_inv (st := initState n g) ⟨List.nodup_nil, List.nodup_nil, by simp [initState]⟩ h

/-- The pages of a successful walk number at most `objectCount`. -/
theorem walk_pages_le {d : OpenDoc} {limits : Limits} {n g : Nat} {st : WalkState}
    (h : walk d limits n g = .ok st) : st.pages.length ≤ d.objectCount := by
  obtain ⟨-, hpn, hsub⟩ := walk_no_repeat h
  have hs : st.pages.map Page.num ⊆ st.visited := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact hsub p hp
  have := hpn.length_le_of_subset hs
  simp only [List.length_map] at this
  have := walk_visits_le h
  omega

/-- `ofOpen` on success: the pages are those of a successful walk. -/
theorem ofOpen_ok {limits : Limits} {d : OpenDoc} {doc : Doc} (h : ofOpen limits d = .ok doc) :
    ∃ n g st, walk d limits n g = .ok st ∧ doc.pages = st.pages.reverse.toArray ∧
      doc.file = d := by
  unfold ofOpen at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · rename_i hw
          cases h
          exact ⟨_, _, _, hw, rfl, rfl⟩
      · cases h
    · cases h

/-- **Page bound**: a document has at most `objectCount` pages. -/
theorem ofOpen_pages_le {limits : Limits} {d : OpenDoc} {doc : Doc}
    (h : ofOpen limits d = .ok doc) : doc.pageCount ≤ d.objectCount := by
  obtain ⟨n, g, st, hw, hp, -⟩ := ofOpen_ok h
  simp only [Doc.pageCount, hp, List.size_toArray, List.length_reverse]
  exact walk_pages_le hw

/-- **Distinct pages**: no page object occurs twice in a document. -/
theorem ofOpen_pages_nodup {limits : Limits} {d : OpenDoc} {doc : Doc}
    (h : ofOpen limits d = .ok doc) : (doc.pages.toList.map Page.num).Nodup := by
  obtain ⟨n, g, st, hw, hp, -⟩ := ofOpen_ok h
  obtain ⟨-, hpn, -⟩ := walk_no_repeat hw
  rw [hp, List.toList_toArray, List.map_reverse]
  exact hpn.perm (List.reverse_perm _).symm

/-! ## Tests -/

section Tests

/-- Test helper: a PDF whose objects `1 …` are the given bodies, with a correct xref table and
`/Root 1 0 R`. -/
private def mkPdf (objs : List String) : ByteArray := Id.run do
  let mut body := "%PDF-1.4\n"
  let mut offs : List Nat := []
  let mut i := 1
  for o in objs do
    offs := offs ++ [body.utf8ByteSize]
    body := body ++ s!"{i} 0 obj\n{o}\nendobj\n"
    i := i + 1
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  let x := body.utf8ByteSize
  let rows := String.join (offs.map row)
  (body ++ s!"xref\n0 {objs.length + 1}\n0000000000 65535 f \n" ++ rows ++
    s!"trailer\n<< /Size {objs.length + 1} /Root 1 0 R >>\nstartxref\n{x}\n%%EOF\n").toUTF8

/-- Test helper: a decimal from an integer. -/
private def D (i : Int) : Decimal := ⟨i, 0⟩

/-- Test helper: a rectangle as a tuple. -/
private def rt (r : Rect) : Decimal × Decimal × Decimal × Decimal := (r.llx, r.lly, r.urx, r.ury)

/-- Test helper: the open result, summarized. -/
private def summary (b : ByteArray) : String :=
  match openDoc Limits.default b with
  | .ok doc => s!"ok n={doc.pageCount} nums={doc.pages.toList.map Page.num}"
  | .error (.cycle _ m) => s!"cycle {m}"
  | .error (.malformed _ m) => s!"err {m}"
  | .error _ => "err"

/-- Test helper: run a check on the opened document. -/
private def withDoc (b : ByteArray) (p : Doc → Bool) : Bool :=
  match openDoc Limits.default b with
  | .ok doc => p doc
  | .error _ => false

private def onePage : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 612 792] >>",
  "<< /Type /Page /Parent 2 0 R /Contents 4 0 R >>"]

#guard summary onePage == "ok n=1 nums=[3]"
#guard withDoc onePage fun doc =>
  doc.pages.toList.map (fun p => rt p.mediaBox) == [(D 0, D 0, D 612, D 792)] &&
  !doc.countMismatch &&
  (match doc.pages.toList with
   | [p] => !p.mediaBoxDefaulted && p.rotate == .r0 &&
     (match p.contents with | some (.ref 4 0) => true | _ => false)
   | _ => false)

/-- Three pages in two levels; MediaBox and Rotate inherited, CropBox clipped. -/
private def threePages : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R 4 0 R] /Count 3 /MediaBox [0 0 595 842] /Rotate 90 >>",
  "<< /Type /Pages /Parent 2 0 R /Kids [5 0 R 6 0 R] /Count 2 /MediaBox [100 200 0 0] >>",
  "<< /Type /Page /Parent 2 0 R >>",
  "<< /Type /Page /Parent 3 0 R /Rotate -180.0 >>",
  "<< /Type /Page /Parent 3 0 R /CropBox [10 10 50 300.5] /Rotate 45 >>"]

#guard summary threePages == "ok n=3 nums=[5, 6, 4]"
#guard withDoc threePages fun doc =>
  doc.pages.toList.map (fun p => rt p.mediaBox) ==
    [(D 0, D 0, D 100, D 200), (D 0, D 0, D 100, D 200), (D 0, D 0, D 595, D 842)] &&
  doc.pages.toList.map (fun p => rt p.cropBox) ==
    [(D 0, D 0, D 100, D 200), (D 10, D 10, D 50, D 200), (D 0, D 0, D 595, D 842)] &&
  doc.pages.toList.map Page.rotate == [.r180, .r0, .r90] &&
  !doc.countMismatch

-- `getPage` is total over `Fin pageCount`.
#guard withDoc threePages fun doc =>
  if h : 2 < doc.pages.size then (doc.getPage ⟨2, h⟩).num == 4 else false

-- A `/Kids` self-cycle and a two-node cycle are `Error.cycle`.
#guard summary (mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [2 0 R] /Count 1 >>"]) == "cycle page tree /Kids cycle"
#guard summary (mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  "<< /Type /Pages /Kids [2 0 R] /Count 1 >>"]) == "cycle page tree /Kids cycle"
-- A page shared by two parents is rejected too (rule W2).
#guard summary (mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R 3 0 R] /Count 2 >>",
  "<< /Type /Page >>"]) == "cycle page tree /Kids cycle"

-- Missing MediaBox: Letter, flagged (rule A4); missing /Type: leaf by structure (W4).
#guard withDoc (mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Kids [3 0 R] /Count 1 >>",
  "<< /Parent 2 0 R >>"]) fun doc =>
  doc.pages.toList.map (fun p => (rt p.mediaBox, p.mediaBoxDefaulted)) ==
    [((D 0, D 0, D 612, D 792), true)]

-- Wrong /Count is data, not an error (rule W7); a dangling kid is skipped (W3).
#guard withDoc (mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R 9 0 R] /Count 5 >>",
  "<< /Type /Page >>"]) fun doc =>
  doc.pageCount == 1 && doc.countMismatch && doc.declaredCount == some 5 && doc.skippedKids == 1

-- Indirect /Kids and /MediaBox are resolved one level; a non-reference kid is malformed.
#guard withDoc (mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids 3 0 R /Count 1 /MediaBox 5 0 R >>",
  "[4 0 R]",
  "<< /Type /Page /Resources << /Font << >> >> >>",
  "[0 0 0.5 1]"]) fun doc =>
  doc.pages.toList.map (fun p => (rt p.mediaBox, p.resources.isSome)) ==
    [((D 0, D 0, ⟨5, 1⟩, D 1), true)]
#guard summary (mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3] /Count 1 >>"]) ==
  "err page tree node 2: /Kids is not an array of references"
-- /Pages pointing at the catalog: an unexpected /Type.
#guard summary (mkPdf ["<< /Type /Catalog /Pages 1 0 R >>"]) ==
  "err page tree node 1 has an unexpected /Type"


/-- Two pages with content streams: page 1 has `[4 0 R 5 0 R 6 0 R]` (`ABC` in hex, `DEF` in
hex with an indirect `/Filter`, raw `xyz`); page 2 has `/Contents 8 0 R`, an array holding a
dangling reference and `4 0 R`. Object 7 is the name `/ASCIIHexDecode`. -/
private def contentPdf : ByteArray := mkPdf [
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R 9 0 R] /Count 2 /MediaBox [0 0 612 792] >>",
  "<< /Type /Page /Parent 2 0 R /Contents [4 0 R 5 0 R 6 0 R] >>",
  "<< /Length 7 /Filter /AHx >>\nstream\n414243>\nendstream",
  "<< /Length 7 /Filter 7 0 R >>\nstream\n444546>\nendstream",
  "<< /Length 3 >>\nstream\nxyz\nendstream",
  "/ASCIIHexDecode",
  "[20 0 R 4 0 R]",
  "<< /Type /Page /Parent 2 0 R /Contents 8 0 R >>"]

/-- Test helper: bytes as (Latin-1) text. -/
private def asText (b : ByteArray) : String :=
  String.ofList (b.data.toList.map fun (u : UInt8) => Char.ofNat u.toNat)

/-- Test helper: decode page `i`'s contents under budget `rem`; parts as strings, or the
error kind, and the budget left. -/
private def pc (i rem : Nat) : String :=
  match openDoc Limits.default contentPdf with
  | .error _ => "open failed"
  | .ok doc =>
    match doc.pages.toList[i]? with
    | none => "no page"
    | some p =>
      let r := doc.decodeContentsB Limits.default ⟨rem⟩ p
      let s := match r.1 with
        | .ok parts =>
          s!"ok {parts.map asText}"
        | .error (.limitExceeded k) => s!"limit {reprStr k}"
        | .error (.malformed _ m) => s!"err {m}"
        | .error _ => "err"
      s!"{s} rem={r.2.remaining}"

-- Budget exactly hit by the three parts (3 + 3 + 3).
#guard pc 0 9 == "ok [ABC, DEF, xyz] rem=0"
-- The raw third part does not fit what is left (2 of 8).
#guard pc 0 8 == "limit SafePdf.LimitKind.decodedTotalBytes rem=2"
-- The second part's decoder hits the remaining budget (1) and is charged it.
#guard pc 0 4 == "limit SafePdf.LimitKind.decodedTotalBytes rem=0"
-- Indirect /Contents array with a dangling reference (skipped).
#guard pc 1 100 == "ok [ABC] rem=97"
-- `decodeStreamOf` on a non-stream object.
#guard (match openDoc Limits.default contentPdf with
  | .ok doc => match (doc.decodeStreamOf Limits.default ⟨10⟩ 7 0).1 with
    | .error (.malformed _ "not a stream") => true
    | _ => false
  | .error _ => false)

end Tests

end SafePdf.Core.Doc
