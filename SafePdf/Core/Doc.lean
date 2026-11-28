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
  The visited list is the specification; the test uses an ordered set that mirrors it
  (`VSet`, `O(log n)`; task 13.22: a list scan made a flat `/Kids` of n pages quadratic).
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
  this cannot happen: `Spec.PageTree.walk_fuel_irrelevant`, `popLive_exhausted`). Every node visit costs at most 6
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

**Charged since task 4.5** (they were bounded per call only): the xref streams at open time
and the object streams decoded inside `Open.getObject` are charged when the document is opened
and walked in a session (`openDocS`, `ofSession`, section "Sessions"), and the stream access of
D1–D3 has session twins `decodeStreamS`, `decodeContentsS` whose fetches are charged as well.
`ofOpen`, `openDoc`, `Doc.decodeStreamOf`, `Doc.decodeContentsB` stay as they were (the
theorems of `Spec.Doc` are stated over them); with enough budget left the session functions
return exactly what they return (`ofSession_eq`, `openDocS_eq`).

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
* Sessions (task 4.5): `Sim` and the `…B_sim` lemmas, `ofSession_le`, `ofSession_eq`,
  `openDocS_eq`, `decodeStreamS_le`, `decodeStreamS_charge`, `decodeContentsS_total` (section
  "Sessions").
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

/-- An ordered set of object numbers (a balanced tree: `O(log n)` per operation in the worst
case; task 13.22: the visited test was a scan of a list, quadratic on a flat `/Kids`). -/
abbrev NumSet := Std.TreeSet Nat compare

/-- A set of object numbers that mirrors the list `l`: the membership test of `l` in
`O(log n)`. The list stays the specification (all theorems are about it); the set is the
index that makes the test fast. -/
def VSet (l : List Nat) : Type := { s : NumSet // ∀ x : Nat, s.contains x = true ↔ x ∈ l }

/-- The empty set mirrors the empty list. -/
def VSet.empty : VSet [] := ⟨∅, fun x => by simp⟩

/-- Membership in the set: `O(log n)`. -/
def VSet.has {l : List Nat} (v : VSet l) (x : Nat) : Bool := v.1.contains x

/-- The set test agrees with list membership. -/
theorem VSet.has_iff {l : List Nat} (v : VSet l) (x : Nat) : v.has x = true ↔ x ∈ l :=
  v.2 x

/-- Adding an element to the set mirrors consing it onto the list. -/
def VSet.insert {l : List Nat} (v : VSet l) (x : Nat) : VSet (x :: l) :=
  ⟨v.1.insert x, fun y => by
    rw [Std.TreeSet.contains_insert, List.mem_cons]
    have h1 : (compare x y == Ordering.eq) = true ↔ x = y := by
      simp
    rw [Bool.or_eq_true, h1, v.2 y, eq_comm (a := x)]⟩

/-- The walk state. -/
structure WalkState where
  /-- Nodes still to visit, next first. -/
  stack : List Entry
  /-- Object numbers of the visited nodes, newest first. -/
  visited : List Nat
  /-- The visited nodes as an ordered set (the fast membership test; mirrors `visited`). -/
  seen : VSet visited
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
def popLive (d : OpenDoc) (limits : Limits) (visited : List Nat) (seen : VSet visited) :
    List Entry → Nat → Except Error (Option (Entry × IndirectBody × List Entry) × Nat)
  | [], k => .ok (none, k)
  | e :: rest, k =>
    if seen.has e.num then .error (.cycle (offsetOf d e.num) "page tree /Kids cycle")
    else
      match d.getObject limits e.num e.gen with
      | .error x => .error x
      | .ok (.obj .null) => popLive d limits visited seen rest (k + 1)
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
                    visited := e.num :: st.visited, seen := st.seen.insert e.num }
        | .leaf =>
          .ok { st with
                visited := e.num :: st.visited
                seen := st.seen.insert e.num
                pages := mkPage e.num e.gen (e.inh.merge own)
                  (Dict.get? nd (Name.ofString "Contents")) :: st.pages }
        | .bad => .error (.malformed (offsetOf d e.num)
            s!"page tree node {e.num} has an unexpected /Type")
    | _ => .error (.malformed (offsetOf d e.num)
        s!"page tree node {e.num} is not a dictionary")

/-- The walk loop: at most `fuel` node visits (rule W6). -/
def loop (d : OpenDoc) (limits : Limits) : Nat → WalkState → Except Error WalkState
  | 0, st =>
    match popLive d limits st.visited st.seen st.stack st.skipped with
    | .error x => .error x
    | .ok (none, k) => .ok { st with stack := [], skipped := k }
    | .ok (some _, _) => .error (.limitExceeded .objects)
  | f + 1, st =>
    match popLive d limits st.visited st.seen st.stack st.skipped with
    | .error x => .error x
    | .ok (none, k) => .ok { st with stack := [], skipped := k }
    | .ok (some (e, b, rest), k) =>
      match visitNode d limits e b { st with stack := rest, skipped := k } with
      | .error x => .error x
      | .ok st' => loop d limits f st'

/-- The initial state: the root `/Pages` node `n g`, nothing inherited. -/
def initState (n g : Nat) : WalkState := ⟨[⟨n, g, 0, {}⟩], [], VSet.empty, [], 0⟩

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
theorem popLive_fresh {d : OpenDoc} {limits : Limits} {visited : List Nat} {seen : VSet visited} :
    ∀ {s : List Entry} {k k' : Nat} {e : Entry} {b : IndirectBody} {rest : List Entry},
      popLive d limits visited seen s k = .ok (some (e, b, rest), k') → e.num ∉ visited
  | [], _, _, _, _, _, h => by simp [popLive] at h
  | e0 :: s, k, k', e, b, rest, h => by
    unfold popLive at h
    split at h
    · cases h
    · rename_i hn
      split at h
      · cases h
      · exact popLive_fresh h
      · cases h; exact fun hm => hn ((seen.has_iff _).2 hm)

/-- **Cycle ⇒ error.** Popping an entry that is already visited is `Error.cycle`. -/
theorem popLive_cycle {d : OpenDoc} {limits : Limits} {visited : List Nat} {seen : VSet visited} {e : Entry}
    {rest : List Entry} {k : Nat} (h : e.num ∈ visited) :
    popLive d limits visited seen (e :: rest) k =
      .error (.cycle (offsetOf d e.num) "page tree /Kids cycle") := by
  have h' : seen.has e.num = true := (seen.has_iff _).2 h
  simp [popLive, h']

/-- **Cycle ⇒ error** for the walk: if the next entry is already visited, the walk fails
with `Error.cycle`, whatever the fuel. -/
theorem loop_cycle {d : OpenDoc} {limits : Limits} {f : Nat} {st : WalkState} {e : Entry}
    {rest : List Entry} (hs : st.stack = e :: rest) (h : e.num ∈ st.visited) :
    (loop d limits f st).isOk = false ∧
      loop d limits f st = .error (.cycle (offsetOf d e.num) "page tree /Kids cycle") := by
  have hp := popLive_cycle (d := d) (limits := limits) (seen := st.seen) (rest := rest) (k := st.skipped) h
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

/-! ## Sessions: one budget for open, walk and decodes (task 4.5)

The functions above fetch with the unbudgeted `OpenDoc.getObject` and stay as they are (the
theorems of this module and of `Spec.Doc` are stated over them). Their **budgeted twins**
below fetch with `OpenDoc.getObjectB`, threading a state `BC` (what is left of the document
budget, and the decoded object streams) exactly like an `Open.Session`:

* S1. `ofOpenB limits d bc` is `ofOpen` with every fetch (root, page-tree nodes, `/Kids`, the
  four attributes, the root `/Count`) made by `getObjectB` from the state `bc`: object-stream
  decodes are charged once per container (cached), and `/Length` decodes (rule L6) are charged
  on every resolution. `ofSession s limits` runs it on a session and returns the session left;
  `openDocS limits bytes` is `Open.Session.open` followed by `ofSession`, so **one budget and
  one cache cover opening, the page-tree walk and every later decode**.
* S2. `decodeStreamS`, `decodeContentsS` are `Doc.decodeStreamOf`, `Doc.decodeContentsB` (rules
  D1–D3) on a session: the fetches (including those of `/Filter` and `/DecodeParms`, rule D2)
  and the stream decodes are charged to the session's budget.

Theorems:

* `Sim` packs the two facts proved of every budgeted function: the budget never grows, and
  **if at least one `OpenDoc.allowance` is left at the end** (a-posteriori) and the cache was
  exact, the result is the unbudgeted function's and the cache stays exact
  (`fetchB_sim` from `Open.getObjectB_eq_post`; `resolveB_sim`, `keyB_sim`, `attrsOfB_sim`,
  `popLiveB_sim`, `visitNodeB_sim`, `loopB_sim`, `declaredCountOfB_sim`, `ofOpenB_sim`).
* `ofSession_eq`: an exact session whose walk ends with an allowance left returns exactly
  `ofOpen limits s.doc`; `openDocS_eq`: if the full budget covers `maxRevisions ·
  decodeAllowance` (the xref chain, as in `Open.Session.open_eq`), a document that `openDocS`
  opens with an allowance left is exactly the document `openDoc` opens, so every theorem of
  `Spec.Doc` about `openDoc` applies to it. (Only this direction is stated: when the budget
  runs out, `openDocS` may fail where `openDoc` succeeds, which is the point of the budget.)
* `ofSession_le`, `decodeStreamS_le`, `decodeContentsS_le`: the budget never grows;
  `decodeStreamS_charge`, `decodeContentsS_total`: decoded bytes plus the budget left are at
  most the budget before.
-/

open SafePdf.Core.Open (Session)
open SafePdf.Core.Xref.ObjStm (Cache CacheExact)

/-- The budgeted state threaded through a walk: what is left of the document budget, and the
decoded object streams (an `Open.Session` without its document). -/
abbrev BC := Budget × Cache

/-- A state is exact for `d` when its cache holds exact decodes (`ObjStm.CacheExact`). -/
def Exact (d : OpenDoc) (limits : Limits) (bc : BC) : Prop :=
  CacheExact d.pre d.lookup limits d.bytes d.objectCount bc.2

/-- **Simulation** of an unbudgeted value `u` by a budgeted computation `x` run from state
`bc`: the budget never grows, and if `bc` is exact and at least `d.allowance limits` is left
at the end, the value is `u` and the final state is exact. -/
def Sim (d : OpenDoc) (limits : Limits) (bc : BC) {α : Type} (x : α × BC) (u : α) : Prop :=
  x.2.1.remaining ≤ bc.1.remaining ∧
  (Exact d limits bc → d.allowance limits ≤ x.2.1.remaining → x.1 = u ∧ Exact d limits x.2)

/-- A value computed without fetching simulates itself. -/
theorem sim_pure {d : OpenDoc} {limits : Limits} {bc : BC} {α : Type} (a : α) :
    Sim d limits bc (a, bc) a :=
  ⟨Nat.le_refl _, fun hx _ => ⟨rfl, hx⟩⟩

/-- A budgeted fetch: `OpenDoc.getObjectB` with the state's budget and cache. -/
def fetchB (d : OpenDoc) (limits : Limits) (bc : BC) (n g : Nat) :
    (Except Error IndirectBody) × BC :=
  d.getObjectB limits bc.1 bc.2 n g

/-- `fetchB` simulates `getObject` (`Open.getObjectB_le`, `Open.getObjectB_eq_post`). -/
theorem fetchB_sim (d : OpenDoc) (limits : Limits) (bc : BC) (n g : Nat) :
    Sim d limits bc (fetchB d limits bc n g) (d.getObject limits n g) :=
  ⟨Open.getObjectB_le _ _ _ _ _ _, fun hx h => Open.getObjectB_eq_post hx h⟩

/-- `resolve` with a budgeted fetch (rule A1). -/
def resolveB (d : OpenDoc) (limits : Limits) (bc : BC) : PdfObject → (Except Error PdfObject) × BC
  | .ref n g =>
    let r := fetchB d limits bc n g
    (match r.1 with
     | .error e => .error e
     | .ok (.obj o) => .ok o
     | .ok (.stream _) => .ok .null, r.2)
  | o => (.ok o, bc)

/-- `resolveB` simulates `resolve`. -/
theorem resolveB_sim (d : OpenDoc) (limits : Limits) (bc : BC) (o : PdfObject) :
    Sim d limits bc (resolveB d limits bc o) (resolve d limits o) := by
  cases o
  case ref n g =>
    obtain ⟨fle, feq⟩ := fetchB_sim d limits bc n g
    refine ⟨fle, fun hx hA => ?_⟩
    obtain ⟨h1, h2⟩ := feq hx hA
    refine ⟨?_, h2⟩
    simp only [resolveB, resolve]
    rw [h1]
    all_goals (rcases d.getObject limits n g with e | (o | s) <;> rfl)
  all_goals exact sim_pure _

/-- `key` with a budgeted fetch. -/
def keyB (d : OpenDoc) (limits : Limits) (bc : BC) (nd : Dict) (k : String) :
    (Except Error PdfObject) × BC :=
  match Dict.get? nd (Name.ofString k) with
  | none => (.ok .null, bc)
  | some o => resolveB d limits bc o

/-- `keyB` simulates `key`. -/
theorem keyB_sim (d : OpenDoc) (limits : Limits) (bc : BC) (nd : Dict) (k : String) :
    Sim d limits bc (keyB d limits bc nd k) (key d limits nd k) := by
  unfold keyB key
  split
  · exact sim_pure _
  · exact resolveB_sim _ _ _ _

/-- Sequencing of budgeted computations that may fail: run `x`, stop on an error, else run
`f` on its value from the state it left. -/
def bindB {α β : Type} (x : (Except Error α) × BC) (f : α → BC → (Except Error β) × BC) :
    (Except Error β) × BC :=
  match x with
  | (.error e, b) => (.error e, b)
  | (.ok a, b) => f a b

/-- `bindB` simulates `Except.bind`. -/
theorem bindB_sim {d : OpenDoc} {limits : Limits} {bc : BC} {α β : Type}
    {x : (Except Error α) × BC} {u : Except Error α} {f : α → BC → (Except Error β) × BC}
    {f' : α → Except Error β} (hx : Sim d limits bc x u)
    (hf : ∀ a b, Sim d limits b (f a b) (f' a)) :
    Sim d limits bc (bindB x f) (u.bind f') := by
  obtain ⟨hle, heq⟩ := hx
  unfold bindB
  rcases x with ⟨_ | a, b⟩
  · refine ⟨hle, fun hx hA => ?_⟩
    obtain ⟨h1, h2⟩ := heq hx hA
    subst h1
    exact ⟨by first | rfl | trivial, h2⟩
  · obtain ⟨hle2, heq2⟩ := hf a b
    refine ⟨Nat.le_trans hle2 hle, fun hx hA => ?_⟩
    obtain ⟨h1, h2⟩ := heq hx (Nat.le_trans hA hle2)
    subst h1
    exact heq2 h2 hA

/-- `attrsOf` with budgeted fetches (rules A1, A2). -/
def attrsOfB (d : OpenDoc) (limits : Limits) (bc : BC) (nd : Dict) :
    (Except Error Attrs) × BC :=
  bindB (keyB d limits bc nd "Resources") fun r b1 =>
  bindB (keyB d limits b1 nd "MediaBox") fun m b2 =>
  bindB (keyB d limits b2 nd "CropBox") fun c b3 =>
  bindB (keyB d limits b3 nd "Rotate") fun t b4 =>
    (.ok { resources := (match r with | .dict x => some x | _ => none),
           mediaBox := rectOf m, cropBox := rectOf c, rotate := rotateOf t }, b4)

/-- `attrsOfB` simulates `attrsOf`. -/
theorem attrsOfB_sim (d : OpenDoc) (limits : Limits) (bc : BC) (nd : Dict) :
    Sim d limits bc (attrsOfB d limits bc nd) (attrsOf d limits nd) := by
  unfold attrsOfB attrsOf
  refine bindB_sim (keyB_sim _ _ _ _ _) fun r b1 => ?_
  refine bindB_sim (keyB_sim _ _ _ _ _) fun m b2 => ?_
  refine bindB_sim (keyB_sim _ _ _ _ _) fun c b3 => ?_
  refine bindB_sim (keyB_sim _ _ _ _ _) fun t b4 => ?_
  exact sim_pure _

/-- `popLive` with budgeted fetches (rules W2, W3). -/
def popLiveB (d : OpenDoc) (limits : Limits) (visited : List Nat) (seen : VSet visited) :
    List Entry → Nat → BC → (Except Error (Option (Entry × IndirectBody × List Entry) × Nat)) × BC
  | [], k, bc => (.ok (none, k), bc)
  | e :: rest, k, bc =>
    if seen.has e.num then (.error (.cycle (offsetOf d e.num) "page tree /Kids cycle"), bc)
    else
      let r := fetchB d limits bc e.num e.gen
      match r.1 with
      | .error x => (.error x, r.2)
      | .ok (.obj .null) => popLiveB d limits visited seen rest (k + 1) r.2
      | .ok b => (.ok (some (e, b, rest), k), r.2)

/-- `popLiveB` simulates `popLive`. -/
theorem popLiveB_sim (d : OpenDoc) (limits : Limits) (visited : List Nat) (seen : VSet visited) :
    (stack : List Entry) → (k : Nat) → (bc : BC) →
    Sim d limits bc (popLiveB d limits visited seen stack k bc) (popLive d limits visited seen stack k)
  | [], k, bc => sim_pure _
  | e :: rest, k, bc => by
    unfold popLiveB popLive
    by_cases hv : seen.has e.num = true
    · simp only [hv, ↓reduceIte]
      exact sim_pure _
    · simp only [hv]
      obtain ⟨fle, feq⟩ := fetchB_sim d limits bc e.num e.gen
      generalize fetchB d limits bc e.num e.gen = R at fle feq ⊢
      rcases R with ⟨r1, b1⟩
      have leaf : ∀ (b : IndirectBody), r1 = .ok b → b ≠ .obj .null →
          Sim d limits bc ((Except.ok (some (e, b, rest), k)), b1)
            (match d.getObject limits e.num e.gen with
             | .error x => .error x
             | .ok (.obj .null) => popLive d limits visited seen rest (k + 1)
             | .ok b => .ok (some (e, b, rest), k)) := by
        intro b hb hn
        refine ⟨fle, fun hx hA => ?_⟩
        obtain ⟨h1, h2⟩ := feq hx hA
        simp only at h1
        rw [← h1, hb]
        refine ⟨?_, h2⟩
        rcases b with o | s
        · cases o <;> first | rfl | exact absurd rfl hn
        · rfl
      rcases r1 with x | (o | s)
      · refine ⟨fle, fun hx hA => ?_⟩
        obtain ⟨h1, h2⟩ := feq hx hA
        simp only at h1
        rw [← h1]
        exact ⟨by first | rfl | trivial, h2⟩
      · cases o
        case null =>
          obtain ⟨ple, peq⟩ := popLiveB_sim d limits visited seen rest (k + 1) b1
          refine ⟨Nat.le_trans ple fle, fun hx hA => ?_⟩
          obtain ⟨h1, h2⟩ := feq hx (Nat.le_trans hA ple)
          simp only at h1
          rw [← h1]
          exact peq h2 hA
        all_goals exact leaf _ rfl (by simp)
      · exact leaf _ rfl (by simp)

/-- `visitNode` with budgeted fetches (rules W4–W6). -/
def visitNodeB (d : OpenDoc) (limits : Limits) (e : Entry) (b : IndirectBody)
    (st : WalkState) (bc : BC) : (Except Error WalkState) × BC :=
  if limits.maxObjectDepth < e.depth then (.error (.limitExceeded .objectDepth), bc)
  else
    match b with
    | .obj (.dict nd) =>
      bindB (attrsOfB d limits bc nd) fun own b1 =>
        match kindOf nd with
        | .inner =>
          bindB (keyB d limits b1 nd "Kids") fun ko b2 =>
            match kidsOf ko with
            | none => (.error (.malformed (offsetOf d e.num)
                s!"page tree node {e.num}: /Kids is not an array of references"), b2)
            | some ks =>
              (.ok { st with
                     stack := ks.map (fun r => ⟨r.1, r.2, e.depth + 1, e.inh.merge own⟩) ++
                       st.stack
                     visited := e.num :: st.visited, seen := st.seen.insert e.num }, b2)
        | .leaf =>
          (.ok { st with
                 visited := e.num :: st.visited
                 seen := st.seen.insert e.num
                 pages := mkPage e.num e.gen (e.inh.merge own)
                   (Dict.get? nd (Name.ofString "Contents")) :: st.pages }, b1)
        | .bad => (.error (.malformed (offsetOf d e.num)
            s!"page tree node {e.num} has an unexpected /Type"), b1)
    | _ => (.error (.malformed (offsetOf d e.num)
        s!"page tree node {e.num} is not a dictionary"), bc)

/-- **Sequencing simulations**: if `x` simulates `u` and the continuation `y` (run from the
state `x` left) costs nothing more than what is left after `x`, it suffices to prove the
continuation's result knowing that `x`'s value is `u` and `x`'s state is exact. -/
theorem sim_of_eq {d : OpenDoc} {limits : Limits} {bc : BC} {α β : Type} {x : α × BC} {u : α}
    {y : β × BC} {w : β} (hx : Sim d limits bc x u) (hle : y.2.1.remaining ≤ x.2.1.remaining)
    (hcont : x.1 = u → Exact d limits x.2 → d.allowance limits ≤ y.2.1.remaining →
      y.1 = w ∧ Exact d limits y.2) : Sim d limits bc y w :=
  ⟨Nat.le_trans hle hx.1, fun hxe hA =>
    let ⟨h1, h2⟩ := hx.2 hxe (Nat.le_trans hA hle)
    hcont h1 h2 hA⟩

/-- `visitNodeB` simulates `visitNode`. -/
theorem visitNodeB_sim (d : OpenDoc) (limits : Limits) (e : Entry) (b : IndirectBody)
    (st : WalkState) (bc : BC) :
    Sim d limits bc (visitNodeB d limits e b st bc) (visitNode d limits e b st) := by
  unfold visitNodeB visitNode
  by_cases hdep : limits.maxObjectDepth < e.depth
  · simp only [hdep, ↓reduceIte]
    exact sim_pure _
  · simp only [hdep, ↓reduceIte]
    rcases b with o | s
    · cases o
      case dict nd =>
        simp only
        have ha := attrsOfB_sim d limits bc nd
        unfold bindB
        generalize attrsOfB d limits bc nd = X at ha ⊢
        rcases X with ⟨_ | own, b1⟩
        · refine sim_of_eq ha (Nat.le_refl _) fun h1 h2 _ => ?_
          simp only at h1
          rw [← h1]
          exact ⟨by first | rfl | trivial, h2⟩
        · simp only
          cases hk : kindOf nd
          · simp only
            have hkey := keyB_sim d limits b1 nd "Kids"
            generalize keyB d limits b1 nd "Kids" = Y at hkey ⊢
            rcases Y with ⟨_ | ko, b2⟩
            · refine sim_of_eq ha hkey.1 fun h1 h2 hA => ?_
              simp only at h1
              rw [← h1]
              simp only
              obtain ⟨h3, h4⟩ := hkey.2 h2 hA
              simp only at h3
              rw [← h3]
              exact ⟨by first | rfl | trivial, h4⟩
            · simp only
              cases hkid : kidsOf ko
              all_goals
                refine sim_of_eq ha hkey.1 fun h1 h2 hA => ?_
                simp only at h1
                rw [← h1]
                simp only
                obtain ⟨h3, h4⟩ := hkey.2 h2 hA
                simp only at h3
                rw [← h3]
                simp only [hkid]
                exact ⟨by first | rfl | trivial, h4⟩
          · refine sim_of_eq ha (Nat.le_refl _) fun h1 h2 _ => ?_
            simp only at h1
            rw [← h1]
            exact ⟨by first | rfl | trivial, h2⟩
          · refine sim_of_eq ha (Nat.le_refl _) fun h1 h2 _ => ?_
            simp only at h1
            rw [← h1]
            exact ⟨by first | rfl | trivial, h2⟩
      all_goals exact sim_pure _
    · exact sim_pure _

/-- `loop` with budgeted fetches (rule W6). -/
def loopB (d : OpenDoc) (limits : Limits) : Nat → WalkState → BC → (Except Error WalkState) × BC
  | 0, st, bc =>
    let r := popLiveB d limits st.visited st.seen st.stack st.skipped bc
    (match r.1 with
     | .error x => .error x
     | .ok (none, k) => .ok { st with stack := [], skipped := k }
     | .ok (some _, _) => .error (.limitExceeded .objects), r.2)
  | f + 1, st, bc =>
    let r := popLiveB d limits st.visited st.seen st.stack st.skipped bc
    match r.1 with
    | .error x => (.error x, r.2)
    | .ok (none, k) => (.ok { st with stack := [], skipped := k }, r.2)
    | .ok (some (e, b, rest), k) =>
      bindB (visitNodeB d limits e b { st with stack := rest, skipped := k } r.2) fun st' b1 =>
        loopB d limits f st' b1

/-- `loopB` simulates `loop`. -/
theorem loopB_sim (d : OpenDoc) (limits : Limits) :
    (fuel : Nat) → (st : WalkState) → (bc : BC) →
    Sim d limits bc (loopB d limits fuel st bc) (loop d limits fuel st)
  | 0, st, bc => by
    unfold loopB loop
    have hp := popLiveB_sim d limits st.visited st.seen st.stack st.skipped bc
    generalize popLiveB d limits st.visited st.seen st.stack st.skipped bc = R at hp ⊢
    refine sim_of_eq hp (Nat.le_refl _) fun h1 h2 _ => ?_
    refine ⟨?_, h2⟩
    rw [← h1]
    all_goals (rcases R.1 with x | ⟨_ | _, k⟩ <;> rfl)
  | f + 1, st, bc => by
    unfold loopB loop
    have hp := popLiveB_sim d limits st.visited st.seen st.stack st.skipped bc
    generalize popLiveB d limits st.visited st.seen st.stack st.skipped bc = R at hp ⊢
    rcases R with ⟨r1, b1⟩
    rcases r1 with x | ⟨_ | ⟨e, b, rest⟩, k⟩
    · refine sim_of_eq hp (Nat.le_refl _) fun h1 h2 _ => ?_
      simp only at h1
      rw [← h1]
      exact ⟨by first | rfl | trivial, h2⟩
    · refine sim_of_eq hp (Nat.le_refl _) fun h1 h2 _ => ?_
      simp only at h1
      rw [← h1]
      exact ⟨by first | rfl | trivial, h2⟩
    · simp only
      unfold bindB
      have hv := visitNodeB_sim d limits e b { st with stack := rest, skipped := k } b1
      generalize visitNodeB d limits e b { st with stack := rest, skipped := k } b1 = V at hv ⊢
      rcases V with ⟨_ | st', b2⟩
      · refine sim_of_eq hp hv.1 fun h1 h2 hA => ?_
        simp only at h1
        rw [← h1]
        simp only
        obtain ⟨h3, h4⟩ := hv.2 h2 hA
        simp only at h3
        rw [← h3]
        exact ⟨by first | rfl | trivial, h4⟩
      · simp only
        have hl := loopB_sim d limits f st' b2
        refine sim_of_eq hp (Nat.le_trans hl.1 hv.1) fun h1 h2 hA => ?_
        simp only at h1
        rw [← h1]
        simp only
        obtain ⟨h3, h4⟩ := hv.2 h2 (Nat.le_trans hA hl.1)
        simp only at h3
        rw [← h3]
        exact hl.2 h4 hA

/-- `walk` with budgeted fetches. -/
def walkB (d : OpenDoc) (limits : Limits) (n g : Nat) (bc : BC) : (Except Error WalkState) × BC :=
  loopB d limits d.objectCount (initState n g) bc

/-- `walkB` simulates `walk`. -/
theorem walkB_sim (d : OpenDoc) (limits : Limits) (n g : Nat) (bc : BC) :
    Sim d limits bc (walkB d limits n g bc) (walk d limits n g) :=
  loopB_sim d limits _ _ _

/-- `declaredCountOf` with a budgeted fetch. -/
def declaredCountOfB (d : OpenDoc) (limits : Limits) (n g : Nat) (bc : BC) : Option Int × BC :=
  let r := fetchB d limits bc n g
  (match r.1 with
   | .ok (.obj (.dict pd)) =>
     match Dict.get? pd (Name.ofString "Count") with
     | some (.int c) => some c
     | _ => none
   | _ => none, r.2)

/-- `declaredCountOfB` simulates `declaredCountOf`. -/
theorem declaredCountOfB_sim (d : OpenDoc) (limits : Limits) (n g : Nat) (bc : BC) :
    Sim d limits bc (declaredCountOfB d limits n g bc) (declaredCountOf d limits n g) := by
  obtain ⟨fle, feq⟩ := fetchB_sim d limits bc n g
  refine ⟨fle, fun hx hA => ?_⟩
  obtain ⟨h1, h2⟩ := feq hx hA
  refine ⟨?_, h2⟩
  unfold declaredCountOfB declaredCountOf
  simp only
  rw [h1]
  all_goals
    rcases d.getObject limits n g with x | (o | s)
    · rfl
    · cases o <;> try rfl
      simp only
      split <;> rfl
    · rfl

/-- `ofOpen` with budgeted fetches (rules W1–W7, S1). -/
def ofOpenB (limits : Limits) (d : OpenDoc) (bc : BC) : (Except Error Doc) × BC :=
  match d.trailer.root? with
  | none => (.error (.malformed 0 "trailer has no /Root"), bc)
  | some (rn, rg) =>
    let r := fetchB d limits bc rn rg
    match r.1 with
    | .error e => (.error e, r.2)
    | .ok (.obj (.dict cat)) =>
      match Dict.get? cat (Name.ofString "Pages") with
      | some (.ref pn pg) =>
        bindB (walkB d limits pn pg r.2) fun st b1 =>
          let c := declaredCountOfB d limits pn pg b1
          (.ok { file := d, catalog := cat, pagesRef := (pn, pg),
                 pages := st.pages.reverse.toArray,
                 declaredCount := c.1, skippedKids := st.skipped }, c.2)
      | _ => (.error (.malformed (offsetOf d rn) "catalog /Pages is not an indirect reference"),
          r.2)
    | .ok _ => (.error (.malformed (offsetOf d rn) "/Root is not a dictionary"), r.2)

/-- `ofOpenB` simulates `ofOpen`. -/
theorem ofOpenB_sim (limits : Limits) (d : OpenDoc) (bc : BC) :
    Sim d limits bc (ofOpenB limits d bc) (ofOpen limits d) := by
  unfold ofOpenB ofOpen
  split
  · exact sim_pure _
  · rename_i rn rg _
    have hf := fetchB_sim d limits bc rn rg
    simp only
    generalize fetchB d limits bc rn rg = R at hf ⊢
    rcases R with ⟨r1, b1⟩
    rcases r1 with x | (o | s)
    · refine sim_of_eq hf (Nat.le_refl _) fun h1 h2 _ => ?_
      simp only at h1
      rw [← h1]
      exact ⟨by first | rfl | trivial, h2⟩
    · cases o
      case dict cat =>
        simp only
        cases hpg : Dict.get? cat (Name.ofString "Pages")
        · refine sim_of_eq hf (Nat.le_refl _) fun h1 h2 _ => ?_
          simp only at h1
          rw [← h1]
          simp only [hpg]
          exact ⟨by first | rfl | trivial, h2⟩
        · rename_i po
          cases po
          case ref pn pg =>
            simp only
            unfold bindB
            have hw := walkB_sim d limits pn pg b1
            generalize walkB d limits pn pg b1 = W at hw ⊢
            rcases W with ⟨_ | st, b2⟩
            · refine sim_of_eq hf hw.1 fun h1 h2 hA => ?_
              simp only at h1
              rw [← h1]
              simp only [hpg]
              obtain ⟨h3, h4⟩ := hw.2 h2 hA
              simp only at h3
              rw [← h3]
              exact ⟨by first | rfl | trivial, h4⟩
            · simp only
              have hc := declaredCountOfB_sim d limits pn pg b2
              refine sim_of_eq hf (Nat.le_trans hc.1 hw.1) fun h1 h2 hA => ?_
              simp only at h1
              rw [← h1]
              simp only [hpg]
              obtain ⟨h3, h4⟩ := hw.2 h2 (Nat.le_trans hA hc.1)
              simp only at h3
              rw [← h3]
              obtain ⟨h5, h6⟩ := hc.2 h4 hA
              refine ⟨?_, h6⟩
              simp only
              rw [h5]
          all_goals
            refine sim_of_eq hf (Nat.le_refl _) fun h1 h2 _ => ?_
            simp only at h1
            rw [← h1]
            simp only [hpg]
            exact ⟨by first | rfl | trivial, h2⟩
      all_goals
        refine sim_of_eq hf (Nat.le_refl _) fun h1 h2 _ => ?_
        simp only at h1
        rw [← h1]
        exact ⟨by first | rfl | trivial, h2⟩
    · refine sim_of_eq hf (Nat.le_refl _) fun h1 h2 _ => ?_
      simp only at h1
      rw [← h1]
      exact ⟨by first | rfl | trivial, h2⟩

/-- **Walk the page tree in a session** (S1): `ofOpenB` from the session's budget and cache;
returns the document and the session left. -/
def ofSession (s : Session) (limits : Limits) : (Except Error Doc) × Session :=
  let r := ofOpenB limits s.doc (s.budget, s.cache)
  (r.1, ⟨s.doc, r.2.1, r.2.2⟩)

/-- `ofSession` never increases the budget and keeps the document. -/
theorem ofSession_le (s : Session) (limits : Limits) :
    (ofSession s limits).2.budget.remaining ≤ s.budget.remaining ∧
    (ofSession s limits).2.doc = s.doc :=
  ⟨(ofOpenB_sim limits s.doc (s.budget, s.cache)).1, rfl⟩

/-- **A session walk is `ofOpen`** (a-posteriori): an exact session whose walk ends with at
least `s.doc.allowance limits` left returns exactly `ofOpen limits s.doc`, and stays exact. -/
theorem ofSession_eq {s : Session} {limits : Limits} (hx : s.Exact limits)
    (h : s.doc.allowance limits ≤ (ofSession s limits).2.budget.remaining) :
    (ofSession s limits).1 = ofOpen limits s.doc ∧ (ofSession s limits).2.Exact limits :=
  (ofOpenB_sim limits s.doc (s.budget, s.cache)).2 hx h

/-- **Budgeted entry point** (S1, task 4.5): open a session (`Open.Session.open`, the full
`maxDecodedTotalBytes` budget) and walk its page tree in it. Returns the document and the
session, whose budget and cache the later decodes (`decodeStreamS`, `decodeContentsS`) use. -/
def openDocS (limits : Limits) (bytes : ByteArray) : Except Error (Doc × Session) :=
  match Session.open limits bytes with
  | .error e => .error e
  | .ok s =>
    match ofSession s limits with
    | (.ok doc, s') => .ok (doc, s')
    | (.error e, _) => .error e

/-- **`openDocS` is `openDoc`** with enough budget (task 4.5): if the full budget covers the
xref chain (`maxRevisions · decodeAllowance`, as in `Open.Session.open_eq`) and the session
`openDocS` returns has at least one `decodeAllowance` left, the document is exactly the one
`openDoc` opens (so the theorems of `Spec.Doc` about `openDoc` apply to it), its `file` is the
session's document, and the session is exact. -/
theorem openDocS_eq {limits : Limits} {bytes : ByteArray}
    (h : limits.maxRevisions * Core.Xref.Chain.decodeAllowance limits bytes ≤
      limits.maxDecodedTotalBytes)
    {doc : Doc} {s : Session} (hs : openDocS limits bytes = .ok (doc, s))
    (hb : Core.Xref.Chain.decodeAllowance limits bytes ≤ s.budget.remaining) :
    openDoc limits bytes = .ok doc ∧ s.Exact limits := by
  unfold openDocS at hs
  rcases ho : Session.open limits bytes with e | s0
  · rw [ho] at hs; cases hs
  · rw [ho] at hs
    simp only at hs
    have hle := ofSession_le s0 limits
    have hbytes : s0.doc.bytes = bytes := Open.Session.open_bytes ho
    rcases hw : ofSession s0 limits with ⟨r, s1⟩
    rw [hw] at hs hle
    rcases r with e | doc'
    · cases hs
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have hb' : s0.doc.allowance limits ≤ (ofSession s0 limits).2.budget.remaining := by
        rw [hw]; unfold OpenDoc.allowance; rw [hbytes]; exact hb
      have hb0 : Core.Xref.Chain.decodeAllowance limits bytes ≤ s0.budget.remaining :=
        Nat.le_trans hb hle.1
      obtain ⟨ho1, hx0⟩ := (Open.Session.open_eq h).1 s0 ho hb0
      obtain ⟨he, hx1⟩ := ofSession_eq hx0 hb'
      rw [hw] at he hx1
      refine ⟨?_, hx1⟩
      unfold openDoc
      rw [ho1]
      exact he.symm

/-! ### Decoded streams in a session (S2) -/

/-- `resolveParamRef` with a budgeted fetch (rule D2). -/
def resolveParamRefB (d : OpenDoc) (limits : Limits) (bc : BC) :
    PdfObject → (Except Error PdfObject) × BC
  | .ref n g =>
    let r := fetchB d limits bc n g
    (match r.1 with
     | .error e => .error e
     | .ok (.obj o) => .ok o
     | .ok (.stream _) =>
       .error (.malformed (offsetOf d n) "/Filter or /DecodeParms refers to a stream"), r.2)
  | o => (.ok o, bc)

/-- `resolveParamRefB` never increases the budget. -/
theorem resolveParamRefB_le (d : OpenDoc) (limits : Limits) (bc : BC) (o : PdfObject) :
    (resolveParamRefB d limits bc o).2.1.remaining ≤ bc.1.remaining := by
  cases o
  case ref n g => exact (fetchB_sim d limits bc n g).1
  all_goals exact Nat.le_refl _

/-- The elements of a `/Filter` or `/DecodeParms` array, each resolved by
`resolveParamRefB`, threading the state. -/
def resolveParamsB (d : OpenDoc) (limits : Limits) :
    BC → List PdfObject → (Except Error (List PdfObject)) × BC
  | bc, [] => (.ok [], bc)
  | bc, o :: os =>
    bindB (resolveParamRefB d limits bc o) fun v b1 =>
    bindB (resolveParamsB d limits b1 os) fun vs b2 => (.ok (v :: vs), b2)

/-- `resolveParamsB` never increases the budget. -/
theorem resolveParamsB_le (d : OpenDoc) (limits : Limits) :
    (bc : BC) → (os : List PdfObject) →
    (resolveParamsB d limits bc os).2.1.remaining ≤ bc.1.remaining
  | bc, [] => Nat.le_refl _
  | bc, o :: os => by
    unfold resolveParamsB bindB
    have h1 := resolveParamRefB_le d limits bc o
    rcases hr : resolveParamRefB d limits bc o with ⟨_ | v, b1⟩
    · rw [hr] at h1; exact h1
    · rw [hr] at h1
      simp only
      have h2 := resolveParamsB_le d limits b1 os
      rcases hr2 : resolveParamsB d limits b1 os with ⟨_ | vs, b2⟩
      · rw [hr2] at h2; exact Nat.le_trans h2 h1
      · rw [hr2] at h2; exact Nat.le_trans h2 h1

/-- `resolveParam` with budgeted fetches. -/
def resolveParamB (d : OpenDoc) (limits : Limits) (bc : BC) :
    PdfObject → (Except Error PdfObject) × BC
  | .array items =>
    bindB (resolveParamsB d limits bc items) fun xs b1 => (.ok (.array xs), b1)
  | o => resolveParamRefB d limits bc o

/-- `resolveParamB` never increases the budget. -/
theorem resolveParamB_le (d : OpenDoc) (limits : Limits) (bc : BC) (o : PdfObject) :
    (resolveParamB d limits bc o).2.1.remaining ≤ bc.1.remaining := by
  cases o
  case array items =>
    have h := resolveParamsB_le d limits bc items
    simp only [resolveParamB, bindB]
    rcases hr : resolveParamsB d limits bc items with ⟨_ | xs, b1⟩ <;> (rw [hr] at h; exact h)
  all_goals exact resolveParamRefB_le _ _ _ _

/-- `resolveStreamDict` with budgeted fetches (rule D2). -/
def resolveStreamDictB (d : OpenDoc) (limits : Limits) : BC → Dict → (Except Error Dict) × BC
  | bc, [] => (.ok [], bc)
  | bc, kv :: rest =>
    bindB (if kv.1 = Name.ofString "Filter" ∨ kv.1 = Name.ofString "DecodeParms" then
             bindB (resolveParamB d limits bc kv.2) fun v b => (.ok (kv.1, v), b)
           else (.ok kv, bc)) fun kv' b1 =>
    bindB (resolveStreamDictB d limits b1 rest) fun rest' b2 => (.ok (kv' :: rest'), b2)

/-- `resolveStreamDictB` never increases the budget. -/
theorem resolveStreamDictB_le (d : OpenDoc) (limits : Limits) :
    (bc : BC) → (sd : Dict) → (resolveStreamDictB d limits bc sd).2.1.remaining ≤ bc.1.remaining
  | bc, [] => Nat.le_refl _
  | bc, kv :: rest => by
    unfold resolveStreamDictB
    have h1 : (if kv.1 = Name.ofString "Filter" ∨ kv.1 = Name.ofString "DecodeParms" then
             bindB (resolveParamB d limits bc kv.2) fun v b => (.ok (kv.1, v), b)
           else ((.ok kv : Except Error (Name × PdfObject)), bc)).2.1.remaining ≤
           bc.1.remaining := by
      split
      · unfold bindB
        have := resolveParamB_le d limits bc kv.2
        rcases hr : resolveParamB d limits bc kv.2 with ⟨_ | v, b⟩ <;> (rw [hr] at this; exact this)
      · exact Nat.le_refl _
    generalize (if kv.1 = Name.ofString "Filter" ∨ kv.1 = Name.ofString "DecodeParms" then
             bindB (resolveParamB d limits bc kv.2) fun v b => (.ok (kv.1, v), b)
           else ((.ok kv : Except Error (Name × PdfObject)), bc)) = X at h1 ⊢
    unfold bindB
    rcases X with ⟨_ | kv', b1⟩
    · exact h1
    · simp only
      have h2 := resolveStreamDictB_le d limits b1 rest
      rcases hr : resolveStreamDictB d limits b1 rest with ⟨_ | rest', b2⟩ <;>
        (rw [hr] at h2; exact Nat.le_trans h2 h1)

/-- Decode a fetched body in a session state (rule D1): a stream is decoded by
`Filter.decodeStreamB` from the state's budget after rule D2; anything else is `malformed`. -/
def decodeBodyS (d : OpenDoc) (limits : Limits) (bc : BC) (off : Nat) :
    IndirectBody → (Except Error Decoded) × BC
  | .stream s =>
    match resolveStreamDictB d limits bc s.dict with
    | (.error e, b1) => (.error e, b1)
    | (.ok sd, b1) =>
      let r := Filter.decodeStreamB limits b1.1 sd s.data
      (r.1, (r.2, b1.2))
  | .obj _ => (.error (.malformed off "not a stream"), bc)

/-- `decodeBodyS` never increases the budget. -/
theorem decodeBodyS_le (d : OpenDoc) (limits : Limits) (bc : BC) (off : Nat)
    (body : IndirectBody) : (decodeBodyS d limits bc off body).2.1.remaining ≤ bc.1.remaining := by
  unfold decodeBodyS
  split
  · rename_i s
    have h1 := resolveStreamDictB_le d limits bc s.dict
    rcases hr : resolveStreamDictB d limits bc s.dict with ⟨_ | sd, b1⟩
    · rw [hr] at h1; exact h1
    · rw [hr] at h1
      exact Nat.le_trans (Filter.decodeStreamB_le _ _ _ _ _) h1
  · exact Nat.le_refl _

/-- **Charge law** of `decodeBodyS`: a decoded stream's bytes plus the budget left are at most
the budget before. -/
theorem decodeBodyS_charge {d : OpenDoc} {limits : Limits} {bc : BC} {off : Nat}
    {body : IndirectBody} {r : Decoded} (h : (decodeBodyS d limits bc off body).1 = .ok r) :
    r.bytes.size + (decodeBodyS d limits bc off body).2.1.remaining ≤ bc.1.remaining := by
  unfold decodeBodyS at h ⊢
  split at h
  · rename_i s
    have h1 := resolveStreamDictB_le d limits bc s.dict
    rcases hr : resolveStreamDictB d limits bc s.dict with ⟨_ | sd, b1⟩
    · rw [hr] at h; cases h
    · rw [hr] at h h1
      simp only at h ⊢
      have := Filter.decodeStreamB_charge h
      dsimp only at h1 this ⊢
      omega
  · cases h

/-- **Budgeted stream access in a session** (S2, rule D1): fetch object `n g` with the
session's budget and cache and decode it as a stream from the same budget. Returns the
decoded stream and the session left. -/
def decodeStreamS (s : Session) (limits : Limits) (n g : Nat) :
    (Except Error Decoded) × Session :=
  let f := fetchB s.doc limits (s.budget, s.cache) n g
  let r : (Except Error Decoded) × BC := match f.1 with
    | .error e => (.error e, f.2)
    | .ok b => decodeBodyS s.doc limits f.2 (offsetOf s.doc n) b
  (r.1, ⟨s.doc, r.2.1, r.2.2⟩)

/-- `decodeStreamS` never increases the budget and keeps the document. -/
theorem decodeStreamS_le (s : Session) (limits : Limits) (n g : Nat) :
    (decodeStreamS s limits n g).2.budget.remaining ≤ s.budget.remaining ∧
    (decodeStreamS s limits n g).2.doc = s.doc := by
  refine ⟨?_, rfl⟩
  unfold decodeStreamS
  have h1 := (fetchB_sim s.doc limits (s.budget, s.cache) n g).1
  rcases hf : fetchB s.doc limits (s.budget, s.cache) n g with ⟨_ | b, bc⟩
  · rw [hf] at h1; exact h1
  · rw [hf] at h1
    exact Nat.le_trans (decodeBodyS_le _ _ _ _ _) h1

/-- **Charge law** (S3) of `decodeStreamS`: the decoded bytes plus the budget left are at
most the session's budget before. -/
theorem decodeStreamS_charge {s : Session} {limits : Limits} {n g : Nat} {r : Decoded}
    (h : (decodeStreamS s limits n g).1 = .ok r) :
    r.bytes.size + (decodeStreamS s limits n g).2.budget.remaining ≤ s.budget.remaining := by
  unfold decodeStreamS at h ⊢
  have h1 := (fetchB_sim s.doc limits (s.budget, s.cache) n g).1
  rcases hf : fetchB s.doc limits (s.budget, s.cache) n g with ⟨_ | b, bc⟩
  · rw [hf] at h; cases h
  · rw [hf] at h h1
    dsimp only at h h1 ⊢
    have := decodeBodyS_charge h
    omega

/-- Decode a `/Contents` array in a session state (rule D3). -/
def decodeRefsS (d : OpenDoc) (limits : Limits) :
    BC → List PdfObject → (Except Error (List ByteArray)) × BC
  | bc, [] => (.ok [], bc)
  | bc, .ref n g :: os =>
    let f := fetchB d limits bc n g
    match f.1 with
    | .error e => (.error e, f.2)
    | .ok (.obj .null) => decodeRefsS d limits f.2 os
    | .ok body =>
      let r := decodeBodyS d limits f.2 (offsetOf d n) body
      match contentData (offsetOf d n) r.1 with
      | .error e => (.error e, r.2)
      | .ok bs =>
        match decodeRefsS d limits r.2 os with
        | (.error e, q) => (.error e, q)
        | (.ok bss, q) => (.ok (bs :: bss), q)
  | bc, _ :: _ =>
    (.error (.malformed 0 "/Contents array element is not an indirect reference"), bc)

/-- **Document-wide bound for content arrays in a session**: the budget never grows, and on
success the decoded parts plus the budget left are at most the budget before. -/
theorem decodeRefsS_total (d : OpenDoc) (limits : Limits) :
    (bc : BC) → (items : List PdfObject) →
    (decodeRefsS d limits bc items).2.1.remaining ≤ bc.1.remaining ∧
    ∀ parts, (decodeRefsS d limits bc items).1 = .ok parts →
      (parts.map ByteArray.size).sum + (decodeRefsS d limits bc items).2.1.remaining ≤
        bc.1.remaining
  | bc, [] => ⟨Nat.le_refl _, fun parts h => by
      simp only [decodeRefsS, Except.ok.injEq] at h ⊢; subst h; simp⟩
  | bc, .ref n g :: os => by
    have h0 := (fetchB_sim d limits bc n g).1
    unfold decodeRefsS
    generalize fetchB d limits bc n g = F at h0 ⊢
    rcases F with ⟨f1, fb⟩
    simp only at h0 ⊢
    rcases f1 with e | body
    · exact ⟨h0, fun parts h => by cases h⟩
    · have hnull : body = .obj .null ∨ body ≠ .obj .null := by
        by_cases hb : body = .obj .null
        · exact .inl hb
        · exact .inr hb
      rcases hnull with hb | hb
      · subst hb
        obtain ⟨r1, r2⟩ := decodeRefsS_total d limits fb os
        exact ⟨Nat.le_trans r1 h0, fun parts h => Nat.le_trans (r2 parts h) h0⟩
      · have hdec := fun (bd : IndirectBody) =>
          decodeBodyS_le d limits fb (offsetOf d n) bd
        have key : ∀ (bd : IndirectBody), bd = body →
            (match contentData (offsetOf d n) (decodeBodyS d limits fb (offsetOf d n) bd).1 with
             | .error e => ((Except.error e : Except Error (List ByteArray)),
                 (decodeBodyS d limits fb (offsetOf d n) bd).2)
             | .ok bs =>
               match decodeRefsS d limits (decodeBodyS d limits fb (offsetOf d n) bd).2 os with
               | (.error e, q) => (.error e, q)
               | (.ok bss, q) => (.ok (bs :: bss), q)).2.1.remaining ≤ bc.1.remaining ∧
            ∀ parts, (match contentData (offsetOf d n)
                (decodeBodyS d limits fb (offsetOf d n) bd).1 with
             | .error e => ((Except.error e : Except Error (List ByteArray)),
                 (decodeBodyS d limits fb (offsetOf d n) bd).2)
             | .ok bs =>
               match decodeRefsS d limits (decodeBodyS d limits fb (offsetOf d n) bd).2 os with
               | (.error e, q) => (.error e, q)
               | (.ok bss, q) => (.ok (bs :: bss), q)).1 = .ok parts →
              (parts.map ByteArray.size).sum + (match contentData (offsetOf d n)
                (decodeBodyS d limits fb (offsetOf d n) bd).1 with
             | .error e => ((Except.error e : Except Error (List ByteArray)),
                 (decodeBodyS d limits fb (offsetOf d n) bd).2)
             | .ok bs =>
               match decodeRefsS d limits (decodeBodyS d limits fb (offsetOf d n) bd).2 os with
               | (.error e, q) => (.error e, q)
               | (.ok bss, q) => (.ok (bs :: bss), q)).2.1.remaining ≤ bc.1.remaining := by
          intro bd _
          have h1 := hdec bd
          generalize hD : decodeBodyS d limits fb (offsetOf d n) bd = D at h1 ⊢
          rcases hc : contentData (offsetOf d n) D.1 with e | bs
          · exact ⟨Nat.le_trans h1 h0, fun parts h => by cases h⟩
          · simp only
            obtain ⟨dd, hdd, hbs⟩ := contentData_ok hc
            have hch := decodeBodyS_charge (d := d) (limits := limits) (bc := fb)
              (off := offsetOf d n) (body := bd) (r := dd) (by rw [hD]; exact hdd)
            rw [hD] at hch
            obtain ⟨r1, r2⟩ := decodeRefsS_total d limits D.2 os
            rcases hq : decodeRefsS d limits D.2 os with ⟨_ | bss, q⟩
            · rw [hq] at r1
              exact ⟨Nat.le_trans r1 (Nat.le_trans h1 h0), fun parts h => by cases h⟩
            · rw [hq] at r1 r2
              refine ⟨Nat.le_trans r1 (Nat.le_trans h1 h0), fun parts h => ?_⟩
              simp only [Except.ok.injEq] at h
              subst h
              have := r2 bss rfl
              simp only [List.map_cons, List.sum_cons]
              rw [← hbs]
              dsimp only at this hch h1 h0 ⊢
              omega
        rcases body with o | st
        · cases o
          case null => exact absurd rfl hb
          all_goals exact key _ rfl
        · exact key _ rfl
  | bc, .null :: _ | bc, .bool _ :: _ | bc, .int _ :: _ | bc, .real _ :: _
  | bc, .string _ :: _ | bc, .name _ :: _ | bc, .array _ :: _ | bc, .dict _ :: _ =>
    ⟨Nat.le_refl _, fun parts h => by simp [decodeRefsS] at h⟩

/-- One content stream `n` with fetched body `body`, decoded in a session state (rule D3). -/
def contentPart (d : OpenDoc) (limits : Limits) (bc : BC) (n : Nat) (body : IndirectBody) :
    (Except Error (List ByteArray)) × BC :=
  let b := decodeBodyS d limits bc (offsetOf d n) body
  match contentData (offsetOf d n) b.1 with
  | .error e => (.error e, b.2)
  | .ok bs => (.ok [bs], b.2)

/-- `contentPart`: the budget never grows; a decoded part plus the budget left are at most
the budget before. -/
theorem contentPart_total (d : OpenDoc) (limits : Limits) (bc : BC) (n : Nat)
    (body : IndirectBody) :
    (contentPart d limits bc n body).2.1.remaining ≤ bc.1.remaining ∧
    ∀ parts, (contentPart d limits bc n body).1 = .ok parts →
      (parts.map ByteArray.size).sum + (contentPart d limits bc n body).2.1.remaining ≤
        bc.1.remaining := by
  unfold contentPart
  have h1 := decodeBodyS_le d limits bc (offsetOf d n) body
  have hch0 := fun (dd : Decoded) (hdd : (decodeBodyS d limits bc (offsetOf d n) body).1 = .ok dd) =>
    decodeBodyS_charge hdd
  generalize decodeBodyS d limits bc (offsetOf d n) body = D at h1 hch0 ⊢
  simp only
  rcases hc : contentData (offsetOf d n) D.1 with e | bs
  · exact ⟨h1, fun parts h => by cases h⟩
  · refine ⟨h1, fun parts h => ?_⟩
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨dd, hdd, hbs⟩ := contentData_ok hc
    have hch := hch0 dd hdd
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [← hbs]
    omega

/-- A page's `/Contents` decoded in a session state (rule D3). -/
def decodeContentsBC (d : OpenDoc) (limits : Limits) (bc : BC) (page : Page) :
    (Except Error (List ByteArray)) × BC :=
  match page.contents with
  | none => (.ok [], bc)
  | some (.array items) => decodeRefsS d limits bc items
  | some (.ref n g) =>
    let f := fetchB d limits bc n g
    match f.1 with
    | .error e => (.error e, f.2)
    | .ok (.obj .null) => (.ok [], f.2)
    | .ok (.obj (.array items)) => decodeRefsS d limits f.2 items
    | .ok body => contentPart d limits f.2 n body
  | some _ =>
    (.error (.malformed (offsetOf d page.num) "/Contents is not a stream or an array"), bc)

/-- `decodeContentsBC`: the budget never grows; the decoded parts plus the budget left are at
most the budget before. -/
theorem decodeContentsBC_total (d : OpenDoc) (limits : Limits) (bc : BC) (page : Page) :
    (decodeContentsBC d limits bc page).2.1.remaining ≤ bc.1.remaining ∧
    ∀ parts, (decodeContentsBC d limits bc page).1 = .ok parts →
      (parts.map ByteArray.size).sum + (decodeContentsBC d limits bc page).2.1.remaining ≤
        bc.1.remaining := by
  unfold decodeContentsBC
  rcases page.contents with _ | o
  · exact ⟨Nat.le_refl _, fun parts h => by
      simp only [Except.ok.injEq] at h; subst h; simp⟩
  · cases o
    case array items => exact decodeRefsS_total d limits bc items
    case ref n g =>
      simp only
      have h0 := (fetchB_sim d limits bc n g).1
      generalize fetchB d limits bc n g = F at h0 ⊢
      rcases F with ⟨f1, fb⟩
      simp only at h0 ⊢
      have key : ∀ body : IndirectBody,
          (contentPart d limits fb n body).2.1.remaining ≤ bc.1.remaining ∧
          ∀ parts, (contentPart d limits fb n body).1 = .ok parts →
            (parts.map ByteArray.size).sum + (contentPart d limits fb n body).2.1.remaining ≤
              bc.1.remaining := fun body =>
        let ⟨c1, c2⟩ := contentPart_total d limits fb n body
        ⟨Nat.le_trans c1 h0, fun parts h => Nat.le_trans (c2 parts h) h0⟩
      rcases f1 with e | (o | st)
      · exact ⟨h0, fun parts h => by cases h⟩
      · cases o
        case null =>
          exact ⟨h0, fun parts h => by simp only [Except.ok.injEq] at h; subst h; simpa using h0⟩
        case array items =>
          obtain ⟨r1, r2⟩ := decodeRefsS_total d limits fb items
          exact ⟨Nat.le_trans r1 h0, fun parts h => Nat.le_trans (r2 parts h) h0⟩
        all_goals exact key _
      · exact key _
    all_goals exact ⟨Nat.le_refl _, fun parts h => by cases h⟩

/-- **Budgeted page contents in a session** (S2, rule D3): the decoded content streams of a
page, in order, every fetch and decode charged to the session's budget. -/
def decodeContentsS (s : Session) (limits : Limits) (page : Page) :
    (Except Error (List ByteArray)) × Session :=
  let r := decodeContentsBC s.doc limits (s.budget, s.cache) page
  (r.1, ⟨s.doc, r.2.1, r.2.2⟩)

/-- **Document-wide bound for a page's contents in a session** (S3): the budget never grows,
the document is kept, and on success the decoded content streams plus the budget left are at
most the session's budget before. -/
theorem decodeContentsS_total (s : Session) (limits : Limits) (page : Page) :
    (decodeContentsS s limits page).2.budget.remaining ≤ s.budget.remaining ∧
    (decodeContentsS s limits page).2.doc = s.doc ∧
    ∀ parts, (decodeContentsS s limits page).1 = .ok parts →
      (parts.map ByteArray.size).sum + (decodeContentsS s limits page).2.budget.remaining ≤
        s.budget.remaining :=
  let ⟨h1, h2⟩ := decodeContentsBC_total s.doc limits (s.budget, s.cache) page
  ⟨h1, rfl, h2⟩

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

/-! ### Sessions (task 4.5) -/

/-- Test helper: open `contentPdf` in a session (`openDocS`) under total budget `rem` and decode
page `i`'s contents in it (`decodeContentsS`): parts or error kind, and the budget left. -/
private def pcS (i rem : Nat) : String :=
  let lim : Limits := { Limits.default with maxDecodedTotalBytes := rem }
  match openDocS lim contentPdf with
  | .error _ => "open failed"
  | .ok (doc, s) =>
    match doc.pages.toList[i]? with
    | none => "no page"
    | some p =>
      let r := decodeContentsS s lim p
      let t := match r.1 with
        | .ok parts => s!"ok {parts.map asText}"
        | .error (.limitExceeded k) => s!"limit {reprStr k}"
        | .error (.malformed _ m) => s!"err {m}"
        | .error _ => "err"
      s!"{t} rem={r.2.budget.remaining}"

-- Classic xref tables: opening and walking decode nothing, so the session budget is the whole
-- budget, and the contents are charged exactly as by `decodeContentsB`.
#guard pcS 0 9 == "ok [ABC, DEF, xyz] rem=0"
#guard pcS 0 8 == "limit SafePdf.LimitKind.decodedTotalBytes rem=2"
#guard pcS 1 100 == "ok [ABC] rem=97"
-- `openDocS` walks the same page tree as `openDoc`.
#guard (match openDocS Limits.default threePages, openDoc Limits.default threePages with
  | .ok (d1, s), .ok d2 =>
    d1.pages.toList.map Page.num == d2.pages.toList.map Page.num &&
      s.budget.remaining == Limits.default.maxDecodedTotalBytes
  | _, _ => false)
-- `decodeStreamS` on a non-stream object.
#guard (match openDocS Limits.default contentPdf with
  | .ok (_, s) => match (decodeStreamS s Limits.default 7 0).1 with
    | .error (.malformed _ "not a stream") => true
    | _ => false
  | .error _ => false)


end Tests

end SafePdf.Core.Doc
